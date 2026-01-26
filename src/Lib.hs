module Lib (module Lib) where

import Data.List (intercalate)
import Control.Monad (unless)
import Prelude hiding (id)
import Data.Map.Strict (Map, singleton, insert, delete, toList, keys)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Bifunctor (second)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Function (id)

type Sym = String
type Levels = Map Sym Int
data AsT = One | Two deriving Eq
type Type i = Expr i
type Erased = Bool
initialErased :: Erased
initialErased = False
type Depth = Int
data Expr i
    = LevelT -- Type for unvirse level
    | Level Sym Int -- Constructor of a level
    | Universe Levels -- Universe where the level is the max of each Sym+Int
    | Lam i (Erased, Sym, Type i) (Expr i) -- Dependent lambda
    | App (Expr i) (Erased, Expr i) -- Application
    | InterT (Sym, Expr i) (Expr i) -- Depedent intersection type
    | Inter (Expr i) (Expr i) -- Dependent intersection term
    | As (Expr i) AsT -- Term of a dependent intersection with either the first or second type depending on the value of `Inter`
    | Let Sym Depth (Type i) (Expr i) (Expr i)
    | Symbol Sym -- Symbol
    deriving Eq

app :: Expr i -> Expr i -> Expr i
app f x = App f (False,x)

app' :: Expr i -> Expr i -> Expr i
app' f x = App f (True,x)

isSymbol :: Sym -> Expr i -> Bool
isSymbol s (Symbol s') = s == s'
isSymbol _ _ = False

instance Show AsT where
    show One = "1"
    show Two = "2"

instance Show (Expr i) where
    show val = show' val 0

show' :: Expr i -> Int -> String
show' LevelT _ = "#L"
show' (Level s i) _ = s ++ "+" ++ show i
show' (Universe l) _ = "#U " ++ showL l
show' (Lam _ (er, s, t) e) d
    | null s = "(" ++ show' t d ++ erasedEnd er ++ " " ++ show' e d
    | isSymbol "" t = s ++ " :-> " ++ show' e d -- only supposed to be produced by erasing so there is no point in showing the erasure as it was removed
    | otherwise = erasedStart er ++ s ++ ": " ++ show' t d ++ erasedEnd er ++ " " ++ show' e d
show' (App f@(Lam _ (_, _, _) _) x) d = "[" ++ show' f d ++ "] " ++ showApp x d
show' (App f x) d = show' f d ++ " " ++ showApp x d
show' (InterT (s, t1) t2) d = "(" ++ s ++ ": " ++ show' t1 d ++ " /\\ " ++ show' t2 d ++ ")"
show' (Inter e1 e2) d = show' e1 d ++ " ^ " ++ show' e2 d
show' (As e i) d = show' e d ++ "." ++ show i
show' (Let s _d t v e) d = "@" ++ s ++ ": " ++ show' t d ++ " = " ++ show' v (d+1) ++ ";" ++ showNewLine d ++ show' e d
show' (Symbol s) _ = s

erasedStart, erasedEnd :: Bool -> String
erasedStart False = "("
erasedStart True = "<"
erasedEnd False = ")"
erasedEnd True = ">"

showNewLine :: Int -> String
showNewLine 0 = "\n"
showNewLine _ = ""

showErrasure :: Erased -> String
showErrasure True = "'"
showErrasure False = ""

showApp :: (Erased, Expr i) -> Int -> String
showApp (er, l@(Lam {})) d = showErrasure er ++ "[" ++ show' l d ++ "]"
showApp (er, App f x) d = showErrasure er ++ "[" ++ show' f d ++ " " ++ showApp x d ++ "]"
showApp (er,e) d = showErrasure er ++ show' e d

showL :: Levels -> String
showL m = showm (toList m)
    where
        showm [] = ""
        showm [(l, i)] = showU l i
        showm lis = "max(" ++ intercalate "," (uncurry showU <$> lis) ++ ")"

showU :: Sym -> Int -> String
showU l i
    | null l =  show i
    | i == 0 =  l
    | otherwise =  l ++ "+" ++ show i

freeVars :: Expr i -> Set Sym
freeVars LevelT = Set.empty
freeVars (Level s _) = Set.singleton s
freeVars (Universe ls) = Set.fromList $ keys ls
freeVars (Lam _ (_, s, t) e) = freeVars t <> Set.delete s (freeVars e)
freeVars (App f (_, a)) = freeVars f <> freeVars a
freeVars (InterT (s, t1) t2) = freeVars t1 <> Set.delete s (freeVars t2)
freeVars (Inter e1 e2) = freeVars e1 <> freeVars e2
freeVars (As e _i) = freeVars e
freeVars (Let s _d t v e) = freeVars t <> freeVars v <> Set.delete s (freeVars e)
freeVars (Symbol s) = Set.singleton s

nf :: Env i -> Expr i -> Expr i
nf env expr = spine expr []
    where
        spine (Lam i (er, s, t) e) [] = Lam i (er, s, nf env t) (nf env e)
        spine (Lam _ (_, s, _t) e) ((_,x):xs) = spine (subst s x e) xs
        spine (App f x) xs = spine f (x:xs)
        spine (InterT (s, t1) t2) [] = InterT (s, nf env t1) (nf env t2)
        spine (Inter e1 e2) [] = Inter (nf env e1) (nf env e2)
        spine (As e i) [] = As (nf env e) i
        spine (Let s d t v e) xs = spine (subst s (replaceBody d t (const v)) e) xs
        spine (Symbol s) xs = case findVar env s of
            Right (Def, _, _, v) -> spine v xs
            _ -> fapp (Symbol s) xs
        spine f xs = fapp f xs
        fapp f xs = foldl App f (map (second (nf env)) xs)
whnf :: Expr i -> Expr i
whnf expr = spine expr []
    where
        spine (Lam _ (_, s, _t) e) ((_,x):xs) = spine (subst s x e) xs
        spine (App f x) xs = spine f (x:xs)
        spine (Let s d t v e) xs = spine (subst s (replaceBody d t (const v)) (whnf e)) xs
        spine f xs = fapp f xs
        fapp f xs = foldl App f (map (second whnf) xs)

subst :: Sym -> Expr i -> Expr i -> Expr i
subst "" _x = id -- if the symbol is empty, no substitution is done
subst s x = sub
    where
        sub LevelT = LevelT
        sub l@(Level s' i) = case x of
            Symbol l' -> if s' == s then Level l' i else l
            Level s'' i' -> if s' == s then Level s'' (i+i') else l
            _ -> l
        sub ul@(Universe ls) = case x of
            Symbol l -> case Map.lookup s ls of
                Just i -> Universe (insert l i $ delete s ls)
                Nothing -> ul
            Level s' i' -> case Map.lookup s ls of
                Just i -> Universe (insert s' (i+i') $ delete s ls)
                Nothing -> ul
            _ -> ul
        sub (Lam i (er, s', t') e')
          | s == s' = Lam i (er, s', sub t') e'
          | s' `elem` fsx =
            let s'' = newSym e' s'
                e'' = substVar s' s'' e'
            in Lam i (er, s'', sub t') (sub e'')
          | otherwise = Lam i (er, s', sub t') (sub e')
        sub (App f (er,x')) = App (sub f) (er,sub x')
        sub (InterT (s', t1) t2)
          | s == s' = InterT (s', sub t1) t2
          | s' `elem` fsx =
            let s'' = newSym t2 s'
                e'' = substVar s' s'' t2
            in InterT (s'', sub t1) (sub e'')
          | otherwise = InterT (s', sub t1) (sub t2)
        sub (Inter e1 e2) = Inter (sub e1) (sub e2)
        sub (As e i) = As (sub e) i
        sub (Let s' d t v e')
          | s == s' = Let s' d (sub t) (sub v) e'
          | s' `elem` fsx =
            let s'' = newSym e' s'
                e'' = substVar s' s'' e'
            in Let s'' d (sub t) (sub v) (sub e'')
          | otherwise = Let s' d (sub t) (sub v) (sub e')
        sub v@(Symbol s') = if s == s' then x else v

        fsx = freeVars x
        newSym e' s' = loop s'
            where
                loop s'' = if s'' `elem` vars then loop (s' ++ "'") else s''
                vars = fsx <> freeVars e'

substVar :: Sym -> Sym -> Expr i -> Expr i
substVar s s' = subst s (Symbol s')

data Direction = Symmetric | Directional Status

alphaEq :: Expr i -> Expr i -> Bool
alphaEq LevelT LevelT = True
alphaEq (Level s i) (Level s' i') = s == s' && i == i'
alphaEq (Universe ls) (Universe ls') = ls == ls'
alphaEq (Lam _ (er, s, t) e) (Lam _ (er', s', t') e') = er == er' && alphaEq e (substVar s' s e') && alphaEq t t'
alphaEq (App f (er,x)) (App f' (er',x')) = er == er' && alphaEq f f' && alphaEq x x'
alphaEq (InterT (s, t1) t2) (InterT (s', t1') t2') = alphaEq t2 (substVar s' s t2') && alphaEq t1 t1'
alphaEq (Inter e1 e2) (Inter e1' e2') = alphaEq e1 e1' && alphaEq e2 e2'
alphaEq (As e i) (As e' i') = alphaEq e e' && i == i'
alphaEq (Let s d t v e) e' = alphaEq (subst s (replaceBody d t (const v)) e) e'
alphaEq e (Let s d t v e') = alphaEq e (subst s (replaceBody d t (const v)) e')
alphaEq (Symbol s) (Symbol s') = s == s'
alphaEq _ _ = False

-- first value correspond to the expected level, so the largest one in the case of cumulative universes
universeValid :: Levels -> Levels -> Bool
universeValid l1 l2 = fromMaybe False (req (toList l2))
    where
        req [] = Nothing
        req [l] = iner l
        req (l:ls) = iner l >>= \b -> (b||) <$> req ls
        iner (l, i) = (i<=) <$> Map.lookup l l1

betaEq :: Env i -> Expr i -> Expr i -> Bool
betaEq env e1 e2 = alphaEq (nf env e1) (nf env e2)

erased :: Expr i -> Expr i
erased LevelT = LevelT
erased (Level s i) = Level s i
erased (Universe ls) = Universe ls
erased (Lam _i (True, _s, _t) e) = erased e
erased (Lam i (False, s, _t) e) = Lam i (False, s, Symbol "") (erased e)
erased (App f (True,_x)) = erased f
erased (App f (False,x)) = App (erased f) (False,erased x)
erased (InterT (s, t1) t2) = InterT (s, erased t1) (erased t2)
erased (Inter e1 _e2) = erased e1
erased (As e _i) = erased e
erased (Let s d t v e) = erased $ subst s (replaceBody d t (const v)) e
erased (Symbol s) = Symbol s

erasedBetaEq :: Env i -> Expr i -> Expr i -> Bool
erasedBetaEq env e1 e2 = alphaEq (erased . nf env $ e1) (erased . nf env $ e2)

data IsDef = Def | Local deriving (Show)
newtype Env i = Env (Map Sym (IsDef, Status, Erased, Expr i)) deriving (Show)

initialEnv :: Env i
initialEnv = Env Map.empty

extend :: Env i -> Sym -> IsDef -> Status -> Erased -> Type i -> Env i
extend env@(Env ls) s isDef status er t = Env $ Map.insert s (isDef, status, er, nf env t) ls

type ErrorMsg = String
type TC a = Either ErrorMsg a
throwError :: String -> TC a
throwError = Left

findVar :: Env i -> Sym -> TC (IsDef, Status, Erased, Expr i)
findVar (Env ls) s =
    case Map.lookup s ls of
        Just j -> return j
        Nothing -> throwError $ "Cannot find variable " ++ s

validTyping :: Show i => Env i -> Expr i -> Expr i -> Expr i -> Bool
validTyping env vt1 vt2 ve2 = valid env (nf env vt1) (nf env vt2) (nf env ve2)
    where
        blank = Symbol "@"
        valid _ LevelT LevelT _ = True
        valid _ (Level s i) (Level s' i') _ = s == s' && i >= i'
        valid _ (Universe ls) (Universe ls') _ = universeValid ls ls'
        valid env' (Universe ls) e _ = either (const False) (universeValid ls) (universe env' e)
        valid env' (Lam _ (er, s, t) e) (Lam _ (er', s', t') e') (Lam _ (_er'', s'', t'') e'') = er == er' && valid (extend env' s Local SType er t) e (substVar s' s e') (substVar s'' s e'') && valid env' t t' t''
        valid env' (Lam _ (er, s, t) e) (Lam _ (er', s', t') e') e'' = er == er' && valid (extend env' s Local SType er t) e (substVar s' s e') e'' && valid env' t t' e''
        valid env' (App f (er,x)) (App f' (er',x')) e'' = er == er' && valid env' f f' e''  && valid env' x x' e''
        valid env' (InterT (s, t1) t2) (InterT (_s', t1') t2') (Inter e1 _e2) = valid env' (subst s e1 t2) t2' blank && valid env' t1 t1' blank
        valid env' (InterT (s, t1) t2) (InterT (s', t1') t2') e'' =  let env'' = extend env' s Local SType False t1 in
            valid env'' t2 (substVar s' s t2') e'' && valid env' t1 t1' e''
        valid env' (Inter e1 e2) (Inter e1' e2') e'' = valid env' e1 e1' e'' && valid env' e2 e2' e''
        valid env' (As e i) (As e' i') e'' = valid env' e e' e'' && i == i'
        valid env' (Let s d t v e) e' e'' = valid env' (subst s (replaceBody d t (const v)) e) e' e''
        valid env' e (Let s d t v e') e'' = valid env' e (subst s (replaceBody d t (const v)) e') e''
        valid env' e e' (Let s d t v e'') = valid env' e e' (subst s (replaceBody d t (const v)) e'')
        valid _ (Symbol s) (Symbol s') _ = s == s'
        valid _ _ _ _ = False

universe :: Show i => Env i -> Expr i -> TC Levels
universe _ LevelT = return $ singleton "" 0
universe _ (Level s i) = throwError $ "The term \"" ++ s ++ "+" ++ show i ++ ")\" does not have a universe."
universe _ (Universe ls) = return ((+1) <$> ls)
universe env (Lam _ (er, s, t) e) = do
    u1 <- universe env t
    u2 <- universe (extend env s Local undefined er t) e
    return $ maxLevel u1 u2
universe env (App f _) = universe env f
universe env (InterT (s, t1) t2) = do
    u1 <- universe env t1
    u2 <- universe (extend env s Local undefined False t1) t2
    return $ maxLevel u1 u2
universe env (Inter e1 e2) = do
    u1 <- universe env e1
    u2 <- universe env e2
    return $ maxLevel u1 u2
universe env (As e _i) = universe env e
universe env (Let s d t v e) = universe env (subst s (replaceBody d t (const v)) e)
universe env (Symbol s) = findVar env s >>= ((((+(-1)) <$>) <$>) . universe env) . (\(_,_,_,x) -> x)

data Status = SExpr | SType | SUniverse deriving (Show, Eq)
downgrade :: Status -> Status
downgrade SUniverse = SType
downgrade SType = SExpr
downgrade SExpr = SExpr

tCheck :: Show i => Env i -> Erased -> Expr i -> TC (Status, Expr i)
tCheck _ _cer LevelT = let l = singleton "" 0 in return (SType, Universe l)
tCheck env _cer (Level s _i) = do
    v <- findVar env s
    case v of
        (_, isT, _er, LevelT) -> return (isT, LevelT)
        t -> throwError $ "The symbol in a level expression must be a \"#l\", found \"" ++ show t ++ "\""
tCheck _ _cer (Universe ls) = do
    -- FIXME should check that all the symbols in ls are in the environement and are of type #L
    let l = (+1) <$> ls in return (SUniverse, Universe l)
tCheck env cer (Lam i (er, s, t) e) = do
    (isT, tt) <- tCheck env True t
    case isT of
        SExpr -> throwError $ "The type of a type must be a universe, which is not the case for \"[" ++ s ++ ": " ++ show t ++ "]: " ++ show tt ++ "\", " ++ show isT ++ " ."
        _ -> do
            let env' = extend env s Local (downgrade isT) er t
            (isT', te) <- tCheck env' cer e
            return (isT', Lam i (er, s, t) te)
tCheck env cer (App f (er,x)) = do
    (isT, tf) <- tCheck env cer f
    case whnf tf of
        Lam _i (er', s, t) b -> do
            unless (er == er') $ throwError $ "In application the erasure must match and be specified manually, erasures \n" ++ show t ++ ",\n" ++ showErrasure er ++ show x ++ "\ndiffer."
            (_isT', tx) <- tCheck env (er || cer) x
            unless (validTyping env t tx x) $ throwError $ "Bad function argument type:\n" ++ show (nf env t) ++ ": U " ++ show (universe env t) ++ ",\n" ++ show (nf env tx) ++ ": U " ++ show (universe env tx) ++ "\nin " ++ show (App f (er,x)) ++ "."
            return (isT, subst s x b)
        e -> throwError $ "Non-function in application (" ++ show (App f (er,x)) ++ "): " ++ show e ++ "."
tCheck env _cer (InterT (s, t1) t2) = do
    (statusT1, tt1) <- tCheck env True t1
    case statusT1 of
        SExpr -> throwError $ "The type of a type must be a universe, which is not the case for \"[" ++ s ++ ": " ++ show t1 ++ "]: " ++ show tt1 ++ "\"."
        _ -> do
            let env' = extend env s Local (downgrade statusT1) False t1
            (isT', tt2) <- tCheck env' True t2
            return (isT', InterT (s, t1) tt2)
tCheck env cer (Inter e1 e2) = do
    unless (erasedBetaEq env e1 e2) $ throwError $ "To construct a term of an intersection, one term of each types must be provided and have the same erasure. The term:\n" ++ show e1 ++ "\nand\n" ++ show e2 ++ "\nhave different erasure:\n" ++ show (erased e1) ++ ",\n" ++ show (erased e2)
    (isT1, t1) <- tCheck env cer e1
    (isT2, t2) <- tCheck env cer e2
    unless (isT1 == isT2) $ throwError $ "The status of both terms in the constructor for an intersection must have the same status, found \"" ++ show isT1 ++ " != " ++ show isT2 ++ "\""
    return (isT2, InterT ("", t1) t2)
tCheck env cer (As e i) = do
    (isT, te) <- tCheck env cer e
    case te of
        (InterT (s, t1) t2) -> case i of
            One -> return (isT, t1)
            Two -> return (isT, subst s (As e One) t2)
        t -> throwError $ "The post-fix operator to access a dependent intersection must be applied to a term whose type is a dependent intersection, provided:\n" ++ show (As e i) ++ ": " ++ show t
tCheck env cer (Let s d t v e) = do
    let rv = replaceBody d t (const v)
    (isT', _tt) <- tCheck env True t
    (_isT, te) <- tCheck env (cer || isT' == SUniverse) rv
    unless (validTyping env t te rv) $ case (nf env t, nf env rv) of
        (InterT (s', t1) t2, Inter e1 _e2) -> throwError $ "Type missmatch:\n" ++ show (InterT (s', t1 ) (subst s' (nf env e1) (nf env t2))) ++ ",\n" ++ show (nf env te) ++ "\n."
        _ -> throwError $ "Type missmatch:\n" ++ show (nf env t) ++ ",\n" ++ show (nf env te) ++ "\n." --"in " ++ show (t ::> e) ++ "."
    tCheck (extend env s Def (downgrade isT') False rv) cer e
tCheck env cer (Symbol s) = findVar env s >>= \(isd, st, er, t) -> if cer || not er
    then case isd of
        Local -> return (st, t)
        Def -> tCheck env cer t
    else throwError $ "An errased value can only be used in an erased context: " ++ show s ++ " is declared to be erased."

lamDepth :: Expr i -> Int
lamDepth (Lam _ _ body) = 1 + lamDepth body
lamDepth _ = 0

replaceBody :: Depth -> Expr i -> (Expr i -> Expr i) -> Expr i
replaceBody 0 body f = f body
replaceBody d (Lam i (er, s, t) body) f = Lam i (er, s, t) (replaceBody (d - 1) body f)
replaceBody _ _ _ = undefined

maxLevel :: Levels -> Levels -> Levels
maxLevel l1 l2 = lmax l1 (toList l2)
    where
        lmax acc [] = acc
        lmax acc ((l, i):ls) = lmax (Map.insertWith max l i acc) ls

typeCheck :: Show i => Expr i -> TC (Expr i)
typeCheck = (snd <$>) . tCheck initialEnv initialErased

showLam :: Show i => Sym -> Expr i -> IO ()
showLam s lam = do
    putStrLn $ s ++ " =\n" ++ show lam
    putStrLn $ s ++ " e= " ++ show (erased lam)
    case typeCheck lam of
        Right t -> do
         putStrLn $ s ++ " :: " ++ show t ++ " | " ++ case universe initialEnv t of
            Right ls -> show (Universe ls :: Expr ())
            Left err -> show err
         putStrLn $ s ++ " e.nf= " ++ show (erased . nf initialEnv $ lam)
        Left err -> putStrLn $ s ++ ": " ++ err

typeCheckVar :: Show i => Expr i -> Expr i -> TC Bool
typeCheckVar ty var = do
    let env = initialEnv
    (_isT, tv) <- tCheck env initialErased var
    return $ validTyping env ty tv var

-- lv :: Sym -> Int -> Levels
-- lv = singleton

-- ui :: Int -> Expr
-- ui i = U (singleton "" i)
-- us :: Sym -> Expr
-- us l = U (singleton l 0)
-- u :: Sym -> Int -> Expr
-- u l i = U (singleton l i)

-- id' :: Expr
-- id' = ("i", L) :-> ("t", us "i") :-> ("x", S "t") :-> S "t" ::> S "x"
-- higher :: Expr
-- higher = ("f", ("t", ui 1) :-> ("", S "t") :-> S "t") :-> S "f"
-- bigger :: Expr
-- bigger = ("f", ("t", ui 1) :-> ("r", ui 4) :-> S "r") :-> S "f"
-- level :: Expr
-- level = ("i", L) :-> ("T", us "i") :-> ("t", S "T") :-> S "T" ::> S "t"
-- false :: Expr
-- false = ("i", L) :-> ("T", us "i") :-> us "i" ::> S "T"
-- maxleveli :: Expr
-- maxleveli = ("i", L) :-> ("Ti", us "i") :-> ("j", L) :-> ("Tj", us "j") :-> U (maxLevel (lv "i" 0) (lv "j" 0)) ::> S "Ti"
-- maxlevelj :: Expr
-- maxlevelj = ("i", L) :-> ("Ti", us "i") :-> ("j", L) :-> ("Tj", us "j") :-> U (maxLevel (lv "i" 0) (lv "j" 0)) ::> S "Tj"
-- invalideLevel :: Expr
-- invalideLevel = ("T", ui 0) :-> ("t", S "T") :-> ("w", S "t") :-> S "w"
-- invalidType :: Expr
-- invalidType = ("T", ui 0) :-> ("T1", ("t", S "T") :-> S "t") :-> S "T1"

-- someFunc :: IO ()
-- someFunc = do
--     showLam "id" id'
--     showLam "i:+1" $ ("i", L) :-> id' :@ "i" :+ 1
--     showLam "higher" higher
--     showLam "bigger" bigger
--     showLam "r" $ ui 1
--     showLam "test"  $ nf $ ("i", L) :-> ("r", us "i") :-> ("l", S "r") :-> id' :@ S "i" :@ S "r" :@ S "l"
--     showLam "level" level
--     showLam "false" false
--     showLam "maxleveli" maxleveli
--     showLam "maxlevelj" maxlevelj
--     showLam "invalideLevel" invalideLevel
--     showLam "invalidType" invalidType
--     showLam "validErased" $ ("i", Erased L) :-> ("T", us "i") :-> ("t", S "T" ) :-> S "T" ::> S "t"
--     showLam "invalidErased" $ ("i", Erased L) :-> ("T", us "i") :-> ("t", S "T" ) :->  L ::> S "i"
--     print $ betaEq (("", S "t") :-> S "t") (("", S "t") :-> S "t")
--     print $ typeCheckVar (("t", ui 1) :-> ("", S "t") :-> S "t") (("r", ui 1) :-> ("x", S "r") :-> S "x")

