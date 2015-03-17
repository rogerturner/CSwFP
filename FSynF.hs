module FSynF where

import Data.List

data Column = A' | B' | C' | D' | E' 
            | F' | G' | H' | I' | J'
              deriving (Eq,Ord,Show,Enum)

type Row    = Int 
type Attack = (Column,Row) 

data Ship = Battleship | Frigate | Submarine | Destroyer 
            deriving Show

data Reaction = Missed | Hit Ship | Sunk Ship
                deriving Show 

type Turn = (Attack,Reaction) 

data Defeat = LostBattle deriving Show

type Surrender = (Attack, Defeat)

data Game = S Surrender | T Turn Game deriving Show

-------------------------------------------------------------------------------

data Colour   = Red | Yellow | Blue | Green | Orange 
                deriving (Eq,Show,Bounded,Enum)

data Answer   = Black | White deriving (Eq,Show)

type Pattern  = [Colour]
type Feedback = [Answer] 

data Sent = Sent NP VP deriving Show
data NP   = SnowWhite  | Alice  | Dorothy | Goldilocks 
          | LittleMook | Atreyu | Everyone | Someone
          | NP1 DET CN | NP2 DET RCN 
          deriving Show
data DET  = The | Every | Some | No | Most
          deriving Show
data CN   = Girl   | Boy   | Princess | Dwarf | Giant 
          | Wizard | Sword | Dagger
          deriving Show 
data ADJ  = Fake deriving Show
data RCN  = RCN1 CN That VP | RCN2 CN That NP TV
          | RCN3 ADJ CN
          deriving Show
data That = That deriving Show
data VP   = Laughed | Cheered | Shuddered 
          | VP1 TV NP | VP2 DV NP NP
          | VP3 AV To INF
          deriving Show 
data TV   = Loved   | Admired | Helped 
          | Defeated | Caught
          deriving Show 

data DV   = Gave deriving Show
data AV   = Hoped | Wanted deriving Show 
data INF  = Laugh | Sheer | Shudder | INF TINF NP deriving Show
data TINF = Love | Admire | Help | Defeat | Catch 
            deriving Show 
data To   = To deriving Show

-------------------------------------------------------------------------------

data Form =  P String | Ng Form | Cnj [Form] | Dsj [Form] 
            deriving Eq

instance Show Form where 
 show (P name) = name 
 show (Ng  f)  = '-': show f
 show (Cnj fs) = '&': show fs
 show (Dsj fs) = 'v': show fs

form1, form2 :: Form
form1 = Cnj [P "p", Ng (P "p")]
form2 = Dsj [P "p1", P "p4", P "p3", Cnj [P "p2", P "p3"]]

-- Ex 4.12
opsNr :: Form -> Int
opsNr (P   _)  = 0
opsNr (Ng  f)  = opsNr f + 1
opsNr (Cnj fs) = sum (map opsNr fs) + 1
opsNr (Dsj fs) = sum (map opsNr fs) + 1

-- Ex 4.13
depth :: Form -> Int
depth (P   _)  = 0
depth (Ng  f)  = opsNr f + 1
depth (Cnj []) = 1
depth (Cnj fs) = maximum (map depth fs) + 1
depth (Dsj []) = 1
depth (Dsj fs) = maximum (map depth fs) + 1

-- Ex 4.14
propNames :: Form -> [String]
propNames (P   s)  = [s]
propNames (Ng  f)  = propNames f
propNames (Cnj fs) = sort $ nub $ concatMap propNames fs
propNames (Dsj fs) = sort $ nub $ concatMap propNames fs

-------------------------------------------------------------------------------

type Name     = String 
type Index    = [Int]
data Variable = Variable Name Index deriving (Eq,Ord)

instance Show Variable where 
  show (Variable name [])  = name
  show (Variable name [i]) = name ++ show i
  show (Variable name is ) = name ++ showInts is
     where showInts []     = "" 
           showInts [i]    = show i  
           showInts (i:is) = show i ++ "_" ++ showInts is

x, y, z :: Variable
x = Variable "x" []
y = Variable "y" []
z = Variable "z" []

data Formula a = Atom String [a]
               | Eq a a
               | Neg  (Formula a)
               | Impl (Formula a) (Formula a) 
               | Equi (Formula a) (Formula a)
               | Conj [Formula a]
               | Disj [Formula a] 
               | Forall Variable (Formula a)
               | Exists Variable (Formula a)
               deriving Eq

instance Show a => Show (Formula a) where 
  show (Atom s [])   = s
  show (Atom s xs)   = s ++ show xs 
  show (Eq t1 t2)    = show t1 ++ "==" ++ show t2
  show (Neg form)    = '~' : (show form)
  show (Impl f1 f2)  = "(" ++ show f1 ++ "==>" 
                           ++ show f2 ++ ")"
  show (Equi f1 f2)  = "(" ++ show f1 ++ "<=>" 
                           ++ show f2 ++ ")"
  show (Conj [])     = "true" 
  show (Conj fs)     = "conj" ++ show fs 
  show (Disj [])     = "false" 
  show (Disj fs)     = "disj" ++ show fs 
  show (Forall v f)  = "A " ++  show v ++ (' ' : show f)
  show (Exists v f)  = "E " ++  show v ++ (' ' : show f)

formula0 = Atom "R" [x,y]
formula1 = Forall x (Atom "R" [x,x])
formula2 = Forall x 
            (Forall y
              (Impl (Atom "R" [x,y]) (Atom "R" [y,x])))

-------------------------------------------------------------------------------

-- Ex 4.18

canon = sort . nub

freeIn :: Formula Variable -> [Variable]
freeIn (Atom _ xs)   = canon xs
freeIn (Eq x y)      = canon [x,y]
freeIn (Neg f)       = canon $ freeIn f
freeIn (Impl f1 f2)  = canon $ freeIn f1 ++ freeIn f2
freeIn (Equi f1 f2)  = canon $ freeIn f1 ++ freeIn f2
freeIn (Conj fs)     = canon $ concatMap freeIn fs
freeIn (Disj fs)     = canon $ concatMap freeIn fs
freeIn (Forall x f)  = delete x (canon $ freeIn f)
freeIn (Exists x f)  = delete x (canon $ freeIn f)

closedForm :: Formula Variable -> Bool
closedForm f = freeIn f == []

-- Ex 4.19

withoutIDs :: Formula Variable -> Formula Variable
withoutIDs (Neg f)      = Neg (withoutIDs f)
withoutIDs (Impl f1 f2) = Disj [Neg (withoutIDs f1), withoutIDs f2]
withoutIDs (Equi f1 f2) = Conj [Disj [Neg (withoutIDs f1), withoutIDs f2],
                                Disj [Neg (withoutIDs f2), withoutIDs f1]]
withoutIDs (Conj fs)    = Conj (map withoutIDs fs)
withoutIDs (Disj fs)    = Disj (map withoutIDs fs)
withoutIDs (Forall x f) = Forall x (withoutIDs f)
withoutIDs (Exists x f) = Exists x (withoutIDs f)
withoutIDs f            = f

formula3 = Forall x
             (Impl (Atom "R" [x]) (Exists y 
               (Equi (Atom "R" [x]) (Atom "S" [y]))))
               
-- Ex 4.20

nnf :: Formula Variable -> Formula Variable
nnf (Neg (Neg f))      = nnf f
nnf (Neg (Impl f1 f2)) = nnf (Neg (withoutIDs (Impl f1 f2)))
nnf (Neg (Equi f1 f2)) = nnf (Neg (withoutIDs (Equi f1 f2)))
nnf (Neg (Forall x f)) = Exists x (nnf (Neg f))
nnf (Neg (Exists x f)) = Forall x (nnf (Neg f))
nnf (Neg (Conj fs))    = Disj $ map (nnf . Neg) fs
nnf (Neg (Disj fs))    = Conj $ map (nnf . Neg) fs
nnf f                  = f

-------------------------------------------------------------------------------

data Term = Var Variable | Struct String [Term] 
            deriving (Eq,Ord)

instance Show Term where 
  show (Var v)       = show v 
  show (Struct s []) = s
  show (Struct s ts) = s ++ show ts

tx, ty, tz :: Term 
tx = Var x
ty = Var y
tz = Var z

isVar :: Term -> Bool
isVar (Var _) = True
isVar _       = False

varsInTerm :: Term -> [Variable]
varsInTerm (Var v)       = [v]
varsInTerm (Struct s ts) = varsInTerms ts

varsInTerms :: [Term] -> [Variable]
varsInTerms = canon . concatMap varsInTerm

-------------------------------------------------------------------------------

-- Ex 4.22

varsInForm :: Formula Term -> [Variable]
varsInForm (Atom _ ts)  = varsInTerms ts
varsInForm (Eq t1 t2)   = canon (varsInTerm t1 ++ varsInTerm t2)
varsInForm (Neg f)      = varsInForm f
varsInForm (Impl f1 f2) = canon (varsInForm f1 ++ varsInForm f2)
varsInForm (Equi f1 f2) = canon (varsInForm f1 ++ varsInForm f2)
varsInForm (Conj fs)    = canon $ concatMap varsInForm fs
varsInForm (Disj fs)    = canon $ concatMap varsInForm fs
varsInForm (Forall x f) = varsInForm f
varsInForm (Exists x f) = varsInForm f

txy = Struct "T" [tx,ty]
formula4 = (Neg (Atom "U" [tz,txy]))
formula5 = Forall x (Impl (Atom "R" [tx]) formula4)
               
