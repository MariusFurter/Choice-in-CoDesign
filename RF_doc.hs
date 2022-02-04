{-|
Module      : RF
Description : A Module by Prof. Alberto Cattaneo implementing definitions from the "Choice in CoDesign" report by Marius Furter (available in git repository JonathanLorand/proj-sp-furter/report).

This module was written by Prof. Alberto Cattaneo and was annotated by Marius Furter. 

WARNING: The conventions used here differ from the report:
- The relation (.>=) used here corresponds to the relation (->) in the report. For example (3 .>= 2) here and (3 -> 2) in the report. 
- Here feasibility relations a -|-> b are viewed as maps a x b^op -> Bool := {True .>= False}, while in the report we view them as monotone maps a^op x b -> Bool := {False -> True}. Observe that Bool here is the opposite version of Bool in the report.
- Here upper and lower sets are taken with respect to (.>=). For example, [1,2] is upward closed in [1,2,3].
- With respect to (.>=), upper sets are ordered by containment, and lower sets by inclusion.
-}

module RF
where

{- |The PO type class implements partial ordering by mapping pairs of type a to Maybe Bool:
    weak inequalities (.<=), (.>=) 
    equality (.==)
    strict inequalities (.<), (.>).
-}
class PO a where
  (.<=) :: a -> a -> Maybe Bool
  
  (.>=) :: a -> a -> Maybe Bool
  a .>= a' = a' .<= a

  (.==) :: a -> a -> Maybe Bool
  a .== a' = (&&) <$>  (a .<= a') <*>  (a' .<= a)

  (./=) :: a -> a -> Maybe Bool
  a ./= a' = not <$> (a .== a')

  (.<) :: a -> a -> Maybe Bool
  a .< a' = (&&) <$> a .<= a' <*> (a ./= a')
  
  (.>) :: a -> a -> Maybe Bool
  a .> a' = (&&) <$>  a' .<= a <*> (a ./= a')

-- |Test if x .>= y and return Bool.
ge :: PO a => a -> a -> Bool
ge x y = x .>= y == Just True


-- Examples of partial ordering --
-- Groceries
data Grocery = BagOfCarrots | Carrot | Potato
  deriving (Show,Eq)

instance PO Grocery where
   Potato .<= Potato             = Just True
   Carrot .<= Carrot             = Just True
   Carrot .<= BagOfCarrots       = Just True
   BagOfCarrots .<= BagOfCarrots = Just True
   BagOfCarrots .<= Carrot       = Just False
   _ .<= _ = Nothing

-- Restaurant
data Restaurant = Curry | Casserole | Chicken | Beef
  deriving (Show,Eq)
  
instance PO Restaurant where
  x .<= y
    | x == y    = Just True
    | otherwise = Nothing

-- Number Systems as PO's.
instance PO Int where
  m .<= n = Just (m <= n)

instance PO Integer where
  m .<= n = Just (m <= n)

instance PO Double where
  m .<= n = Just (m <= n)

instance PO Float where
  m .<= n = Just (m <= n)

instance PO Bool where
  m .<= n = Just (m <= n)

-- New type used to inherit partial ordering from Ord.
newtype Po a = Po a
  deriving (Show, Eq)

-- Any instance of Ord as PO.
instance Ord a => PO (Po a) where
  Po x .<= Po y = Just (x <= y)

data MiniTree = N1 | NL | NR
  deriving (Show, Eq)
  
instance PO MiniTree where
  N1 .<= N1 = Just True
  NL .<= NL = Just True
  NR .<= NR = Just True
  N1 .<= NL = Just True
  N1 .<= NR = Just True
  _ .<= _ = Just False

-- Feasibility relations (Report Sec. 2.2) --

-- |Rel a b represents a relation a -|-> b.
newtype Rel a b =  Rel ([(a,b)],[a],[b])
  deriving Show

-- |Check if a relation is a feasibility relation.
isFeasRel :: (PO a, Eq a, PO b, Eq b) => Rel a b -> Bool
isFeasRel (Rel (p, xs, ys)) = null [(x,y) | (r,f) <- p, x <- xs, y <- ys, x .>= r == Just True, f .>= y == Just True, not (elem (x,y) p)] 

-- Examples
phi :: Rel Int Grocery
phi = Rel ([(3,BagOfCarrots),(3,Carrot),(2,Carrot),(1,Carrot),(1,Potato),(2,Potato),(3,Potato)],[3,2,1,0], [BagOfCarrots, Carrot, Potato])

phi' :: Rel (Po Int) Grocery
phi' = Rel ([(Po 3,BagOfCarrots),(Po 3,Carrot),(Po 2,Carrot),(Po 1,Carrot),(Po 1,Potato),(Po 2,Potato),(Po 3,Potato)],map Po [3,2,1,0], [BagOfCarrots, Carrot, Potato])


-- Set-theoretical constructions --

-- |Check if xs is subset of ys.
isSubset :: Eq a => [a] -> [a] -> Bool
isSubset [] _ = True
isSubset (x:xs) ys = elem x ys && isSubset xs ys

-- |Order lists of xs by inclusion in PO.
instance Eq a => PO [a] where
  xs .<= ys = Just (isSubset xs ys)

-- |Filter a set xs by a predicate f.
toSubset :: (a -> Bool) -> [a] -> [a]
toSubset f xs = [x | x <- xs, f x]

-- |Construct the power set of a set.
powerSet :: [a] -> [[a]]
powerSet [] = [[]]
powerSet (x:xs) = map (x:) (powerSet xs) ++ powerSet xs

-- |Intersect xs with ys
cap :: Eq a => [a] -> [a] -> [a]
cap xs ys = [x | x <- xs, elem x ys]

-- |Intersect a collection [xs] of sets.
bigCap :: Eq a => [[a]] -> [a]
bigCap [] = []
bigCap [xs] = xs 
bigCap (xs:xss) = cap xs (bigCap xss)

-- |Eliminate duplicates from a list.
red :: Eq a => [a] -> [a]
red [] = []
red (x:xs) = x : red [y | y <- xs, y /= x]

-- |Union of xs and ys.
cup :: Eq a => [a] -> [a] -> [a]
cup xs ys = red (xs ++ ys)

-- |Union of a collection [xs].
bigCup :: Eq a => [[a]] -> [a]
bigCup [] = []
bigCup [xs] = xs 
bigCup (xs:xss) = cup xs (bigCup xss)

-- |Cartesian product of xs and ys.
pairs :: [a] -> [b] -> [(a,b)]
pairs xs ys = [(x,y) | x <- xs, y <- ys]

-- |Check for set equality.
eq :: Eq a => [a] -> [a] -> Bool
[] `eq` [] = True
[] `eq` _  = False
(x:xs) `eq` ys = elem x ys && xs `eq` [y | y <- ys, y /= x]

-- |Define a feasibility relation by generating relation. (Report Def. 2.6)
genFeasRel :: (PO a, Eq a, PO b, Eq b) => Rel a b -> Rel a b
genFeasRel (Rel (rel,xs,ys)) = Rel (p,xs,ys) where
  p = bigCap [relation | relation <- powerSet $ pairs xs ys, isSubset rel relation, isFeasRel (Rel (relation,xs,ys))]

-- |Check if function f: xs->ys is monotone.
isMonotone :: (PO a, PO b) => (a -> b) -> [a] -> Bool
isMonotone f xs = null [y | x <- xs, y <- xs, y `ge` x, not (f y `ge` f x)]

-- |Check if function f: xs->ys is order embedding.
isOrderEmbedding :: (PO a, PO b) => (a -> b) -> [a] -> Bool
isOrderEmbedding f xs = isMonotone f xs && null [y | x <- xs, y <- xs, f y `ge` f x, not (y `ge` x)]

-- |Unzip a collection of pairs without repetitions.
factors :: (Eq a, Eq b) => [(a,b)] -> ([a],[b])
factors prod = (red $ map fst prod, red $ map snd prod)
  
{- Relations as maps to Bool; not really needed

newtype Rel' a b = Rel' ((a,b) -> Bool, [(a,b)])

-- |Convert relation a -|-> b to function a x b -> Bool. 
fromRel2Rel' :: (Eq a, Eq b) => Rel a b -> Rel' a b
fromRel2Rel' (Rel (p,xs,ys)) = Rel' (\(x,y) -> elem (x,y) p, pairs xs ys)

-- |Convert a function a x b -> Bool to a relation a -|-> b.
showRel' :: (Eq a, Eq b) =>  Rel' a b -> Rel a b
showRel' (Rel' (f, prod)) = Rel ([rel | rel <- prod, f rel == True], fst $ factors prod, snd $ factors prod)

-}

-- |Opposite order
newtype Op a = Op a
  deriving Show

instance PO a => PO (Op a) where
  Op x .<= Op y = y .<= x

-- |Product order  
newtype Prod a b = Prod (a,b)
  deriving Show

instance (PO a, PO b) => PO (Prod a b) where
  Prod (x,y) .<= Prod (x',y') = (&&) <$> x .<= x' <*> y .<= y'

-- |Feasibility relations as monotone maps to Bool.
newtype RelIndicator a b = RelIndicator ((Prod a (Op b)) -> Bool, [(a,b)])

-- |Convert relation a -|-> b to map a x b^op -> Bool.
fromRel2RelIndicator :: (Eq a, Eq b) => Rel a b -> RelIndicator a b
fromRel2RelIndicator (Rel (p,xs,ys)) = RelIndicator (\(Prod (x,Op y)) -> (elem (x,y) p), pairs xs ys)

-- |Convert map map a x b^op -> Bool to relation a -|-> b.
showRelIndicator :: (Eq a, Eq b) =>  RelIndicator a b -> Rel a b
showRelIndicator (RelIndicator (f, prod)) = Rel ([(x,y) | (x,y) <- prod, f (Prod (x, Op y))], fst $ factors prod, snd $ factors prod)

-- |Check if map a x b^op -> Bool corresponds to feasibility relation.
isFeasRelIndicator :: (PO a, Eq a, PO b, Eq b) => RelIndicator a b -> Bool
isFeasRelIndicator (RelIndicator (f, prod)) = isMonotone f [Prod (x, Op y) | (x,y) <- prod]


--Upper and lower sets (Report Sec. 3.2) --

-- |Check if xs is upward closed in ys.
isUpward :: (Eq a, PO a) => [a] -> [a] -> Bool
isUpward xs ys = and [elem y xs | x <-xs, y <- ys, x `ge` y] 

-- |Check if xs is downward closed in ys.
isDownward :: (Eq a, PO a) => [a] -> [a] -> Bool
isDownward xs ys = and [elem y xs | x <-xs, y <- ys, y `ge` x] 

-- |Generate the upper closure of xs in ys.
upperClosure :: (Eq a, PO a) => [a] -> [a] -> [a]
upperClosure xs ys = [p | p <- ys, or [x `ge` p | x <- xs]] 

-- |Generate the lower closure of xs in ys.
lowerClosure :: (Eq a, PO a) => [a] -> [a] -> [a]
lowerClosure xs ys = [p | p <- ys, or [p `ge` x| x <- xs]] 

-- |Defines the set of upper sets of a.
newtype UpperSets a = UP[a]
  deriving (Show, Eq)

-- |Generate set of upper sets of a.
upperSets :: (Eq a, PO a) => [a] -> [UpperSets a]
upperSets ys = [UP u | u <- powerSet ys, isUpward u ys]

-- |Defines the set of lower sets of a.
newtype LowerSets a = LP[a]
  deriving (Show, Eq)

-- |Order upper sets by containment (w.r.t. .>=).
instance Eq a => PO (UpperSets a) where
  UP xs .<= UP ys = Just (isSubset xs ys)

-- |Embed p in ys into the upper sets of ys.
iU :: (Eq a, PO a) => [a] -> a -> UpperSets a
iU ys p = UP (upperClosure [p] ys)

-- |Generate set of lower sets of a.
lowerSets :: (Eq a, PO a) => [a] -> [LowerSets a]
lowerSets ys = [LP u | u <- powerSet ys, isDownward u ys]

-- |Order lower sets by inclusion (w.r.t. .>=).
instance Eq a => PO (LowerSets a) where
  LP xs .<= LP ys = Just (isSubset ys xs)

-- |Embed p in ys into the lower sets of ys.
iL :: (Eq a, PO a) => [a] -> a -> LowerSets a
iL ys p = LP (lowerClosure [p] ys)

-- |Embed p in ys into the upper sets of lower sets of ys.
iC :: (Eq a, PO a) => [a] -> a -> UpperSets (LowerSets a)
iC ys p = iU (lowerSets ys) (iL ys p)

-- |Convert upper set type to list.
stripUP :: UpperSets a -> [a]
stripUP (UP xs) = xs

-- |Convert lower set type to list.
stripLP :: LowerSets a -> [a]
stripLP (LP xs) = xs
  
-- |Convert upper set of lower sets type to list.
stripC :: UpperSets (LowerSets a) -> [[a]]
stripC xs = map stripLP  (stripUP xs) 


-- Choices (Report Sec 3.3) --

-- |Perform free choice among collection of upper lower sets uls.
freeC :: (PO a, Eq a) => [UpperSets (LowerSets a)] -> UpperSets (LowerSets a)
freeC uls = UP $ map LP (bigCup (map stripC uls))

-- |Perform forced choice among collection of upper lower sets uls.
forcedC :: (PO a, Eq a) => [UpperSets (LowerSets a)] -> UpperSets (LowerSets a)
forcedC uls = UP $ map LP (bigCap (map stripC uls))

-- |Perform free choice among collection xs of elements of ys by first embedding the xs into U(L(ys))).
free :: (PO a, Eq a) => [a] -> [a] -> UpperSets (LowerSets a)
free ys xs = freeC [iC ys p | p <- xs]
  
-- |Perform forced choice among collection xs of elements of ys by first embedding the xs into U(L(ys))).
forced :: (PO a, Eq a) => [a] -> [a] -> UpperSets (LowerSets a)
forced ys xs = forcedC [iC ys p | p <- xs]

{- Alternate implementations of free and forced.

free' :: (PO a, Eq a) => [a] -> [a] -> UpperSets (LowerSets a)
free' ys xs = UP $ upperClosure [iL ys x | x <- xs] (lowerSets ys)

forced' :: (PO a, Eq a) => [a] -> [a] -> UpperSets (LowerSets a)
forced' ys xs =  iU (lowerSets ys) (LP (lowerClosure ys xs))

-}


-- Lifts (Report Sec. 4.1) --

-- |Lift relation a -|-> b to relation L(a) -|-> L(b). (Report Sec. 4.1)
liftL :: (PO a, Eq a, PO b, Eq b) => Rel a b -> Rel (LowerSets a) (LowerSets b)
liftL (Rel (p, xs, ys)) = Rel (pp, lxs, lys) where
  lxs = lowerSets xs
  lys = lowerSets ys
  pp = [(aa,bb) | aa <- lxs, bb <- lys, and [not $ null [(a,b) |b <- stripLP bb, elem (a,b) p] | a <- stripLP aa] ]

-- |Lift relation a -|-> b to relation U(a) -|-> U(b). (Report Sec. 4.1)
liftU :: (PO a, Eq a, PO b, Eq b) => Rel a b -> Rel (UpperSets a) (UpperSets b)
liftU (Rel (p, xs, ys)) = Rel (pp, uxs, uys) where
  uxs = upperSets xs
  uys = upperSets ys
  pp = [(aa,bb) | aa <- uxs, bb <- uys, and [not $ null [(a,b) | a <- stripUP aa, elem (a,b) p] | b <- stripUP bb] ]

-- |Lift relation a -|-> b to relation U(L(a)) -|-> U(L(b)). (Report Sec. 4.1)
liftUL :: (PO a, Eq a, PO b, Eq b) => Rel a b -> Rel (UpperSets (LowerSets a)) (UpperSets (LowerSets b))
liftUL = liftU . liftL

{- |Check if the feasibility relation on UL is a lift. If true, it is the lift of the returned relation. This uses the characterization Thm. 4.5 in the report. c0 checks if the (co)domains match, c1-c3 are conditions (i)-(iii) of Thm. 4.5.
-}
isLiftUL :: (PO a, Eq a, PO b, Eq b) => [a] -> [b] -> Rel (UpperSets (LowerSets a)) (UpperSets (LowerSets b)) -> (Bool, Rel a b)
isLiftUL xs ys (Rel (pp, ulxs, ulys)) = (c0 && c1 && c2 && c3, Rel (p, xs, ys)) where
  c0 = ulxs == upperSets (lowerSets xs) && ulys == upperSets (lowerSets ys)
  p  = [(r,f) | r <- xs, f <- ys, elem (iC xs r, iC ys f) pp]
  c1 =  pp `eq` [(aa,bb) | aa <- ulxs, bb <- ulys, 
    and [or [and [or [elem (iC xs r, iC ys f) pp | f <- b] |  r <- a] | a <- stripC aa] | b <- stripC bb] ]
  c2 =  and [(elem (aa, freeC sul) pp && and [elem (aa,y) pp | y <- sul]) || (not $ elem (aa, freeC sul) pp && or [not $ elem (aa,y) pp | y <- sul]) 
    | aa <- ulxs, sul <- powerSet ulys]
  c3 =  and [(elem (forcedC sul, bb) pp && and [elem (x,bb) pp | x <- sul]) || (not $ elem (forcedC sul, bb) pp && or [not $ elem (x,bb) pp | x <- sul]) 
    | bb <- ulys, sul <- powerSet ulxs]


-- Queries (Report Sec. 4.4) --

-- |Query resources in xs.
queryr :: (PO a, Eq a, PO b, Eq b) => [a] -> Rel (UpperSets (LowerSets a)) (UpperSets (LowerSets b)) -> UpperSets (LowerSets b) -> [a]
queryr xs (Rel (pp, _, _)) bb = [r | r <- xs, elem (iC xs r,bb) pp]

-- |Query functionalities in ys.
queryf :: (PO a, Eq a, PO b, Eq b) => [b] -> Rel (UpperSets (LowerSets a)) (UpperSets (LowerSets b)) -> UpperSets (LowerSets a) -> [b]
queryf ys (Rel (pp, _, _)) aa = [f | f <- ys, elem (aa, iC ys f) pp]
