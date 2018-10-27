module CatenableList (CatenableList(..)) where
import Prelude hiding(head,tail,(++))

class CatenableList c where
  empty :: c a
  isEmpty :: c a -> Bool

  cons :: a -> c a -> c a
  snoc :: c a -> a -> c a
  (++) :: c a -> c a -> c a

  head :: c a -> a
  tail :: c a -> c a

module CatList (CatList) where
import Prelude hiding (head,tail,(++))
import CatenableList
import Queue (Queue)
import qualified Queue

data CatList q a = E | C a (q(CatList q a))

link (C x q) s = C x (Queue.snoc q s)

instance Queue q => CatenableList (CatList q) where
  empty = E
  isEmpty E = True
  isEmpty _ = False

  xs ++ E = xs
  E ++ xs = xs
  xs ++ ys = link xs ys

  cons x xs = C x Queue.empty ++ xs
  snoc xs s = xs ++ C x Queue.empty

  head E = error "empty list"
  head (C x q) = x

  tail E = error "empty list"
  tail (C x q) = if Queue.isEmpty q then E else linkAll q
  where linkAll q = if Queue.isEmpty q' then t else link t (linkAll q')
          where t = Queue.head q
          q' = Queue.tail q

module CatenableDequeue (CatenableDequeue(..)) where
import Prelude hiding (head,tail,last,init,(++))
import Dequeue

class Dequeue d => CatenableDequeue d where
  (++) :: d a -> d a -> d a


module SimpleCatenableDequeue (SimpleCatDequeue) where
import Prelude hiding (head,tail,last,init,(++))
import CatenableDequeue

data SimpleCatDequeue q a =
  SHALLOW (d a)
  | DEEP (d a) (SimpleCatDequeue d (d a)) (d a)

tooSmall d = isEmpty d || isEmpty (tail d)

dappendL d_1 d_2 = if isEmpty d_1 then d_2 else cons (head d_1) d_2
dappendR d_1 d_2 = if isEmpty d_2 then d_1 else snoc d_1 (head d_2)

instance Dequeue d => Dequeue (SimpleCatDequeue d) where
  empty = SHALLOW empty
  isEmpty = (SHALLOW d) = isEmpty d
  isEmpty _ = False

  cons x (SHALLOW d) = SHALLOW (cons x d)
  cons x (DEEP f m r) = DEEP (cons x f) m r

  head (SHALLOW d) = head d
  head (DEEP f m r) = head f

  tail (SHALLOW d) = SHALLOW (tail d)
  tail (DEEP f m r)
    | not (tooSmall f') = DEEP f' m r
    | isEmpty m = SHALLOW (dappendL f' r)
    | otherwise = DEEP (dappendL (head m)) (tail m) r
    where f' = tail f

instance Dequeue d => CatenableDequeue (SimpleCatDequeue d) where
  (SHALLOW d_1) ++ (SHALLOW d_2)
    | tooSmall d_1 = SHALLOW (dappendL d_1 d_2)
    | tooSmall d_2 = SHALLOW (dappendR d_1 d_2)
    | otherwise = DEEP d_1 empty d_2
  (SHALLOW d) ++ (DEEP f m r)
    | tooSmall d = DEEP (dappendL d f) m r
    | otherwise = DEEP d (cons f m) r
  (DEEP f m r) ++ (SHALLOW d)
    | tooSmall d = DEEP f m (dappendR r d)
    | otherwise = DEEP f (snoc m r) d
  (DEEP f_1 m_1 r_1) ++ (DEEP f_2 m_2 r_2) =
    DEEP f_1 (snoc m_1 r_1 ++ cons f_2 m_2) r_2

module ImplicitCatenableDequeue (Sized(..), ImplicitCatDequeue) where
import Prelude hiding (head,tail,last,init,(++))
import CatenableDequeue

class Sized d where
  size :: d a -> Int

data ImplicitCatDequeue d a =
  SHALLOW (d a)
  | DEEP (d a) (ImplicitCatDequeue d (CmpdElem d a)) (d a)
    (ImplicitCatDequeue d (CmpdElem d a)) (d a)

data CmpdElem d a =
  SIMPLE (d a)
  | CMPD (d a) (ImplicitCatDequeue d (CmpdElem d a)) (d a)

share f r = (init f, m, tail r)
where m = cons (last f) (cons (head r) empty)

dappendL d_1 d_2 =
  if isEmpty d_1 then d_2 else dappendL (init d_1 9cons (last d_1) d_2)
dappendR d_1 d_2 =
  if isEmpty d_2 then d_1 else dappendR (snoc d_1 (head d_2)) (tail d_2)

replaceHead x (SHALLOW d) = SHALLOW (cons x (tail d))
replaceHead x (DEEP f a m b r) = DEEP (cons x (tail f)) a m b r

instance Dequeue d, Sized d) => Dequeue (ImplicitCatDequeue d) where
empty = SHALLOW empty
isEmpty (SHALLOW d) = isEmpty d
isEmpty _ = False

cons x (SHALLOW d) = SHALLOW (cons x d)
cons x (DEEP f a m b r) = DEEP (cons x f) a m b r

head (SHALLOW d) = head d
head (DEEP f a m b r) = head f

tail (SHALLOW d) = SHALLOW (tail d)
tail (DEEP f a m b r)
  |size f > 3 = DEEP (tail f) a m b r
  | not (isEmpty a) =
    case head a of
      SIMPLE d -> DEEP f' (tail a) m b r
        where f' = dappendL (tail f) d
      CMPD f' c' r' -> DEEP f'' a'' m b r
        where f'' = dappendL (tail f) f'
              a'' = c' ++ replaceHead (SIMPLE r') a

  | not (isEmpty b) =
    case head b of
      SIMPLE d -> DEEP f' empty d (tail b) r
        where f' = dappendL (tail f) m
      CMPD f' c' r' -> DEEP f'' a'' r' (tail b) r
        where f'' = dappendL (tail f) m
              a'' = cons (SIMPLE f') c'

  | otherwise = SHALLOW (dappendL (tail f) m) ++ SHALLOW r

instance (Dequeue d, Sized d) => CatenableDequeue (ImplicitCatDequeue d)
where
(SHALLOW d_1) ++ (SHALLOW d_2)
  | size d_1 < 4 = SHALLOW (dappendL d_1 d_2)
  | size d_2 < 4 = SHALLOW (dappendR d_1 d_2)
  |otherwise = let (f, m, r) = share d_1 d_2 in DEEP f empty m empty r
(SHALLOW d) ++ (DEEP f a m b r)
  | size d < 4 = DEEP (dappendL d f) a m b r
  | otherwise = DEEP d (cons (SIMPLE f ) a) m b r
(DEEP f a m b r) ++ (SHALLOW d)
  | size d < 4 = DEEP f a m b (dappendR r d)
  | otherwise = DEEP f a m (snoc b (SIMPLE r)) d
    (DEEP f_1 a_1 m_1 b_1 r_1) ++ (DEEP f_2 a_2 m_2 b_2 r_2) = DEEP f_1 a_1' m b_2' r_2
    where (r_1', m, f_2') = share r_1 f_2
          a_1' = snoc a_1 (CMPD m_1 b_1 r_1')
          b_2' = cons (CMPD f_2' a_2 m_2) b_2