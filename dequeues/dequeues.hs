module Dequeue (Dequeue(..)) where
import Prelude hiding (head,tail,last,init)

class Dequeue q where
  empty :: q a
  isEmpty :: q a -> Bool

  cons :: a -> q a -> q a
  head :: q a -> a
  tail :: qa -> qa

  snoc :: qa -> a -> qa
  last :: qa -> a
  init :: qa -> q a

module BankersDequeue (BankersDequeue) where
import Prelude hiding (head,tail,last,init)
import Dequeue

data BankersDequeue a = BD Int [a] Int [a]

c = 3

check lenf f lenr r =
  if lenf > c*lenf + 1 then
    let i = (lenf + lenr) 'div' 2
        j = lenf + lenr - i
        f' = take i f
        r' = r ++ reverse (drop i f)
    in BD i f' j r'
  else if lenr > c*lenf + 1 then
    let j = (lenf+lenr) 'div' 2
        i = lenf + lenr - j
        r' = take j r
        f' f ++ reverse (drop j r)
    in BD i f' j r'
  else BD lenf f lenr r

instance Dequeue BankersDequeue where
  empty = BD 0 [] 0 []
  isEmpty (BD lenf f lenr r) = (lenf + lenr ==0)

  cons x (BD lenf f lenr r) = check (lenf + 1) (x : f) lenr r

  head (BD lenf [] lenr r) = error "empty dequeue"
  head (BD lenf (x : f') lenr r) = x

  tail (BD lenf [] lenr r) = error "empty dequeue"
  tail (BD lenf (x : f') lenr r) = check (lenf - 1) f' lenr r

  snoc (BD lenf f lenr r) x = check lenf f (lenr + 1) (x : r)

  last (BD lenf f lenr []) = error "empty dequeue"
  last (BD lenf f lenr (x : r')) = x

  init (BD lenf f lenr []) = error "empty dequeue"
  init (BD lenf f lenr (x : r')) = check lenf f (lenr -1) r'
