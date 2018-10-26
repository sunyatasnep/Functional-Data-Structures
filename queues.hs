-- | Basic queue
module Queue (Queue(..)) where
	import Prelude hiding (head,tail)

	class Queue q where
		empty	:: q a
		isEmpty	q a -> Bool

		snoc	:: q a -> a -> q a
		head	:: q a -> a
		tail	:: q a -> q a


-- | Batched queue 
module BatchedQueue (BatchedQueue) where
	import Prelude hiding (head,tail)
	import Queue

	data BatchedQueue a = BQ [a] [a] 

	check [] r = BQ (reverse r) []
	check f r = BQ f r

	instance Queue BatchedQueue where
		empty = BQ [] []
		isEmpty (BQ f r) = null f

		snoc (BQ f r) x = check f (x : r)

		head (BQ [] _) = error "empty queue"
		head (BQ (x : f) r) = x

		tail (BQ [] _) = error "empty queue"
		tail (BQ (x : f) r) = check f r

-- | Banker's Queue
module BankersQueue (BankersQueue) where
	import Prelude hiding (head,tail)
	import Queue

	data BankersQueue a = BQ int [a] int [a]

	check lenf f lenr r = 
		if lenr =< lenf then BQ lenf f lenr r
		else BQ (lenf + lenr) (f ++ reverse r) 0 []

	instance Queue BankersQueue where
		empty = BQ 0 [] 0 []
		isEmpty (BQ lenf f lenr r) = (lenf == 0)

		snoc (BQ lenf f lenr r) x = check lenf f (lenr + 1) (x : r)

		head (BQ lenf [] lenr r) = error "empty queue"
		head (BQ lenf (x : f') lenr r) = x

		tail (BQ lenf [] lenr r) = error "empty queue"
		tail (BQ lenf (x : f') lenr r) = check (lenf - 1) f' lenr r

-- | Physicist's Queue
module PhysicistsQueue (PhysicistsQueue) where
	import Prelude hiding (head,tail)
	import Queue

	data PhysicistsQueue a = PQ [a] int [a] int [a]

	check w lenf f lenr r =
		if lenr =< lenf then checkw w lenf f lenr r
		else checkw f (lenf + lenr) (f ++ reverse r) 0 []

	checkw [] lenf f lenr r = PQ f lenf f lenr r
	checkw w lenf f lenr r = PQ w lenf f lenr r

	instance Queue PhysicistsQueue where
		empty = PQ [] 0 [] 0 []
		isEmpty (PQ w lenf f lenr r) = (lenf == 0)

		snoc (PQ w lenf f lenr r) x = check w lenf f (lenr + 1) (x : r)

		head (PQ [] lenf f lenr r) = error "empty queue"
		head (PQ (x : w) lenf f lenr r) = x

		tail (PQ [] lenf f lenr r) = error "empty queue"
		tail (PQ (x : w) lenf f lenr r) = check w (lenf - 1) (Prelude.tail f) lenr r

-- | Hood Melville Queue
module HoodMelvilleQueue (HoodMelvilleQueue) where
	import Prelude hiding (head,tail)
	import Queue

	data RotationState a = 
		Idle
		| Reversing int [a] [a] [a] [a]
		| Appending int [a] [a]
		| Done [a]
	
	data HoodMelvilleQueue a = HM int [a] (RotationState a) int [a]

	exec (Reversing ok (x : f) f' (y : r) r') = Reversing (ok + 1) f (x : f') r (y : r')
	exec (Reversing ok [] f' [y] r') = Appending ok f' (y : r')
	exec (Appending 0 f' r') = Done r'
	exec (Appending ok (x : f' r') = Appending (ok - 1) f' (x : r')
	exec state = state

	invalidate (Reversing ok f f' r r') = Reversing (ok - 1) f f' r r'
	invalidate (Appending 0 f' (x : r')) = Done r'
	invalidate (Appending ok f' r') = Appending (ok - 1) f' r'
	invalidate state = state

	exec2 lenf f state len r =
		case exec (exec state) of
			Done newf -> HM lenf newf Idle lenr r
			newstate -> HM lenf f newstate lenr r

	check lenf f state lenr r =
		if lenr =< lenf then exec2 lenf f state lenr r
		else let newstate Reversing 0 f [] r []
			in exec2 (lenf + lenr) f newstate 0 []

	instance Queue HoodMelvilleQueue where
		empty = HM 0 [] Idle 0 []
		isEmpty (HM lenf f state lenr r) = (lenf == 0)

		snoc (HM lenf f state lenr r) x = check lenf f state (lenr + 1) (x : r)

		head (HM _ [] _ _ _) = error "empty queue"
		head (HM _ (x : f') _ _ _) = x

		tail (HM lenf [] state lenr r) = error "empty queue"
		tail (HM lenf (x : f') state lenr r) =
			check (lenf - 1) f' (invalidate state) lenr r

-- | Bootstrapped Queue
module BootstrappedQueue (BootstrappedQueue) where
	import Prelude hiding (head,tail)
	import Queue

	data BootstrappedQueue a =
		E | Q int [a] (BootstrappedQueue [a]) int [a]
	
	checkQ,checkF :: int -> [a] -> (BootstrappedQueue [a]) -> int -> [a]
		-> BootstrappedQueue a

	checkQ lenfm f m lenr r =
		if lenr =< lenfm then checkF lenfm f m lenr r
		else checkF (lenfm + lenr) f (snoc m (reverse r)) 0 []

	checkF lenfm [] E lenr F = E
	checkF lenfm [] m lenr r = Q lenfm (head m) (tail m) lenr r
	checkF lenfm f m lenr r = Q lenfm f m lenr r

	instance Queue BootstrappedQueue where
		empty = Q 0 [] E 0 []
		isEmpty E = True
		isEmpty _ = False

		snoc E x = q 1 [x] E 0 []
		snoc (Q lenfm f m lenr r) x = checkQ lenfm f m (lenr + 1) (x : r)

		head E = error "empty queue"
		head (Q lenfm (x : f') m lenr r) = x

		tail E = error "empty queue"
		tail (Q lenfm (x : f') m lenr r) = checkQ (lenfm - 1) f' m lenr r

-- | Implicit Queue
module ImplicitQueue (ImplicitQueue) where
	 import Prelude hiding (head,tail)
	 import Queue

	 data Digit a = ZERO | ONE a | TWO aa
	 data ImplicitQueue a = 
	 	SHALLOW (Digit a)
		| DEEP (Digit a) (ImplicitQueue (a, a)) (Digit a)

	instance Queue ImplicitQueue where
		empty = SHALLOW ZERO
		isEmpty (SHALLOW ZERO) = True
		isEmpty _ = False

		snoc (SHALLOW ZERO) y = SHALLOW (ONE y)
		snoc (SHALLOW (ONE x)) y = DEEP (TWO x y) empty ZERO
		snoc (DEEP f m ZERO) y = DEEP f m (ONE y)
		snoc (DEEP f m (ONE x)) y = DEEP f (snoc m (x, y)) ZERO

		head (SHALLOW ZERO) = error "empty queue"
		head (SHALLOW (ONE x)) = x
		head (DEEP (ONE x) m r) = x
		head (DEEP (TWO x y) m r) = x

		tail (SHALLOW ZERO) = error "empty queue"
		tail (SHALLOW (ONE x)) = empty
		tail (DEEP (TWO x y) m r) = DEEP (ONE y) m r
		tail (DEEP (ONE x) m r) =
			if isEmpty m then SHALLOW r else DEEP (TWO y z) (tail m) r
			where (y, z) = head m
