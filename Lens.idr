module Lens

Lens0 : Type -> Type -> Type -> Type -> Type
Lens0 s t a b = (s -> a, s -> b -> t)

data  Prod a b = Pr a b

get0 : Prod a b -> a
get0 (Pr a b) = a

set0 : Prod a b -> c -> Prod c b
set0 (Pr a b) c = Pr c b

lens0 : Lens0 (Prod a b) (Prod a' b) a a'
lens0 = (get0, set0)

data Lens1 : Type -> Type -> Type -> Type -> Type where
  L1 : {c : Type} -> (s -> (a, c)) -> ((b, c) -> t) -> Lens1 s t a b

decomp : Prod a b -> (a, b)
decomp (Pr a b) = (a, b)
comp   : (a, b) -> Prod a b
comp (a, b) = Pr a b

lens1 : Lens1 (Prod a b) (Prod a' b) a a'
lens1 = L1 decomp comp

interface Profunctor (p : Type -> Type -> Type) where
  dimap : (a' -> a) -> (b -> b') -> p a b -> p a' b'

interface Profunctor p => Strong (p : Type -> Type -> Type) where
  first' : {c : Type} -> p a b -> p (a, c) (b, c)

Lens2 : Type -> Type -> Type -> Type -> Type
Lens2 s t a b =  {p : Type -> Type -> Type} -> (Strong p => p a b -> p s t)

data Hom : Type -> Type -> Type where
  H : (a -> b) -> Hom a b

Profunctor Hom where
  dimap f g (H h) = H (g . h . f)

Strong Hom where
  -- (a->b) -> (a, c) -> (b, c)
  first' {c} (H ab) = H (\(a, c) => (ab a, c))

data InvLens : Type -> Type -> Type -> Type -> Type where
  IL : Lens0 s t a b -> InvLens a b s t

-- A Lens0 is a strong profunctor in the arguments s and t
Profunctor (InvLens a b) where
  -- (s' -> s) -> (t -> t') -> (s -> a, s -> b -> t) -> (s' -> a, s' -> b -> t')
  dimap f g (IL (get, set)) = IL (get . f, \s' => g . set (f s'))

Strong (InvLens a b) where
  -- ((s, c) -> a,  (s, c) -> b -> (t, c))
  first' {c} (IL (get, set)) = IL (\(s, c) => get s, \(s, c) => (\b => (set s b, c)))

fromGetSet2 : (get : s -> a) -> (set : s -> b -> t) -> (Strong p => p a b -> p s t)
fromGetSet2 {s} get set pab = dimap (\s => (get s, s)) (\(b, s) => set s b) (first' {c = s} pab)

lens2 : Lens2 (Prod a c) (Prod a' c) a a'
lens2 = fromGetSet2 get0 set0

toGetSet2 : Lens2 s t a b -> Lens0 s t a b
toGetSet2 lens2 = let (IL l2) = lens2 (IL (id, \s => id)) in l2

toGet2 : Lens2 s t a b -> s -> a
toGet2 = fst . toGetSet2

toSet2 : Lens2 s t a b -> s -> b -> t
toSet2 = snd . toGetSet2

s1 : Prod (Prod Char Int) String
s1 = Pr (Pr 'a' 1) "one"


-- lens2 : Lens2 (Prod a c) (Prod a' c) a a'
-- toGetSet2 : Lens2 s t a b -> Lens0 s t a b
z : Lens0 (Prod a c) (Prod a' c) a a'
z = toGetSet2 lens2

main : IO ()
main = do
  print ()
