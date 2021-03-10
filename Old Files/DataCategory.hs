data GraphCat a b where
  GraphId :: Graph a -> GraphCat a a
  GraphMor :: (Graph a -> Graph b) -> GraphMor a b

newtype GraphMorphism = GraphMorphism {unGM :: Graph a -> Graph b}

instance Functor Forget where
  type Dom = GraphCat
  type Cod = (->)
  Forget :% GraphId g = (Prelude.id)
  Forget :% GraphMor f = f

data Dom1 = A | B
data Dom2 = X | Y | z

instance Graph Basic where
  type Vertex (Basic a) = a 

data MajoritySig = Majority |Edge | Red | Blue

Int :: *
[] :: * -> *
Two :: Nat
Fin :: Nat -> *  Fin Two

class Signature sym where
  type Arity :: sym -> Nat
  intrep :: sym -> [Vec (Arity sym) a]

instance Signature MajoritySig where
  type Arity Edge = Two
  type Arity Majority = Three
  type Arity Red = One
  type Arity Blue = One

intrep Edge :: Edge [Cons 1 2]  