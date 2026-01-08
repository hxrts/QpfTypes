import Qpf

open Card

-- Basic smoke test for the Card-based polynomial functor wrapper.

def ExampleP : MvPFunctorCard 1 where
  A := Bool
  B := fun
    | false, _ => Card.fin 2
    | true, _ => Card.infinite Nat

#check (ExampleP : MvPFunctor 1)
#check (MvPFunctorCard.toMvPFunctor ExampleP)
