import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs

class IsQuaternionAlgebra (F D) [Field F] [Ring D] [Algebra F D] : Prop where
  cond : (sorry : Prop)

class RamifiedExactlyAtInfinitePlaces (F D) [Field F] [Ring D] [Algebra F D] [IsQuaternionAlgebra F D] : Prop where
  cond : (sorry : Prop)
