import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Instances.Matrix

universe u

open IsDedekindDomain

variable (F : Type u) [Field F] [NumberField F] -- totally real number field with 2 | [F : ℚ]

variable (R) [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F] -- 𝒪_F

variable {𝒪L} [CommRing 𝒪L] [LocalRing 𝒪L]

instance {n R} [DecidableEq n] [Fintype n] [TopologicalSpace R] [CommRing R] [TopologicalRing R] :
  TopologicalSpace (GL n R) := by delta Matrix.GeneralLinearGroup; infer_instance

instance {n R} [DecidableEq n] [Fintype n] [TopologicalSpace R] [CommRing R] [TopologicalRing R] :
  TopologicalGroup (GL n R) := by delta Matrix.GeneralLinearGroup; infer_instance

def LocalRing.withIdeal {R} [CommRing R] [LocalRing R] : WithIdeal R := ⟨maximalIdeal R⟩

attribute [local instance] LocalRing.withIdeal

variable (r : ContinuousMonoidHom (Field.absoluteGaloisGroup F) (GL (Fin 2) 𝒪L)) -- regular algebraic ℓ-adic rep

def trFrob : HeightOneSpectrum R → 𝒪L := fun _ ↦ Matrix.trace (r sorry).1
