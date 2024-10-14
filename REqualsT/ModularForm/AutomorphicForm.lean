import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import REqualsT.QuaternionAlgebra.Defs

universe u

open TensorProduct DedekindDomain IsDedekindDomain

variable (F : Type u) [Field F] [NumberField F] -- totally real number field with 2 | [F : ℚ]

variable (R) [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F] -- 𝒪_F

variable (D) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D] [RamifiedExactlyAtInfinitePlaces F D] -- the quaternion algebra

variable (U : Subgroup (GL (Fin 2) (FiniteAdeleRing R F))) -- Need open-compact and some integrality conditions.

variable (A) [CommRing A]

-- The double quotient Dˣ \ (D ⊗[F] FiniteAdeleRing R F)ˣ / U (FiniteAdeleRing R F)ˣ
def AutomorphicFormInd : Type _ := F × R × D × U × (sorry : Type)

instance : Fintype (AutomorphicFormInd F R D U) := sorry
noncomputable
instance : DecidableEq (AutomorphicFormInd F R D U) := Classical.decEq _

-- The quotient map
def AutomorphicFormInd.of (d : D ⊗[F] FiniteAdeleRing R F) : AutomorphicFormInd F R D U := sorry

lemma AutomorphicFormInd.of_surjective : Function.Surjective (of F R D U) := sorry

-- S(U, 𝔸_F)
def AutomorphicForm : Type _ := AutomorphicFormInd F R D U → A

local notation "𝒮" => AutomorphicForm F R D U

instance : AddCommGroup (𝒮 A) := by delta AutomorphicForm; infer_instance
instance {B} [CommRing B] [Algebra A B] : Module A (𝒮 B) := by delta AutomorphicForm; infer_instance
instance {A' B} [CommRing A'] [CommRing B] [Algebra A B] [Algebra A' B] [Algebra A A'] [IsScalarTower A A' B] :
  IsScalarTower A A' (𝒮 B) := by delta AutomorphicForm; infer_instance
instance : Module.Free A (𝒮 A) := by delta AutomorphicForm; infer_instance
instance : Module.Finite A (𝒮 A) := by delta AutomorphicForm; infer_instance

noncomputable
def AutomorphicForm.tensorEquiv (B) [CommRing B] [Algebra A B] : B ⊗[A] (𝒮 A) ≃ₗ[B] (𝒮 B) := TensorProduct.piScalarRight ..

noncomputable
def AutomorphicForm.mapEnd (B) [CommRing B] [Algebra A B] : (Module.End A (𝒮 A)) →ₐ[A] (Module.End B (𝒮 B)) :=
  ((LinearEquiv.algConj (AutomorphicForm.tensorEquiv F R D U A B)).restrictScalars A).toAlgHom.comp
    (Module.End.baseChangeHom A B (𝒮 A))
