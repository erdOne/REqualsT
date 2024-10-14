import Mathlib
import REqualsT.Deformation.Basic
import REqualsT.ModularForm.Localization

universe u uR uD uA uL uOL

open TensorProduct DedekindDomain IsDedekindDomain CategoryTheory

variable (F : Type u) [Field F] [NumberField F] -- totally real number field with 2 | [F : ℚ]

variable (R : Type uR) [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F] -- 𝒪_F

variable (D : Type uD) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D] [RamifiedExactlyAtInfinitePlaces F D] -- the quaternion algebra

variable (U : Subgroup (GL (Fin 2) (FiniteAdeleRing R F))) -- Need open-compact and some integrality conditions.

variable (A : Type uA) [CommRing A]

local notation "𝒮" => AutomorphicForm F R D U

local notation "T" => heckeOperator F R D U
local notation "𝕋" => HeckeAlgebra F R D U
local notation "𝕋.T" => HeckeAlgebra.heckeOperator F R D U

variable {L : Type uL} [Field L]
variable (𝒪L : Type uOL) [CommRing 𝒪L] [LocalRing 𝒪L] [Algebra 𝒪L L] [IsFractionRing 𝒪L L]
variable [IsNoetherianRing 𝒪L] [IsCompleteLocalRing 𝒪L] [Algebra.IsIntegral ℤ 𝒪L] -- ring of integers of L

variable (S : Finset (HeightOneSpectrum R)) -- Need condition U ⊇ GL₂(𝒪_F^S) x (some open ⊆ Π_{v ∈ S} GL₂(Fᵥ))

variable (ℓ : ℕ) [Fact ℓ.Prime]

local notation "ℚ‾_[" ℓ "]" => AlgebraicClosure (ℚ_[ℓ])

variable [Algebra ℚ_[ℓ] L] [Module.Finite ℚ_[ℓ] L] -- Some finite extension `L / ℚℓ`

variable (ι : 𝒪L →+* ℚ‾_[ℓ]) -- Fix an embedding

local notation "L'" => HeckeAlgebra.field F R D U S ℓ ι

local notation "𝒪L'" => integralClosure ℤ L'

attribute [local instance] LocalRing.withIdeal

variable (r : ContinuousMonoidHom (Field.absoluteGaloisGroup F) (GL (Fin 2) 𝒪L)) -- regular algebraic ℓ-adic rep

local notation "𝔪" => HeckeAlgebra.maximalIdeal F R D U

local notation "𝕋𝔪" => HeckeAlgebra.localization F R D U

-- attribute [local irreducible] HeckeAlgebra.subalgebraPi

-- variable (D : (dim2Repr 𝒪 G).Subfunctor) -- Deformation functor
-- variable [D.toFunctor.IsCorepresentable]

-- local notation3 "Rᵘⁿⁱᵛ" => D.toFunctor.coreprX
-- local notation "rᵘⁿⁱᵛ" => D.toFunctor.coreprx

-- #check rᵘⁿⁱᵛ

attribute [pp_with_univ] DeformationCat

/-- A representation comming from local langlands? -/
def HeckeAlgebra.reprSubalgebraPi :
  ContinuousMonoidHom (Field.absoluteGaloisGroup F)
    (GL (Fin 2) (HeckeAlgebra.subalgebraPi F R D U 𝒪L S ℓ ι r)) := sorry

universe v

/-- The type of deformations we are considering -/
def deformationType : (dim2Repr 𝒪L (Field.absoluteGaloisGroup F)).Subfunctor := sorry

instance : (deformationType F 𝒪L).toFunctor.IsCorepresentable := sorry

universe u₁ u₂ in
def DeformationCat.uLift : DeformationCat.{u₁} 𝒪L ⥤ DeformationCat.{max u₁ u₂} 𝒪L where
  obj X := { X := ULift X.X, localRing := sorry, isNoetherianRing := sorry, isCompleteLocalRing := sorry, isLocalRingHom := sorry, bijective := sorry }
  map f := sorry
  map_id := sorry
  map_comp := sorry

universe u₁ u₂ in
def deformationType_ulift (X) :
    (DeformationCat.uLift.{uOL, u₁, u₂} 𝒪L ⋙ (deformationType F 𝒪L).toFunctor).obj X ≃ (deformationType F 𝒪L).obj X := sorry

noncomputable
def DeformationCat.subalgebraPi : DeformationCat 𝒪L where
  X := (HeckeAlgebra.subalgebraPi F R D U 𝒪L S ℓ ι r)
  isLocalRingHom := sorry
  bijective := sorry

/-- The representation satisfies the deformation problem. -/
lemma HeckeAlgebra.reprSubalgebraPi_mem_deformationType :
  Quotient.mk (equivRepr _ _) (HeckeAlgebra.reprSubalgebraPi F R D U 𝒪L S ℓ ι r) ∈
    (deformationType F 𝒪L).obj (DeformationCat.subalgebraPi F R D U 𝒪L S ℓ ι r) :=
  sorry

local notation3 "Rᵘⁿⁱᵛ" => (deformationType F 𝒪L).toFunctor.coreprX

def ULift.algEquiv {R A} [CommSemiring R] [Semiring A] [Algebra R A] : ULift A ≃ₐ[R] A where
  __ := ULift.ringEquiv
  commutes' _ := rfl

noncomputable
def RToA : Rᵘⁿⁱᵛ.X →ₐ[𝒪L] HeckeAlgebra.subalgebraPi F R D U 𝒪L S ℓ ι r :=
  (ULift.algEquiv).toAlgHom.comp <|
  ((deformationType F 𝒪L).toFunctor.coreprW.inv.app
    ((DeformationCat.uLift 𝒪L).obj (DeformationCat.subalgebraPi F R D U 𝒪L S ℓ ι r))
    ((deformationType_ulift F 𝒪L _).symm ⟨_, HeckeAlgebra.reprSubalgebraPi_mem_deformationType F R D U 𝒪L S ℓ ι r⟩)).toAlgHom

lemma range_RToA : (RToA F R D U 𝒪L S ℓ ι r).range = (HeckeAlgebra.locToSubalgebraPi F R D U 𝒪L S ℓ ι r).range := sorry

noncomputable
def RToT : Rᵘⁿⁱᵛ.X →ₐ[𝒪L] 𝕋𝔪 𝒪L S r := by
  refine (AlgEquiv.ofInjective _ (HeckeAlgebra.locToSubalgebraPi_injective F R D U 𝒪L S ℓ ι r)).symm.toAlgHom.comp ?_
  refine AlgHom.comp ?_ (RToA F R D U 𝒪L S ℓ ι r).rangeRestrict
  exact (Subalgebra.equivOfEq _ _ (range_RToA F R D U 𝒪L S ℓ ι r)).toAlgHom

lemma RToT_surjective : Function.Surjective (RToT F R D U 𝒪L S ℓ ι r) := by
  refine (AlgEquiv.toEquiv (AlgEquiv.ofInjective _ (HeckeAlgebra.locToSubalgebraPi_injective F R D U 𝒪L S ℓ ι r)).symm).surjective.comp ?_
  refine (AlgEquiv.toEquiv (Subalgebra.equivOfEq _ _ (range_RToA F R D U 𝒪L S ℓ ι r))).surjective.comp ?_
  apply AlgHom.rangeRestrict_surjective
