import Mathlib
import REqualsT.ModularForm.AutomorphicForm

universe u

open TensorProduct DedekindDomain IsDedekindDomain

variable (F : Type u) [Field F] [NumberField F] -- totally real number field with 2 | [F : ℚ]

variable (R) [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F] -- 𝒪_F

variable (D) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D] [RamifiedExactlyAtInfinitePlaces F D] -- the quaternion algebra

variable (U : Subgroup (GL (Fin 2) (FiniteAdeleRing R F))) -- Need open-compact and some integrality conditions.

variable (A) [CommRing A]

variable (S : Finset (HeightOneSpectrum R)) -- Need condition U ⊇ GL₂(𝒪_F^S) x (some open ⊆ Π_{v ∈ S} GL₂(Fᵥ))

local notation "𝒮" => AutomorphicForm F R D U

variable {S} in
def heckeOperator {v : HeightOneSpectrum R} (hv : v ∉ S) : Module.End A (𝒮 A) := sorry -- need some condition on v

local notation "T" => heckeOperator F R D U

lemma commute_heckeOperator {v₁ v₂} (hv₁ : v₁ ∉ S) (hv₂ : v₂ ∉ S) : Commute (T A hv₁) (T A hv₂) := sorry

def HeckeAlgebra : Subalgebra A (Module.End A (𝒮 A)) := Algebra.adjoin A ({ T A hv | (v) (hv : v ∉ S) })

local notation "𝕋" => HeckeAlgebra F R D U

lemma HeckeAlgebra.commute {x y} (hx : x ∈ 𝕋 A S) (hy : y ∈ 𝕋 A S) : Commute x y := by
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy
  rintro _ ⟨v₂, hv₂, rfl⟩
  symm
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx
  rintro _ ⟨v₁, hv₁, rfl⟩
  exact commute_heckeOperator F R D U A S hv₂ hv₁

instance : CommRing (𝕋 A S) where
  mul_comm x y := Subtype.ext (HeckeAlgebra.commute F R D U A S x.2 y.2)

variable {S} in
protected
def HeckeAlgebra.heckeOperator {v : HeightOneSpectrum R} (hv : v ∉ S) : 𝕋 A S :=
  ⟨T A hv, Algebra.subset_adjoin ⟨_, _, rfl⟩⟩

local notation "𝕋.T" => HeckeAlgebra.heckeOperator F R D U

set_option linter.unusedSectionVars false in
lemma HeckeAlgebra.adjoin_heckeOperator :
    Algebra.adjoin A ({ 𝕋.T A hv | (v) (hv : v ∉ S) }) = ⊤ := by
  apply Subalgebra.map_injective (f := (𝕋 A S).val) Subtype.val_injective
  rw [Algebra.map_top, Subalgebra.range_val, AlgHom.map_adjoin]
  conv_rhs => delta HeckeAlgebra
  congr
  ext x
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩

lemma mapEnd_heckeOperator (B) [CommRing B] [Algebra A B] {v} (hv : v ∉ S) :
    AutomorphicForm.mapEnd F R D U A B (T A hv) = T B hv := sorry

lemma HeckeAlgebra.adjoin_map_mapEnd (B) [CommRing B] [Algebra A B] :
    Algebra.adjoin B ((𝕋 A S).map (AutomorphicForm.mapEnd F R D U A B)) = 𝕋 B S := by
  simp only [HeckeAlgebra, AlgHom.map_adjoin, Algebra.adjoin_adjoin_of_tower]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; exact ⟨v, hv, (mapEnd_heckeOperator ..).symm⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨_, ⟨v, hv, rfl⟩, (mapEnd_heckeOperator ..)⟩

noncomputable
def HeckeAlgebra.map (B) [CommRing B] [Algebra A B] : 𝕋 A S →ₐ[A] 𝕋 B S :=
  AlgHom.codRestrict ((AutomorphicForm.mapEnd F R D U A B).comp
    (𝕋 A S).val) ((𝕋 B S).restrictScalars A) (fun x ↦ by
    rw [← adjoin_map_mapEnd F R D U A, Subalgebra.mem_restrictScalars]
    refine Algebra.subset_adjoin ⟨_, x.2, rfl⟩)

lemma HeckeAlgebra.map_heckeOperator (B) [CommRing B] [Algebra A B] (v) (hv : v ∉ S) :
    map F R D U A S B (𝕋.T A hv) = 𝕋.T B hv :=
  Subtype.ext (mapEnd_heckeOperator F R D U A S B hv)

variable {A} in
noncomputable
def HeckeAlgebra.mapRingHom {B} [CommRing B] (f : A →+* B) : 𝕋 A S →+* 𝕋 B S :=
  letI := f.toAlgebra; (HeckeAlgebra.map ..).toRingHom

noncomputable
def HeckeAlgebra.mapTensor (B) [CommRing B] [Algebra A B] : B ⊗[A] 𝕋 A S →ₐ[B] 𝕋 B S :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (HeckeAlgebra.map ..) (fun _ _ ↦ .all _ _)

lemma HeckeAlgebra.mapTensor_surjective (B) [CommRing B] [Algebra A B] :
    Function.Surjective (mapTensor F R D U A S B) := by
  rw [← Algebra.range_top_iff_surjective, ← top_le_iff, ← adjoin_heckeOperator, Algebra.adjoin_le_iff]
  rintro x ⟨v, hv, rfl⟩
  exact ⟨1 ⊗ₜ 𝕋.T A hv, by simp [mapTensor, HeckeAlgebra.map_heckeOperator]⟩

/-- Equivalence class of eigenforms? Do we need the components on Hecke characters? -/
def HeckeAlgebra.decompInd : Type _ := F × R × D × U × S × (sorry : Type)

variable (ℓ : ℕ) [Fact ℓ.Prime]

local notation "ℚ‾_[" ℓ "]" => AlgebraicClosure (ℚ_[ℓ])

/-- Maybe depends on an identification `ℚ‾_[ℓ] ≃ ℂ` -/
def HeckeAlgebra.decomp : 𝕋 ℚ‾_[ℓ] S ≃ₐ[ℚ‾_[ℓ]] (HeckeAlgebra.decompInd F R D U S) → ℚ‾_[ℓ] := sorry

variable {L} [Field L] [Algebra ℚ_[ℓ] L] [Module.Finite ℚ_[ℓ] L] -- Some finite extension `L / ℚℓ`
variable {𝒪L} [CommRing 𝒪L] [LocalRing 𝒪L] [Algebra 𝒪L L] [IsFractionRing 𝒪L L] [Algebra.IsIntegral ℤ 𝒪L] -- ring of integers of L
variable {𝔽} [Field 𝔽] [Algebra 𝒪L 𝔽] [IsLocalRingHom (algebraMap 𝒪L 𝔽)]
variable (h : Function.Bijective (LocalRing.ResidueField.lift (algebraMap 𝒪L 𝔽))) -- 𝔽 is the residue field of 𝒪L (do we need this?)

variable (ι : 𝒪L →+* ℚ‾_[ℓ]) -- Fix an embedding

-- Is this true?
lemma HeckeAlgebra.isIntegral : IsIntegral ℤ ((decomp F R D U S ℓ) ((mapRingHom F R D U S ι) i) t) := sorry

noncomputable
def HeckeAlgebra.field : Subfield (ℚ‾_[ℓ]) := Subfield.closure ι.range ⊔ ⨆ i : HeckeAlgebra.decompInd F R D U S,
  Subfield.closure ((Pi.evalRingHom _ i).comp <| (HeckeAlgebra.decomp F R D U S ℓ).toAlgHom.toRingHom.comp
    (HeckeAlgebra.mapRingHom F R D U S ι)).range.carrier

local notation "L'" => HeckeAlgebra.field F R D U S ℓ ι

local notation "𝒪L'" => integralClosure ℤ L'

instance : LocalRing 𝒪L' := sorry

noncomputable
def HeckeAlgebra.toPiField : 𝕋 𝒪L S →+* (HeckeAlgebra.decompInd F R D U S) → L' :=
  Pi.ringHom (fun i ↦ ((Pi.evalRingHom _ i).comp <| (HeckeAlgebra.decomp F R D U S ℓ).toAlgHom.toRingHom.comp
    (HeckeAlgebra.mapRingHom F R D U S ι)).codRestrict L'
    (fun t ↦ SetLike.le_def.mp ((le_iSup _ i).trans le_sup_right) (by exact Subfield.subset_closure ⟨t, rfl⟩)))

lemma HeckeAlgebra.isIntegral_toPiField (i t) : IsIntegral ℤ (HeckeAlgebra.toPiField F R D U S ℓ ι i t) :=
  (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ L' ℚ‾_[ℓ]) Subtype.val_injective).mp (HeckeAlgebra.isIntegral ..)

noncomputable
def HeckeAlgebra.toPiRingHom : 𝕋 𝒪L S →+* (HeckeAlgebra.decompInd F R D U S) → 𝒪L' :=
  Pi.ringHom (fun i ↦ ((Pi.evalRingHom _ i).comp <| HeckeAlgebra.toPiField F R D U S ℓ ι).codRestrict 𝒪L'
    (fun _ ↦ HeckeAlgebra.isIntegral_toPiField ..))

noncomputable
def HeckeAlgebra.toIntegralClosureField : 𝒪L →+* 𝒪L' :=
  (ι.codRestrict L' (fun t ↦ SetLike.le_def.mp le_sup_left (by exact Subfield.subset_closure ⟨t, rfl⟩))).codRestrict 𝒪L'
  (fun t ↦ (Algebra.IsIntegral.isIntegral (R := ℤ) t).map (RingHom.toIntAlgHom _))

noncomputable
instance : Algebra 𝒪L 𝒪L' := (HeckeAlgebra.toIntegralClosureField F R D U S ℓ ι).toAlgebra

noncomputable
def HeckeAlgebra.toPi : 𝕋 𝒪L S →ₐ[𝒪L] (HeckeAlgebra.decompInd F R D U S) → 𝒪L' where
  __ := toPiRingHom F R D U S ℓ ι
  commutes' x := by
    ext i
    letI := ι.toAlgebra
    show HeckeAlgebra.decomp F R D U S ℓ (map F R D U 𝒪L S ℚ‾_[ℓ] _) i = ι x
    rw [AlgHom.commutes, IsScalarTower.algebraMap_eq 𝒪L ℚ‾_[ℓ] (𝕋 ℚ‾_[ℓ] S), RingHom.comp_apply,
      AlgEquiv.commutes]
    rfl


-- We can prove some finite-ness condition on `𝕋` or `𝒪L`.
