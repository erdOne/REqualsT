import Mathlib
import REqualsT.ModularForm.HeckeAlgebra
import REqualsT.GaloisTheory.Frob
import REqualsT.Utils.CompleteRing

universe u

open TensorProduct DedekindDomain IsDedekindDomain

variable (F : Type u) [Field F] [NumberField F] -- totally real number field with 2 | [F : ℚ]

variable (R) [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F] -- 𝒪_F

variable (D) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D] [RamifiedExactlyAtInfinitePlaces F D] -- the quaternion algebra

variable (U : Subgroup (GL (Fin 2) (FiniteAdeleRing R F))) -- Need open-compact and some integrality conditions.

variable (A) [CommRing A]

local notation "𝒮" => AutomorphicForm F R D U

local notation "T" => heckeOperator F R D U
local notation "𝕋" => HeckeAlgebra F R D U
local notation "𝕋.T" => HeckeAlgebra.heckeOperator F R D U

variable {L} [Field L]
variable (𝒪L) [CommRing 𝒪L] [LocalRing 𝒪L] [Algebra 𝒪L L] [IsFractionRing 𝒪L L] [Algebra.IsIntegral ℤ 𝒪L] -- ring of integers of L

variable (S : Finset (HeightOneSpectrum R)) -- Need condition U ⊇ GL₂(𝒪_F^S) x (some open ⊆ Π_{v ∈ S} GL₂(Fᵥ))

variable (ℓ : ℕ) [Fact ℓ.Prime]

local notation "ℚ‾_[" ℓ "]" => AlgebraicClosure (ℚ_[ℓ])

variable [Algebra ℚ_[ℓ] L] [Module.Finite ℚ_[ℓ] L] -- Some finite extension `L / ℚℓ`

variable (ι : 𝒪L →+* ℚ‾_[ℓ]) -- Fix an embedding

local notation "L'" => HeckeAlgebra.field F R D U S ℓ ι

local notation "𝒪L'" => integralClosure ℤ L'

attribute [local instance] LocalRing.withIdeal

variable (r : ContinuousMonoidHom (Field.absoluteGaloisGroup F) (GL (Fin 2) 𝒪L)) -- regular algebraic ℓ-adic rep

def HeckeAlgebra.maximalIdeal : Ideal (𝕋 𝒪L S) :=
  (LocalRing.maximalIdeal 𝒪L).map (algebraMap _ _) ⊔
  Ideal.span { 𝕋.T 𝒪L hv - algebraMap _ _ (trFrob F R r v) | (v) (hv : v ∉ S) }

local notation "𝔪" => HeckeAlgebra.maximalIdeal F R D U

lemma HeckeAlgebra.maximalIdeal_ne_top : 𝔪 𝒪L S r ≠ ⊤ := sorry

noncomputable
def HeckeAlgebra.toQuotient : LocalRing.ResidueField 𝒪L →ₐ[𝒪L] 𝕋 𝒪L S ⧸ 𝔪 𝒪L S r :=
  Ideal.quotientMapₐ _ (Algebra.ofId _ _) (by exact Ideal.map_le_iff_le_comap.mp le_sup_left)

set_option linter.unusedSectionVars false in
lemma HeckeAlgebra.toQuotient_mk (x) :
  toQuotient F R D U 𝒪L S r (Ideal.Quotient.mk _ x) = algebraMap 𝒪L (𝕋 𝒪L S ⧸ 𝔪 𝒪L S r) x := rfl

attribute [local instance 99999] Ideal.Quotient.isScalarTower SetLike.instIsScalarTower AddCommGroup.toAddGroup

set_option linter.unusedSectionVars false in
lemma HeckeAlgebra.toQuotient_surjective : Function.Surjective (toQuotient F R D U 𝒪L S r) := by
  rw [← Algebra.range_top_iff_surjective, ← top_le_iff,
    ← (Algebra.range_top_iff_surjective (IsScalarTower.toAlgHom 𝒪L (𝕋 𝒪L S) (𝕋 𝒪L S ⧸ 𝔪 𝒪L S r))).mpr,
    ← Algebra.map_top,
    ← adjoin_heckeOperator, Subalgebra.map_le, Algebra.adjoin_le_iff]
  · rintro x ⟨v, hv, rfl⟩
    use Ideal.Quotient.mk _ (trFrob F R r v)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, toQuotient_mk, IsScalarTower.coe_toAlgHom,
      Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_eq 𝒪L (𝕋 𝒪L S) (𝕋 𝒪L S ⧸ 𝔪 𝒪L S r),
      RingHom.comp_apply]
    rw [eq_comm, ← sub_eq_zero, ← RingHom.map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact SetLike.le_def.mp le_sup_right (Ideal.subset_span (by exact ⟨v, hv, rfl⟩))
  · exact Ideal.Quotient.mk_surjective

noncomputable
def HeckeAlgebra.quotientEquiv : (𝕋 𝒪L S ⧸ 𝔪 𝒪L S r) ≃ₐ[𝒪L] LocalRing.ResidueField 𝒪L := by
  haveI : Nontrivial (𝕋 𝒪L S ⧸ 𝔪 𝒪L S r) :=
    Ideal.Quotient.nontrivial (HeckeAlgebra.maximalIdeal_ne_top F R D U 𝒪L S r)
  refine (AlgEquiv.ofBijective (HeckeAlgebra.toQuotient F R D U 𝒪L S r)
    ⟨(HeckeAlgebra.toQuotient F R D U 𝒪L S r).toRingHom.injective,
      HeckeAlgebra.toQuotient_surjective F R D U 𝒪L S r⟩).symm

instance : (𝔪 𝒪L S r).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    ((HeckeAlgebra.quotientEquiv F R D U 𝒪L S r).toMulEquiv.isField _
      (Semifield.toIsField (LocalRing.ResidueField 𝒪L)))

/-- The equivalence class of eigenforms whose associated mod-`ℓ` reps coincide with r mod `ℓ`. -/
def HeckeAlgebra.LocInd : Type := (sorry : _ → _ → Type) (F × R × D × U × S) r

def HeckeAlgebra.LocInd.toInd : HeckeAlgebra.LocInd F R D U 𝒪L S r → HeckeAlgebra.decompInd F R D U S := sorry

instance : Nonempty (HeckeAlgebra.LocInd F R D U 𝒪L S r) := sorry
instance : Fintype (HeckeAlgebra.LocInd F R D U 𝒪L S r) := sorry -- is this true?

-- In #15131
@[simps!]
def Pi.algHom {R : Type*} {I} {f : I → Type*} [CommSemiring R] [s : ∀ i, Semiring (f i)]
    [∀ i, Algebra R (f i)] {A} [Semiring A] [Algebra R A] (g : ∀ i, A →ₐ[R] f i) :
      A →ₐ[R] ∀ i, f i where
  __ := Pi.ringHom fun i ↦ (g i).toRingHom
  commutes' r := by ext; simp

variable {𝒪L} in
noncomputable
def HeckeAlgebra.toPiLocInd : 𝕋 𝒪L S →ₐ[𝒪L] (HeckeAlgebra.LocInd F R D U 𝒪L S r) → 𝒪L' :=
  (Pi.algHom (fun i ↦ Pi.evalAlgHom _ _ i.toInd)).comp (HeckeAlgebra.toPi F R D U S ℓ ι)

lemma HeckeAlgebra.isUnit_toPiLocInd (x) (hx : x ∉ 𝔪 𝒪L S r) : IsUnit (toPiLocInd F R D U S ℓ ι r x) := sorry

abbrev HeckeAlgebra.localization := Localization.AtPrime (𝔪 𝒪L S r)

local notation "𝕋𝔪" => HeckeAlgebra.localization F R D U

noncomputable
def HeckeAlgebra.locToPiRingHom : 𝕋𝔪 𝒪L S r →+* (HeckeAlgebra.LocInd F R D U 𝒪L S r) → 𝒪L' :=
  IsLocalization.lift (fun x : (𝔪 𝒪L S r).primeCompl ↦ isUnit_toPiLocInd F R D U 𝒪L S ℓ ι r x x.2)

attribute [local instance 99999] OreLocalization.instIsScalarTower

noncomputable
def HeckeAlgebra.locToPi : 𝕋𝔪 𝒪L S r →ₐ[𝒪L] (HeckeAlgebra.LocInd F R D U 𝒪L S r) → 𝒪L' where
  __ := locToPiRingHom F R D U 𝒪L S ℓ ι r
  commutes' x := by
    rw [IsScalarTower.algebraMap_eq 𝒪L (𝕋 𝒪L S) (𝕋𝔪 𝒪L S r)]
    simp only [locToPiRingHom, AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.coe_comp, Function.comp_apply, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, IsLocalization.lift_eq, RingHom.coe_coe, AlgHom.commutes]

lemma HeckeAlgebra.locToPi_injective : Function.Injective (locToPi F R D U 𝒪L S ℓ ι r) := sorry

def LocalRing.modConstSubalgebra (I R : Type*) [CommRing R] [LocalRing R] : Subalgebra R (I → R) where
  carrier := { s | ∀ i j, s i - s j ∈ maximalIdeal R }
  mul_mem' {a b} ha hb i j := by
    convert add_mem (Ideal.mul_mem_right (b i) _ (ha i j)) (Ideal.mul_mem_left _ (a j) (hb i j)) using 1
    dsimp
    ring
  add_mem' {a b} ha hb i j := by
    convert add_mem (ha i j) (hb i j) using 1
    exact add_sub_add_comm ..
  algebraMap_mem' r i j := by
    convert zero_mem (maximalIdeal R) using 1
    exact sub_self _

lemma Pi.isUnit_iff {I R : Type*} [Monoid R] {f : I → R} : IsUnit f ↔ ∀ i, IsUnit (f i) :=
  ⟨fun H i ↦ H.map (Pi.evalMonoidHom _ i), fun H ↦ ⟨⟨f, fun i ↦ ((H i).unit⁻¹ : _),
    funext fun i ↦ (H i).unit.3, funext fun i ↦ (H i).unit.4⟩, rfl⟩⟩

lemma LocalRing.isUnit_modConstSubalgebra {I R : Type*} [CommRing R] [LocalRing R]
    (a : modConstSubalgebra I R) (i : I) (ha : IsUnit (a.1 i)) :
    IsUnit a := by
    have : IsUnit a.1 := by
      refine Pi.isUnit_iff.mpr fun j ↦ ?_
      by_contra H
      apply (LocalRing.maximalIdeal R).add_mem (a.2 i j) H
      rwa [sub_add_cancel]
    have H : ∀ i, (this.unit⁻¹).1 i * a.1 i = 1 := fun i ↦ congr_fun this.unit.4 i
    refine ⟨⟨a, ⟨(this.unit⁻¹).1, fun i j ↦ ?_⟩, Subtype.ext this.unit.3, Subtype.ext this.unit.4⟩, rfl⟩
    convert Ideal.mul_mem_left _ ((this.unit⁻¹).1 i * (this.unit⁻¹).1 j) (a.2 j i) using 1
    rw [mul_sub, mul_assoc, H, mul_one, mul_comm ((this.unit⁻¹).1 i), mul_assoc, H, mul_one]

instance (I R : Type*) [CommRing R] [LocalRing R] [Nonempty I] :
    LocalRing (LocalRing.modConstSubalgebra I R) where
  isUnit_or_isUnit_of_add_one {a b} e := by
    have ⟨i⟩ := ‹Nonempty I›
    wlog h : IsUnit (a.1 i) generalizing a b
    · refine (@this b a (add_comm a b ▸ e) ?_).symm
      exact (LocalRing.isUnit_or_isUnit_of_add_one (congr_fun congr($e.1) i)).resolve_left h
    exact Or.inl (LocalRing.isUnit_modConstSubalgebra a i h)

lemma LocalRing.mem_maximalIdeal_modConstSubalgebra
    {I R : Type*} [CommRing R] [LocalRing R] [Nonempty I] {a} :
    a ∈ maximalIdeal (modConstSubalgebra I R) ↔ ∀ i, a.1 i ∈ maximalIdeal R := by
  constructor
  · exact fun H ↦ (H <| isUnit_modConstSubalgebra a · ·)
  · have ⟨i⟩ := ‹Nonempty I›
    intro H ha
    exact H i (Pi.isUnit_iff.mp (ha.map (modConstSubalgebra I R).val) i)

attribute [local instance 99999] Function.algebra

noncomputable
def HeckeAlgebra.subalgebraPi : Type _ :=
  LocalRing.modConstSubalgebra (HeckeAlgebra.LocInd F R D U 𝒪L S r) 𝒪L'

noncomputable
instance : CommRing (HeckeAlgebra.subalgebraPi F R D U 𝒪L S ℓ ι r) := by
  delta HeckeAlgebra.subalgebraPi; infer_instance
instance : LocalRing (HeckeAlgebra.subalgebraPi F R D U 𝒪L S ℓ ι r) := by
  delta HeckeAlgebra.subalgebraPi; infer_instance
set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
noncomputable
instance {R₀} [CommRing R₀] [Algebra R₀ 𝒪L'] : Algebra R₀ (HeckeAlgebra.subalgebraPi F R D U 𝒪L S ℓ ι r) :=
  Subalgebra.algebra' (LocalRing.modConstSubalgebra (HeckeAlgebra.LocInd F R D U 𝒪L S r) 𝒪L')
instance : IsNoetherianRing (HeckeAlgebra.subalgebraPi F R D U 𝒪L S ℓ ι r) := sorry -- easy?
instance : IsCompleteLocalRing (HeckeAlgebra.subalgebraPi F R D U 𝒪L S ℓ ι r) := sorry

lemma HeckeAlgebra.locToPi_mem_subalgebraPi (x) :
    locToPi F R D U 𝒪L S ℓ ι r x ∈ LocalRing.modConstSubalgebra (HeckeAlgebra.LocInd F R D U 𝒪L S r) 𝒪L' := sorry

set_option synthInstance.maxHeartbeats 0 in
noncomputable
def HeckeAlgebra.locToSubalgebraPi : 𝕋𝔪 𝒪L S r →ₐ[𝒪L] subalgebraPi F R D U 𝒪L S ℓ ι r :=
  (locToPi F R D U 𝒪L S ℓ ι r).codRestrict
    ((LocalRing.modConstSubalgebra (HeckeAlgebra.LocInd F R D U 𝒪L S r) 𝒪L').restrictScalars 𝒪L)
    (locToPi_mem_subalgebraPi F R D U 𝒪L S ℓ ι r)

lemma HeckeAlgebra.locToSubalgebraPi_injective :
    Function.Injective (locToSubalgebraPi F R D U 𝒪L S ℓ ι r) :=
  fun _ _ e ↦ locToPi_injective F R D U 𝒪L S ℓ ι r congr($e.1)
