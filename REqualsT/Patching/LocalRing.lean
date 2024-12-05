import Mathlib
import REqualsT.Patching.VanishingFilter

set_option autoImplicit false
variable (R₀ : Type*) [CommRing R₀]
variable {ι : Type*} {R M : ι → Type*} [∀ i, CommRing (R i)] [∀ i, AddCommGroup (M i)]
variable [∀ i, Algebra R₀ (R i)] [∀ i, Module (R i) (M i)]
variable (I : ∀ i, Ideal (R i)) (N : ∀ i, Submodule (R i) (M i))
variable [∀ i, IsLocalRing (R i)]


open IsLocalRing

local notation "𝔭(" F ")" => eventuallyProd (maximalIdeal <| R ·) F

lemma le_eventuallyProd_vanishingFilter (p : Ideal (Π i, R i)) :
    p ≤ 𝔭(vanishingFilter p) :=
  fun _ ↦ eventually_vanishingFilter_not_isUnit _

lemma eventuallyProd_vanishingFilter_eq_iff {p : Ideal (Π i, R i)} :
    𝔭(vanishingFilter p) = p ↔
      Ideal.jacobson ⊥ ≤ p := by
  rw [le_antisymm_iff, and_iff_left (le_eventuallyProd_vanishingFilter _),
    eventuallyProd_eq_sup, sup_le_iff, and_iff_right (eventuallyProd_vanishingFilter_le _),
    ← pi'_jacobson]
  congr! with i
  exact (IsLocalRing.jacobson_eq_maximalIdeal _ (by simp)).symm

lemma eventuallyProd_vanishingFilter (p : Ideal (Π i, R i))
    (hp : Ideal.jacobson ⊥ ≤ p) :
    𝔭(vanishingFilter p) = p :=
  eventuallyProd_vanishingFilter_eq_iff.mpr hp

@[simps]
def IsLocalRing.idealPiEquiv :
    { I : Ideal (Π i, R i) // Ideal.jacobson ⊥ ≤ I } ≃ Filter ι where
  toFun p := vanishingFilter p.1
  invFun F := ⟨𝔭(F), by
    rw [← eventuallyProd_vanishingFilter_eq_iff, vanishingFilter_eventuallyProd]
    exact fun i ↦ Ideal.IsPrime.ne_top'⟩
  left_inv p := Subtype.ext (eventuallyProd_vanishingFilter_eq_iff.mpr p.2)
  right_inv F := vanishingFilter_eventuallyProd _ _ (fun i ↦ Ideal.IsPrime.ne_top')

def IsLocalRing.idealPiQuotientEquiv :
    Ideal ((Π i, R i) ⧸ (Ideal.jacobson (R := Π i, R i) ⊥)) ≃ Filter ι :=
  (Ideal.idealQuotientEquiv _).trans idealPiEquiv

@[simps]
def IsLocalRing.idealPiIsPrimeEquiv :
    { I : Ideal (Π i, R i) // I.IsPrime ∧ Ideal.jacobson ⊥ ≤ I } ≃ Ultrafilter ι where
  toFun p := letI := p.2.1; vanishingUltrafilter p.1
  invFun F := ⟨𝔭(F), by
    rw [← eventuallyProd_vanishingFilter_eq_iff, vanishingFilter_eventuallyProd]
    exacts [⟨inferInstance, rfl⟩, fun i ↦ Ideal.IsPrime.ne_top']⟩
  left_inv p := Subtype.ext (eventuallyProd_vanishingFilter_eq_iff.mpr p.2.2)
  right_inv F := Ultrafilter.coe_injective
    (vanishingFilter_eventuallyProd _ _ (fun i ↦ Ideal.IsPrime.ne_top'))

variable (F : Ultrafilter ι)

section UltraProduct

variable (R)

abbrev UltraLocalization := Localization.AtPrime 𝔭(F)

lemma ker_algebraMap_localization_eventuallyProd :
    RingHom.ker (algebraMap (Π i, R i) (UltraLocalization R F)) =
      eventuallyProd ⊥ F := by
  ext x
  suffices (∃ a, (∀ᶠ i in F, IsUnit (a i)) ∧ a * x = 0) ↔ ∀ᶠ i in F, x i = 0 by
    simp only [RingHom.mem_ker, mem_eventuallyProd,
      IsLocalization.map_eq_zero_iff (M := Ideal.primeCompl 𝔭(F))]
    simpa [Ideal.primeCompl]
  constructor
  · rintro ⟨a, h₁, h₂⟩
    filter_upwards [h₁] with i hi
    apply hi.mul_right_injective
    simpa using congr_fun h₂ i
  · intro H
    classical
    refine ⟨(if x · = 0 then 1 else 0), ?_, by aesop⟩
    filter_upwards [H] with i hi
    simp [hi]

def UltraProduct.toLocalization :
    UltraProduct R F →ₐ[R₀] UltraLocalization R F :=
  Ideal.Quotient.liftₐ (eventuallyProd (R := R) (M := R) ⊥ F)
    (IsScalarTower.toAlgHom _ _ _)
    (ker_algebraMap_localization_eventuallyProd R F).ge

lemma UltraProduct.toLocalization_injective :
    Function.Injective (toLocalization R₀ R F) :=
  RingHom.lift_injective_of_ker_le_ideal _ _
    (ker_algebraMap_localization_eventuallyProd R F).le

variable (M) in
abbrev UltraModuleLocalization := LocalizedModule (Ideal.primeCompl 𝔭(F)) (Π i, M i)

variable (M) in
abbrev UltraModuleLocalization.mkLinearMap : (Π i, M i) →ₗ[Π i, R i] UltraModuleLocalization R M F :=
  LocalizedModule.mkLinearMap _ _

-- set_option diagnostics true in
lemma ker_mkLinearMap_localization_eventuallyProd :
    LinearMap.ker (LocalizedModule.mkLinearMap (Ideal.primeCompl 𝔭(F)) (Π i, M i)) =
      eventuallyProd ⊥ F := by
  ext x
  suffices (∃ a : Π i, R i, (∀ᶠ i in F, IsUnit (a i)) ∧ a • x = 0) ↔ ∀ᶠ i in F, x i = 0 by
    simpa only [Ideal.primeCompl, LinearMap.mem_ker, LocalizedModule.mkLinearMap_apply,
      ← LocalizedModule.zero_mk (s := 1), LocalizedModule.mk_eq, one_smul, Submonoid.smul_def,
      smul_zero (M := Π i, R i), Subtype.exists, Submonoid.mem_mk, Subsemigroup.mem_mk,
      SetLike.mem_coe, mem_eventuallyProd, mem_maximalIdeal, mem_nonunits_iff, Set.mem_compl_iff,
      Filter.not_eventually, not_not, Ultrafilter.frequently_iff_eventually, exists_prop,
      Pi.bot_apply, Submodule.mem_bot]
  constructor
  · rintro ⟨a, h₁, h₂⟩
    filter_upwards [h₁] with i hi
    rw [← hi.smul_left_cancel]
    simpa using congr_fun h₂ i
  · intro H
    classical
    refine ⟨(if x · = 0 then 1 else 0), ?_, by ext; simp⟩
    filter_upwards [H] with i hi
    simp [hi]

variable (M) in
def UltraProduct.toModuleLocalization :
    UltraProduct M F →ₗ[Π i, R i] UltraModuleLocalization R M F :=
  Submodule.liftQ (eventuallyProd (R := R) (M := M) ⊥ F)
    (LocalizedModule.mkLinearMap (Ideal.primeCompl 𝔭(F)) (Π i, M i))
    (ker_mkLinearMap_localization_eventuallyProd ..).ge

@[simp]
lemma UltraProduct.toModuleLocalization_πₗ (x) :
    toModuleLocalization R M F (πₗ R M F x) =
      UltraModuleLocalization.mkLinearMap R M F x := rfl

lemma UltraProduct.toModuleLocalization_injective :
    Function.Injective (toModuleLocalization R M F) := by
  rw [← LinearMap.ker_eq_bot, toModuleLocalization, Submodule.ker_liftQ_eq_bot]
  exact (ker_mkLinearMap_localization_eventuallyProd ..).le

end UltraProduct

section Finite

variable [Finite R₀] (H : ∀ᶠ i in F, Function.Bijective (algebraMap R₀ (R i)))

include H in
/--
If `R₀` is a finite cardinality local ring, and `Rᵢ` is a family of `R₀` algebras
such that `F`-many of them are isomorphic to `R₀`,
then the localization `Π Rᵢ` at `𝔭(F)` is isomorphic to `R₀`.
-/
lemma UltraLocalization.bijective_of_eventually_bijective :
    Function.Bijective (algebraMap R₀ (UltraLocalization R F)) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intros x hx
    rw [IsScalarTower.algebraMap_apply R₀ (Π i, R i) (Localization.AtPrime _),
      IsLocalization.map_eq_zero_iff (M := Ideal.primeCompl 𝔭(F))] at hx
    obtain ⟨a, ha₁, ha₂⟩ : ∃ a : Π i, R i, (∀ᶠ i in F, IsUnit (a i)) ∧
        ∀ i, a i * (algebraMap R₀ _) x = 0 := by
      simpa [Ideal.primeCompl, funext_iff] using hx
    obtain ⟨i, hi, hi'⟩ := (H.and ha₁).exists
    apply hi.1
    simpa only [mul_zero, ← mul_assoc, IsUnit.val_inv_mul, one_mul, map_zero]
      using congr(hi'.unit⁻¹ * $(ha₂ i))
  · intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.primeCompl 𝔭(F)) x
    simp_rw [IsScalarTower.algebraMap_apply R₀ (Π i, R i) (Localization.AtPrime _),
      ← IsLocalization.mk'_one (M := Ideal.primeCompl 𝔭(F)),
      IsLocalization.mk'_eq_iff_eq (M := Ideal.primeCompl 𝔭(F)),
      IsLocalization.eq_iff_exists (Ideal.primeCompl 𝔭(F))]
    simp only [Ideal.primeCompl, OneMemClass.coe_one, one_mul, funext_iff, Pi.mul_apply,
      Pi.algebraMap_apply, Subtype.exists, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, mem_eventuallyProd, mem_maximalIdeal, mem_nonunits_iff, Filter.not_eventually,
      not_not, Ultrafilter.frequently_iff_eventually, exists_prop] at hs ⊢
    have : ∀ᶠ i in F, ∃ b : R₀, s i * algebraMap R₀ (R i) b = x i := by
      filter_upwards [H, hs] with i hi hsi
      obtain ⟨z, hz⟩ := hi.2 (hsi.unit⁻¹ * x i)
      exact ⟨z, by rw [hz, ← mul_assoc, IsUnit.mul_val_inv, one_mul]⟩
    obtain ⟨b, hb⟩ := F.eventually_exists_of_finite.mp this
    refine ⟨b, (fun i ↦ if s i * algebraMap _ _ b = x i then 1 else 0), ?_, ?_⟩
    · filter_upwards [hb] with i hi
      rw [if_pos hi]; exact isUnit_one
    · intro i
      simp only [ite_mul, one_mul, zero_mul]
      split_ifs
      · assumption
      · rfl

include H in
lemma UltraProduct.bijective_toLocalization_of_eventually_bijective :
    Function.Bijective (toLocalization R₀ R F) :=
  ⟨toLocalization_injective .., .of_comp (g := algebraMap R₀ _) <| by
    convert (UltraLocalization.bijective_of_eventually_bijective R₀ F H).2⟩

include H in
lemma UltraProduct.bijective_algebraMap_of_eventually_bijective :
    Function.Bijective (algebraMap R₀ (UltraProduct R F)) :=
  (Function.Bijective.of_comp_iff' (bijective_toLocalization_of_eventually_bijective R₀ F H) _).mp
    (by convert UltraLocalization.bijective_of_eventually_bijective R₀ F H)

variable [∀ i, Module R₀ (M i)] [∀ i, IsScalarTower R₀ (R i) (M i)]

include H in
lemma UltraProduct.bijective_toModuleLocalization_of_eventually_bijective :
    Function.Bijective (UltraProduct.toModuleLocalization R M F) := by
  classical
  refine ⟨UltraProduct.toModuleLocalization_injective .., ?_⟩
  intro z
  induction' z using LocalizedModule.induction_on with m s
  obtain ⟨t, ht⟩ := (UltraLocalization.bijective_of_eventually_bijective R₀ F H).2 (Localization.mk 1 s)
  refine ⟨t • .πₗ R M F m, ?_⟩
  rw [← IsScalarTower.algebraMap_smul (Π i, R i), map_smul,
    ← IsScalarTower.algebraMap_smul (UltraLocalization R F),
    ← IsScalarTower.algebraMap_apply, ht]
  show Localization.mk 1 s • LocalizedModule.mk m 1 = _
  rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]

lemma UltraProduct.bijective_toModuleLocalization [IsLocalRing R₀] :
    Function.Bijective (UltraProduct.toModuleLocalization (fun _ ↦ R₀) M F) :=
  bijective_toModuleLocalization_of_eventually_bijective R₀ _ (.of_forall fun _ ↦ Function.bijective_id)

end Finite
