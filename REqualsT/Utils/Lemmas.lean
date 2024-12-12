import Mathlib.Data.Finsupp.Fintype
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Finiteness.TensorProduct
import Mathlib.RingTheory.JacobsonIdeal
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.Support
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Ideal.MinimalPrime
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic

lemma IsUnit.pi_iff {ι} {M : ι → Type*} [∀ i, Monoid (M i)] {x : Π i, M i} :
    IsUnit x ↔ ∀ i, IsUnit (x i) := by
  simp_rw [isUnit_iff_exists, funext_iff, ← forall_and]
  exact Classical.skolem (p := fun i y ↦ x i * y = 1 ∧ y * x i = 1).symm

lemma forall_prod_iff {ι} {β : ι → Type*} (P : ∀ i, β i → Prop) [∀ i, Nonempty (β i)]:
    (∀ i : ι, ∀ (y : Π i, β i), P i (y i)) ↔ (∀ i y, P i y) :=
  letI := Classical.decEq
  ⟨fun H i y ↦ by simpa using H i (fun j ↦ if h : i = j then h ▸ y else
    Nonempty.some inferInstance), fun H i y ↦ H _ _⟩

@[simps]
def Ideal.idealQuotientEquiv {R : Type*} [CommRing R] (I : Ideal R) :
  Ideal (R ⧸ I) ≃ { J // I ≤ J } where
    toFun J := ⟨J.comap (Ideal.Quotient.mk I),
      (I.mk_ker : _).symm.trans_le (Ideal.comap_mono bot_le)⟩
    invFun J := J.1.map (Ideal.Quotient.mk I)
    left_inv J := map_comap_of_surjective _ Quotient.mk_surjective _
    right_inv J := by
      ext1
      simpa [comap_map_of_surjective _ Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot] using J.2

set_option autoImplicit false
variable {ι : Type*} {R M : ι → Type*} [∀ i, CommRing (R i)] [∀ i, AddCommGroup (M i)]
variable [∀ i, Module (R i) (M i)]
variable (I : ∀ i, Ideal (R i)) (N : ∀ i, Submodule (R i) (M i))

def Submodule.pi' : Submodule (Π i, R i) (Π i, M i) where
  carrier := { x | ∀ i, x i ∈ N i }
  add_mem' := by aesop
  zero_mem' := by aesop
  smul_mem' := by aesop

variable {N} in
@[simp]
lemma Submodule.mem_pi' {x} : x ∈ Submodule.pi' N ↔ ∀ i, x i ∈ N i := Iff.rfl

open scoped Filter in
lemma Ultrafilter.eventually_exists_of_finite {ι α : Type*} (F : Ultrafilter ι)
    {P : α → ι → Prop} [Finite α] :
    (∀ᶠ i in F, ∃ a, P a i) ↔ ∃ a, ∀ᶠ i in F, P a i := by
  simp only [Filter.Eventually, Ultrafilter.mem_coe]
  convert F.finite_biUnion_mem_iff Set.finite_univ (s := P) with i
  · ext; simp; rfl
  · simp; rfl

variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module (R i) (N i)] in
@[simps]
def LinearMap.piMap (f : ∀ i, M i →ₗ[R i] N i) : (Π i, M i) →ₗ[Π i, R i] Π i, N i where
  toFun g i := f i (g i)
  map_add' := by aesop
  map_smul' := by aesop

instance {ι : Type*} {R A : ι → Type*} [∀ i, CommSemiring (R i)]
    [∀ i, Semiring (A i)] [∀ i, Algebra (R i) (A i)] : Algebra (Π i, R i) (Π i, A i) where
  __ := Pi.ringHom fun i ↦ (algebraMap (R i) (A i)).comp (Pi.evalRingHom R i)
  commutes' r a := funext fun i ↦ Algebra.commutes _ _
  smul_def' r a := funext fun i ↦ by simp [Algebra.smul_def]

lemma pi'_jacobson :
    Submodule.pi' (fun i ↦ Ideal.jacobson (R := R i) ⊥) = Ideal.jacobson ⊥ := by
  ext v
  simp only [Submodule.mem_pi', Ideal.mem_jacobson_bot, IsUnit.pi_iff]
  conv_rhs => rw [forall_comm]
  exact (forall_prod_iff (fun i y ↦ IsUnit (v i * y + 1))).symm

open TensorProduct in
lemma Submodule.finite_quotient_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (I : Ideal R) {N : Submodule R M} [Finite (R ⧸ I)] [Finite (M ⧸ N)] (hN : N.FG) : Finite (M ⧸ I • N) := by
  suffices (I • N).toAddSubgroup.FiniteIndex by
    exact (I • N).toAddSubgroup.finite_quotient_of_finiteIndex
  suffices Nat.card (N ⧸ (I • N).comap N.subtype) ≠ 0 by
    constructor
    rw [← AddSubgroup.relindex_mul_index
      (H := (I • N).toAddSubgroup) (K := N.toAddSubgroup) Submodule.smul_le_right]
    have inst : Finite (M ⧸ N.toAddSubgroup) := ‹_›
    exact mul_ne_zero this AddSubgroup.index_ne_zero_of_finite
  let e : (N ⧸ (I • N).comap N.subtype) ≃ₗ[R] (R ⧸ I) ⊗[R] N :=
    Submodule.quotEquivOfEq _ (I • (⊤ : Submodule R N)) (Submodule.map_injective_of_injective
      N.injective_subtype (by simp [Submodule.smul_le_right])) ≪≫ₗ (quotTensorEquivQuotSMul N I).symm
  rw [Nat.card_congr e.toEquiv]
  have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
  have : Finite ((R ⧸ I) ⊗[R] N) := Module.finite_of_finite (R ⧸ I)
  exact Nat.card_pos.ne'

open TensorProduct in
lemma Submodule.index_quotient_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) {N : Submodule R M} [Finite (R ⧸ I)]
    (s : Finset M) (hs : Submodule.span R s = N) :
    (I • N).toAddSubgroup.index ≤ I.toAddSubgroup.index ^ s.card * N.toAddSubgroup.index := by
  classical
  cases nonempty_fintype (R ⧸ I)
  rw [← AddSubgroup.relindex_mul_index
    (H := (I • N).toAddSubgroup) (K := N.toAddSubgroup) Submodule.smul_le_right]
  gcongr
  show (Nat.card (N ⧸ (I • N).comap N.subtype)) ≤ Nat.card (R ⧸ I) ^ s.card
  let e : (N ⧸ (I • N).comap N.subtype) ≃ₗ[R] (R ⧸ I) ⊗[R] N :=
    Submodule.quotEquivOfEq _ (I • (⊤ : Submodule R N)) (Submodule.map_injective_of_injective
      N.injective_subtype (by simp [Submodule.smul_le_right])) ≪≫ₗ (quotTensorEquivQuotSMul N I).symm
  rw [Nat.card_congr e.toEquiv]
  have H : LinearMap.range (Finsupp.linearCombination R (α := s) (↑)) = N := by
    rw [Finsupp.range_linearCombination, ← hs, Subtype.range_val]; rfl
  let f : (s →₀ R) →ₗ[R] N := (Finsupp.linearCombination R (↑)).codRestrict _
    (Set.range_subset_iff (s := N.carrier).mp <| by exact H.le)
  have hf : Function.Surjective f := fun x ↦ by obtain ⟨y, hy⟩ := H.ge x.2; exact ⟨y, Subtype.ext hy⟩
  have : Function.Surjective
      (f.lTensor (R ⧸ I) ∘ₗ (finsuppScalarRight R (R ⧸ I) s).symm.toLinearMap) :=
    (LinearMap.lTensor_surjective (R ⧸ I) hf).comp (LinearEquiv.surjective _)
  refine (Nat.card_le_card_of_surjective _ this).trans ?_
  simp only [Nat.card_eq_fintype_card, Fintype.card_finsupp, Fintype.card_coe, le_rfl]

lemma Ideal.finite_quotient_pow {R : Type*} [CommRing R] {I : Ideal R}
    (hI : I.FG) [Finite (R ⧸ I)] (n) : Finite (R ⧸ I ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top]
    infer_instance
  | succ n _ =>
    exact Submodule.finite_quotient_smul (I ^ n) hI

lemma Ideal.index_quotient_pow {R : Type*} [CommRing R] {I : Ideal R}
    (s : Finset R) (hs : Ideal.span s = I) [Finite (R ⧸ I)] (n) :
    (I ^ n).toAddSubgroup.index ≤ I.toAddSubgroup.index ^ ∑ i in Finset.range n, s.card ^ i := by
  have := Ideal.finite_quotient_pow ⟨s, hs⟩
  induction n with
  | zero =>
    simp
  | succ n IH =>
    refine (Submodule.index_quotient_smul (I ^ n) s hs).trans ?_
    refine (Nat.mul_le_mul (Nat.pow_le_pow_left IH _) le_rfl).trans ?_
    rw [← pow_mul, ← pow_succ, geom_sum_succ, mul_comm]

open Topology in
@[to_additive]
lemma TopologicalGroup.isInducing_of_nhds_one {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [TopologicalGroup G] [TopologicalGroup H] (f : G →* H)
    (hf : 𝓝 (1 : G) = (𝓝 (1 : H)).comap f) : Topology.IsInducing f := by
  rw [Topology.isInducing_iff_nhds]
  intro x
  rw [← nhds_translation_mul_inv, ← nhds_translation_mul_inv (f x), Filter.comap_comap, hf,
    Filter.comap_comap]
  congr 1
  ext; simp

lemma Filter.skolem {ι : Type*} {α : ι → Type*} [∀ i, Nonempty (α i)] {P : ∀ (i : ι), α i → Prop} {F : Filter ι} :
    (∃ b : Π i, α i, ∀ᶠ i in F, P i (b i)) ↔ ∀ᶠ i in F, ∃ b, P i b := by
  classical
  refine ⟨fun ⟨b, hb⟩ ↦ hb.mp (.of_forall fun x a ↦ ⟨_, a⟩), fun H ↦ ?_⟩
  refine ⟨fun i ↦ if h : ∃ b, P i b then h.choose else Nonempty.some inferInstance, ?_⟩
  filter_upwards [H] with i hi
  exact dif_pos hi ▸ hi.choose_spec

instance {R} [CommRing R] [TopologicalSpace R] [CompactSpace R] (I : Ideal R) :
    CompactSpace (R ⧸ I) :=
  Quotient.compactSpace

open Set Pointwise Filter Topology in
theorem exists_mem_nhds_zero_mul_subset {G} [TopologicalSpace G] [MulZeroClass G] [ContinuousMul G]
    {K U : Set G} (hK : IsCompact K) (hU : U ∈ 𝓝 0) : ∃ V ∈ 𝓝 0, K * V ⊆ U := by
  refine hK.induction_on ?_ ?_ ?_ ?_
  · exact ⟨univ, by simp⟩
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V ∩ W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_mul_left V.inter_subset_left).trans hV')
        ((mul_subset_mul_left V.inter_subset_right).trans hW')
  · intro x hx
    have := tendsto_mul (show U ∈ 𝓝 (x * 0) by simpa using hU)
    rw [nhds_prod_eq, mem_map, mem_prod_iff] at this
    rcases this with ⟨t, ht, s, hs, h⟩
    rw [← image_subset_iff, image_mul_prod] at h
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, s, hs, h⟩

lemma isOpen_singleton_zero (K) [GroupWithZero K] [TopologicalSpace K]
    [ContinuousMul K] [CompactSpace K] [T1Space K] :
    IsOpen {(0 : K)} := by
  obtain ⟨U, hU, h0U, h1U⟩ := t1Space_iff_exists_open.mp (inferInstanceAs (T1Space K)) zero_ne_one
  obtain ⟨W, hW, hW'⟩ := exists_mem_nhds_zero_mul_subset isCompact_univ (hU.mem_nhds h0U)
  by_cases H : ∃ x ≠ 0, x ∈ W
  · obtain ⟨x, hx, hxW⟩ := H
    cases h1U (hW' (by simpa [hx] using Set.mul_mem_mul (Set.mem_univ x⁻¹) hxW))
  · obtain rfl : W = {0} := subset_antisymm
      (by simpa [not_imp_not] using H) (by simpa using mem_of_mem_nhds hW)
    simpa [isOpen_iff_mem_nhds]

instance (priority := 100) {K} [DivisionRing K] [TopologicalSpace K]
    [TopologicalRing K] [CompactSpace K] [T2Space K] : Finite K := by
  suffices DiscreteTopology K by
    exact finite_of_compact_of_discrete
  rw [discreteTopology_iff_isOpen_singleton_zero]
  exact isOpen_singleton_zero K

open Topology in
@[to_additive]
theorem exists_subgroup_isOpen_and_subset {α} [TopologicalSpace α]
    [CompactSpace α] [T2Space α] [TotallyDisconnectedSpace α]
    [CommGroup α] [TopologicalGroup α] {U : Set α} (hU : U ∈ 𝓝 1) :
    ∃ G : Subgroup α, IsOpen (X := α) G ∧ (G : Set α) ⊆ U := by
  obtain ⟨V, hVU, hV, h1V⟩ := mem_nhds_iff.mp hU
  obtain ⟨K, hK, hxK, hKU⟩ := compact_exists_isClopen_in_isOpen hV h1V
  obtain ⟨⟨G, hG⟩, hG'⟩ := TopologicalGroup.exist_openSubgroup_sub_clopen_nhd_of_one hK hxK
  exact ⟨G, hG, (hG'.trans hKU).trans hVU⟩

@[simp]
theorem TwoSidedIdeal.span_le {α} [NonUnitalNonAssocRing α] {s : Set α} {I : TwoSidedIdeal α} :
    span s ≤ I ↔ s ⊆ I :=
  ⟨subset_span.trans, fun h _ hx ↦ mem_span_iff.mp hx I h⟩

@[simp]
theorem TwoSidedIdeal.span_neg {α} [NonUnitalNonAssocRing α] (s : Set α) :
    TwoSidedIdeal.span (-s) = TwoSidedIdeal.span s := by
  apply le_antisymm <;> rw [span_le]
  · rintro x hx
    exact neg_neg x ▸ neg_mem _ (subset_span (s := s) hx)
  · rintro x hx
    exact neg_neg x ▸ neg_mem _ (subset_span (Set.neg_mem_neg.mpr hx))

@[simp]
theorem TwoSidedIdeal.span_singleton_zero {α} [NonUnitalNonAssocRing α] :
    span {(0 : α)} = ⊥ :=
  le_bot_iff.mp (span_le.mpr (by simp))

theorem TwoSidedIdeal.mem_span_singleton {α} [NonUnitalNonAssocRing α] {x : α} :
    x ∈ span {x} :=
  subset_span rfl

def TwoSidedIdeal.leAddSubgroup {α} [NonUnitalNonAssocRing α] (G : AddSubgroup α) :
    TwoSidedIdeal α :=
  .mk'
    { x | (span {x} : Set α) ⊆ G }
    (by simp [Set.subset_def, G.zero_mem])
    (fun {x y} hx hy ↦ by
      have : span {x + y} ≤ span {x} ⊔ span {y} :=
        span_le.mpr <| Set.singleton_subset_iff.mpr <|
          mem_sup.mpr ⟨x, mem_span_singleton, y, mem_span_singleton, rfl⟩
      refine subset_trans (c := (G : Set α)) this fun a ha ↦ ?_
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup.mp ha
      exact G.add_mem (hx ha₁) (hy ha₂))
    (fun {x} hx ↦ by simpa only [Set.mem_setOf_eq, ← Set.neg_singleton, TwoSidedIdeal.span_neg])
    (fun {x y} hy ↦ subset_trans (c := (G : Set α))
      (TwoSidedIdeal.span_le.mpr <| by
        simpa using TwoSidedIdeal.mul_mem_left _ x y mem_span_singleton) hy)
    (fun {x y} hy ↦ subset_trans (c := (G : Set α))
      (TwoSidedIdeal.span_le.mpr <| by
        simpa using TwoSidedIdeal.mul_mem_right _ x y mem_span_singleton) hy)

lemma TwoSidedIdeal.leAddSubgroup_subset {α} [NonUnitalNonAssocRing α] (G : AddSubgroup α) :
    (leAddSubgroup G : Set α) ⊆ G :=
  fun x hx ↦ hx ((sub_zero x).symm ▸ mem_span_singleton)

lemma TwoSidedIdeal.mem_leAddSubgroup' {α} [NonUnitalNonAssocRing α] {G : AddSubgroup α} {x : α} :
    x ∈ leAddSubgroup G ↔ (span {x} : Set α) ⊆ G := by
  conv_rhs => rw [← sub_zero x]
  rfl

lemma TwoSidedIdeal.mem_leAddSubgroup {α} [Ring α] {G : AddSubgroup α} {x : α} :
    x ∈ leAddSubgroup G ↔ ∀ a b, a * x * b ∈ G := by
  constructor
  · intro hx a b
    exact hx (mul_mem_right _ _ _ (mul_mem_left _ _ _ ((sub_zero x).symm ▸ mem_span_singleton)))
  · intro H a ha
    simpa using mem_span_iff.mp ha (.mk' { x | ∀ a b, a * x * b ∈ G }
      (by simp [G.zero_mem]) (by simp +contextual [mul_add, add_mul, G.add_mem])
      (by simp) (fun {x y} ↦ by simp +contextual [← mul_assoc _ x y])
      (fun {x y} ↦ by simp +contextual [mul_assoc])) (by simpa) 1 1

open Topology Pointwise in
theorem exists_twoSidedIdeal_isOpen_and_subset {α} [TopologicalSpace α]
    [CompactSpace α] [T2Space α] [TotallyDisconnectedSpace α]
    [Ring α] [TopologicalRing α] {U : Set α} (hU : U ∈ 𝓝 0) :
    ∃ I : TwoSidedIdeal α, IsOpen (X := α) I ∧ (I : Set α) ⊆ U := by
  obtain ⟨G, hG, hGU⟩ := exists_addSubgroup_isOpen_and_subset hU
  refine ⟨_, isOpen_iff_mem_nhds.mpr ?_, (TwoSidedIdeal.leAddSubgroup_subset G).trans hGU⟩
  intro x hx
  replace hx := TwoSidedIdeal.mem_leAddSubgroup.mp hx
  suffices
    ∀ s t, IsCompact s → IsCompact t →
      ∃ V ∈ 𝓝 x, ∀ a ∈ s, ∀ b ∈ V, ∀ c ∈ t, a * b * c ∈ G by
    obtain ⟨V, hV, H⟩ := this Set.univ Set.univ isCompact_univ isCompact_univ
    refine (𝓝 x).mem_of_superset hV fun b hb ↦ ?_
    replace H := fun a c ↦ H a trivial b hb c trivial
    simpa [TwoSidedIdeal.mem_leAddSubgroup]
  intros s t hs ht
  refine hs.induction_on ?_ ?_ ?_ ?_
  · simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨Set.univ, Filter.univ_mem⟩
  · rintro s₁ s₂ hs₁s₂ ⟨V, hV, H⟩
    exact ⟨V, hV, fun a ha b hb c hc ↦ H a (hs₁s₂ ha) b hb c hc⟩
  · rintro s₁ s₂ ⟨V₁, hV₁, H₁⟩ ⟨V₂, hV₂, H₂⟩
    exact ⟨V₁ ∩ V₂, Filter.inter_mem hV₁ hV₂,
      fun a ha b hb c hc ↦ ha.elim (H₁ a · b hb.1 c hc) (H₂ a · b hb.2 c hc)⟩
  intro a has
  refine ht.induction_on ?_ ?_ ?_ ?_
  · simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true, and_true,
      exists_and_right]
    exact ⟨⟨_, Filter.univ_mem⟩, ⟨_, Filter.univ_mem⟩⟩
  · rintro s₁ s₂ hs₁s₂ ⟨V, hV, U, hU, H⟩
    exact ⟨V, hV, U, hU, fun a ha b hb c hc ↦ H a ha b hb c (hs₁s₂ hc)⟩
  · rintro s₁ s₂ ⟨V₁, hV₁, U₁, hU₁, H₁⟩ ⟨V₂, hV₂, U₂, hU₂, H₂⟩
    exact ⟨V₁ ∩ V₂, Filter.inter_mem hV₁ hV₂, U₁ ∩ U₂, Filter.inter_mem hU₁ hU₂,
      fun a ha b hb c hc ↦ hc.elim (H₁ a ha.1 b hb.1 c) (H₂ a ha.2 b hb.2 c)⟩
  · intros b hbt
    have : Continuous fun p : α × α × α ↦ p.1 * p.2.1 * p.2.2 := by fun_prop
    have := (this.tendsto (a, x, b)) (hG.mem_nhds (hx _ _))
    simp only [nhds_prod_eq, Filter.mem_map, Filter.mem_prod_iff] at this
    obtain ⟨t₁, ht₁, T, ⟨t₂, ht₂, t₃, ht₃, hT⟩, H⟩ := this
    refine ⟨t₃, mem_nhdsWithin_of_mem_nhds ht₃, t₁, mem_nhdsWithin_of_mem_nhds ht₁,
      t₂, ht₂, fun a ha b hb c hc ↦ ?_⟩
    exact H (Set.mk_mem_prod ha (hT <| Set.mk_mem_prod hb hc))

open Topology in
theorem exists_ideal_isOpen_and_subset {α} [TopologicalSpace α]
    [CompactSpace α] [T2Space α] [TotallyDisconnectedSpace α]
    [Ring α] [TopologicalRing α] {U : Set α} (hU : U ∈ 𝓝 0) :
    ∃ I : Ideal α, IsOpen (X := α) I ∧ (I : Set α) ⊆ U := by
  obtain ⟨I, hI, hIU⟩ := exists_twoSidedIdeal_isOpen_and_subset hU
  exact ⟨I.asIdeal, hI, hIU⟩

instance (priority := 100) {α} [TopologicalSpace α] [DiscreteTopology α] :
    TotallyDisconnectedSpace α :=
  ⟨fun s _ hs x hxs y hys ↦ not_not.mp fun hxy ↦ by
    simpa using hs _ _ (isOpen_discrete {y}) (isOpen_discrete (s \ {y}))
      (by simp) ⟨y, by simpa⟩ ⟨x, by simp_all⟩⟩

lemma WellFoundedGT.exists_eq_sup {α} [CompleteLattice α] [WellFoundedGT α]
    (f : ℕ →o α) : ∃ i, f i = ⨆ i, f i := by
  obtain ⟨n, hn⟩ := WellFounded.monotone_chain_condition.mp
    (IsWellFounded.wf (self := ‹WellFoundedGT α›)) f
  exact ⟨n, le_antisymm (le_iSup _ _) (iSup_le fun i ↦
    (le_total i n).elim (f.2 ·) (fun h ↦ (hn _ h).ge))⟩

lemma WellFoundedLT.exists_eq_inf {α} [CompleteLattice α] [WellFoundedLT α]
    (f : ℕ →o αᵒᵈ) : ∃ i, f i = (⨅ i, f i : α) :=
  WellFoundedGT.exists_eq_sup (α := αᵒᵈ) f

lemma IsLocalRing.maximalIdeal_pow_card_smul_top_le {R M}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] (N : Submodule R M)
    [Finite (M ⧸ N)] : maximalIdeal R ^ Nat.card (M ⧸ N) • ⊤ ≤ N := by
  let f (n) : Submodule R (M ⧸ N) := maximalIdeal R ^ n • ⊤
  have hf : ∀ i j, i ≤ j → f j ≤ f i :=
    fun i j h ↦ Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl
  have H : ∃ i, f i = ⊥ := by
    obtain ⟨i, hi⟩ := WellFoundedLT.exists_eq_inf ⟨f, hf⟩
    have := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := R) (M := M ⧸ N) _
      (maximalIdeal.isMaximal R).ne_top
    exact ⟨i, by simpa [f, this] using hi⟩
  have (i) : Set.ncard (α := M ⧸ N) (f i) ≤ Nat.card (M ⧸ N) - i + 1 := by
    induction i with
    | zero =>
      refine (Set.ncard_mono (Set.subset_univ _)).trans ?_
      simp [Set.ncard_univ]
    | succ n IH =>
      cases (hf _ _ n.le_succ).lt_or_eq with
      | inl h =>
        rw [← tsub_tsub]
        refine (Nat.le_sub_one_of_lt <| (Set.ncard_strictMono h).trans_le IH).trans ?_
        omega
      | inr h =>
        have (i) : f (i + n) = f n := by
          induction i with
          | zero => simp
          | succ m IH =>
            unfold f at *
            simp only [add_assoc, pow_add _ m, mul_smul, ← Nat.succ_eq_one_add, h]
            simp only [← mul_smul, ← pow_add, IH]
        obtain ⟨i, hi⟩ := H
        replace hf := hf _ _ (i.le_add_right n)
        rw [this, hi, ← h, le_bot_iff] at hf
        simp [hf]
  have : f (Nat.card (M ⧸ N)) = ⊥ := by
    rw [← le_bot_iff]
    show (f (Nat.card (M ⧸ N)) : Set (M ⧸ N)) ⊆ {0}
    exact (Set.eq_of_subset_of_ncard_le (by simp) ((this _).trans (by simp))).ge
  simpa only [f, ← LinearMap.range_eq_top.mpr N.mkQ_surjective, ← Submodule.map_top,
    ← Submodule.map_smul'', ← le_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot,
    Submodule.ker_mkQ] using this

theorem Submodule.comap_smul_of_le_range {R M M'} [CommRing R] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M') (S : Submodule R M') (hS : S ≤ LinearMap.range f) (I : Ideal R) :
    (I • S).comap f = (I • S.comap f) ⊔ LinearMap.ker f := by
  rw [← comap_map_eq, map_smul'', Submodule.map_comap_eq, inf_eq_right.mpr hS]

theorem Submodule.comap_smul_of_surjective {R M M'} [CommRing R] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M') (S : Submodule R M') (hS : Function.Surjective f) (I : Ideal R) :
    (I • S).comap f = (I • S.comap f) ⊔ LinearMap.ker f :=
  comap_smul_of_le_range f S (le_top.trans_eq (LinearMap.range_eq_top_of_surjective f hS).symm) I

noncomputable
def Pi.liftQuotientₗ {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite ι]
    (f : (ι → R) →ₗ[R] M) (I : Ideal R) : (ι → R ⧸ I) →ₗ[R] M ⧸ (I • ⊤ : Submodule R M) := by
  refine Submodule.liftQ _ (Submodule.mkQ _ ∘ₗ f) ?_ ∘ₗ
    (((Algebra.linearMap R (R ⧸ I)).compLeft ι).quotKerEquivOfSurjective ?_).symm.toLinearMap
  · intro x hx
    replace hx : ∀ i, x i ∈ I := by
      simpa [funext_iff, Ideal.Quotient.eq_zero_iff_mem] using hx
    cases nonempty_fintype ι
    classical
    have : x = ∑ i : ι, x i • (Pi.single i 1 : ι → R) := by
      simp [← Pi.single_smul, Finset.univ_sum_single]
    rw [this]
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    simp only [map_sum, map_smul]
    exact sum_mem fun i hi ↦ Submodule.smul_mem_smul (hx i) Submodule.mem_top
  · exact Function.Surjective.comp_left Ideal.Quotient.mk_surjective

lemma Pi.liftQuotientₗ_surjective {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite ι]
    (f : (ι → R) →ₗ[R] M) (I : Ideal R) (hf : Function.Surjective f) :
    Function.Surjective (Pi.liftQuotientₗ f I) := by
  simp only [liftQuotientₗ, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.surjective_comp]
  rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
  exact (Submodule.mkQ_surjective _).comp hf

lemma Pi.liftQuotientₗ_bijective {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite ι]
    (f : (ι → R) →ₗ[R] M) (I : Ideal R) (hf : Function.Surjective f)
    (hf' : LinearMap.ker f ≤ LinearMap.ker ((Algebra.linearMap R (R ⧸ I)).compLeft ι)) :
    Function.Bijective (Pi.liftQuotientₗ f I) := by
  refine ⟨?_, liftQuotientₗ_surjective f I hf⟩
  simp only [liftQuotientₗ, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp]
  rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, ← le_bot_iff, Submodule.map_le_iff_le_comap,
      Submodule.comap_bot, Submodule.ker_mkQ, LinearMap.ker_comp, Submodule.ker_mkQ,
      Submodule.comap_smul_of_surjective _ _ hf, Submodule.comap_top]
  refine sup_le (Submodule.smul_le.mpr ?_) hf'
  rintro r hr m -
  simp only [LinearMap.mem_ker, funext_iff, LinearMap.compLeft_apply, Function.comp_apply,
    smul_apply, Algebra.linearMap_apply, Ideal.Quotient.algebraMap_eq, zero_apply,
    Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul, I.mul_mem_right _ hr, implies_true]

lemma Finsupp.comapDomain_surjective {α β M} [Zero M] [Finite β]
    (f : α → β) (hf : Function.Injective f) :
    Function.Surjective fun l : β →₀ M ↦ Finsupp.comapDomain f l hf.injOn := by
  classical
  intro x
  cases isEmpty_or_nonempty α
  · refine ⟨0, Finsupp.ext <| fun a ↦ IsEmpty.elim ‹_› a⟩
  obtain ⟨g, hg⟩ := hf.hasLeftInverse
  refine ⟨Finsupp.equivFunOnFinite.symm (x ∘ g), Finsupp.ext <| fun a ↦ by simp [hg a]⟩

lemma Submodule.isCompact_of_fg {R M : Type*} [CommRing R] [TopologicalSpace R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsModuleTopology R M] [CompactSpace R] {N : Submodule R M} (hN : N.FG) :
    IsCompact (X := M) N := by
  have := IsModuleTopology.toContinuousAdd R M
  obtain ⟨s, hs⟩ := hN
  have : LinearMap.range (Fintype.linearCombination R R (α := s) Subtype.val) = N := by
    simp [Finsupp.range_linearCombination, hs]
  rw [← this]
  refine isCompact_range ?_
  simp only [Fintype.linearCombination, Finset.univ_eq_attach, smul_eq_mul, LinearMap.coe_mk,
    AddHom.coe_mk]
  continuity

lemma Ideal.isCompact_of_fg {R : Type*} [CommRing R] [TopologicalSpace R] [TopologicalRing R] [CompactSpace R]
    {I : Ideal R} (hI : I.FG) : IsCompact (X := R) I :=
  Submodule.isCompact_of_fg hI

lemma IsModuleTopology.compactSpace
    (R M : Type*) [CommRing R] [TopologicalSpace R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
    [CompactSpace R] [Module.Finite R M] : CompactSpace M :=
  ⟨Submodule.isCompact_of_fg (Module.Finite.out (R := R))⟩

lemma Module.annihilator_eq_bot {R M} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.annihilator R M = ⊥ ↔ FaithfulSMul R M := by
  rw [← le_bot_iff]
  refine ⟨fun H ↦ ⟨fun {r s} H' ↦ ?_⟩, fun ⟨H⟩ {a} ha ↦ ?_⟩
  · rw [← sub_eq_zero]
    exact H (Module.mem_annihilator (r := r - s).mpr
      (by simp only [sub_smul, H', sub_self, implies_true]))
  · exact @H a 0 (by simp [Module.mem_annihilator.mp ha])

section localized_smul

variable {R S M N : Type*}
variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]
variable (M' : Submodule R M) (I : Ideal R)

lemma Submodule.localized₀_smul : (I • M').localized₀ p f = I • M'.localized₀ p f := by
  apply le_antisymm
  · rintro _ ⟨a, ha, s, rfl⟩
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro r hr n hn
      rw [IsLocalizedModule.mk'_smul]
      exact Submodule.smul_mem_smul hr ⟨n, hn, s, rfl⟩
    · simp +contextual only [IsLocalizedModule.mk'_add, add_mem, implies_true]
  · refine Submodule.smul_le.mpr ?_
    rintro r hr _ ⟨a, ha, s, rfl⟩
    rw [← IsLocalizedModule.mk'_smul]
    exact ⟨_, Submodule.smul_mem_smul hr ha, s, rfl⟩

end localized_smul

theorem Module.support_quotient {R M} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] (I : Ideal R) :
    Module.support R (M ⧸ (I • ⊤ : Submodule R M)) =
      Module.support R M ∩ PrimeSpectrum.zeroLocus I := by
  apply subset_antisymm
  · refine Set.subset_inter ?_ ?_
    · exact Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _)
    · rw [support_eq_zeroLocus]
      apply PrimeSpectrum.zeroLocus_anti_mono_ideal
      rw [Submodule.annihilator_quotient]
      exact fun x hx ↦ Submodule.mem_colon.mpr fun p ↦ Submodule.smul_mem_smul hx
  · rintro p ⟨hp₁, hp₂⟩
    rw [Module.mem_support_iff] at hp₁ ⊢
    let Rₚ := Localization.AtPrime p.asIdeal
    let Mₚ := LocalizedModule p.asIdeal.primeCompl M
    let Mₚ' := LocalizedModule p.asIdeal.primeCompl (M ⧸ (I • ⊤ : Submodule R M))
    let f : Mₚ →ₗ[R] Mₚ' := (LocalizedModule.map _ (Submodule.mkQ _)).restrictScalars R
    have hf : LinearMap.ker f = I • ⊤ := by
      refine (LinearMap.ker_localizedMap_eq_localized'_ker Rₚ ..).trans ?_
      show Submodule.localized₀ _ _ _ = _
      simp only [Submodule.ker_mkQ, Submodule.localized₀_smul, Submodule.localized₀_top]
    let f' : (Mₚ ⧸ (I • ⊤ : Submodule R Mₚ)) ≃ₗ[R] Mₚ' :=
      LinearEquiv.ofBijective (Submodule.liftQ _ f hf.ge) <| by
        constructor
        · rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, hf,
            ← le_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
        · rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
          exact (LocalizedModule.map_surjective _ _ (Submodule.mkQ_surjective _))
    have : Module.Finite Rₚ Mₚ :=
      Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap _ _)
    have : Nontrivial (Mₚ ⧸ (I • ⊤ : Submodule R Mₚ)) := by
      apply Submodule.Quotient.nontrivial_of_lt_top
      rw [lt_top_iff_ne_top]
      intro H
      have : I.map (algebraMap R Rₚ) • (⊤ : Submodule Rₚ Mₚ) = ⊤ := by
        rw [← top_le_iff]
        show ⊤ ≤ (I.map (algebraMap R Rₚ) • (⊤ : Submodule Rₚ Mₚ)).restrictScalars R
        rw [← H, Submodule.smul_le]
        intro r hr n hn
        rw [← algebraMap_smul Rₚ, Submodule.restrictScalars_mem]
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) hn
      have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ ⊤ Module.Finite.out this.ge
        ((Ideal.map_mono hp₂).trans (by
          rw [Localization.AtPrime.map_eq_maximalIdeal]
          exact IsLocalRing.maximalIdeal_le_jacobson _))
      exact top_ne_bot this
    exact f'.symm.nontrivial

theorem Module.comap_annihilator {R S M} [CommRing R]
    [CommRing S] [AddCommGroup M] [Module R M] [Module S M]
    [Algebra R S] [IsScalarTower R S M] :
    (Module.annihilator S M).comap (algebraMap R S) = Module.annihilator R M := by
  ext x
  simp [mem_annihilator]

lemma ringKrullDim_quotient {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) := by
  let e : PrimeSpectrum (R ⧸ I) ≃ (PrimeSpectrum.zeroLocus (R := R) I) :=
    (Equiv.ofInjective _ (PrimeSpectrum.comap_injective_of_surjective _
      Ideal.Quotient.mk_surjective)).trans (Equiv.setCongr
      (by rw [PrimeSpectrum.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker]))
  let e' : PrimeSpectrum (R ⧸ I) ≃o (PrimeSpectrum.zeroLocus (R := R) I) :=
    { __ := e, map_rel_iff' := fun {a b} ↦ by
        show a.asIdeal.comap _ ≤ b.asIdeal.comap _ ↔ a ≤ b
        rw [← Ideal.map_le_iff_le_comap,
          Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
        rfl }
  rw [ringKrullDim, Order.krullDim_eq_of_orderIso e']

lemma disjoint_nonZeroDivisors_of_mem_minimalPrimes
    {R : Type*} [CommRing R] (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    Disjoint (p : Set R) (nonZeroDivisors R) := by
  classical
  rw [← Set.subset_compl_iff_disjoint_right, Set.subset_def]
  simp only [SetLike.mem_coe, Set.mem_compl_iff, mem_nonZeroDivisors_iff, not_forall,
    Classical.not_imp]
  intro x hxp
  have := hp.1.1
  have : p.map (algebraMap R (Localization.AtPrime p)) ≤ nilradical _ := by
    rw [nilradical, Ideal.radical_eq_sInf, le_sInf_iff]
    rintro q ⟨-, hq⟩
    obtain ⟨h₁, h₂⟩ := ((IsLocalization.AtPrime.orderIsoOfPrime _ p) ⟨q, hq⟩).2
    rw [Ideal.map_le_iff_le_comap]
    exact hp.2 ⟨h₁, bot_le⟩ h₂
  obtain ⟨n, hn : _ = 0⟩ := this (Ideal.mem_map_of_mem _ hxp)
  rw [← map_pow, ← map_zero (algebraMap R _), IsLocalization.eq_iff_exists p.primeCompl] at hn
  obtain ⟨t, ht⟩ := hn
  simp only [mul_zero] at ht
  have H : ∃ n, t.1 * x ^ n = 0 := ⟨n, ht⟩
  have : Nat.find H ≠ 0 := by
    intro h
    have := Nat.find_spec H
    simp only [h, pow_zero, mul_one] at this
    exact t.2 (this ▸ zero_mem p)
  refine ⟨t.1 * x ^ (Nat.find H - 1), ?_, ?_⟩
  · rw [mul_assoc, ← pow_succ, tsub_add_cancel_of_le, Nat.find_spec H]
    rwa [Nat.one_le_iff_ne_zero]
  · exact Nat.find_min H (Nat.sub_one_lt this)

lemma ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    {R : Type*} [CommRing R] (r : R) (hr : r ∈ nonZeroDivisors R) :
    ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim R := by
  by_cases hr' : Ideal.span {r} = ⊤
  · rw [hr', ringKrullDim_eq_bot_of_subsingleton]
    simp
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) (Ideal.span {r})) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, ne_eq,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have := Ideal.Quotient.nontrivial hr'
  have := (Ideal.Quotient.mk (Ideal.span {r})).domain_nontrivial
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_length, ringKrullDim,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intros l
  obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le (J := l.head.1.asIdeal) bot_le
  let p' : PrimeSpectrum R := ⟨p, hp.1.1⟩
  have hp' : p' < l.head := lt_of_le_of_ne hp' (by
    intro h
    have := disjoint_nonZeroDivisors_of_mem_minimalPrimes p hp
    exact Set.disjoint_iff.mp this ⟨show r ∈ p by simpa [← h] using l.head.2, hr⟩)
  refine le_trans ?_ (le_iSup _ ((l.map Subtype.val (fun _ _ ↦ id)).cons p' hp'))
  show (l.length + 1 : ℕ∞) ≤ ↑(0 + l.length + 1)
  simp
