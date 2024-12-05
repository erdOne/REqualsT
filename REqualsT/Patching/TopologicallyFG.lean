import Mathlib.RingTheory.FiniteType
import Mathlib.Topology.Algebra.Ring.Basic

variable (R S) [CommRing R] [Ring S] [Algebra R S] [TopologicalSpace S]

class Algebra.TopologicallyFG [TopologicalRing S] : Prop where
  out : ∃ s : Finset S, Dense (Algebra.adjoin R (s : Set S) : Set S)

instance (priority := 100) [TopologicalRing S] [Algebra.FiniteType R S] :
    Algebra.TopologicallyFG R S where
  out := have ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S); ⟨s, by simp [hs]⟩

variable {M} [AddCommGroup M] [Module R M] [TopologicalSpace M] [T2Space M]

@[elab_as_elim]
lemma Dense.induction {α} [TopologicalSpace α] {s : Set α} (hs : Dense s) {P : α → Prop}
    (H : ∀ x ∈ s, P x) (isClosed : IsClosed { x | P x }) (x) : P x := by
  have : { x | P x } = Set.univ := Set.univ_subset_iff.mp
    (hs.closure_eq.symm.subset.trans (isClosed.closure_subset_iff.mpr H))
  exact this.symm.subset trivial

lemma Algebra.TopologicallyFG.module_ext (s : Set S)
    (hs' : Dense (Algebra.adjoin R (s : Set S) : Set S)) {m₁ m₂ : Module S M}
    (hm₁ : letI := m₁; IsScalarTower R S M) (hm₂ : letI := m₂; IsScalarTower R S M)
    (hm₁' : letI := m₁; ContinuousSMul S M) (hm₂' : letI := m₂; ContinuousSMul S M)
    (H : ∀ x ∈ s, ∀ m : M, (letI := m₁; x • m) = (letI := m₂; x • m)) :
    m₁ = m₂ := by
  ext r m
  induction r using hs'.induction with
  | H x hx =>
    induction hx using Algebra.adjoin_induction generalizing m with
    | mem x hx => exact H x hx m
    | algebraMap r =>
      exact .trans (letI := m₁; algebraMap_smul ..) (.symm (letI := m₂; algebraMap_smul ..))
    | add x y hx hy hx' hy' =>
      exact ((m₁.add_smul _ _ _).trans congr($(hx' _) + $(hy' _))).trans (m₂.add_smul _ _ _).symm
    | mul x y hx hy hx' hy' =>
      exact (((m₁.mul_smul _ _ _).trans (hx' _)).trans
        congr(x • $(hy' _))).trans (m₂.mul_smul _ _ _).symm
  | isClosed =>
    exact isClosed_eq (hm₁'.1.comp (continuous_prod_mk.mpr ⟨continuous_id', continuous_const⟩))
      (hm₂'.1.comp (continuous_prod_mk.mpr ⟨continuous_id', continuous_const⟩))
