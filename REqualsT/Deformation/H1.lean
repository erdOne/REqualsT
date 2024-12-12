import REqualsT.Deformation.TangentSpace
import Mathlib

universe u

open CategoryTheory IsLocalRing

variable (𝒪 : Type u) [CommRing 𝒪] [IsNoetherianRing 𝒪]
variable [IsLocalRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
variable (G : Type u) [TopologicalSpace G] [Group G] [TopologicalGroup G] [CompactSpace G]
variable (n : Type) [DecidableEq n] [Fintype n]

variable {𝒪 G n}

attribute [local instance] IsLocalRing.withIdeal
variable (𝒟 : DeformationProblem.{uO} 𝒪 G n) [𝒟.toFunctor.IsCorepresentable]
variable (ρ : ContinuousMonoidHom G (GL n (ResidueField 𝒪)))

def Representation.glAdjoint (n k : Type*) [Fintype n] [DecidableEq n] [CommRing k] :
    Representation k (GL n k) (Matrix n n k) :=
  .ofDistribMulAction k (ConjAct (GL n k)) (Matrix n n k)

@[simp]
lemma Representation.glAdjoint_apply (n k : Type*) [Fintype n] [DecidableEq n] [CommRing k] (g m) :
    glAdjoint n k g m = g.1 * m * g⁻¹.1 := rfl

abbrev DeformationCat.H1 : Type _ :=
  groupCohomology.H1 (Rep.of ((Representation.glAdjoint n (ResidueField 𝒪)).comp ρ.toMonoidHom))

noncomputable
instance {k G : Type u} [CommRing k] [Group G] (A : Rep k G) : DistribMulAction G A where
  smul g m := A.ρ g m
  one_smul m := DFunLike.congr_fun A.ρ.map_one m
  mul_smul g₁ g₂ m := DFunLike.congr_fun (A.ρ.map_mul g₁ g₂) m
  smul_zero g := (A.ρ g).map_zero
  smul_add g := (A.ρ g).map_add

noncomputable
instance {k G V : Type u} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
    [TopologicalSpace V] (ρ : G →* V →ₗ[k] V) : TopologicalSpace (Rep.of ρ) := ‹_›

noncomputable
instance {k G V : Type u} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
    [TopologicalSpace V] [TopologicalAddGroup V] (ρ : G →* V →ₗ[k] V) :
  TopologicalAddGroup (Rep.of ρ) := ‹_›

nonrec
def groupCohomology.H1.Continuous {k G : Type u} [CommRing k] [Group G]
    [TopologicalSpace G]
    {A : Rep k G} [TopologicalSpace A] [TopologicalAddGroup A]
    [ContinuousSMul G A] (σ : groupCohomology.H1 A) : Prop :=
  Quotient.liftOn σ (fun σ ↦ Continuous σ.1) fun σ₁ σ₂ e ↦ by
    suffices ∀ σ₁ σ₂ : oneCocycles A, (oneCoboundaries A).quotientRel.r σ₁ σ₂ →
        Continuous σ₂.1 → Continuous σ₁.1 by
      refine eq_iff_iff.mpr ⟨this σ₂ σ₁ ((oneCoboundaries A).quotientRel.symm e), this σ₁ σ₂ e⟩
    rintro σ₁ σ₂ ⟨⟨⟨r, hr⟩, a, ha⟩, rfl⟩ H
    obtain rfl := congr_arg Subtype.val ha
    show Continuous fun x ↦ σ₂ x + (x • a - a)
    continuity

local notation "𝕜" => ResidueField 𝒪

@[simp]
lemma ContinuousMonoidHom.toMonoidHom_eq_coe {M N} [Monoid M] [Monoid N]
  [TopologicalSpace M] [TopologicalSpace N] (f : ContinuousMonoidHom M N) :
  f.toMonoidHom = f := rfl

lemma toResidueField_dualNumber : (DeformationCat.DualNumber (𝒪 := 𝒪)).toResidueField.toAlgHom =
    (TrivSqZeroExt.fstHom 𝕜 𝕜 𝕜).restrictScalars _ := by
  ext ⟨r₁, r₂⟩
  rw [DeformationCat.to_residueField_apply, DeformationCat.residue_preimage_eq_iff]
  obtain ⟨r₁, rfl⟩ := residue_surjective r₁
  show residue (DualNumber 𝕜) _ = residue (DualNumber 𝕜) (residue 𝒪 r₁, 0)
  refine Ideal.Quotient.eq.mpr ?_
  convert_to ((by exact (0, r₂)) : DualNumber 𝕜) ∈ maximalIdeal (DualNumber 𝕜)
  · apply TrivSqZeroExt.ext <;> simp [DeformationCat.DualNumber]
  simp [TrivSqZeroExt.isUnit_iff_isUnit_fst]

noncomputable
def overDualNumberEquivToFun
    (ρ' : ContinuousMonoidHom G (GL n DeformationCat.DualNumber.X))
    (hρ' : Quotient.mk'' ρ' ∈ (DeformationProblem.Over 𝒪 G n ρ).obj DeformationCat.DualNumber) :
    DeformationCat.H1 ρ :=
  Submodule.Quotient.mk ⟨fun g ↦ (ρ' g).1.map TrivSqZeroExt.snd * (ρ g⁻¹).1, (by
    refine funext fun ⟨g₁, g₂⟩ ↦ ?_
    dsimp [groupCohomology.oneCocycles, groupCohomology.dOne]
    apply (ρ g₁).isUnit.mul_right_cancel
    apply (ρ g₂).isUnit.mul_right_cancel
    simp only [mul_assoc, ← Units.val_mul, map_mul, add_mul, sub_mul, inv_mul_cancel,
      zero_mul, one_mul, map_inv]
    simp only [Units.val_one, mul_one, Units.val_mul]
    rw [sub_add_eq_add_sub, sub_eq_zero, ← (equivRepr_iff_eq _ 𝕜).mp (Quotient.eq.mp hρ')]
    erw [ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.comp_toFun]
    simp only [toResidueField_dualNumber, AlgHom.coe_restrictScalars,
      ContinuousMonoidHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Matrix.GeneralLinearGroup.continuousMap_apply]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply,
      Matrix.zero_apply, ← Finset.sum_add_distrib, DeformationCat.DualNumber,
      TrivSqZeroExt.snd_mul, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, TrivSqZeroExt.snd_sum]
    rfl)⟩

instance :
    ContinuousSMul G (Rep.of ((Representation.glAdjoint n (ResidueField 𝒪)).comp ρ.toMonoidHom)) := by
  constructor
  show Continuous fun p : G × Matrix n n 𝕜 ↦ (ρ p.1).1 * p.2 * (ρ p.1)⁻¹.1
  apply Continuous.mul
  · refine Continuous.mul ?_ continuous_snd
    exact Units.continuous_val.comp (ρ.continuous_toFun.comp continuous_fst)
  · exact Units.continuous_coe_inv.comp (ρ.continuous_toFun.comp continuous_fst)

lemma DualNumber.maximalIdeal_pow {k} [Field k] :
    maximalIdeal (DualNumber k) ^ 2 = ⊥ := by
  rw [← le_bot_iff, pow_two, Ideal.mul_le]
  rintro ⟨ra, rb⟩ hr ⟨sa, sb⟩ hs
  simp only [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst,
    TrivSqZeroExt.fst_mk, isUnit_iff_ne_zero, ne_eq, not_not] at hr hs
  ext <;> simp [hr, hs]

instance : DiscreteTopology (DeformationCat.DualNumber (𝒪 := 𝒪)).X := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  convert isOpen_maximalIdeal_pow (DeformationCat.DualNumber (𝒪 := 𝒪)).X 2
  erw [DualNumber.maximalIdeal_pow]
  rfl

lemma continuous_overDualNumberEquivToFun
    (ρ' : ContinuousMonoidHom G (GL n DeformationCat.DualNumber.X))
    (hρ' : Quotient.mk'' ρ' ∈ (DeformationProblem.Over 𝒪 G n ρ).obj DeformationCat.DualNumber) :
    (overDualNumberEquivToFun ρ ρ' hρ').Continuous := by
  show Continuous fun g ↦ _ * _
  refine Continuous.mul (M := Matrix n n 𝕜) ?_ ?_
  · refine Continuous.matrix_map ?_ ?_
    · exact Units.continuous_val.comp ρ'.continuous_toFun
    · exact continuous_of_discreteTopology
  · exact Units.continuous_val.comp (ρ.continuous_toFun.comp continuous_inv)

omit
  [TopologicalGroup G]
  [CompactSpace G] in
lemma overDualNumberEquivToFun_eq
    (ρ₁ ρ₂ : ContinuousMonoidHom G (GL n (DeformationCat.DualNumber (𝒪 := 𝒪)).X))
    (H : (equivRepr _ _).r ρ₁ ρ₂)
    (hρ₁ hρ₂) :
    overDualNumberEquivToFun ρ ρ₁ hρ₁ = overDualNumberEquivToFun ρ ρ₂ hρ₂ := by
  obtain ⟨r, hr₁, hr₂⟩ := H
  refine (Submodule.Quotient.eq _).mpr ?_
  refine ⟨r.1.map TrivSqZeroExt.snd, Subtype.ext ?_⟩
  ext g
  apply (ρ g).isUnit.mul_right_cancel
  simp only [ContinuousMonoidHom.toMonoidHom_eq_coe, Rep.coe_of, LinearMap.codRestrict_apply,
    map_inv, AddSubgroupClass.coe_sub, Pi.sub_apply, ← sub_mul]
  erw [groupCohomology.dZero_apply]
  rw [sub_mul]
  simp only [Rep.coe_of, Rep.of_ρ, MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
    Representation.glAdjoint_apply, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  rw [sub_eq_sub_iff_add_eq_add]
  have hr₃ (i j) : (r.1 i j).fst = (1 : Matrix n n 𝕜) i j := by
    trans ((1 : Matrix n n (DualNumber 𝕜)) i j).fst
    · simpa [TrivSqZeroExt.isUnit_iff_isUnit_fst, DeformationCat.DualNumber, sub_eq_zero] using hr₂ i j
    · simp [Matrix.one_apply, apply_ite]
  convert congr_arg (fun M ↦ Matrix.map (Units.val M) TrivSqZeroExt.snd) (hr₁ g).symm
  · rw [← mul_one ((ρ₂ g).1.map _)]
    ext i j
    rw [← (equivRepr_iff_eq _ 𝕜).mp (Quotient.eq.mp hρ₂)]
    erw [ContinuousMonoidHom.comp_toFun]
    simp only [toResidueField_dualNumber, AlgHom.coe_restrictScalars,
      ContinuousMonoidHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Matrix.GeneralLinearGroup.continuousMap_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.GeneralLinearGroup.map_apply, RingHom.coe_coe, Matrix.map_apply, Units.val_mul,
      TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, ← Finset.sum_add_distrib, hr₃]
    rfl
  · rw [← one_mul ((ρ₁ g).1.map _)]
    ext i j
    rw [← (equivRepr_iff_eq _ 𝕜).mp (Quotient.eq.mp hρ₁)]
    erw [ContinuousMonoidHom.comp_toFun]
    simp only [toResidueField_dualNumber, AlgHom.coe_restrictScalars,
      ContinuousMonoidHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Matrix.GeneralLinearGroup.continuousMap_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.GeneralLinearGroup.map_apply, RingHom.coe_coe, Matrix.map_apply, Units.val_mul,
      TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, ← Finset.sum_add_distrib, hr₃]
    rfl

lemma DualNumber.matrixMap_inr {k n m : Type*} [CommRing k] (M : Matrix n m k) :
    M.map TrivSqZeroExt.inr = DualNumber.eps (R := k) • M.map (TrivSqZeroExt.inl (M := k)) := by
  ext <;> simp

lemma TrivSqZeroExt.matrixMap_inl_mul {R M n m k : Type*}
    [Fintype m] [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    (M₁ : Matrix n m R) (M₂ : Matrix m k R) :
    (M₁ * M₂).map (TrivSqZeroExt.inl (M := M)) =
      M₁.map (TrivSqZeroExt.inl (M := M)) * M₂.map (TrivSqZeroExt.inl (M := M)) := by
  ext <;> simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum, TrivSqZeroExt.snd_sum]

lemma TrivSqZeroExt.matrixMap_inl_add {R M n m : Type*} [Add R] [AddZeroClass M]
    (M₁ M₂ : Matrix n m R) :
    (M₁ + M₂).map (TrivSqZeroExt.inl (M := M)) =
      M₁.map (TrivSqZeroExt.inl (M := M)) + M₂.map (TrivSqZeroExt.inl (M := M)) := by
  ext <;> simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum, TrivSqZeroExt.snd_sum]

lemma TrivSqZeroExt.matrixMap_inl_sub {R M n m : Type*} [Sub R] [AddCommGroup M]
    (M₁ M₂ : Matrix n m R) :
    (M₁ - M₂).map (TrivSqZeroExt.inl (M := M)) =
      M₁.map (TrivSqZeroExt.inl (M := M)) - M₂.map (TrivSqZeroExt.inl (M := M)) := by
  ext <;> simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum, TrivSqZeroExt.snd_sum]

@[simps]
noncomputable
def overDualNumberEquivInvFunMonoidHom {k G : Type*} [Field k]
  [Group G] {n : Type} [DecidableEq n] [Fintype n] (ρ : G →* GL n k)
  (σ : G → Matrix n n k) (hσ : σ 1 = 0)
  (hσ' : ∀ x y, σ (x * y) * (ρ x).1 = σ x * (ρ x).1 + (ρ x).1 * σ y) :
    G →* GL n (DualNumber k) where
  toFun g :=
    { val := (1 + (σ g).map TrivSqZeroExt.inr) * (ρ g).1.map TrivSqZeroExt.inl
      inv := (ρ g⁻¹).1.map TrivSqZeroExt.inl * (1 - (σ g).map TrivSqZeroExt.inr)
      val_inv := by
        have h₁ : (ρ g).1.map (TrivSqZeroExt.inl (M := k)) * (ρ g⁻¹).1.map TrivSqZeroExt.inl = 1 := by
          show (TrivSqZeroExt.inlHom k k).mapMatrix (ρ g).1 * (TrivSqZeroExt.inlHom k k).mapMatrix (ρ g⁻¹).1 = 1
          rw [← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel]
          simp only [map_one, Units.val_one]
        have h₂ : (1 + (σ g).map (TrivSqZeroExt.inr (R := k))) * (1 - (σ g).map TrivSqZeroExt.inr) = 1 := by
          rw [← (Commute.one_left _).sq_sub_sq, one_pow, pow_two, sub_eq_self]
          ext1 i j
          simp only [Matrix.mul_apply, Matrix.map_apply, DualNumber.inr_eq_smul_eps,
            Algebra.mul_smul_comm, Algebra.smul_mul_assoc, DualNumber.eps_mul_eps, smul_zero,
            Finset.sum_const_zero, Matrix.zero_apply]
        rw [mul_assoc, ← mul_assoc (Matrix.map _ _), h₁, one_mul, h₂]
      inv_val := by
        have h₁ : (ρ g⁻¹).1.map (TrivSqZeroExt.inl (M := k)) * (ρ g).1.map TrivSqZeroExt.inl = 1 := by
          show (TrivSqZeroExt.inlHom k k).mapMatrix (ρ g⁻¹).1 * (TrivSqZeroExt.inlHom k k).mapMatrix (ρ g).1 = 1
          rw [← map_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel]
          simp only [map_one, Units.val_one]
        have h₂ : (1 - (σ g).map (TrivSqZeroExt.inr (R := k))) * (1 + (σ g).map TrivSqZeroExt.inr) = 1 := by
          rw [← (Commute.one_left _).mul_self_sub_mul_self_eq', one_mul, sub_eq_self]
          ext1 i j
          simp only [Matrix.mul_apply, Matrix.map_apply, DualNumber.inr_eq_smul_eps,
            Algebra.mul_smul_comm, Algebra.smul_mul_assoc, DualNumber.eps_mul_eps, smul_zero,
            Finset.sum_const_zero, Matrix.zero_apply]
        rw [mul_assoc, ← mul_assoc (_ - _), h₂, one_mul, h₁] }
  map_one' := by
    ext1
    simp only [map_one, Units.val_one, TrivSqZeroExt.inl_zero, TrivSqZeroExt.inl_one,
      Matrix.map_one, mul_one, add_right_eq_self, hσ,
      DualNumber.inr_eq_smul_eps, zero_smul, Matrix.map_zero]
  map_mul' x y := by
    ext1
    have : ((ρ x).1 * (ρ y).1).map (TrivSqZeroExt.inl (M := k)) =
        (ρ x).1.map TrivSqZeroExt.inl * (ρ y).1.map TrivSqZeroExt.inl :=
      map_mul ((TrivSqZeroExt.inlHom k k).mapMatrix) (ρ x).1 (ρ y).1
    simp only [map_mul, Units.val_mul, map_inv, Matrix.coe_units_inv, this, ← mul_assoc]
    congr 1
    simp only [add_mul, one_mul, mul_add, mul_one]
    simp only [DualNumber.matrixMap_inr, Matrix.smul_mul, ← TrivSqZeroExt.matrixMap_inl_mul,
      Matrix.mul_smul, ← mul_smul]
    simp only [DualNumber.eps_mul_eps, zero_smul, add_zero, hσ', TrivSqZeroExt.matrixMap_inl_add,
      smul_add, add_assoc]


set_option maxHeartbeats 0 in
@[simps!]
noncomputable
def overDualNumberEquivInvFunContinuousMonoidHom
    (σ : groupCohomology.oneCocycles (Rep.of ((Representation.glAdjoint n (ResidueField 𝒪)).comp ρ.toMonoidHom)))
    (hσ : groupCohomology.H1.Continuous (Submodule.Quotient.mk σ)) :
    ContinuousMonoidHom G (GL n (DeformationCat.DualNumber (𝒪 := 𝒪)).X) where
  __ := overDualNumberEquivInvFunMonoidHom ρ.1 σ.1
      (groupCohomology.oneCocycles_map_one _) (fun x y ↦ by
      rw [(groupCohomology.mem_oneCocycles_iff _).mp σ.2]
      simp only [ContinuousMonoidHom.toMonoidHom_eq_coe, Rep.coe_of, Rep.of_ρ, MonoidHom.coe_comp,
        MonoidHom.coe_coe, Function.comp_apply, groupCohomology.oneCocycles.val_eq_coe,
        Representation.glAdjoint_apply, add_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, mul_one]
      rw [add_comm])
  continuous_toFun := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine ((continuous_add_left _).comp ?_).mul ?_
      · exact hσ.matrix_map (R := DeformationCat.DualNumber.X) continuous_of_discreteTopology
      · refine Continuous.matrix_map (R := DeformationCat.DualNumber.X) ?_ ?_
        · exact Units.continuous_val.comp ρ.continuous_toFun
        · exact continuous_of_discreteTopology
    · refine Continuous.mul ?_ ((continuous_sub_left _).comp ?_)
      · refine Continuous.matrix_map (R := DeformationCat.DualNumber.X) ?_ ?_
        · exact Units.continuous_val.comp (ρ.continuous_toFun.comp continuous_inv)
        · exact continuous_of_discreteTopology
      · exact hσ.matrix_map (R := DeformationCat.DualNumber.X) continuous_of_discreteTopology

set_option maxHeartbeats 0 in
noncomputable
def overDualNumberEquivInvFun (σ : DeformationCat.H1 ρ) (hσ : σ.Continuous) :
    (DeformationProblem.Over 𝒪 G n ρ).obj DeformationCat.DualNumber :=
  Quotient.hrecOn σ (fun σ hσ ↦ ⟨Quotient.mk'' (overDualNumberEquivInvFunContinuousMonoidHom ρ σ hσ), by
      -- sorry
      obtain ⟨σ, hσ'⟩ := σ
      show Quotient.mk'' _ = Quotient.mk'' _
      congr 1
      ext g : 2
      simp only [DeformationCat.residueField, toResidueField_dualNumber, AlgHom.coe_restrictScalars,
        ContinuousMonoidHom.toMonoidHom_eq_coe, ContinuousMonoidHom.comp_toFun, MonoidHom.coe_coe,
        Matrix.GeneralLinearGroup.continuousMap_apply, Matrix.GeneralLinearGroup.map,
        RingHom.toMonoidHom_eq_coe, Units.coe_map, RingHom.mapMatrix_apply, RingHom.coe_coe]
      erw [val_overDualNumberEquivInvFunContinuousMonoidHom_toFun]
      erw [Matrix.map_mul, Matrix.map_add _ (by simp), Matrix.map_one _ (by simp)]
      convert one_mul _
      · ext i j
        simp only [DeformationCat.DualNumber, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Matrix.map_map, Matrix.add_apply, Matrix.map_apply, Function.comp_apply,
          DualNumber.inr_eq_smul_eps, map_smul, TrivSqZeroExt.fstHom_apply, DualNumber.fst_eps,
          smul_eq_mul, mul_zero, add_zero]
      · exact map_one _
        ⟩) (by
      rintro σ₁ σ₂ H
      apply Function.hfunext
      · congr 1; exact Quotient.sound H
      · refine fun _ _ _ ↦ heq_of_eq ?_
        ext1
        obtain ⟨⟨⟨a⟩, r : Matrix n n _, rfl : _ = a⟩, rfl⟩ := H
        refine Quotient.eq.mpr ?_
        refine ⟨⟨1 + r.map TrivSqZeroExt.inr, 1 - r.map TrivSqZeroExt.inr, ?_, ?_⟩, fun g ↦ ?_, ?_⟩
        · rw [← (Commute.one_left _).mul_self_sub_mul_self_eq, one_mul, ← pow_two,
            DualNumber.matrixMap_inr, smul_pow (N := Matrix n n (DualNumber 𝕜)), pow_two,
            DualNumber.eps_mul_eps, zero_smul, sub_zero]
        · rw [← (Commute.one_left _).mul_self_sub_mul_self_eq', one_mul, ← pow_two,
            DualNumber.matrixMap_inr, smul_pow (N := Matrix n n (DualNumber 𝕜)), pow_two,
            DualNumber.eps_mul_eps, zero_smul, sub_zero]
        · ext1
          convert_to (1 + r.map TrivSqZeroExt.inr) *
            ((1 + Matrix.map (β := DualNumber 𝕜) (σ₂ g + ((ρ g).1 * r * (ρ g)⁻¹.1 - r)) TrivSqZeroExt.inr) *
              (ρ g).1.map TrivSqZeroExt.inl) =
            (1 + (σ₂ g).map TrivSqZeroExt.inr) * (ρ g).1.map TrivSqZeroExt.inl * (1 + r.map TrivSqZeroExt.inr)
          dsimp only [ContinuousMonoidHom.toMonoidHom_eq_coe, Rep.coe_of]
          simp only [DualNumber.matrixMap_inr, mul_assoc, add_mul, one_mul, Matrix.smul_mul, ←
            TrivSqZeroExt.matrixMap_inl_mul, sub_mul, ← Units.val_mul, inv_mul_cancel,
            Units.val_one, mul_one, mul_add, Matrix.mul_smul, ← mul_smul, DualNumber.eps_mul_eps,
            zero_smul, add_zero, add_assoc, ← smul_add, ← TrivSqZeroExt.matrixMap_inl_add]
          congr! 3
          abel
        · erw [add_sub_cancel_left]
          intro i j
          simp only [DeformationCat.DualNumber, Matrix.map_apply, DualNumber.inr_eq_smul_eps,
            mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst,
            TrivSqZeroExt.fst_smul, DualNumber.fst_eps, smul_eq_mul, mul_zero, isUnit_iff_ne_zero,
            ne_eq, not_true_eq_false, not_false_eq_true]) hσ

-- set_option maxHeartbeats 0 in
noncomputable
def overDualNumberEquiv :
    (DeformationProblem.Over 𝒪 G n ρ).obj DeformationCat.DualNumber ≃
      { σ : DeformationCat.H1 ρ // σ.Continuous } where
  toFun ρ' := ⟨Quotient.hrecOn ρ'.1 (overDualNumberEquivToFun ρ) (by
      rintro ρ₁ ρ₂ H
      apply Function.hfunext
      · congr 1; exact Quotient.sound H
      exact fun _ _ _ ↦ heq_of_eq (overDualNumberEquivToFun_eq _ _ _ H _ _)) ρ'.2, by
      obtain ⟨⟨ρ'⟩, hρ'⟩ := ρ'; exact continuous_overDualNumberEquivToFun ρ ρ' hρ'⟩
  invFun σ := overDualNumberEquivInvFun ρ σ.1 σ.2
  left_inv ρ' := by
    ext
    obtain ⟨⟨ρ'⟩, hρ'⟩ := ρ'
    dsimp [overDualNumberEquivInvFun, Quotient.hrecOn, Quot.hrecOn, Quot.recOn, Quot.rec]
    show Quotient.mk (equivRepr G DeformationCat.DualNumber.X)
        (overDualNumberEquivInvFunContinuousMonoidHom ρ _ _) =
      Quotient.mk _ ρ'
    refine Quotient.eq.mpr ?_
    refine ⟨1, fun g ↦ ?_, by simp⟩
    show _ = _
    simp only [ContinuousMonoidHom.toMonoidHom_eq_coe, Rep.coe_of, map_inv, one_mul, mul_one]
    ext1
    show (1 + ((ρ' g).1.map TrivSqZeroExt.snd * (ρ g)⁻¹.1).map TrivSqZeroExt.inr) *
      (ρ g).1.map TrivSqZeroExt.inl = (ρ' g).1
    simp only [DualNumber.matrixMap_inr, add_mul, one_mul, Matrix.smul_mul, ←
      TrivSqZeroExt.matrixMap_inl_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mul_one]
    rw [← (equivRepr_iff_eq _ 𝕜).mp (Quotient.eq.mp hρ')]
    ext1 i j
    simp only [toResidueField_dualNumber, AlgHom.coe_restrictScalars, Matrix.map_map,
      Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, Function.comp_apply, smul_eq_mul]
    simp only [DeformationCat.DualNumber, DeformationCat.residueField,
      ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Matrix.GeneralLinearGroup.continuousMap_apply, Matrix.GeneralLinearGroup.map_apply,
      RingHom.coe_coe, TrivSqZeroExt.fstHom_apply]
    ext <;> simp
  right_inv σ := by
    obtain ⟨⟨σ⟩, hσ⟩ := σ
    ext1
    dsimp [overDualNumberEquivInvFun, Quotient.hrecOn, Quot.hrecOn, Quot.recOn, Quot.rec]
    show overDualNumberEquivToFun ρ (overDualNumberEquivInvFunContinuousMonoidHom ρ σ _) _ =
      Quotient.mk _ _
    refine (Submodule.Quotient.eq _).mpr ⟨0, ?_⟩
    apply Subtype.ext
    ext g
    dsimp
    simp only [map_zero, map_inv]
    refine (sub_eq_zero.mpr ?_).symm
    apply (ρ g).isUnit.mul_left_injective
    refine (mul_assoc _ _ _).trans ?_
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    ext i j
    simp only [DeformationCat.DualNumber, add_mul, one_mul, Matrix.map_apply, Matrix.add_apply,
      Matrix.mul_apply, DualNumber.inr_eq_smul_eps, Algebra.smul_mul_assoc, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_mul,
      DualNumber.fst_eps, smul_eq_mul, mul_zero, TrivSqZeroExt.fst_inl, DualNumber.snd_eps,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, zero_add,
      groupCohomology.oneCocycles.val_eq_coe, ContinuousMonoidHom.toMonoidHom_eq_coe, Rep.coe_of]
