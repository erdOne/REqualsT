import REqualsT.Deformation.Basic
import Mathlib

universe u uO uF uG un

open CategoryTheory IsLocalRing

variable (𝒪 : Type uO) [CommRing 𝒪] [IsNoetherianRing 𝒪]
variable [IsLocalRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
variable (G : Type uG) [TopologicalSpace G] [Group G] [TopologicalGroup G] [CompactSpace G]
variable (n : Type un) [DecidableEq n] [Fintype n]

variable {𝒪 G n}

variable (R : DeformationCat.{uO} 𝒪)

abbrev DeformationCat.Cotangent : Type _ :=
  maximalIdeal R.X ⧸ Submodule.comap (maximalIdeal R.X).subtype ((maximalIdeal 𝒪).map (algebraMap 𝒪 R.X) ⊔ maximalIdeal R.X ^ 2)

instance : Module (ResidueField 𝒪) R.Cotangent := Module.IsTorsionBySet.module <| by
  delta DeformationCat.Cotangent
  refine (Module.isTorsionBySet_quotient_iff ((Submodule.comap (maximalIdeal R.X).subtype ((maximalIdeal 𝒪).map
    (algebraMap 𝒪 R.X) ⊔ maximalIdeal R.X ^ 2)).restrictScalars 𝒪) _).mpr ?_
  rintro ⟨s, hs⟩ r hr
  rw [← algebraMap_smul (R := 𝒪) R.X, pow_two]
  exact Submodule.mem_sup_right (Ideal.mul_mem_mul (fun h ↦ hr ((isUnit_map_iff _ _).mp h)) hs)

instance : IsScalarTower 𝒪 (ResidueField 𝒪) R.Cotangent := .of_algebraMap_smul fun _ _ ↦ rfl

section CotangentToEquiv

variable {R}

noncomputable
def cotangentToEquivToFunApply (l : R.Cotangent →ₗ[ResidueField 𝒪] ResidueField 𝒪) (a : R.X) : DualNumber (ResidueField 𝒪) :=
  ⟨residue _ (DeformationCat.preimage a), l (Submodule.Quotient.mk ⟨_, DeformationCat.preimage_spec a⟩)⟩

lemma cotangentToEquivToFunApply_add (l : R.Cotangent →ₗ[ResidueField 𝒪] ResidueField 𝒪)
    (a : 𝒪) (b : R.X) (hb : b ∈ maximalIdeal R.X) : cotangentToEquivToFunApply l (algebraMap _ _ a + b) =
    ⟨residue _ a, l (Submodule.Quotient.mk ⟨b, hb⟩)⟩ := by
  ext
  · refine DeformationCat.residue_preimage_eq_iff.mpr ?_
    simpa [ResidueField.map_residue] using hb
  · simp only [cotangentToEquivToFunApply, TrivSqZeroExt.snd_mk]
    congr 1
    rw [Submodule.Quotient.eq]
    refine Submodule.mem_sup_left ?_
    simp only [add_sub_right_comm, Submodule.mem_comap, Submodule.coe_subtype,
      AddSubgroupClass.coe_sub, sub_add_cancel, ← map_sub]
    refine Ideal.mem_map_of_mem _ ?_
    rw [← residue_eq_zero_iff]
    apply R.bijective.1
    simpa [ResidueField.map_residue, DeformationCat.residue_preimage] using hb

lemma Submodule.zero_def {R M} [Semiring R] [AddCommMonoid M] [Module R M] (N : Submodule R M) :
    (0 : N) = ⟨0, zero_mem N⟩ := rfl

noncomputable
nonrec def DeformationCat.DualNumber : DeformationCat 𝒪 where
  X := DualNumber (ResidueField 𝒪)
  isAdicComplete := sorry
  isLocalHom := by
    constructor
    intro x hx
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero] at hx
    exact not_not.mp ((residue_eq_zero_iff _).not.mp hx)
  bijective := sorry

open DeformationCat in
@[simps (config := .lemmasOnly)]
noncomputable
def cotangentToEquivToFun (l : R.Cotangent →ₗ[ResidueField 𝒪] ResidueField 𝒪) : R.X →ₐ[𝒪] DualNumber (ResidueField 𝒪) where
  toFun := cotangentToEquivToFunApply l
  map_one' := by simpa [← Submodule.zero_def] using cotangentToEquivToFunApply_add l 1 0 (zero_mem _)
  map_mul' x y := by
    have := cotangentToEquivToFunApply_add l (preimage x * preimage y)
      (x * y - algebraMap _ _ (preimage x * preimage y))
      ((residue_eq_zero_iff _).mp (by simp [residue_preimage]))
    simp only [map_mul, add_sub_cancel] at this
    simp only [this]
    unfold cotangentToEquivToFunApply
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mk, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mk, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      simp only [← ResidueField.algebraMap_eq, ← Algebra.smul_def, ← LinearMap.map_smul_of_tower,
        ← map_add, mul_comm (l _), ← Submodule.mkQ_apply]
      congr 1
      refine (Submodule.Quotient.eq _).mpr (Submodule.mem_sup_right ?_)
      rw [pow_two]
      convert Ideal.mul_mem_mul (preimage_spec x) (preimage_spec y) using 1
      simp [Algebra.smul_def, mul_sub]
      ring
  map_zero' := by simpa [← Submodule.zero_def] using cotangentToEquivToFunApply_add l 0 0 (zero_mem _)
  map_add' x y := by
    have := cotangentToEquivToFunApply_add l (preimage x + preimage y)
      (x + y - algebraMap _ _ (preimage x + preimage y))
      ((residue_eq_zero_iff _).mp (by simp [residue_preimage]))
    simp only [map_add, add_sub_cancel] at this
    simp only [this]
    unfold cotangentToEquivToFunApply
    ext
    · simp
    · simp only [← map_add, TrivSqZeroExt.snd_mk, TrivSqZeroExt.snd_add, ← Submodule.Quotient.mk_add]
      congr 3
      rw [map_add, add_sub_add_comm]
  commutes' r := by simpa [← Submodule.zero_def] using cotangentToEquivToFunApply_add l r 0 (zero_mem _)

open DeformationCat in
noncomputable
instance isLocalHom_cotangentToEquivToFun (l : R.Cotangent →ₗ[ResidueField 𝒪] ResidueField 𝒪) :
    IsLocalHom (cotangentToEquivToFun l).toRingHom := by
  constructor
  intro x hx
  replace hx := TrivSqZeroExt.isUnit_iff_isUnit_fst.mp hx
  rw [isUnit_iff_ne_zero] at hx
  simpa using residue_preimage_eq_iff.not.mp hx

instance {R} [CommRing R] : IsLocalHom (algebraMap R R) := ⟨fun _ ↦ id⟩

instance {R S T} [CommRing R] [CommRing S] [CommRing T] [IsLocalRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] [IsLocalHom (algebraMap R T)] [IsLocalHom (algebraMap S T)] :
    IsScalarTower R S (ResidueField T) := IsScalarTower.of_algebraMap_eq' <| by
  show (algebraMap T _).comp (algebraMap R T) = _
  rw [IsScalarTower.algebraMap_eq R S]
  rfl

def cotangentToEquivInvFun (f : R.X →ₐ[𝒪] DualNumber (ResidueField 𝒪)) [IsLocalHom f] :
    R.Cotangent →ₗ[ResidueField 𝒪] ResidueField 𝒪 := by
  refine LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective ?_
  refine Submodule.liftQ ((Submodule.comap (maximalIdeal R.X).subtype ((maximalIdeal 𝒪).map
    (algebraMap 𝒪 R.X) ⊔ maximalIdeal R.X ^ 2)).restrictScalars 𝒪) ?_ ?_
  · exact (TrivSqZeroExt.sndHom _ _).restrictScalars 𝒪 ∘ₗ f.toLinearMap ∘ₗ (maximalIdeal R.X).subtype.restrictScalars 𝒪
  · rintro ⟨x, hx₁⟩ hx
    obtain ⟨x, hx₂, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    have H₁ : f x = 0 := by
      clear! y
      induction hx₂ using Submodule.span_induction with
      | mem x h =>
        obtain ⟨x, hx, rfl⟩ := h
        simp only [AlgHom.commutes]
        ext
        · exact (residue_eq_zero_iff _).mpr hx
        · rfl
      | zero => simp
      | add x y hx hy _ _ => simp [*]
      | smul a x hx _ => simp [*]
    have H₂' (x) (hx : x ∈ maximalIdeal R.X) : (f x).fst = 0 := by
      rwa [← not_ne_iff, ← isUnit_iff_ne_zero, ← TrivSqZeroExt.isUnit_iff_isUnit_fst,
        isUnit_map_iff]
    have H₂ : f y = 0 := by
      clear! x
      rw [pow_two, Submodule.mul_eq_span_mul_set] at hy
      induction hy using Submodule.span_induction with
      | mem x h =>
        obtain ⟨a, ha, b, hb, rfl⟩ := h
        ext
        · simp [H₂' a ha, H₂' b hb]
        · simp [H₂' a ha, H₂' b hb]
      | zero => simp
      | add x y hx hy _ _ => simp [*]
      | smul a x hx _ => simp [*]
    simp [H₁, H₂]

lemma cotangentToEquivInvFun_apply (f : R.X →ₐ[𝒪] DualNumber (ResidueField 𝒪)) [IsLocalHom f] (x) :
    cotangentToEquivInvFun f (Submodule.Quotient.mk x) = (f x.1).snd := rfl

noncomputable
def cotangentToEquiv : (R.Cotangent →ₗ[ResidueField 𝒪] ResidueField 𝒪) ≃ (R ⟶ DeformationCat.DualNumber) where
  toFun l := { toAlgHom := cotangentToEquivToFun l, isLocalHom := isLocalHom_cotangentToEquivToFun l }
  invFun f := @cotangentToEquivInvFun _ _ _ _ _ _ f.toAlgHom ⟨f.isLocalHom.1⟩
  left_inv l := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    dsimp [cotangentToEquivInvFun_apply, cotangentToEquivToFun, cotangentToEquivToFunApply]
    congr 1
    rw [Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
      sub_sub_cancel_left, neg_mem_iff]
    refine Submodule.mem_sup_left ?_
    refine Ideal.mem_map_of_mem _ ?_
    rw [← residue_eq_zero_iff, DeformationCat.residue_preimage_eq_iff]
    simp
  right_inv f := by
    apply DeformationCat.Hom.ext
    ext x
    have H (x) (hx : x ∈ maximalIdeal R.X) : (f.toAlgHom x).fst = 0 := by
        rw [← not_ne_iff, ← isUnit_iff_ne_zero, ← TrivSqZeroExt.isUnit_iff_isUnit_fst]
        exact (isUnit_map_iff f.toAlgHom.toRingHom _).not.mpr hx
    apply TrivSqZeroExt.ext
    · show (algebraMap 𝒪 DeformationCat.DualNumber.X _).fst = _
      rw [← f.toAlgHom.commutes, eq_comm, ← sub_eq_zero, ← TrivSqZeroExt.fst_sub,
        ← map_sub f.toAlgHom, H]
      exact DeformationCat.preimage_spec _
    · show (f.toAlgHom (x - _)).snd = _
      rw [map_sub, TrivSqZeroExt.snd_sub, f.toAlgHom.commutes]
      exact sub_zero _

end CotangentToEquiv

variable (𝒟 : DeformationProblem.{uO} 𝒪 G n) [𝒟.toFunctor.IsCorepresentable]

noncomputable
def cotangentToCoreprXEquiv :
    (𝒟.toFunctor.coreprX.Cotangent →ₗ[ResidueField 𝒪] ResidueField 𝒪) ≃ 𝒟.obj DeformationCat.DualNumber :=
  cotangentToEquiv.trans 𝒟.toFunctor.corepresentableBy.homEquiv
