import Mathlib.LinearAlgebra.Matrix.Ideal
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import REqualsT.Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Topology
import REqualsT.Utils.AdicTopology
import REqualsT.Utils.Subfunctor

/-!
Sources:
https://www1.iwr.uni-heidelberg.de/fileadmin/groups/arithgeo/templates/data/Gebhard_Boeckle/Boeckle-Barcelona-DefTheory-Rev.pdf
https://math.berkeley.edu/~fengt/249A_2018.pdf

-/

universe u uO uF

open CategoryTheory IsLocalRing

variable (𝒪 : Type uO) [CommRing 𝒪] [IsNoetherianRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

structure DeformationCat [IsNoetherianRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] where
  X : Type u
  [commRing : CommRing X]
  [isLocalRing : IsLocalRing X]
  [isNoetherianRing : IsNoetherianRing X]
  [isAdicComplete : IsAdicComplete (maximalIdeal X) X]
  [algebra : Algebra 𝒪 X]
  [isLocalHom : IsLocalHom (algebraMap 𝒪 X)]
  bijective : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap 𝒪 X))

namespace DeformationCat

attribute [instance] commRing isLocalRing algebra isNoetherianRing isAdicComplete isLocalHom

scoped[Deformation] notation "𝒞" => DeformationCat

open scoped Deformation

variable {𝒪 F}

@[ext]
structure Hom (A B : 𝒞 𝒪) where
  toAlgHom : A.X →ₐ[𝒪] B.X
  [isLocalHom : IsLocalHom toAlgHom.toRingHom]

attribute [instance] Hom.isLocalHom

instance : Quiver (𝒞 𝒪) where
  Hom := Hom

instance (A B : 𝒞 𝒪) (f : A ⟶ B) : IsLocalHom (RingHomClass.toRingHom f.toAlgHom) :=
  Hom.isLocalHom ..

instance (A B : 𝒞 𝒪) (f : A ⟶ B) : IsLocalHom f.toAlgHom :=
  ⟨IsLocalHom.map_nonunit (f := f.toAlgHom.toRingHom)⟩

instance : Category (𝒞 𝒪) where
  id A := Hom.mk (AlgHom.id _ _) (isLocalHom := ⟨fun _ ↦ id⟩)
  comp f g := Hom.mk (g.toAlgHom.comp f.toAlgHom)
    (isLocalHom := inferInstanceAs (IsLocalHom (g.toAlgHom.toRingHom.comp f.toAlgHom.toRingHom)))

instance : ConcreteCategory (𝒞 𝒪) where
  forget := { obj := X, map := fun f ↦ f.toAlgHom }
  forget_faithful := ⟨(Hom.ext <| AlgHom.ext <| congr_fun ·)⟩

instance : HasForget₂ (𝒞 𝒪) CommRingCat where
  forget₂ := { obj := fun R ↦ .of R.X, map := fun f ↦ f.toAlgHom.toRingHom }

variable {R : 𝒞 𝒪}

lemma exists_sub_mem_maximalIdeal (r : R.X) : ∃ (a : 𝒪), r - algebraMap _ _ a ∈ maximalIdeal _ := by
  obtain ⟨a, ha⟩ := R.bijective.2 (residue _ r)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact ha.symm

noncomputable
def preimage (r : R.X) : 𝒪 := (exists_sub_mem_maximalIdeal r).choose

lemma preimage_spec (r : R.X) : r - algebraMap _ _ (preimage r) ∈ maximalIdeal _ :=
  (exists_sub_mem_maximalIdeal r).choose_spec

lemma residue_preimage (r : R.X) : residue _ (algebraMap _ _ (preimage r)) = residue _ r :=
  (Ideal.Quotient.eq.mpr (preimage_spec r)).symm

lemma residue_preimage_eq_iff {r : R.X} {a} :
    residue _ (preimage r) = a ↔ residue _ r = ResidueField.map (algebraMap 𝒪 R.X) a := by
  rw [← R.bijective.1.eq_iff, ResidueField.map_residue, residue_preimage]

def self : 𝒞 𝒪 :=
  { X := 𝒪, isLocalHom := ⟨fun _ ↦ id⟩, bijective := (ResidueField.mapEquiv (RingEquiv.refl 𝒪)).bijective }

def residueField : 𝒞 𝒪 where
  X := ResidueField 𝒪
  isAdicComplete := sorry
  isLocalHom := .of_surjective _ residue_surjective
  bijective := sorry

def fromSelf (R : 𝒞 𝒪) : self ⟶ R := Hom.mk (Algebra.ofId 𝒪 R.X) (isLocalHom := ⟨R.isLocalHom.1⟩)

noncomputable
def toResidueField (R : 𝒞 𝒪) : R ⟶ residueField :=
  Hom.mk ⟨(RingEquiv.ofBijective _ R.bijective).symm.toRingHom.comp (residue _), fun _ ↦ R.bijective.1
    ((RingEquiv.ofBijective _ R.bijective).apply_symm_apply _)⟩
    (isLocalHom := .of_surjective _ ((RingEquiv.ofBijective _ R.bijective).symm.surjective.comp residue_surjective))

lemma to_residueField_apply {R : 𝒞 𝒪} (f : R ⟶ residueField) (r : R.X) : f.toAlgHom r = residue _ (preimage r)  := by
  trans f.toAlgHom (algebraMap _ _ (preimage r))
  · rw [← sub_eq_zero, ← map_sub, ← not_ne_iff,
      ← @isUnit_iff_ne_zero _ (inferInstanceAs (GroupWithZero (ResidueField 𝒪))),
      isUnit_map_iff f.toAlgHom, ← mem_nonunits_iff, ← mem_maximalIdeal]
    exact preimage_spec _
  · simp; rfl

lemma to_residueField_ext {R : 𝒞 𝒪} (f₁ f₂ : R ⟶ residueField) : f₁ = f₂ := by
  refine Hom.ext ?_
  ext r
  rw [to_residueField_apply, to_residueField_apply]

end DeformationCat

open scoped Deformation

universe v uG

variable (G : Type uG) [TopologicalSpace G] [Group G] [TopologicalGroup G] [CompactSpace G] -- or even profinite

attribute [local instance] IsLocalRing.withIdeal

variable {n : Type*} [DecidableEq n] [Fintype n]

def equivRepr (A) [CommRing A] [IsLocalRing A] : Setoid (ContinuousMonoidHom G (GL n A)) where
  r ρ₁ ρ₂ := ∃ r : GL n A, (∀ i, SemiconjBy r (ρ₁ i) (ρ₂ i)) ∧
    r.val - 1 ∈ (IsLocalRing.maximalIdeal A).matricesOver _
  iseqv := by
    constructor
    · exact fun _ ↦ ⟨1, by simp⟩
    · rintro x y ⟨r, h₁, h₂⟩
      refine ⟨r⁻¹, fun i ↦ (h₁ i).inv_symm_left, ?_⟩
      rw [← Ideal.unit_mul_mem_iff_mem _ r.isUnit.neg]
      convert h₂ using 1
      simp [mul_sub, ← sub_eq_neg_add]
    · rintro x y z ⟨r, hr₁, hr₂⟩ ⟨s, hs₁, hs₂⟩
      refine ⟨s * r, fun i ↦ (hs₁ i).mul_left (hr₁ i), ?_⟩
      simpa [mul_sub] using add_mem (Ideal.mul_mem_left _ s.1 hr₂) hs₂

omit
  [TopologicalGroup G]
  [CompactSpace G] in
lemma equivRepr_iff_eq (K) [Field K] {a b} : (equivRepr G (n := n) K).r a b ↔ a = b := by
  refine ⟨fun ⟨r, h₁, h₂⟩ ↦ ?_, fun e ↦ e ▸ (equivRepr G (n := n) K).refl a⟩
  obtain rfl : r = 1 := by simpa [equivRepr, Matrix.ext_iff (N := 1), sub_eq_zero] using h₂
  ext1 i
  simpa [SemiconjBy] using h₁ i

variable (n) in
def deformationFunctor : 𝒞 𝒪 ⥤ Type _ where
  obj R := _root_.Quotient (equivRepr (n := n) G R.X)
  map {R S} f := Quotient.map ((Matrix.GeneralLinearGroup.continuousMap f.toAlgHom
    (Continuous.of_isLocalHom _))).comp fun ρ₁ ρ₂ ↦ by
      intro ⟨r, hr, hr'⟩
      refine ⟨r.map f.toAlgHom, fun g ↦ ?_, ?_⟩
      · exact (hr g).map (Matrix.GeneralLinearGroup.map f.toAlgHom.toRingHom)
      · intro i j
        rw [← map_one f.toAlgHom.toRingHom.mapMatrix]
        simpa [-map_one, ← map_sub, isUnit_map_iff] using hr' i j
  map_id X := funext (Quotient.ind fun _ ↦ rfl)
  map_comp f g := funext (Quotient.ind fun _ ↦ rfl)

variable (n) in
abbrev DeformationProblem : Type _ := (deformationFunctor.{uO, uG, _, u} 𝒪 G n).Subfunctor

variable (n) in
def DeformationProblem.Over (ρ : ContinuousMonoidHom G (GL n (ResidueField 𝒪))) :
    DeformationProblem.{uO} 𝒪 G n where
  obj A := { ρ' | (deformationFunctor 𝒪 G n).map A.toResidueField ρ' = Quotient.mk'' ρ }
  map f ρ' hρ' := by
    dsimp
    show ((deformationFunctor 𝒪 G n).map _ ≫ (deformationFunctor 𝒪 G n).map _) ρ' = _
    rw [← Functor.map_comp, ← hρ', DeformationCat.to_residueField_ext (_ ≫ _)]
