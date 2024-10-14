import Mathlib
import REqualsT.Utils.Subfunctor
import REqualsT.Utils.CompleteRing
import REqualsT.GaloisTheory.Frob

/-!
Sources:
https://www1.iwr.uni-heidelberg.de/fileadmin/groups/arithgeo/templates/data/Gebhard_Boeckle/Boeckle-Barcelona-DefTheory-Rev.pdf
https://math.berkeley.edu/~fengt/249A_2018.pdf

-/

universe u uO uF

open CategoryTheory LocalRing

variable (𝒪 : Type uO) [CommRing 𝒪] [IsNoetherianRing 𝒪] [LocalRing 𝒪] [IsCompleteLocalRing 𝒪]

structure DeformationCat where
  X : Type u
  [commRing : CommRing X]
  [localRing : LocalRing X]
  [isNoetherianRing : IsNoetherianRing X]
  [isCompleteLocalRing : IsCompleteLocalRing X]
  [algebra : Algebra 𝒪 X]
  [isLocalRingHom : IsLocalRingHom (algebraMap 𝒪 X)]
  bijective : Function.Bijective (LocalRing.ResidueField.map (algebraMap 𝒪 X))

namespace DeformationCat

attribute [instance] commRing localRing algebra isNoetherianRing isCompleteLocalRing isLocalRingHom

scoped[Deformation] notation "𝒞" => DeformationCat

open scoped Deformation

variable {𝒪 F}

@[ext]
structure Hom (A B : 𝒞 𝒪) where
  toAlgHom : A.X →ₐ[𝒪] B.X
  [isLocalRingHom : IsLocalRingHom toAlgHom.toRingHom]

attribute [instance] Hom.isLocalRingHom

instance : Quiver (𝒞 𝒪) where
  Hom := Hom

instance (A B : (𝒞 𝒪)) (f : A ⟶ B) : IsLocalRingHom (RingHomClass.toRingHom f.toAlgHom) :=
  Hom.isLocalRingHom ..

instance : Category (𝒞 𝒪) where
  id A := Hom.mk (AlgHom.id _ _) (isLocalRingHom := ⟨fun _ ↦ id⟩)
  comp f g := Hom.mk (g.toAlgHom.comp f.toAlgHom)
    (isLocalRingHom := inferInstanceAs (IsLocalRingHom (g.toAlgHom.toRingHom.comp f.toAlgHom.toRingHom)))

instance : ConcreteCategory (𝒞 𝒪) where
  forget := { obj := X, map := fun f ↦ f.toAlgHom }
  forget_faithful := ⟨(Hom.ext <| AlgHom.ext <| congr_fun ·)⟩

instance : HasForget₂ (𝒞 𝒪) CommRingCat where
  forget₂ := { obj := fun R ↦ .of R.X, map := fun f ↦ f.toAlgHom.toRingHom }

instance : Bot (𝒞 𝒪) where
  bot := { X := 𝒪, isLocalRingHom := ⟨fun _ ↦ id⟩, bijective := (ResidueField.mapEquiv (RingEquiv.refl 𝒪)).bijective }

end DeformationCat

open scoped Deformation

universe v uG

variable (G : Type uG) [TopologicalSpace G] [Group G] [TopologicalGroup G] [CompactSpace G] -- or even profinite

attribute [local instance] LocalRing.withIdeal

def equivRepr (A) [CommRing A] [LocalRing A] : Setoid (ContinuousMonoidHom G (GL (Fin 2) A)) where
  r ρ₁ ρ₂ := ∃ r : (GL (Fin 2) A), (∀ i, ρ₁ i = r * ρ₂ i * r⁻¹) ∧
    (∀ i j, (r - 1 : Matrix (Fin 2) (Fin 2) A) i j ∈ LocalRing.maximalIdeal A)
  iseqv := sorry

open Filter in
def dim2Repr : (𝒞 𝒪) ⥤ Type _ where
  obj R := _root_.Quotient (equivRepr G R.X)
  map {R S} f ρ := sorry
  map_id := sorry
  map_comp := sorry
