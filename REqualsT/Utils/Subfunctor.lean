import Mathlib.CategoryTheory.Types

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

structure Functor.Subfunctor where
  obj : ∀ X, Set (F.obj X)
  map : ∀ {X Y : C} (f : X ⟶ Y), Set.MapsTo (F.map f) (obj X) (obj Y)

variable {F}

@[simps]
def Functor.Subfunctor.toFunctor (G : F.Subfunctor) : C ⥤ Type w where
  obj X := G.obj X
  map f := (G.map f).restrict

end CategoryTheory
