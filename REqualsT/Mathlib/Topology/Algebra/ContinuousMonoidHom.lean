import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[simps! toFun]
def Units.continuousMap {G H : Type*} [Monoid G] [Monoid H] [TopologicalSpace G] [TopologicalSpace H]
    (f : ContinuousMonoidHom G H) : ContinuousMonoidHom Gˣ Hˣ where
  __ := Units.map f
  continuous_toFun := by exact
    Units.continuous_iff.mpr ⟨f.continuous.comp Units.continuous_val,
      f.continuous.comp Units.continuous_coe_inv⟩
