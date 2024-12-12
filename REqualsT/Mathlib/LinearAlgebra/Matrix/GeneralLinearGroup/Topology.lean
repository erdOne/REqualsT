import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import REqualsT.Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.Matrix

def Matrix.GeneralLinearGroup.continuousMap {R S n : Type*} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [DecidableEq n] [Fintype n] (f : R →+* S) (hf : Continuous f) :
    ContinuousMonoidHom (GL n R) (GL n S) :=
  Units.continuousMap ⟨(RingHom.mapMatrix f).toMonoidHom,
    continuous_pi fun i ↦ continuous_pi fun j ↦ hf.comp (continuous_apply_apply i j)⟩

@[simp]
lemma Matrix.GeneralLinearGroup.continuousMap_apply
    {R S n : Type*} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [DecidableEq n] [Fintype n] (f : R →+* S) (hf : Continuous f) (M : GL n R) :
  continuousMap f hf M = M.map f := rfl
