import Mathlib.Algebra.Module.ZLattice.Covolume

namespace Commons.Lattice.Minkowski

open MeasureTheory
open scoped ENNReal

set_option linter.style.haveILetI false in
theorem covolume_zeroDim_trivial :
    ZLattice.covolume (⊥ : Submodule ℤ (EuclideanSpace ℝ (Fin 0))) = 1 := by
  let E := EuclideanSpace ℝ (Fin 0)
  let L : Submodule ℤ E := ⊥
  change ZLattice.covolume L = 1
  unfold ZLattice.covolume
  -- The whole space is a (trivial) fundamental domain for the zero lattice `⊥`.
  have hfd : IsAddFundamentalDomain L Set.univ (volume : Measure E) := by
    refine IsAddFundamentalDomain.mk' ?_ ?_
    · refine ⟨Set.univ, MeasurableSet.univ, ?_⟩
      exact ae_of_all _ (by intro x; simp)
    · intro x
      refine ⟨0, by simp, ?_⟩
      intro y hy
      exact Subsingleton.elim y 0
  -- Translations by elements of the zero lattice preserve the measure.
  have hfinv : VAddInvariantMeasure L E (volume : Measure E) := by
    constructor
    intro c s hs
    have hf : (fun x : E => c +ᵥ x) = id := by
      funext x
      exact Subsingleton.elim (c +ᵥ x) x
    rw [hf]
    simp
  haveI : VAddInvariantMeasure L E (volume : Measure E) := hfinv
  have hvol := IsAddFundamentalDomain.covolume_eq_volume (ν := volume) hfd
  rw [hvol]
  -- In the zero-dimensional Euclidean space, `volume` is the Dirac measure at `0`.
  rw [volume_euclideanSpace_eq_dirac (ι := Fin 0)]
  simp

end Commons.Lattice.Minkowski