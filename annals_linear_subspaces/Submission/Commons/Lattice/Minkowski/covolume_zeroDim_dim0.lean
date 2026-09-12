import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Lattice.Minkowski

open scoped ENNReal
open MeasureTheory

set_option linter.style.haveILetI false in
theorem covolume_zeroDim_dim0 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (hE : Module.finrank ℝ E = 0) :
    ZLattice.covolume (⊥ : Submodule ℤ E) = 1 := by
  classical
  -- A zero-dimensional real inner product space is a singleton.
  haveI : Subsingleton E := (Module.finrank_zero_iff (R := ℝ) (M := E)).mp hE
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
  -- In a zero-dimensional inner product space, the total volume is 1: the volume
  -- measure is transported by an orthonormal basis to the Euclidean space of
  -- dimension `finrank ℝ E = 0`, where the measure is the Dirac mass at `0`.
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  have hF : (volume : Measure F) Set.univ = 1 := by
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by
      constructor
      intro a
      have hal : a.val < Module.finrank ℝ E := a.isLt
      omega
    rw [volume_euclideanSpace_eq_dirac (ι := Fin (Module.finrank ℝ E))]
    simp
  let b := stdOrthonormalBasis ℝ E
  have hmp : MeasurePreserving (⇑(b.repr : E ≃ₗᵢ[ℝ] F)) (volume : Measure E) (volume : Measure F) := by
    simpa [F] using (b.measurePreserving_repr : MeasurePreserving (⇑b.repr) volume volume)
  have htot : (volume : Measure E) Set.univ = (volume : Measure F) Set.univ := by
    symm
    calc
      (volume : Measure F) Set.univ = (Measure.map (⇑(b.repr : E ≃ₗᵢ[ℝ] F)) (volume : Measure E)) Set.univ := by
        rw [hmp.map_eq]
      _ = (volume : Measure E) ((⇑(b.repr : E ≃ₗᵢ[ℝ] F)) ⁻¹' Set.univ) := by
        exact Measure.map_apply hmp.measurable MeasurableSet.univ
      _ = (volume : Measure E) Set.univ := by simp
  have hUniv : (volume : Measure E) Set.univ = 1 := htot.trans hF
  rw [hUniv]
  simp

end Commons.Lattice.Minkowski