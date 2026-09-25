import Mathlib
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts

namespace Work.Geometry

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

/-- **Unfolding identity for the point count.** Averaging the number of points of the coset
`a + Λ` of the lattice `Λ = Lattice K I` that lie in the window `B_R` over a fundamental
domain of `Λ` counts every lattice point exactly once, so the integral equals the volume of
the window. This is the basic step of the averaging ("Minkowski") argument: it expresses an
average of point counts as the volume of the window `B_R`. -/
theorem lintegral_pointCount (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) :
    ∫⁻ a in Fund K I, pointCount K I R a = volume (Window K R) := by
  -- the lattice subgroup is countable, so that the fundamental domain unwinds the integral
  have hcount : Countable ↥((Lattice K I).toAddSubgroup) :=
    inferInstanceAs (Countable (Lattice K I))
  have hfd := isAddFundamentalDomain_fund (K := K) I
  -- each summand `a ↦ 1_B_R (a + l)` is almost everywhere measurable
  have hmeas : ∀ l : Lattice K I, AEMeasurable
      (fun a => (Window K R).indicator (fun _ => (1 : ENNReal))
        (a + (l : mixedEmbedding.mixedSpace K))) (volume.restrict (Fund K I)) :=
    fun l =>
      ((measurable_const : Measurable
          (fun _ : mixedEmbedding.mixedSpace K => (1 : ENNReal))).indicator
        (measurableSet_window R)).comp_aemeasurable
        (measurable_add_const _).aemeasurable
  -- unfold the point count as a sum of indicators over the lattice, and exchange integral
  -- and sum (Tonelli for the countable lattice)
  unfold pointCount
  rw [lintegral_tsum hmeas]
  -- the volume of the window is the integral of its indicator
  rw [← lintegral_indicator_one (measurableSet_window R)]
  -- the translates of the fundamental domain tile the space: unwinding the integral
  -- `∑' l, ∫⁻ a in Fund, 1_B_R (l +ᵥ a)` gives back the integral of `1_B_R` over the space
  rw [hfd.lintegral_eq_tsum'']
  apply tsum_congr
  intro l
  apply lintegral_congr
  intro a
  -- `l +ᵥ a` is the translation `↑l + a` in the mixed space
  change (Window K R).indicator (fun _ => (1 : ENNReal)) (a + (l : mixedEmbedding.mixedSpace K))
      = (Window K R).indicator (fun _ => (1 : ENNReal)) ((l : mixedEmbedding.mixedSpace K) + a)
  rw [add_comm]

end Work.Geometry
