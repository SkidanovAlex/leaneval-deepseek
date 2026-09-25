import Mathlib
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts

/-!
# The unfolding identity for the pair count

For a coset `a + Λ` of the lattice `Λ = Lattice K I`, the function `a ↦ pairCountOne K I R a u`
counts the lattice points `l` with both `a + l` and `a + l + Φ u` in `B_R`.  Integrating it over a
fundamental domain of `Λ` unfolds the sum over the lattice into an integral over the whole mixed
space, and the resulting integrand `1_{B_R}(x) · 1_{B_R}(x + Φ u)` is the indicator function of
`WindowShift K R (Φ u) = B_R ∩ (B_R - Φ u)`.  Hence

  `∫⁻ a in Fund K I, pairCountOne K I R a u = volume (WindowShift K R (mixedEmbedding K u))`.

The same argument gives the simpler point-count identity
`∫⁻ a in Fund K I, pointCount K I R a = volume (Window K R)`.
-/

namespace Work.Geometry

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

theorem lintegral_pairCountOne (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) (u : K) :
    ∫⁻ a in Fund K I, pairCountOne K I R a u
      = volume (WindowShift K R (mixedEmbedding K u)) := by
  classical
  -- `Fund K I` is a fundamental domain for the lattice, so the sum over the lattice of the
  -- translates of a function unfolds to the integral of that function over the whole space.
  have hcount : Countable ↥(Lattice K I).toAddSubgroup :=
    inferInstanceAs (Countable ↥(Lattice K I))
  -- The unfolded integrand: `1_{B_R}(x) · 1_{B_R}(x + Φ u)`.
  set g : mixedEmbedding.mixedSpace K → ENNReal :=
    fun x => (Window K R).indicator (fun _ => (1 : ENNReal)) x *
             (Window K R).indicator (fun _ => (1 : ENNReal)) (x + mixedEmbedding K u) with hgdef
  have hWin : MeasurableSet (Window K R) := measurableSet_window R
  have hgm : Measurable g := by
    rw [hgdef]
    exact (measurable_const.indicator hWin).mul
      ((measurable_const.indicator hWin).comp (measurable_id.add_const _))
  have hWs : MeasurableSet (WindowShift K R (mixedEmbedding K u)) :=
    hWin.inter (hWin.preimage (measurable_id.add_const _))
  -- `pairCountOne` is the lattice sum of the translates of `g`.
  have hpt : ∀ a : mixedEmbedding.mixedSpace K, pairCountOne K I R a u =
      ∑' l : ↥(Lattice K I).toAddSubgroup, g (l +ᵥ a) := by
    intro a
    rw [pairCountOne, hgdef]
    apply tsum_congr
    intro l
    rw [add_comm a (l : mixedEmbedding.mixedSpace K)]
    rw [show l +ᵥ (a : mixedEmbedding.mixedSpace K) = (l : mixedEmbedding.mixedSpace K) + a
      from rfl]
  -- First step: rewrite the integrand pointwise.
  have hstep : ∫⁻ a in Fund K I, pairCountOne K I R a u
      = ∫⁻ a in Fund K I, ∑' l : ↥(Lattice K I).toAddSubgroup, g (l +ᵥ a) :=
    lintegral_congr hpt
  -- Second step: exchange the integral and the (countable) lattice sum (Tonelli).
  have hton : ∫⁻ a in Fund K I, ∑' l : ↥(Lattice K I).toAddSubgroup, g (l +ᵥ a)
      = ∑' l : ↥(Lattice K I).toAddSubgroup, ∫⁻ a in Fund K I, g (l +ᵥ a) :=
    lintegral_tsum (fun l => (hgm.comp (measurable_const_vadd l)).aemeasurable)
  -- Third step: unfolding — integrating the lattice sum over a fundamental domain recovers the
  -- integral over the whole space.
  have hunfold := (isAddFundamentalDomain_fund I).lintegral_eq_tsum'' g
  -- Fourth step: the unfolded integrand is the indicator of `WindowShift`.
  have hfinal : ∫⁻ x, g x ∂volume = volume (WindowShift K R (mixedEmbedding K u)) := by
    have hgeq : g = (WindowShift K R (mixedEmbedding K u)).indicator (fun _ => (1 : ENNReal)) := by
      rw [hgdef]; funext x
      simp only [WindowShift, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.indicator]
      by_cases h1 : x ∈ Window K R <;> by_cases h2 : x + mixedEmbedding K u ∈ Window K R <;>
        simp [h1, h2]
    rw [hgeq]
    exact lintegral_indicator_one hWs
  rw [hstep, hton, ← hunfold, hfinal]

end Work.Geometry
