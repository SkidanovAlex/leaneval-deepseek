import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_ang_le
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


/-- **A pointwise bound on the constituents of `CoefTh 1 f`.**  Any `mixed b i (∂_θ f)` with
`b + i ≤ 1` is bounded on the open quadrant by `CoefTh 1 f` itself.  (`CoefThMem 1 f` is
needed only to know that the relevant `supAbsO` is not the junk value `0`.) -/
theorem t2SupF_pth_le_coefTh {α : ℝ} {f : Fn} (hsf : T2SF α f) {b i : ℕ} (hbi : b + i ≤ 1)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ1 : θ < π / 2) :
    |Work.Spaces.mixed b i (Work.Spaces.pth f) z θ| ≤ Work.FTS.VocabO.CoefTh 1 f := by
  obtain ⟨K, hK⟩ := hsf.coef b i hbi
  have h1 : |Work.Spaces.mixed b i (Work.Spaces.pth f) z θ|
      ≤ Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) :=
    Work.FTS.H2.le_supAbsO hz hθ hθ1
      (fun z' θ' hz' hθ' hθ'1 => hK z' θ' hz' hθ' hθ'1)
  exact le_trans h1 (supAbsO_le_coefTh (f := f) hbi)





/-! ## Weighted slot comparisons (ingredients of the angular total-variation device)

The two pointwise bounds below (Step 4 of the plan in `NOTES_t2SupF.md`) upgrade the pure-`z` and
the mixed `ℋ⁴`-slot summands to a general angular weight `sin(2θ)^{-c}`, which is what the angular
device `Work.FTS.TransportS.TvUniform.tv_uniform_bound` consumes. -/


/-- The mixed slot with a general angular weight: for `c ≤ γ`,
`(mixed j i f z θ)² · w(z)² · sin(2θ)^{-c} ≤ HkIntegrand α 4 f z θ`. -/
theorem mixed_sq_w_rpow_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ c : ℝ}
    (hsin : 0 < Real.sin (2 * θ)) (hc : c ≤ Work.Spaces.gam α) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 4) :
    (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-c) ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have h1 : (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij
    have h2 : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      have hw : Work.Spaces.Wt α z θ
          = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
      have hs2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
          = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [sq, ← Real.rpow_add hsin,
          show -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2)
            = -(Work.Spaces.gam α) by ring]
      rw [hw, mul_pow, mul_pow, hs2]
      ring
    rwa [h2] at h
  have h3 : (Real.sin (2 * θ)) ^ (-c) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    have hs1 : Real.sin (2 * θ) ^ Work.Spaces.gam α ≤ Real.sin (2 * θ) ^ c :=
      Real.rpow_le_rpow_of_exponent_ge hsin (Real.sin_le_one (2 * θ)) hc
    rw [Real.rpow_neg (le_of_lt hsin) c, Real.rpow_neg (le_of_lt hsin) (Work.Spaces.gam α),
      ← one_div, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hsin (Work.Spaces.gam α)) hs1
  calc (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-c)
      ≤ (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := h1


end Work.FTS.TransportS
