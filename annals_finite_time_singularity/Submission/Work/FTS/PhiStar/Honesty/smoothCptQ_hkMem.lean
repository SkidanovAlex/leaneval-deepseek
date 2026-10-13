/-
# `FTS/PhiStar/Honesty/smoothCptQ_hkMem` — a `C^∞` source supported in the open quadrant
lies in `ℋ^k`

The "honest-for-free" route of the `Honesty/` directory needs, for a source `G` which is
`C^∞` on all of `ℝ²` and whose support is a compact subset of the *open* quadrant
`Q0 = (0,∞) × (0,π/2)`, that `G` lies in the weighted space `ℋ^k` of the paper
(`Work.Spaces.HkMem α k G`) for **every** `k`, with no dependence on the small parameters.

The proof does not need any smallness of `α` (the weights are all bounded on the support
rectangle, for every `α ∈ ℝ`), and — crucially — it does *not* need `Work.Spaces.SmoothNbhd`
(analyticity on a neighbourhood of the closed quadrant): the `C^∞`-on-the-open-quadrant
hypothesis `Work.FTS.EllipticEst.SmoothOpen` is enough, because the integrand is dominated by
a *compactly supported constant*, and the domination is by `0` off the support box.

Route:

* `Work.FTS.PhiStar.Honesty.mixed_eq_zero_off_box`: off the support box (in either variable)
  every iterated mixed derivative of `G` vanishes — the complement of the closed box is open,
  so the slices are locally `0` and the totalised `deriv` vanishes;
* `Work.FTS.PhiStar.Honesty.hkIntegrand_bound_on_box`: `Work.Spaces.HkIntegrand α k G` is
  continuous on the open quadrant, hence bounded above on the compact support box;
* with the majorant `M z θ = 1_{[a,b]}(z) · C` (constant in `θ`, supported in the box), the
  three hypotheses of `Work.FTS.LocData.HkMem_of_majorant` are immediate.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptDefs
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.PhiStar.Honesty.mixed_eq_zero_off_box
import Submission.Work.FTS.PhiStar.Honesty.hkIntegrand_bound_on_box

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **Off the support box the `ℋ^k`-integrand vanishes.**  If all the iterated mixed
derivatives of `G` vanish off `Icc a b ×ˢ Icc c d`, then so does every summand of
`Work.Spaces.HkIntegrand α k G`, since each summand is a square of a mixed derivative
(`DzIter i G = mixed i 0 G`) times a weight. -/
theorem HkIntegrand_eq_zero_off_box {α : ℝ} {G : ℝ → ℝ → ℝ} {k : ℕ} {a b c d : ℝ}
    (hoff : ∀ j i : ℕ, ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) →
      Work.Spaces.mixed j i G z θ = 0) :
    ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) →
      Work.Spaces.HkIntegrand α k G z θ = 0 := by
  intro z θ hcond
  rw [Work.Spaces.HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i G z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      have h : Work.Spaces.DzIter i G z θ = 0 := hoff i 0 z θ hcond
      rw [h]; ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc, hoff j i z θ hcond]; ring
      · rw [if_neg hc]
  rw [h1, h2, add_zero]

/-- **A `C^∞` source compactly supported in the open quadrant belongs to `ℋ^k` for every
`k`.** -/
theorem smoothCptQ_hkMem {α : ℝ} {G : ℝ → ℝ → ℝ}
    (h : Work.FTS.PhiStar.Honesty.SmoothCptQ G) (k : ℕ) :
    Work.Spaces.HkMem α k G := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hsupp⟩ := h.cpt
  -- off the box every mixed derivative of `G` vanishes, hence so does the integrand
  have hoff := mixed_eq_zero_off_box hsupp
  have hzero := HkIntegrand_eq_zero_off_box (α := α) (k := k) (a := a) (b := b) (c := c)
    (d := d) hoff
  -- and on the box the integrand is bounded
  obtain ⟨C, hCnn, hCb⟩ := hkIntegrand_bound_on_box (α := α) (G := G) (k := k)
    h.smoothOpen ha (le_of_lt hab) hc (le_of_lt hcd) hd
  -- the majorant: the constant `C` on the `z`-box `[a,b]`, zero elsewhere
  refine Work.FTS.LocData.HkMem_of_majorant
    (M := fun z (_ : ℝ) => (Set.Icc a b).indicator (fun _ => C) z) α k
    (h.smoothOpen.continuousOn_HkIntegrand α k) ?_ ?_ ?_
  · -- the angular slices of the majorant are constant, and `Iθ` has finite measure
    intro z _
    exact MeasureTheory.integrableOn_const (ne_of_lt Work.Spaces.volume_Iθ_lt_top)
  · -- the `z`-integral of the majorant is the indicator of `[a,b]` times `C · (π/2)`
    have hEq : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Set.Icc a b).indicator (fun _ => C) z)
        = (Set.Icc a b).indicator (fun _ => (π / 2) * C) := by
      funext z
      by_cases hzab : z ∈ Set.Icc a b
      · rw [Set.indicator_of_mem hzab, Set.indicator_of_mem hzab,
          MeasureTheory.setIntegral_const, Work.Spaces.volume_real_Iθ, smul_eq_mul]
      · rw [Set.indicator_of_notMem hzab, Set.indicator_of_notMem hzab]
        simp
    rw [hEq]
    refine (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr ?_
    have hfin : (volume.restrict Work.Spaces.Iz) (Set.Icc a b) ≠ ⊤ := by
      rw [Measure.restrict_apply measurableSet_Icc]
      have h1 : volume (Set.Icc a b ∩ Work.Spaces.Iz) ≤ volume (Set.Icc a b) :=
        measure_mono Set.inter_subset_left
      have h2 : volume (Set.Icc a b) < ⊤ := by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
      exact ne_of_lt (lt_of_le_of_lt h1 h2)
    exact MeasureTheory.integrableOn_const hfin
  · -- the domination, pointwise on the closed quadrant
    intro z _ θ _
    by_cases hzab : z ∈ Set.Icc a b
    · by_cases hθcd : θ ∈ Set.Icc c d
      · rw [Set.indicator_of_mem hzab]
        exact hCb z θ hzab hθcd
      · rw [hzero z θ (Or.inr hθcd), Set.indicator_of_mem hzab]
        exact hCnn
    · rw [hzero z θ (Or.inl hzab), Set.indicator_of_notMem hzab]

end Work.FTS.PhiStar.Honesty
