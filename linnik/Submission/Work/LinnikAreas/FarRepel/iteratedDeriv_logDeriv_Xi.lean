import Mathlib
import Submission.Work.LinnikAreas.DhK.ZSBase
import Submission.Work.LinnikAreas.FarRepel.digammaDerivSeries

open Filter
open scoped Topology

namespace Work.LinnikAreas.FarRepel

/-- (in namespace `Work.LinnikAreas.FarRepel`; module `Submission.Work.LinnikAreas.FarRepel.iteratedDeriv_logDeriv_Xi`)

**Splitting the `k`-th derivative of `logDeriv Ξ`.**  `Ξ = 1/2 + (1/2)·s(s-1)·Λ₀(s)` (`Work.LinnikAreas.DhK.Xi`) is the entire completion of the Riemann zeta function.  For `k ≥ 1` and `1 < Re s`:

`(logDeriv Ξ)^(k)(s) = (-1)^k k! (1/s)^(k+1) + (-1)^k k! (1/(s-1))^(k+1) + (logDeriv Gammaℝ)^(k)(s) + (logDeriv ζ)^(k)(s)`.

PROOF ROUTE: `Work.LinnikAreas.DhK.Xi_logDeriv` gives `logDeriv Ξ =ᶠ[𝓝 s] fun z => 1/z + 1/(z-1) + logDeriv Complex.Gammaℝ z + logDeriv riemannZeta z` on `Re s > 1`; use `Filter.EventuallyEq.iteratedDeriv_eq`.  Then split the sum with `iteratedDeriv_add` (three times), which needs `ContDiffAt ℂ k _ s` for each summand — each of `z ↦ 1/z`, `z ↦ 1/(z-1)`, `logDeriv Complex.Gammaℝ`, `logDeriv riemannZeta` is analytic at `s` when `Re s > 1` (for the last two use that `Complex.Gammaℝ`, resp. `riemannZeta`, is analytic and non-vanishing near `s`, so that `logDeriv f = deriv f / f` is analytic there).  Finally `Work.LinnikAreas.FarRepel.iteratedDeriv_inv_add_const` (stated in the `digammaDerivSeries` module) gives `iteratedDeriv k (fun z => (z + c)⁻¹) s = (-1)^k k! (1/(s+c))^(k+1)`, applied with `c = 0` and `c = -1`; note `1/z = z⁻¹` and `1/(z-1) = (z + -1)⁻¹`. -/
theorem iteratedDeriv_logDeriv_Xi (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s
      = (-1 : ℂ) ^ k * (k.factorial : ℂ) * (1 / s) ^ (k + 1)
        + (-1 : ℂ) ^ k * (k.factorial : ℂ) * (1 / (s - 1)) ^ (k + 1)
        + iteratedDeriv k (logDeriv Complex.Gammaℝ) s
        + iteratedDeriv k (logDeriv riemannZeta) s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  -- `logDeriv Ξ` agrees near `s` with the explicit sum of the four log-derivatives
  have hev : logDeriv Work.LinnikAreas.DhK.Xi =ᶠ[𝓝 s] (fun z : ℂ => 1/z)
      + (fun z : ℂ => 1/(z-1)) + logDeriv Complex.Gammaℝ + logDeriv riemannZeta := by
    filter_upwards [Work.LinnikAreas.DhK.isOpen_re_gt_one.mem_nhds
      (show s ∈ {z : ℂ | 1 < z.re} from hs)] with z hz
    exact Work.LinnikAreas.DhK.Xi_logDeriv z hz
  rw [hev.iteratedDeriv_eq k]
  -- analyticity (hence `C^k`) of the four summands at `s`
  have h1 : ContDiffAt ℂ (k : ℕ) (fun z : ℂ => 1/z) s := by
    have h : ContDiffAt ℂ (k : ℕ) (fun z : ℂ => z⁻¹) s := (contDiffAt_id (x := s)).inv hs0
    simpa only [one_div] using h
  have h2 : ContDiffAt ℂ (k : ℕ) (fun z : ℂ => 1/(z-1)) s := by
    have hs1' : s - 1 ≠ 0 := by intro h; exact hs1 (sub_eq_zero.mp h)
    have h : ContDiffAt ℂ (k : ℕ) (fun z : ℂ => (z - 1)⁻¹) s :=
      (contDiffAt_id (x := s)).sub contDiffAt_const |>.inv hs1'
    simpa only [one_div] using h
  have h3 : ContDiffAt ℂ (k : ℕ) (logDeriv Complex.Gammaℝ) s := by
    have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    -- `Γℝ` is analytic at `s`, being the inverse of the entire function `Γℝ⁻¹`
    have hana : AnalyticAt ℂ Complex.Gammaℝ s := by
      have h1' : AnalyticAt ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) s :=
        Complex.differentiable_Gammaℝ_inv.analyticAt s
      have h2' : AnalyticAt ℂ (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) s :=
        h1'.inv (by simpa using hG)
      rwa [show (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) = Complex.Gammaℝ from
        funext fun s => inv_inv _] at h2'
    have hder : AnalyticAt ℂ (deriv Complex.Gammaℝ) s := hana.deriv
    have hdiv : AnalyticAt ℂ (deriv Complex.Gammaℝ / Complex.Gammaℝ) s := hder.div hana hG
    simpa only [logDeriv] using hdiv.contDiffAt
  have h4 : ContDiffAt ℂ (k : ℕ) (logDeriv riemannZeta) s := by
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    have hana : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using hs1)
    have hder : AnalyticAt ℂ (deriv riemannZeta) s := hana.deriv
    have hdiv : AnalyticAt ℂ (deriv riemannZeta / riemannZeta) s := hder.div hana hz
    simpa only [logDeriv] using hdiv.contDiffAt
  have h12 : ContDiffAt ℂ (k : ℕ) ((fun z : ℂ => 1/z) + (fun z : ℂ => 1/(z-1))) s := h1.add h2
  have h123 : ContDiffAt ℂ (k : ℕ)
      ((fun z : ℂ => 1/z) + (fun z : ℂ => 1/(z-1)) + logDeriv Complex.Gammaℝ) s := h12.add h3
  -- split the `k`-th derivative of the sum
  rw [iteratedDeriv_add h123 h4, iteratedDeriv_add h12 h3, iteratedDeriv_add h1 h2]
  -- the two rational summands
  have h1v : iteratedDeriv k (fun z : ℂ => 1/z) s
      = (-1 : ℂ)^k * (k.factorial : ℂ) * (1/s)^(k+1) := by
    have h := iteratedDeriv_inv_add_const k 0 s
    simpa only [one_div, add_zero] using h
  have h2v : iteratedDeriv k (fun z : ℂ => 1/(z-1)) s
      = (-1 : ℂ)^k * (k.factorial : ℂ) * (1/(s-1))^(k+1) := by
    have h := iteratedDeriv_inv_add_const k (-1) s
    simpa only [one_div, sub_eq_add_neg] using h
  rw [h1v, h2v]

end Work.LinnikAreas.FarRepel
