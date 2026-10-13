import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE3.Taylor.Arc.complexify_order

namespace Work.WilE3.Taylor.Arc

open FormalMultilinearSeries Filter
open scoped Topology

/-- Restricting a function holomorphic at `0` to the real line preserves the order of vanishing at
`0`.  Concretely, if `F : ℂ → ℂ` is analytic at `0` then the order of vanishing of
`x ↦ F (x : ℂ)` at `0` (as a function `ℝ → ℂ`) equals the order of vanishing of `F` at `0`.

The proof compares the two orders with the order of a formal power series.  If `p` is the complex
power series of `F` at `0`, then the *same* coefficients, viewed as a formal power series over `ℝ`
with values in `ℂ`, are a power series for the real restriction; the two series vanish in exactly
the same degrees, hence have the same order. -/
theorem order_restrict (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) :
    analyticOrderAt (fun x : ℝ => F ((x : ℝ) : ℂ)) 0 = analyticOrderAt F 0 := by
  obtain ⟨p, hp⟩ := hF
  -- The complex power series of `F` at `0`, reinterpreted as a formal power series over `ℝ`.
  let q : FormalMultilinearSeries ℝ ℝ ℂ :=
    fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (p.coeff n)
  -- The two series have literally the same coefficients.
  have hqcoeff : ∀ n, q.coeff n = p.coeff n := by
    intro n
    simp only [FormalMultilinearSeries.coeff, q, ContinuousMultilinearMap.mkPiRing_apply,
      Pi.one_apply, Finset.prod_const_one, one_smul]
  -- Hence they vanish in exactly the same degrees.
  have hqzero : ∀ n, q n = 0 ↔ p n = 0 := by
    intro n
    rw [← FormalMultilinearSeries.coeff_eq_zero (p := q), hqcoeff n,
      FormalMultilinearSeries.coeff_eq_zero (p := p)]
  -- `q` is a power series for the real restriction of `F` at `0`.
  have hqe : ∀ᶠ x in (𝓝 (0 : ℝ) : Filter ℝ),
      HasSum (fun n => x ^ n • q.coeff n) (F ((x : ℝ) : ℂ)) := by
    have hpe : ∀ᶠ z in (𝓝 (0 : ℂ) : Filter ℂ),
        HasSum (fun n => z ^ n • p.coeff n) (F z) := by
      have h0 := hasFPowerSeriesAt_iff'.mp hp
      simpa using h0
    have h := (Complex.continuous_ofReal.continuousAt (x := 0)).eventually hpe
    exact h.mono (fun x hx => by
      have key : (fun n => ((x : ℂ)) ^ n • p.coeff n) = (fun n => x ^ n • q.coeff n) := by
        funext n
        rw [hqcoeff n, ← Complex.ofReal_pow, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
        rfl
      rwa [key] at hx)
  have hq : HasFPowerSeriesAt (fun x : ℝ => F ((x : ℝ) : ℂ)) q 0 :=
    hasFPowerSeriesAt_iff'.mpr (by simpa using hqe)
  -- The two formal power series have the same order.
  have horder : q.order = p.order := by
    have hset : {n : ℕ | q n ≠ 0} = {n : ℕ | p n ≠ 0} := by
      ext n; exact not_congr (hqzero n)
    simp only [FormalMultilinearSeries.order, hset]
  by_cases hp0 : p = 0
  · -- Both functions vanish identically near `0`, so both orders are infinite.
    have hq0 : q = 0 := funext fun n => (hqzero n).mpr (by rw [hp0]; rfl)
    rw [analyticOrderAt_eq_top_of_series_eq_zero hp hp0,
      analyticOrderAt_eq_top_of_series_eq_zero hq hq0]
  · -- Both series are nonzero, so both orders are the (finite) order of the series.
    have hqne : q ≠ 0 := fun n' => hp0 (funext fun n => (hqzero n).mp (by rw [n']; rfl))
    rw [analyticOrderAt_eq_order_coe hp hp0, analyticOrderAt_eq_order_coe hq hqne, horder]

end Work.WilE3.Taylor.Arc
