import Mathlib

namespace Work.LinnikAreas

open scoped Topology

/-!
# The orders of `Λ = completedRiemannZeta` at its two poles

The completed Riemann zeta function satisfies
`Λ(s) = Λ₀(s) - 1/s - 1/(1-s)` with `Λ₀ = completedRiemannZeta₀` entire.  Hence near `s = 1`
(resp. `s = 0`) the function `Λ` differs from the simple pole `1/(s-1)` (resp. `-1/s`) by a
function whose order at that point is `≥ 0`, which is strictly larger than `-1`.  This gives
`meromorphicOrderAt Λ 1 = -1` and `meromorphicOrderAt Λ 0 = -1`.
-/

/-- If `f` agrees, in a punctured neighbourhood of `x`, with `g z * (z-x)^{-1}` where `g` is
analytic at `x` with `g x ≠ 0`, then `f` has a simple pole at `x`: its meromorphic order is
`-1`. -/
private lemma meromorphicOrderAt_eq_neg_one_of_eventuallyEq {f g : ℂ → ℂ} {x : ℂ}
    (hg : AnalyticAt ℂ g x) (hgx : g x ≠ 0)
    (h : f =ᶠ[𝓝[≠] x] fun z => g z * (z - x) ^ (-1 : ℤ)) :
    meromorphicOrderAt f x = -1 := by
  have h' : f =ᶠ[𝓝[≠] x] g • fun z : ℂ => (z - x) ^ (-1 : ℤ) := by
    filter_upwards [h] with z hz
    simpa [Pi.smul_apply] using hz
  rw [meromorphicOrderAt_congr h', meromorphicOrderAt_smul_of_ne_zero hg hgx]
  exact meromorphicOrderAt_zpow_id_sub_const

/-- `Λ` equals the simple pole `((z-1)(Λ₀ z - 1/z) + 1)/(z-1)` away from `z = 1`; the numerator
extends analytically to `z = 1` with value `1 ≠ 0`. -/
private lemma completedRiemannZeta_eq_at_one (z : ℂ) (hz : z ≠ 1) :
    completedRiemannZeta z = ((z - 1) * (completedRiemannZeta₀ z - 1 / z) + 1) / (z - 1) := by
  rw [completedRiemannZeta_eq]
  rw [show (1:ℂ)/(1-z) = -(1/(z-1)) by
    rw [show (1:ℂ) - z = -(z-1) by ring, div_neg]]
  have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  rw [sub_neg_eq_add, add_div, mul_div_cancel_left₀ _ hz']

/-- `Λ` equals `(z Λ₀ z - 1 - z/(1-z))/z` away from `z = 0`; the numerator extends
analytically to `z = 0` with value `-1 ≠ 0`. -/
private lemma completedRiemannZeta_eq_at_zero (z : ℂ) (hz : z ≠ 0) :
    completedRiemannZeta z = (z * completedRiemannZeta₀ z - 1 - z/(1-z)) / z := by
  have h : z * completedRiemannZeta z = z * completedRiemannZeta₀ z - 1 - z/(1-z) := by
    rw [completedRiemannZeta_eq]
    rw [mul_sub, mul_sub, mul_one_div, mul_one_div, div_self hz]
  exact (eq_div_iff hz).2 (by rw [mul_comm]; exact h)

private lemma analyticAt_aux_one :
    AnalyticAt ℂ (fun z : ℂ => (z - 1) * (completedRiemannZeta₀ z - 1 / z) + 1) 1 := by
  have hΛ₀ : AnalyticAt ℂ completedRiemannZeta₀ 1 := differentiable_completedZeta₀.analyticAt 1
  fun_prop (disch := norm_num)

private lemma analyticAt_aux_zero :
    AnalyticAt ℂ (fun z : ℂ => z * completedRiemannZeta₀ z - 1 - z / (1 - z)) 0 := by
  have hΛ₀ : AnalyticAt ℂ completedRiemannZeta₀ 0 := differentiable_completedZeta₀.analyticAt 0
  fun_prop (disch := norm_num)

/-- The completed Riemann zeta function `Λ = completedRiemannZeta` has simple poles at `0` and
`1`: both meromorphic orders are `-1`. -/
theorem completedRiemannZeta_orderAt_zero_one :
    meromorphicOrderAt completedRiemannZeta 1 = (-1 : ℤ) ∧
    meromorphicOrderAt completedRiemannZeta 0 = (-1 : ℤ) := by
  constructor
  · have hgx : (fun z : ℂ => (z - 1) * (completedRiemannZeta₀ z - 1 / z) + 1) 1 ≠ 0 := by
      norm_num
    have hev : completedRiemannZeta =ᶠ[𝓝[≠] (1:ℂ)]
        fun z => ((z - 1) * (completedRiemannZeta₀ z - 1 / z) + 1) * (z - 1) ^ (-1 : ℤ) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [completedRiemannZeta_eq_at_one z hz]
      rw [zpow_neg_one, div_eq_mul_inv]
    exact meromorphicOrderAt_eq_neg_one_of_eventuallyEq analyticAt_aux_one hgx hev
  · have hgx : (fun z : ℂ => z * completedRiemannZeta₀ z - 1 - z / (1 - z)) 0 ≠ 0 := by
      norm_num
    have hev : completedRiemannZeta =ᶠ[𝓝[≠] (0:ℂ)]
        fun z => (z * completedRiemannZeta₀ z - 1 - z / (1 - z)) * (z - 0) ^ (-1 : ℤ) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [completedRiemannZeta_eq_at_zero z hz]
      rw [zpow_neg_one, div_eq_mul_inv]
      simp
    exact meromorphicOrderAt_eq_neg_one_of_eventuallyEq analyticAt_aux_zero hgx hev

end Work.LinnikAreas
