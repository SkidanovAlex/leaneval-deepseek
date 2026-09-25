import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# The finite multiplicity sum bound for the zeros of `ζ₁`

This module provides the *farLeft*-side form of the bound on the multiplicity weighted zero sum

`∑_{ρ ∈ S} m_ρ / ‖ρ‖² ≤ 2 + γ − log (4π)`   (`m_ρ = zeta1Order ρ`),

for a finite set `S` of zeros of `ζ₁` lying in the open critical strip with `‖ρ‖ ≤ R`.

The farLeft corpus module `Commons.NumberTheory.Zeta.zeroSum_finset_le_beta` states this bound
with the weight `d_R(ρ)/‖ρ‖²` given by the **divisor of the completed ξ-function** rather than
`zeta1Order`.  The two weights agree at a zero `ρ` of `ζ₁` in the strip: this is
`zeta1Order_eq_xi_divisor`, an immediate consequence of
`Commons.NumberTheory.Zeta.divisor_xi_eq_logDeriv_pole_order` and the definition of
`zeta1Order` as the multiplicity produced by `zeta1_logDeriv_pole_removal`.

The companion fact `re_eq_half_of_riemannZeta1_eq_zero` (RH puts every non-trivial zero of
`ζ₁` on the critical line) is proved here as well, since it is needed by the tilted-sum bound.
-/

open scoped BigOperators

namespace Work.RHContract.A

/-- **RH puts non-trivial zeros of `ζ₁` on the critical line.**  A zero of `ζ₁` which is not one
of the trivial zeros `-2(n+1)` is a non-trivial zero of `ζ`, hence (under RH) has real part
`1/2`. -/
theorem re_eq_half_of_riemannZeta1_eq_zero (h : RiemannHypothesis) {ρ : ℂ}
    (hρ : riemannZeta₁ ρ = 0) (hnt : ¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) : ρ.re = 1 / 2 := by
  have hρne1 : ρ ≠ 1 := by
    intro hh
    rw [hh, riemannZeta₁_one] at hρ
    exact one_ne_zero hρ
  have hz : riemannZeta ρ = 0 := by
    rw [riemannZeta_eq_inv_sub_mul hρne1, hρ, mul_zero]
  exact h ρ hz hnt hρne1

/-- **`zeta1Order` is the divisor of the ξ-function.**  At a zero `ρ` of `ζ₁` in the open
critical strip with `‖ρ‖ ≤ R`, the multiplicity `zeta1Order ρ` agrees with the order of
vanishing of the completed ξ-function `1/2 + (1/2) s (s-1) Λ₀(s)` on the closed ball of radius
`R`. -/
theorem zeta1Order_eq_xi_divisor {R : ℝ} (hR : 0 ≤ R) {ρ : ℂ} (hρ : riemannZeta₁ ρ = 0)
    (hρR : ‖ρ‖ ≤ R) (hre : (1 / 4 : ℝ) < ρ.re) (hre2 : ρ.re < 2) :
    (Commons.NumberTheory.Zeta.zeta1Order ρ : ℤ) =
      (MeromorphicOn.divisor (fun z : ℂ =>
        (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
        (Metric.closedBall 0 R)) ρ := by
  rw [Commons.NumberTheory.Zeta.zeta1Order, dif_pos hρ]
  obtain ⟨hm1, F, hFa, hFev⟩ :=
    Classical.choose_spec (Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal ρ hρ)
  exact Commons.NumberTheory.Zeta.divisor_xi_eq_logDeriv_pole_order hR hρ hρR hre hre2 hm1
    ⟨F, hFa, hFev⟩

/-- **The finite multiplicity sum bound.**  Under RH, for every finite set `S` of zeros of `ζ₁`
in the open critical strip with `‖ρ‖ ≤ R`,

`∑_{ρ ∈ S} m_ρ / ‖ρ‖² ≤ 2 + γ − log (4π)`,

where `m_ρ = zeta1Order ρ`.  This is `zeroSum_finset_le_beta` with the divisor weight replaced by
the multiplicity (`zeta1Order_eq_xi_divisor`). -/
theorem zeroSum_finset_multiplicity_le (h : RiemannHypothesis) (R : ℝ) (hR : 0 ≤ R)
    (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, riemannZeta₁ ρ = 0 ∧ ‖ρ‖ ≤ R ∧ (1 / 4 : ℝ) < ρ.re ∧ ρ.re < 2) :
    S.sum (fun ρ => (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)
      ≤ 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  have hb := Commons.NumberTheory.Zeta.zeroSum_finset_le_beta h R hR S hS
  refine le_trans (Finset.sum_le_sum (fun ρ hρ => ?_)) hb
  obtain ⟨hz, hlt, hre1, hre2⟩ := hS ρ hρ
  have hD := zeta1Order_eq_xi_divisor hR hz hlt hre1 hre2
  rw [← Int.cast_natCast, hD]

end Work.RHContract.A
