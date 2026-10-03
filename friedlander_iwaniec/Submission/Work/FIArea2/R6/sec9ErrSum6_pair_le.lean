import Mathlib
import Submission.Work.FIArea2.R6.Area6eDefs
import Submission.Work.FIArea2.R6.BetaPrim6
import Submission.Work.FIArea2.R6.Sec9Log6
import Submission.Work.FIArea2.Count.gnorm_prod_rpow_le

namespace Work.FIArea2.R6

open scoped BigOperators

/-- Elementary bookkeeping of the pair estimate (9.1): the three independent bounds
`G ≤ N'`, `L ≤ 4K`, `H ≤ 64U` multiply to `G·L·H ≤ 256·K·N'·U`, and the common non-negative
coefficient `X·C` carries the comparison to the target form `X·G·(C·L·H) ≤ 256·K·N'·(X·C·U)`.
No sign hypothesis is needed on `H` (the bound `H ≤ 64U` with `U ≥ 0` is used only through the
multipliers `G·L ≥ 0` and `N'`). -/
private lemma pair_core_le_aux (X G N' C L H U K : ℝ)
    (hX : 0 ≤ X) (hG0 : 0 ≤ G) (hN0 : 0 ≤ N') (hC0 : 0 ≤ C) (hL0 : 0 ≤ L)
    (hU0 : 0 ≤ U)
    (hG : G ≤ N') (hL : L ≤ 4 * K) (hH : H ≤ 64 * U) :
    X * G * (C * L * H) ≤ 256 * K * N' * (X * C * U) := by
  have h64U : 0 ≤ 64 * U := by linarith
  have hGL0 : 0 ≤ G * L := mul_nonneg hG0 hL0
  have hL64U : 0 ≤ L * (64 * U) := mul_nonneg hL0 h64U
  have hGLH : G * L * H ≤ G * L * (64 * U) := mul_le_mul_of_nonneg_left hH hGL0
  have hGLN' : G * L * (64 * U) ≤ N' * L * (64 * U) := by
    have h := mul_le_mul_of_nonneg_right hG hL64U
    linarith [h]
  have hN'L : N' * L ≤ N' * (4 * K) := mul_le_mul_of_nonneg_left hL hN0
  have hstep4 : N' * L * (64 * U) ≤ N' * (4 * K) * (64 * U) := by
    have h := mul_le_mul_of_nonneg_right hN'L h64U
    linarith [h]
  have hGLH4 : G * L * H ≤ 256 * K * N' * U := by
    have hb := le_trans hGLH (le_trans hGLN' hstep4)
    have heq : N' * (4 * K) * (64 * U) = 256 * K * N' * U := by ring
    linarith [hb, heq]
  have hXC0 : 0 ≤ X * C := mul_nonneg hX hC0
  have hfinal := mul_le_mul_of_nonneg_left hGLH4 hXC0
  linarith [hfinal]

/-- **The per-pair (9.1) estimate of §9 at the round-6 scale.**  For a pair of the box with
`(z₁,z₂) = 1`,

  `|β_{z₁}β_{z₂}|·|z₁z₂|^{-1/2}·τ(Δ)³|Δ|^{-1}·log(2+1/(1-γ²))·H(z₁,z₂)`
    `≤ 256(log N + 2)N^{-1/2}·|β_{z₁}β_{z₂}|·sec9Core6·H_{unif}(z₁,z₂)`,

i.e. the three elementary bounds of §9 concatenated: `|z₁z₂|^{-1/2} ≤ N^{-1/2}` (the polar-box
range), `log(2+1/(1-γ²)) ≤ 4(log N + 2)` (`sec9_log_bound6`) and `Haver ≤ 64·sec9Usum`
(`Haver_le_uniform`), with the pair weight identified with `sec9Core6` on the support. -/
theorem sec9ErrSum6_pair_le (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    ∀ z1 ∈ Work.FITop.boxN Pa, ∀ z2 ∈ Work.FITop.boxN Pa,
      Work.FIPlan.GaussCoprime z1 z2 →
      ‖β z1‖ * ‖β z2‖ * (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
        * ((((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
            / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
            * Work.FIArea2.Haver Pa z1 z2)
      ≤ (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2))
          * (‖β z1‖ * ‖β z2‖ * Work.FIArea2.R6.sec9Core6 Pa z1 z2
              * Work.FIArea2.sec9Usum Pa z1 z2) := by
  intro z1 _ z2 _ hcop
  by_cases hb1 : β z1 = 0
  · simp [hb1]
  by_cases hb2 : β z2 = 0
  · simp [hb2]
  obtain ⟨hn1, hn1'⟩ := Work.FIArea2.R6.IsBetaCoeff6.gnorm_bounds hβ hb1
  obtain ⟨hn2, hn2'⟩ := Work.FIArea2.R6.IsBetaCoeff6.gnorm_bounds hβ hb2
  have hG := Work.FIArea2.Count.gnorm_prod_rpow_le Pa z1 z2 hn1 hn2
  have hlog := Work.FIArea2.R6.sec9_log_bound6 Pa z1 z2 Pa.hN1 hn1 hn1' hn2 hn2'
      (Work.FIArea2.R6.theta_le_one6 Pa)
  have hH := Work.FIArea2.R6.IsBetaCoeff6.haver_le6 hβ hcop hb1 hb2
  have hcs := Work.FIArea2.R6.sec9Core6_eq_of Pa hcop
      (Work.FITop4.IsBetaCoeff6.isAxisFree hβ hb1)
      (Work.FITop4.IsBetaCoeff6.isAxisFree hβ hb2)
  obtain ⟨hg0, hg1⟩ := Work.FIArea2.R6.IsBetaCoeff6.gamOf_bounds6 hβ hcop hb1 hb2
  have hX : 0 ≤ ‖β z1‖ * ‖β z2‖ := by positivity
  have hG0 : 0 ≤ (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hNpos : 0 < Pa.N := by linarith [Pa.hN1]
  have hN0 : 0 ≤ Pa.N ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hNpos) _
  have hC0 : 0 ≤ (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3
      / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) := by
    rw [← hcs]; exact Work.FIArea2.R6.sec9Core6_nonneg Pa z1 z2
  have hL0 : 0 ≤ Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2)) := by
    apply Real.log_nonneg
    have h1 : (Work.FIArea2.gamOf z1 z2) ^ 2 < 1 := by nlinarith [hg0, hg1]
    have hpos : 0 < 1 - (Work.FIArea2.gamOf z1 z2) ^ 2 := by linarith
    have hdiv : 0 ≤ 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) := div_nonneg zero_le_one hpos.le
    linarith
  have hU0 : 0 ≤ Work.FIArea2.sec9Usum Pa z1 z2 := Work.FIArea2.sec9Usum_nonneg Pa z1 z2
  have key := pair_core_le_aux (‖β z1‖ * ‖β z2‖)
    (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
    (Pa.N ^ (-(1 : ℝ) / 2))
    (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3
      / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
    (Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2)))
    (Work.FIArea2.Haver Pa z1 z2)
    (Work.FIArea2.sec9Usum Pa z1 z2) (Real.log Pa.N + 2)
    hX hG0 hN0 hC0 hL0 hU0 hG hlog hH
  rw [hcs]
  exact key

end Work.FIArea2.R6
