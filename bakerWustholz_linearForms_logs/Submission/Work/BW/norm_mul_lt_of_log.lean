import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Combinatorial core: if `log N + log c < b + X` and `log Lam ≤ −X` with `N, c, Lam > 0`,
then `N · c · Lam < exp b`. Obtained by exponentiating: `N·c < exp(b+X) = exp b · exp X` and
`Lam ≤ exp(−X)`. -/
lemma log_transfer {N c Lam b X : ℝ} (hN : 0 < N) (hc : 0 < c) (hLam : 0 < Lam)
    (h1 : Real.log N + Real.log c < b + X) (h2 : Real.log Lam ≤ -X) :
    N * c * Lam < Real.exp b := by
  have hA : 0 < N * c := mul_pos hN hc
  have hexpb : 0 < Real.exp b := Real.exp_pos b
  have hX : 0 < Real.exp X := Real.exp_pos X
  have h3 : Real.log (N * c) < Real.log (Real.exp (b + X)) := by
    rw [Real.log_exp, Real.log_mul (ne_of_gt hN) (ne_of_gt hc)]
    exact h1
  have h4 : N * c < Real.exp b * Real.exp X := by
    have h := (Real.log_lt_log_iff hA (Real.exp_pos (b + X))).mp h3
    rwa [Real.exp_add] at h
  have h5 : Lam ≤ Real.exp (-X) := by
    have h := Real.exp_le_exp.mpr h2
    rwa [Real.exp_log hLam] at h
  have h6 : N * c * Lam < Real.exp b * Real.exp X * Real.exp (-X) :=
    mul_lt_mul h4 h5 hLam (le_of_lt (mul_pos hexpb hX))
  have hE : Real.exp b * Real.exp X * Real.exp (-X) = Real.exp b := by
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rwa [hE] at h6

/-- If `log N + log(2 ξ^{-rI} S) < log π + v log 2 + 9·2^r S D` and `log λ ≤ −9·2^r S D`, then
`N · 2^{−v} · λ < π/𝒮` where `𝒮 = calS r d h = 2 ξ^{-rI} S`, `S = pS r d h`, `D = pD r d σ`,
`ξ = pxi r`, `I = pI r d`. This is the exp/log transfer of BW §21 (the output of `h10_log_bound`
plus hypothesis (10) gives the `hΛ` input of `multiplicity_prop`).
*Proof:* `λ ≤ exp(−X)` with `X = 9·2^r S D`; `log(N·2^{−v}·exp(−X)) = log N − v log2 − X <
log π − log 𝒮 = log(π/𝒮)` using the hypothesis (`Real.log_mul`, `Real.log_inv`,
`Real.log_pow`, `Real.log_exp`), then `Real.exp_lt_exp` (all quantities positive: `ξ > 0` for
`r ≥ 2`, `S > 0`, `N > 0`, `λ > 0`). -/
theorem norm_mul_lt_of_log {d h r v : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h)
    (σ : Fin r → ℝ) (N Lam : ℝ) (hN : 0 < N) (hLam : 0 < Lam)
    (hlog : Real.log N + Real.log (2 * pxi r ^ (-((r * pI r d : ℕ) : ℤ)) * (pS r d h : ℝ)) <
        Real.log Real.pi + (v : ℝ) * Real.log 2 + 9 * 2 ^ r * (pS r d h : ℝ) * pD r d σ)
    (h10 : Real.log Lam ≤ -(9 * 2 ^ r * (pS r d h : ℝ) * pD r d σ)) :
    N * ((2 : ℝ) ^ v)⁻¹ * Lam < Real.pi / calS r d h := by
  -- unfold `calS` so that the hypothesis and the goal refer to the same expression
  change N * ((2 : ℝ) ^ v)⁻¹ * Lam <
    Real.pi / (2 * pxi r ^ (-((r * pI r d : ℕ) : ℤ)) * (pS r d h : ℝ))
  set e : ℝ := 2 * pxi r ^ (-((r * pI r d : ℕ) : ℤ)) * (pS r d h : ℝ) with he
  have hr0 : 0 < r := by omega
  have hd0 : 0 < d := by omega
  have hh0 : 0 < h := by omega
  have hSpos : (0 : ℝ) < (pS r d h : ℝ) := by
    rw [pS]; positivity
  have hxi : 0 < pxi r := by
    rw [pxi]
    have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have hle : (0.536 : ℝ) / r ≤ 0.536 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hr2
    have h2 : (0.536 : ℝ) / 2 < 1 := by norm_num
    linarith
  have hcpos : 0 < e := by rw [he]; positivity
  have key := log_transfer hN hcpos hLam hlog h10
  have hexpb : Real.exp (Real.log Real.pi + (v : ℝ) * Real.log 2) = Real.pi * (2 : ℝ) ^ v := by
    rw [Real.exp_add, Real.exp_log Real.pi_pos]
    congr 1
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [hexpb] at key
  have h2vpos : (0 : ℝ) < (2 : ℝ) ^ v := by positivity
  rw [lt_div_iff₀ hcpos]
  have h := mul_lt_mul_of_pos_right key (inv_pos.mpr h2vpos)
  have hrhs : (Real.pi * (2 : ℝ) ^ v) * ((2 : ℝ) ^ v)⁻¹ = Real.pi := by
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt h2vpos), mul_one]
  rw [hrhs] at h
  rwa [show (N * e * Lam) * ((2 : ℝ) ^ v)⁻¹ = N * ((2 : ℝ) ^ v)⁻¹ * Lam * e by ring] at h

end Work.BW
