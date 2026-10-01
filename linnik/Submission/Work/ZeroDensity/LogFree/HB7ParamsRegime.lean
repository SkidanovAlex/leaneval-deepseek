import Mathlib
import Submission.Work.ZeroDensity.LogFree.poleLSDefs

namespace Work.ZeroDensity.LogFree

/-! Scale-bookkeeping for the parameter packet `p : Params`.  For `𝓓 = scale q T = q(T+2)`
large enough (depending on `p` only), with `L = Lscale q T = log 𝓓`, `X = Dpow q T p.x = 𝓓^{p.x}`
and `U' = Dpow q T p.u / L^2`:

* `1 ≤ L`, `0 < X`, `1 ≤ U'`, `2 U' ≤ X`, and `log (X/U') ≤ (p.x - p.u + 2) * L`.

Uses `P1`, `P2` of `Params` only through `1/2 ≤ p.u` and `1/2 ≤ p.x - p.u` (both elementary
consequences), and `𝓓^c = exp (c * L)`, `L → ∞`, `exp` dominating `L²` (e.g.
`2 * L^2 ≤ exp (L/2)` for `L ≥ 1000`, from `Real.log_le_rpow_div`). -/
theorem HB7ParamsRegime (p : Work.ZeroDensity.LogFree.Params) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T : ℝ), 1 ≤ T →
      D₀ ≤ Work.ZeroDensity.LogFree.scale q T →
      1 ≤ Work.ZeroDensity.LogFree.Lscale q T ∧
      0 < Work.ZeroDensity.LogFree.Dpow q T p.x ∧
      1 ≤ Work.ZeroDensity.LogFree.Dpow q T p.u / (Work.ZeroDensity.LogFree.Lscale q T) ^ 2 ∧
      2 * (Work.ZeroDensity.LogFree.Dpow q T p.u / (Work.ZeroDensity.LogFree.Lscale q T) ^ 2)
        ≤ Work.ZeroDensity.LogFree.Dpow q T p.x ∧
      Real.log (Work.ZeroDensity.LogFree.Dpow q T p.x /
          (Work.ZeroDensity.LogFree.Dpow q T p.u / (Work.ZeroDensity.LogFree.Lscale q T) ^ 2))
        ≤ (p.x - p.u + 2) * Work.ZeroDensity.LogFree.Lscale q T := by
  refine ⟨(2 : ℝ) ^ 24, by norm_num, ?_⟩
  intro q hq _inst T hT hD
  simp only [Lscale, Dpow]
  set c : ℝ := scale q T with hcdef
  -- `c = 𝓓` is at least `2^24`, so in particular `0 < c`, `1 ≤ c`.
  have hcD : (2 : ℝ) ^ 24 ≤ c := hD
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hcD
  have hcone : 1 ≤ c := le_trans (by norm_num) hcD
  -- `1 ≤ L = log c`
  have hL1 : 1 ≤ Real.log c := by
    rw [Real.le_log_iff_exp_le hcpos]
    exact le_trans (le_of_lt Real.exp_one_lt_three) (le_trans (by norm_num) hcD)
  have hLpos : 0 < Real.log c := lt_of_lt_of_le one_pos hL1
  have hLsq_pos : 0 < (Real.log c) ^ 2 := pow_pos hLpos 2
  have hLsq_ge1 : 1 ≤ (Real.log c) ^ 2 := one_le_pow₀ hL1
  -- `(log c)^2 ≤ c^{1/2}`
  have hlogsq : (Real.log c) ^ 2 ≤ c ^ (1 / 2 : ℝ) := by
    have hlog_le : Real.log c ≤ 8 * c ^ (1 / 8 : ℝ) := by
      have h := Real.log_le_rpow_div (le_of_lt hcpos) (by norm_num : (0 : ℝ) < (1 / 8 : ℝ))
      have heq : c ^ (1 / 8 : ℝ) / (1 / 8 : ℝ) = 8 * c ^ (1 / 8 : ℝ) := by
        rw [div_eq_mul_inv, show ((1 : ℝ) / 8)⁻¹ = 8 by norm_num]
        ring
      linarith [h, heq]
    have hc8 : 8 ≤ c ^ (1 / 8 : ℝ) := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 24) hcD
        (by norm_num : (0 : ℝ) ≤ (1 / 8 : ℝ))
      norm_num at h
      exact h
    have hstep : Real.log c ≤ c ^ (1 / 4 : ℝ) := by
      have h2 : 8 * c ^ (1 / 8 : ℝ) ≤ c ^ (1 / 8 : ℝ) * c ^ (1 / 8 : ℝ) := by
        nlinarith [hc8, Real.rpow_nonneg (le_of_lt hcpos) (1 / 8 : ℝ)]
      have h3 : c ^ (1 / 8 : ℝ) * c ^ (1 / 8 : ℝ) = c ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_add hcpos]; norm_num
      linarith [hlog_le, h2, h3]
    have hlogpos : 0 ≤ Real.log c := le_of_lt hLpos
    have h4 := pow_le_pow_left₀ hlogpos hstep 2
    have h5 : (c ^ (1 / 4 : ℝ)) ^ 2 = c ^ (1 / 2 : ℝ) := by
      rw [pow_two, ← Real.rpow_add hcpos]; norm_num
    linarith [h4, h5]
  -- `1/2 ≤ p.u` and `1/2 ≤ p.x - p.u`, from `P1`, `P2`.
  have hu_half : 1 / 2 ≤ p.u := by
    have hu_pos : 0 < p.u := lt_trans p.hw p.hwu
    have h1 : p.u * (2 * p.σ₀ - 1) ≤ p.u := by
      refine mul_le_of_le_one_right (le_of_lt hu_pos) ?_
      linarith [p.hσ₀1]
    have h2 : 1 / 2 ≤ p.u * (2 * p.σ₀ - 1) := by
      have := p.P2
      linarith [this, p.hw, p.hη]
    linarith
  have hxu_half : 1 / 2 ≤ p.x - p.u := by
    have hxpos : 0 < p.x := lt_trans (lt_trans (lt_trans p.hw p.hwu) p.huv) p.hvx
    have h1 : p.x * p.σ₀ ≤ p.x := mul_le_of_le_one_right (le_of_lt hxpos) p.hσ₀1
    have h2 : 1 / 2 + p.v + p.w + 2 * p.η ≤ p.x := by
      have := p.P1
      linarith [this, h1]
    have h3 : p.u < p.v := p.huv
    have h4 : 1 / 2 + p.w + 2 * p.η ≤ p.x - p.u := by linarith
    linarith [h4, p.hw, p.hη]
  refine ⟨hL1, ?_, ?_, ?_, ?_⟩
  · exact Real.rpow_pos_of_pos hcpos _
  · rw [one_le_div hLsq_pos]
    exact le_trans hlogsq (Real.rpow_le_rpow_of_exponent_le hcone hu_half)
  · have hcu_pos : 0 < c ^ p.u := Real.rpow_pos_of_pos hcpos _
    have hstep1 : 2 * (c ^ p.u / (Real.log c) ^ 2) ≤ 2 * c ^ p.u := by
      have h : c ^ p.u / (Real.log c) ^ 2 ≤ c ^ p.u := by
        rw [div_le_iff₀ hLsq_pos]
        simpa using mul_le_mul_of_nonneg_left hLsq_ge1 (le_of_lt hcu_pos)
      linarith
    have hcxu_ge2 : 2 ≤ c ^ (p.x - p.u) := by
      have h1 : (2 : ℝ) ≤ c ^ (1 / 2 : ℝ) := by
        have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ (4 : ℝ))
          (le_trans (by norm_num : (4 : ℝ) ≤ (2 : ℝ) ^ 24) hcD)
          (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
        norm_num at h
        exact h
      exact le_trans h1 (Real.rpow_le_rpow_of_exponent_le hcone hxu_half)
    have hsplit : c ^ p.u * c ^ (p.x - p.u) = c ^ p.x := by
      rw [← Real.rpow_add hcpos]; congr 1; ring
    have hstep2 : 2 * c ^ p.u ≤ c ^ p.x := by
      rw [← hsplit]
      have := mul_le_mul_of_nonneg_left hcxu_ge2 (le_of_lt hcu_pos)
      linarith
    linarith
  · have hXpos : 0 < c ^ p.x := Real.rpow_pos_of_pos hcpos _
    have hcu_pos : 0 < c ^ p.u := Real.rpow_pos_of_pos hcpos _
    have hdivpos : 0 < c ^ p.u / (Real.log c) ^ 2 := div_pos hcu_pos hLsq_pos
    have hlogeq : Real.log (c ^ p.x / (c ^ p.u / (Real.log c) ^ 2))
        = (p.x - p.u) * Real.log c + 2 * Real.log (Real.log c) := by
      rw [Real.log_div (ne_of_gt hXpos) (ne_of_gt hdivpos)]
      rw [Real.log_div (ne_of_gt hcu_pos) (ne_of_gt hLsq_pos)]
      rw [Real.log_rpow hcpos p.x, Real.log_rpow hcpos p.u, Real.log_pow]
      ring
    rw [hlogeq]
    have := Real.log_le_self (le_of_lt hLpos)
    nlinarith

end Work.ZeroDensity.LogFree
