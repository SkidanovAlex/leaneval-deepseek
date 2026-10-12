import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.fsXpLogSmall`

`fsXp t c = t ^ (c / 323)` is a positive power of `t`, so as `t → 0⁺` it decays
polynomially; the factor `(1 + |log t|) ^ M` (the typical source of logarithmic
losses in the energy estimates) grows only logarithmically, hence slower than any
negative power of `t`.  Consequently the product tends to `0` and is therefore
dominated by any prescribed `K > 0` for all sufficiently small `t > 0`:

  `∃ ε₀ > 0, ∀ t ∈ (0, ε₀], fsXp t c * (1 + |log t|)^M ≤ K`.

The auxiliary lemma `one_add_abs_log_pow_le` records the quantitative form of
the logarithmic bound (`(1 + |log t|)^M = O(t^{-δ})` for `δ > 0`) used in the
assembly.
-/

namespace Work.BoseFixB1S

/-- `(1 + |log t|)^M` is dominated by `t ^ (-δ)` near `t = 0` (more precisely on
`(0, 1]`), for every `M ≥ 0` and every `δ > 0`.  This is the quantitative
"`log` is slower than any power" statement. -/
lemma one_add_abs_log_pow_le {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      (1 + |Real.log t|) ^ M ≤ C * t ^ (-δ) := by
  rcases eq_or_lt_of_le hM with hM0 | hMpos
  · -- `M = 0`: the left-hand side is `1` and `t ^ (-δ) ≥ 1` on `(0, 1]`.
    refine ⟨1, one_pos, fun t ht ht1 => ?_⟩
    rw [← hM0, Real.rpow_zero, one_mul, Real.rpow_neg ht.le δ]
    exact (one_le_inv₀ (Real.rpow_pos_of_pos ht δ)).2 (Real.rpow_le_one ht.le ht1 hδ.le)
  · -- `M > 0`: use `log u ≤ u ^ b / b` with `b = δ / M` and `u = t⁻¹`.
    set b : ℝ := δ / M with hb
    have hbpos : 0 < b := by rw [hb]; positivity
    have hbM : b * M = δ := by rw [hb]; exact div_mul_cancel₀ δ hMpos.ne'
    refine ⟨(1 + 1 / b) ^ M, Real.rpow_pos_of_pos (by positivity) M, fun t ht ht1 => ?_⟩
    have hs : |Real.log t| = Real.log t⁻¹ := by
      rw [abs_of_nonpos (Real.log_nonpos ht.le ht1), Real.log_inv]
    have h1 : 1 ≤ t⁻¹ := (one_le_inv₀ ht).2 ht1
    have hlog : Real.log t⁻¹ ≤ t ^ (-b) / b := by
      have h := Real.log_le_rpow_div (x := t⁻¹) (ε := b) (inv_nonneg.mpr ht.le) hbpos
      rwa [← Real.rpow_neg_eq_inv_rpow t b] at h
    have htbp : 1 ≤ t ^ (-b) := by
      rw [Real.rpow_neg_eq_inv_rpow]
      exact Real.one_le_rpow h1 hbpos.le
    have h2 : 1 + Real.log t⁻¹ ≤ t ^ (-b) * (1 + 1 / b) := by
      have h3 : 1 + t ^ (-b) / b ≤ t ^ (-b) * (1 + 1 / b) := by
        have heq : t ^ (-b) * (1 + 1 / b) = t ^ (-b) + t ^ (-b) / b := by ring
        linarith
      linarith
    have hb0 : 0 ≤ 1 + Real.log t⁻¹ := by
      have := Real.log_nonneg h1
      linarith
    have h4 : (1 + |Real.log t|) ^ M ≤ (t ^ (-b) * (1 + 1 / b)) ^ M := by
      rw [hs]
      exact Real.rpow_le_rpow hb0 h2 hM
    have h5 : (t ^ (-b) * (1 + 1 / b)) ^ M = t ^ (-δ) * (1 + 1 / b) ^ M := by
      rw [Real.mul_rpow (Real.rpow_nonneg ht.le (-b)) (by positivity : (0:ℝ) ≤ 1 + 1 / b),
          ← Real.rpow_mul ht.le (-b) M, neg_mul, hbM]
    calc (1 + |Real.log t|) ^ M ≤ (t ^ (-b) * (1 + 1 / b)) ^ M := h4
      _ = t ^ (-δ) * (1 + 1 / b) ^ M := h5
      _ = (1 + 1 / b) ^ M * t ^ (-δ) := by ring

theorem fsXpLogSmall {c M K : ℝ} (hK : 0 < K) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ t : ℝ, 0 < t → t ≤ ε₀ →
      Work.BoseBox.fsXp t c * (1 + |Real.log t|) ^ M ≤ K := by
  set a : ℝ := c / 323 with ha_def
  have ha : 0 < a := by rw [ha_def]; positivity
  have ha2 : 0 < a / 2 := by linarith
  -- the logarithmic factor is dominated by `t ^ (-(a/2))`
  obtain ⟨C, hCpos, hC⟩ := one_add_abs_log_pow_le (M := M) (δ := a / 2) hM ha2
  have hKCpos : 0 < K / C := div_pos hK hCpos
  refine ⟨min 1 ((K / C) ^ (2 / a)),
    lt_min one_pos (Real.rpow_pos_of_pos hKCpos (2 / a)), fun t ht htle => ?_⟩
  have ht1 : t ≤ 1 := htle.trans (min_le_left _ _)
  have htKC : t ≤ (K / C) ^ (2 / a) := htle.trans (min_le_right _ _)
  -- `t ^ (a/2) ≤ K / C` for `t` below the threshold
  have hstep : t ^ (a / 2) ≤ K / C := by
    have h1 : t ^ (a / 2) ≤ ((K / C) ^ (2 / a)) ^ (a / 2) :=
      Real.rpow_le_rpow ht.le htKC ha2.le
    have h2 : ((K / C) ^ (2 / a)) ^ (a / 2) = K / C := by
      rw [← Real.rpow_mul hKCpos.le (2 / a) (a / 2)]
      have h : 2 / a * (a / 2) = 1 := by field_simp
      rw [h, Real.rpow_one]
    rw [h2] at h1
    exact h1
  have hXY : t ^ a * t ^ (-(a / 2)) = t ^ (a / 2) := by
    rw [← Real.rpow_add ht a (-(a / 2))]
    congr 1
    ring
  calc Work.BoseBox.fsXp t c * (1 + |Real.log t|) ^ M
      = t ^ a * (1 + |Real.log t|) ^ M := by simp [Work.BoseBox.fsXp, ha_def]
    _ ≤ t ^ a * (C * t ^ (-(a / 2))) :=
        mul_le_mul_of_nonneg_left (hC t ht ht1) (Real.rpow_nonneg ht.le a)
    _ = C * t ^ (a / 2) := by
        rw [← hXY]; ring
    _ ≤ C * (K / C) := mul_le_mul_of_nonneg_left hstep hCpos.le
    _ = K := mul_div_cancel₀ K hCpos.ne'

end Work.BoseFixB1S
