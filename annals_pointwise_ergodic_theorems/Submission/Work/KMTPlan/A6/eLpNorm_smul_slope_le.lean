import Mathlib
import Submission.Work.KMTPlan.A6.FkrBasic

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal

lemma eLpNorm_smul_slope_le {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    {r R : ℝ} (hR : 1 ≤ R) {K : ℕ} {β : ℕ → ℝ} (bK : ℝ) (hbK : 0 < bK)
    (w : ℕ → X → ℂ) (g : ℕ → X → ℂ)
    (hdens : ∀ k ∈ Finset.Icc 1 K, ∀ x,
        w k x * ((β k - β (k - 1) : ℝ) : ℂ) = g k x - g (k - 1) x)
    (hho : ∀ p q, p ≤ q → q ≤ K →
        MeasureTheory.eLpNorm (fun x => g q x - g p x) (ENNReal.ofReal r) μ
          ≤ ENNReal.ofReal ((bK * (β q - β p)) ^ (1 / R)))
    {k : ℕ} (hk : k ∈ Finset.Icc 1 K) (hkpos : β (k - 1) < β k)
    {c : ℝ} (hc0 : 0 ≤ c) (hcC : c ≤ β k - β (k - 1)) :
    MeasureTheory.eLpNorm (fun x => ((c : ℝ) : ℂ) * w k x) (ENNReal.ofReal r) μ
      ≤ ENNReal.ofReal (bK ^ (1 / R) * c ^ (1 / R)) := by
  have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
  have hdpos : 0 < β k - β (k - 1) := sub_pos.mpr hkpos
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRinvpos : 0 < 1 / R := one_div_pos.mpr hRpos
  have hRinvle : 1 / R ≤ 1 := by
    rw [one_div]; exact inv_le_one_of_one_le₀ hR
  have hcd : 0 ≤ c / (β k - β (k - 1)) := div_nonneg hc0 hdpos.le
  -- The equations `w k x * (β k - β (k-1)) = g k x - g (k-1) x` exhibit `w k` as the
  -- slope of `g` on the `k`-th block; multiplying by `c` is the same as multiplying
  -- `g k - g (k-1)` by the scalar `c / (β k - β (k-1))`.
  have hpt : ∀ x, ((c : ℝ) : ℂ) * w k x
      = (((c / (β k - β (k - 1)) : ℝ)) : ℂ) * (g k x - g (k - 1) x) := by
    intro x
    have hcdd : (((c / (β k - β (k - 1)) : ℝ)) : ℂ) * (((β k - β (k - 1) : ℝ)) : ℂ)
        = ((c : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, div_mul_cancel₀ c hdpos.ne']
    calc ((c : ℝ) : ℂ) * w k x
        = ((((c / (β k - β (k - 1)) : ℝ)) : ℂ)
            * (((β k - β (k - 1) : ℝ)) : ℂ)) * w k x := by rw [hcdd]
      _ = (((c / (β k - β (k - 1)) : ℝ)) : ℂ)
            * (w k x * (((β k - β (k - 1) : ℝ)) : ℂ)) := by ring
      _ = (((c / (β k - β (k - 1)) : ℝ)) : ℂ) * (g k x - g (k - 1) x) := by
            rw [hdens k hk x]
  have hsmul : (fun x => ((c : ℝ) : ℂ) * w k x)
      = (((c / (β k - β (k - 1)) : ℝ)) : ℂ) • (fun x => g k x - g (k - 1) x) := by
    funext x
    rw [hpt x]
    rfl
  have hnorm : ‖((((c / (β k - β (k - 1)) : ℝ))) : ℂ)‖ₑ
      = ENNReal.ofReal (c / (β k - β (k - 1))) := by
    have h1 : ‖((((c / (β k - β (k - 1)) : ℝ))) : ℂ)‖ = c / (β k - β (k - 1)) := by
      rw [show ‖((((c / (β k - β (k - 1)) : ℝ))) : ℂ)‖
            = |(c / (β k - β (k - 1)) : ℝ)| from
            by simpa using RCLike.norm_ofReal (K := ℂ) (c / (β k - β (k - 1))),
          abs_of_nonneg hcd]
    rw [← ofReal_norm, h1]
  -- the scalar arithmetic: with `d = β k - β (k-1) > 0` and `0 ≤ c ≤ d`,
  -- `(c/d) * (bK * d)^{1/R} ≤ bK^{1/R} * c^{1/R}` (the exponent `1/R ≤ 1` is what
  -- makes the "small slope" gain work).
  have hreal : (c / (β k - β (k - 1))) * (bK * (β k - β (k - 1))) ^ (1 / R)
      ≤ bK ^ (1 / R) * c ^ (1 / R) := by
    have hstep : c * (β k - β (k - 1)) ^ (1 / R - 1) ≤ c ^ (1 / R) := by
      rcases eq_or_lt_of_le hc0 with h0 | hlt
      · obtain rfl : c = 0 := h0.symm
        rw [zero_mul, Real.zero_rpow hRinvpos.ne']
      · have hmono : (β k - β (k - 1)) ^ (1 / R - 1) ≤ c ^ (1 / R - 1) :=
          Real.rpow_le_rpow_of_nonpos hlt hcC (by linarith)
        calc c * (β k - β (k - 1)) ^ (1 / R - 1)
            ≤ c * c ^ (1 / R - 1) := mul_le_mul_of_nonneg_left hmono hlt.le
          _ = c ^ (1 + (1 / R - 1)) := by rw [Real.rpow_add hlt, Real.rpow_one]
          _ = c ^ (1 / R) := by congr 1; ring
    have hdecomp : (c / (β k - β (k - 1))) * (β k - β (k - 1)) ^ (1 / R)
        = c * (β k - β (k - 1)) ^ (1 / R - 1) := by
      rw [Real.rpow_sub hdpos, Real.rpow_one]
      ring
    rw [Real.mul_rpow hbK.le hdpos.le]
    calc (c / (β k - β (k - 1))) * (bK ^ (1 / R) * (β k - β (k - 1)) ^ (1 / R))
        = bK ^ (1 / R) * ((c / (β k - β (k - 1))) * (β k - β (k - 1)) ^ (1 / R)) := by ring
      _ = bK ^ (1 / R) * (c * (β k - β (k - 1)) ^ (1 / R - 1)) := by rw [hdecomp]
      _ ≤ bK ^ (1 / R) * c ^ (1 / R) :=
          mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hbK.le _)
  calc MeasureTheory.eLpNorm (fun x => ((c : ℝ) : ℂ) * w k x) (ENNReal.ofReal r) μ
      ≤ ‖((((c / (β k - β (k - 1)) : ℝ))) : ℂ)‖ₑ
          * ENNReal.ofReal ((bK * (β k - β (k - 1))) ^ (1 / R)) := by
        rw [hsmul, eLpNorm_const_smul]
        exact mul_le_mul_of_nonneg_left (hho (k - 1) k (Nat.sub_le k 1) hkK) (by positivity)
    _ = ENNReal.ofReal (c / (β k - β (k - 1)))
          * ENNReal.ofReal ((bK * (β k - β (k - 1))) ^ (1 / R)) := by rw [hnorm]
    _ = ENNReal.ofReal ((c / (β k - β (k - 1))) * (bK * (β k - β (k - 1))) ^ (1 / R)) :=
        (ENNReal.ofReal_mul hcd).symm
    _ ≤ ENNReal.ofReal (bK ^ (1 / R) * c ^ (1 / R)) := ENNReal.ofReal_le_ofReal hreal

end Work.KMTPlan.A6
