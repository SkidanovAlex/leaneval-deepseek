import Mathlib
import Submission.Work.A3.mArcKernel_lower

namespace Work.A3

/-- The arithmetic of the transition-arc estimate in the regime `|β| ≤ N^{-d}` (which includes `β = 0`, where the singular integral is of size `N`): the block-decomposition error `C₁ q^{1-δ}(3 L (N+q) + 6)` with `L = 2π |β| A d (N+q)^{d-1}` is dominated by `C' q^{-δ} mArcKernel N d β` with the explicit constant `C' = 100 * 2^{1/d} * 100^{1/d} * (C₁ * (2π A d 2^d + 1) + 1)`.  Proof ingredients: `mArcKernel ≥ 2^{-1/d} N` (`mArcKernel_lower`), `|β| N^d ≤ 1`, `q ≤ N`, and `N+q ≤ 2N`.  Note `q^{1-δ} = q · q^{-δ}` (as `q ≥ 1`), so `δ` only enters through positivity. -/
lemma transition_arith_case_small (C₁ A : ℝ) (hC₁ : 0 < C₁) (hA : 0 < A)
    (N q d : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) (hd : 2 ≤ d) (hqN : q ≤ N)
    {δ : ℝ} (hδ : 0 < δ) {β : ℝ}
    (hreg : |β| ≤ (N:ℝ)^(-(d:ℝ))) :
    C₁ * (q:ℝ)^(1-δ) * (3 * (2 * Real.pi * |β| * A * (d:ℝ) * ((N:ℝ)+(q:ℝ))^(d-1)) * ((N:ℝ)+(q:ℝ)) + 6)
      ≤ (100 * 2^(1/(d:ℝ)) * 100^(1/(d:ℝ)) * (C₁ * (2 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 1) + 1))
          * (q:ℝ)^(-δ) * Work.A3.mArcKernel N d β := by
  have hd1 : 1 ≤ d := by omega
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNnn : (0:ℝ) ≤ (N:ℝ) := hNpos.le
  have hqN' : (q:ℝ) ≤ (N:ℝ) := by exact_mod_cast hqN
  -- The two normalising constants.
  set W : ℝ := C₁ * (2 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 1) + 1 with hW
  have hWpos : 0 < W := by rw [hW]; positivity
  set Cc : ℝ := 100 * (2:ℝ)^(1/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)) * W with hCc
  have hCcpos : 0 < Cc := by rw [hCc]; positivity
  -- The kernel is at least `2^{-1/d} N` in the regime `|β| ≤ N^{-d}`.
  have hkern : (2:ℝ)^(-(1:ℝ)/(d:ℝ)) * (N:ℝ) ≤ Work.A3.mArcKernel N d β :=
    (Work.A3.mArcKernel_lower N d hN hd1 β).2 hreg
  -- `q^{1-δ} = q q^{-δ}`.
  have hqpow : (q:ℝ)^(1-δ) = (q:ℝ) * (q:ℝ)^(-δ) := by
    rw [show (1:ℝ) - δ = 1 + (-δ) by ring, Real.rpow_add hq0, Real.rpow_one]
  have hqdpos : 0 < (q:ℝ)^(-δ) := Real.rpow_pos_of_pos hq0 _
  -- The regularising hypothesis gives `|β| (N+q)^d ≤ 2^d` (since `N + q ≤ 2N`).
  have hβxd : |β| * ((N:ℝ)+(q:ℝ))^d ≤ (2:ℝ)^d := by
    have hdiv : (N:ℝ)^(-(d:ℝ)) * ((N:ℝ)+(q:ℝ))^d = (((N:ℝ)+(q:ℝ))/(N:ℝ))^d := by
      rw [Real.rpow_neg hNnn, Real.rpow_natCast, div_pow]
      ring
    have h2 : (((N:ℝ)+(q:ℝ))/(N:ℝ))^d ≤ (2:ℝ)^d := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_iff₀ hNpos]
      linarith
    calc |β| * ((N:ℝ)+(q:ℝ))^d ≤ (N:ℝ)^(-(d:ℝ)) * ((N:ℝ)+(q:ℝ))^d :=
          mul_le_mul_of_nonneg_right hreg (by positivity)
      _ = (((N:ℝ)+(q:ℝ))/(N:ℝ))^d := hdiv
      _ ≤ (2:ℝ)^d := h2
  -- The block term `3 L (N+q)` is at most `6 π A d 2^d`.
  have hM : 3 * (2 * Real.pi * |β| * A * (d:ℝ) * ((N:ℝ)+(q:ℝ))^(d-1)) * ((N:ℝ)+(q:ℝ)) + 6
      ≤ 6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 6 := by
    have hxpow : ((N:ℝ)+(q:ℝ))^(d-1) * ((N:ℝ)+(q:ℝ)) = ((N:ℝ)+(q:ℝ))^d := by
      rw [← pow_succ, Nat.sub_add_cancel hd1]
    have h1 : 3 * (2 * Real.pi * |β| * A * (d:ℝ) * ((N:ℝ)+(q:ℝ))^(d-1)) * ((N:ℝ)+(q:ℝ))
        = 6 * Real.pi * |β| * A * (d:ℝ) * (((N:ℝ)+(q:ℝ))^(d-1) * ((N:ℝ)+(q:ℝ))) := by ring
    rw [h1, hxpow]
    have h2 : 6 * Real.pi * |β| * A * (d:ℝ) * ((N:ℝ)+(q:ℝ))^d
        = 6 * Real.pi * A * (d:ℝ) * (|β| * ((N:ℝ)+(q:ℝ))^d) := by ring
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left hβxd (by positivity : (0:ℝ) ≤ 6 * Real.pi * A * (d:ℝ))
    linarith
  -- The elementary constant comparison `C₁ (6πAd2^d + 6) ≤ 100·100^{1/d}·W`.
  have hconst : C₁ * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 6) ≤ 100 * (100:ℝ)^(1/(d:ℝ)) * W := by
    have hrpow1 : (1:ℝ) ≤ (100:ℝ)^(1/(d:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
    have hgnn : (0:ℝ) ≤ Real.pi * A * (d:ℝ) * (2:ℝ)^d * C₁ := by positivity
    have h1 : 6 * (Real.pi * A * (d:ℝ) * (2:ℝ)^d * C₁)
        ≤ 200 * (Real.pi * A * (d:ℝ) * (2:ℝ)^d * C₁) :=
      mul_le_mul_of_nonneg_right (by norm_num : (6:ℝ) ≤ 200) hgnn
    have h2 : 6 * C₁ ≤ 100 * C₁ + 100 := by nlinarith [hC₁]
    have hbase : C₁ * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 6)
        ≤ 100 * (C₁ * (2 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 1) + 1) := by
      nlinarith [h1, h2]
    have hle : (100:ℝ) ≤ 100 * (100:ℝ)^(1/(d:ℝ)) := by nlinarith [hrpow1]
    rw [hW]
    exact hbase.trans (mul_le_mul_of_nonneg_right hle hWpos.le)
  -- `2^{1/d} · 2^{-1/d} = 1`.
  have h2rpow : (2:ℝ)^(1/(d:ℝ)) * (2:ℝ)^(-(1:ℝ)/(d:ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    have hexp : (1:ℝ)/(d:ℝ) + (-1)/(d:ℝ) = 0 := by rw [← add_div, add_neg_cancel, zero_div]
    rw [hexp, Real.rpow_zero]
  -- The two `2`-powers cancel in the constant.
  have hCc2 : Cc * (2:ℝ)^(-(1:ℝ)/(d:ℝ)) = 100 * (100:ℝ)^(1/(d:ℝ)) * W := by
    rw [hCc]
    calc 100 * (2:ℝ)^(1/(d:ℝ)) * (100:ℝ)^(1/(d:ℝ)) * W * (2:ℝ)^(-(1:ℝ)/(d:ℝ))
        = 100 * (100:ℝ)^(1/(d:ℝ)) * W * ((2:ℝ)^(1/(d:ℝ)) * (2:ℝ)^(-(1:ℝ)/(d:ℝ))) := by ring
      _ = 100 * (100:ℝ)^(1/(d:ℝ)) * W := by rw [h2rpow, mul_one]
  have hkern' : (N:ℝ) * (2:ℝ)^(-(1:ℝ)/(d:ℝ)) ≤ Work.A3.mArcKernel N d β := by
    rw [mul_comm]; exact hkern
  -- `q ≤ N` and the constant comparison.
  have hA1nn : (0:ℝ) ≤ C₁ * ((q:ℝ) * (q:ℝ)^(-δ)) := by positivity
  have hstep5 : C₁ * (q:ℝ) * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 6)
      ≤ C₁ * (N:ℝ) * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 6) := by
    have hm : (0:ℝ) ≤ 6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 6 := by positivity
    apply mul_le_mul_of_nonneg_right _ hm
    exact mul_le_mul_of_nonneg_left hqN' hC₁.le
  calc C₁ * (q:ℝ)^(1-δ) * (3 * (2 * Real.pi * |β| * A * (d:ℝ) * ((N:ℝ)+(q:ℝ))^(d-1)) * ((N:ℝ)+(q:ℝ)) + 6)
      = C₁ * ((q:ℝ) * (q:ℝ)^(-δ)) * (3 * (2 * Real.pi * |β| * A * (d:ℝ) * ((N:ℝ)+(q:ℝ))^(d-1)) * ((N:ℝ)+(q:ℝ)) + 6) := by
        rw [hqpow]
    _ ≤ C₁ * ((q:ℝ) * (q:ℝ)^(-δ)) * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 6) :=
        mul_le_mul_of_nonneg_left hM hA1nn
    _ = (q:ℝ)^(-δ) * (C₁ * (q:ℝ) * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 6)) := by ring
    _ ≤ (q:ℝ)^(-δ) * (C₁ * (N:ℝ) * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 6)) :=
        mul_le_mul_of_nonneg_left hstep5 hqdpos.le
    _ ≤ (q:ℝ)^(-δ) * ((N:ℝ) * (100 * (100:ℝ)^(1/(d:ℝ)) * W)) := by
        apply mul_le_mul_of_nonneg_left _ hqdpos.le
        calc C₁ * (N:ℝ) * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 6)
            = (N:ℝ) * (C₁ * (6 * Real.pi * A * (d:ℝ) * (2:ℝ)^d + 6)) := by ring
          _ ≤ (N:ℝ) * (100 * (100:ℝ)^(1/(d:ℝ)) * W) :=
              mul_le_mul_of_nonneg_left hconst hNnn
    _ = (q:ℝ)^(-δ) * ((N:ℝ) * (Cc * (2:ℝ)^(-(1:ℝ)/(d:ℝ)))) := by rw [← hCc2]
    _ ≤ (q:ℝ)^(-δ) * (Cc * Work.A3.mArcKernel N d β) := by
        apply mul_le_mul_of_nonneg_left _ hqdpos.le
        have : (N:ℝ) * (Cc * (2:ℝ)^(-(1:ℝ)/(d:ℝ)))
            = Cc * ((N:ℝ) * (2:ℝ)^(-(1:ℝ)/(d:ℝ))) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hkern' hCcpos.le
    _ = Cc * (q:ℝ)^(-δ) * Work.A3.mArcKernel N d β := by ring

end Work.A3
