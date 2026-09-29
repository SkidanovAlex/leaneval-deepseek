import Mathlib
import Submission.Work.Fx.piDefs
import Submission.Work.Fx.piSqrtBound
import Submission.Work.Fx.piDvalBound
import Submission.Work.Fx.piTwoSubAseq
import Submission.Work.Fx.piFloor

/-!
# Final bound on the fixed-point π word (`Work.Fx.piUBound`)

Assembles the pieces of the fixed-point evaluation of `π` by the nested-square-root sequence
`Aseq k = sqrtTwoAddSeries 0 k = 2 cos (π/2^(k+1))`:

* `piSqrtBound`   : the real-analytic core, `|2^(2p+1) √(2 - aval p p/2^(2 qq p)) - 2^p π| ≤ 1/4`;
* `piDvalBound`   : `Dval p` (the integer floor of `√(C0c p - aval p p)`) compared with the real
                    square root, at the precision `2^(qq p)`;
* `piTwoSubAseq`  : the quantitative non-degeneracy `4/2^(qq p) ≤ 2 - Aseq p` of the model sequence;
* `piFloor`       : the final rounding step `⌊Dval p·2^(2p+1)/2^(qq p) + 1/2⌋` versus `2^p π`.

Everything is combined below to deduce `|uval p - 2^p π| ≤ 1`.
-/

set_option autoImplicit false

namespace Work.Fx

theorem piUBound (p : ℕ) (h100 : 100 ≤ p)
    (herr : |(2 : ℝ) ^ (2 * Work.Fx.qq p) * Work.Fx.Aseq p - (Work.Fx.aval p p : ℝ)|
        ≤ 4 * (2 : ℝ) ^ Work.Fx.qq p) :
    |(Work.Fx.uval p : ℝ) - 2 ^ p * Real.pi| ≤ 1 := by
  have hp1 : 1 ≤ p := by omega
  -- non-degeneracy of the model sequence, from the quantitative bound on `2 - Aseq p`
  have h2A : 4 / (2 : ℝ) ^ qq p ≤ 2 - Aseq p := piTwoSubAseq p hp1
  have hQ2pos : (0:ℝ) < (2:ℝ) ^ (2 * qq p) := by positivity
  have hquot : (2:ℝ) ^ (2 * qq p) / (2:ℝ) ^ qq p = (2:ℝ) ^ qq p := by
    rw [div_eq_mul_inv, ← pow_sub₀ (2:ℝ) (by norm_num) (by omega : qq p ≤ 2 * qq p)]
    congr 1
    omega
  -- `aval p p ≤ C0c p`, so that `Dval p` really is `⌊√(C0c p - aval p p)⌋`
  have hreal : (aval p p : ℝ) ≤ (C0c p : ℝ) := by
    have h1 : -(4 * (2:ℝ)^qq p) ≤ (2:ℝ)^(2*qq p) * Aseq p - (aval p p : ℝ) :=
      (abs_le.mp herr).1
    have h2 : (aval p p : ℝ) ≤ (2:ℝ)^(2*qq p) * Aseq p + 4 * (2:ℝ)^qq p := by linarith
    have hmul : (2:ℝ)^(2*qq p) * (4/(2:ℝ)^qq p) = 4 * (2:ℝ)^qq p := by
      rw [mul_div_assoc', mul_comm ((2:ℝ)^(2*qq p)) 4, mul_div_assoc, hquot]
    have h3 : (2:ℝ)^(2*qq p) * Aseq p + 4 * (2:ℝ)^qq p
        = (2:ℝ)^(2*qq p) * (Aseq p + 4/(2:ℝ)^qq p) := by
      rw [mul_add, hmul]
    have h4 : Aseq p + 4/(2:ℝ)^qq p ≤ 2 := by linarith
    have h5 : (2:ℝ)^(2*qq p) * (Aseq p + 4/(2:ℝ)^qq p) ≤ (2:ℝ)^(2*qq p) * 2 :=
      mul_le_mul_of_nonneg_left h4 hQ2pos.le
    have h6 : (2:ℝ)^(2*qq p) * 2 = (2:ℝ)^(2*qq p + 1) := by
      simpa [mul_comm] using (pow_succ' (2:ℝ) (2*qq p)).symm
    have h7 : ((C0c p : ℤ) : ℝ) = (2:ℝ)^(2*qq p + 1) := by
      rw [C0c]; push_cast; ring
    rw [h7]
    linarith
  have ha0 : 0 ≤ aval p p := sq_nonneg' p p
  have hC : aval p p ≤ C0c p := by exact_mod_cast hreal
  have hDv := piDvalBound p ha0 hC
  have hSq := piSqrtBound p h100 herr
  -- the scaling `2^(2p+1)` of the `Dval` comparison
  have hpQ : (2:ℝ)^(2*p+1)/(2:ℝ)^(qq p) = 1/(2:ℝ)^(2*p-1) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    rw [← pow_add]
    rw [qq]
    simp only [one_mul]
    congr 1
    omega
  have hf : (Dval p : ℝ) * (2:ℝ)^(2*p+1)/(2:ℝ)^(qq p)
      - (2:ℝ)^(2*p+1) * Real.sqrt (2 - (aval p p:ℝ)/(2:ℝ)^(2*qq p))
      = (2:ℝ)^(2*p+1) * ((Dval p : ℝ)/(2:ℝ)^(qq p)
          - Real.sqrt (2 - (aval p p:ℝ)/(2:ℝ)^(2*qq p))) := by
    rw [mul_sub, mul_div_assoc']
    ring
  have hc : (0:ℝ) < (2:ℝ)^(2*p+1) := by positivity
  have huv : |(Dval p : ℝ) * (2:ℝ)^(2*p+1)/(2:ℝ)^(qq p)
      - (2:ℝ)^(2*p+1) * Real.sqrt (2 - (aval p p:ℝ)/(2:ℝ)^(2*qq p))|
      ≤ 1/(2:ℝ)^(2*p-1) := by
    calc |(Dval p : ℝ) * (2:ℝ)^(2*p+1)/(2:ℝ)^(qq p)
          - (2:ℝ)^(2*p+1) * Real.sqrt (2 - (aval p p:ℝ)/(2:ℝ)^(2*qq p))|
        = (2:ℝ)^(2*p+1) * |(Dval p : ℝ)/(2:ℝ)^(qq p)
            - Real.sqrt (2 - (aval p p:ℝ)/(2:ℝ)^(2*qq p))| := by
          rw [hf, abs_mul, abs_of_pos hc]
      _ ≤ (2:ℝ)^(2*p+1) * (1/(2:ℝ)^(qq p)) := mul_le_mul_of_nonneg_left hDv hc.le
      _ = 1/(2:ℝ)^(2*p-1) := by rw [mul_one_div, hpQ]
  have h4 : 1/(2:ℝ)^(2*p-1) ≤ 1/4 := by
    have hden : (4:ℝ) ≤ (2:ℝ)^(2*p-1) := by
      calc (4:ℝ) = (2:ℝ)^2 := by norm_num
        _ ≤ (2:ℝ)^(2*p-1) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact one_div_le_one_div_of_le (by norm_num) hden
  have htri := abs_sub_le ((Dval p : ℝ) * (2:ℝ)^(2*p+1)/(2:ℝ)^(qq p))
      ((2:ℝ)^(2*p+1) * Real.sqrt (2 - (aval p p:ℝ)/(2:ℝ)^(2*qq p))) ((2:ℝ)^p * Real.pi)
  have hDa : |(Dval p : ℝ) * (2:ℝ)^(2*p+1)/(2:ℝ)^(qq p) - (2:ℝ)^p * Real.pi| ≤ 1/2 := by
    linarith [htri, huv, hSq, h4]
  exact piFloor p hp1 hDa

end Work.Fx
