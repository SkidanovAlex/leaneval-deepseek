import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auH_err
import Submission.Work.Resample.auTailExp
import Submission.Work.Resample.exp_nat_le_two_pow

namespace Work.Resample

theorem auHExpClose (p : ℕ) (hp : 100 ≤ p) (Z : ℤ) (hZ0 : 0 ≤ Z)
    (hZle : (Z : ℝ) ≤ ((p : ℝ) + 10) * (2 : ℝ) ^ Work.Resample.auPrec p) :
    |((Work.Resample.auH p (-Z) (Work.Resample.auNstep p) : ℤ) : ℝ) / (2 : ℝ) ^ Work.Resample.auPrec p
        - Real.exp (-((Z : ℝ) / (2 : ℝ) ^ Work.Resample.auPrec p))| ≤ 2 / (2 : ℝ) ^ p := by
  have h2P : (0:ℝ) < (2:ℝ)^(auPrec p) := by positivity
  have hZp : (0:ℝ) ≤ (Z:ℝ) := by exact_mod_cast hZ0
  set y : ℝ := (Z:ℝ)/(2:ℝ)^(auPrec p) with hy
  have hyle : y ≤ (p:ℝ) + 10 := by
    rw [hy, div_le_iff₀ h2P]
    simpa using hZle
  -- ### numeric bounds
  have hA2 : (2:ℝ)^(2*p+21)/(2:ℝ)^(auPrec p) ≤ 1/(2:ℝ)^p := by
    rw [div_le_div_iff₀ h2P (by positivity), one_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by simp only [auPrec]; omega)
  have hA : (2/(2:ℝ)^(auPrec p)) * Real.exp y ≤ 1/(2:ℝ)^p := by
    have he : Real.exp y ≤ (2:ℝ)^(2*p+20) := by
      have h1 : Real.exp y ≤ Real.exp ((p:ℝ)+10) := Real.exp_le_exp.mpr hyle
      have h2 : Real.exp ((p:ℝ)+10) ≤ (2:ℝ)^(2*p+20) := by
        have h3 := exp_nat_le_two_pow (p+10)
        have hcast : ((p+10 : ℕ) : ℝ) = (p:ℝ) + 10 := by push_cast; ring
        rw [hcast] at h3
        rwa [show 2*(p+10) = 2*p+20 by omega] at h3
      linarith
    calc (2/(2:ℝ)^(auPrec p)) * Real.exp y
        ≤ (2/(2:ℝ)^(auPrec p)) * (2:ℝ)^(2*p+20) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = (2:ℝ)^(2*p+21)/(2:ℝ)^(auPrec p) := by
          rw [show (2:ℝ)^(2*p+21) = (2:ℝ)^(2*p+20) * 2 by
            rw [show 2*p+21 = 2*p+20+1 by omega, pow_succ]]
          ring
      _ ≤ 1/(2:ℝ)^p := hA2
  have hB : 1/(2:ℝ)^(2*p+160) ≤ 1/(2:ℝ)^p :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  -- ### the two error estimates
  have hyg : 0 ≤ y := div_nonneg hZp (le_of_lt h2P)
  have hAB : |(auH p (-Z) (auNstep p) : ℝ)/(2:ℝ)^(auPrec p)
      - Work.Fx.pot (-y) 0 (auNstep p+1)| ≤ (2/(2:ℝ)^(auPrec p)) * Real.exp y := by
    have hneg : ((↑(-Z) : ℝ))/(2:ℝ)^(auPrec p) = -y := by rw [hy]; push_cast; ring
    have habs : |((↑(-Z) : ℝ))/(2:ℝ)^(auPrec p)| = y := by
      rw [abs_div, abs_of_pos h2P, Int.cast_neg, abs_neg, abs_of_nonneg hZp, hy]
    have h := auH_err p (-Z) (auNstep p) le_rfl
    rw [Nat.sub_self, hneg] at h
    rwa [abs_neg, abs_of_nonneg hyg] at h
  have hBC : |Work.Fx.pot (-y) 0 (auNstep p+1) - Real.exp (-y)| ≤ 1/(2:ℝ)^(2*p+160) := by
    rw [Work.Fx.expRec.2.2.2.2]
    exact auTailExp p hp (-y) (by rw [abs_neg, abs_of_nonneg hyg]; exact hyle)
  -- ### assembly
  have htri : |(auH p (-Z) (auNstep p) : ℝ)/(2:ℝ)^(auPrec p) - Real.exp (-y)|
      ≤ |(auH p (-Z) (auNstep p) : ℝ)/(2:ℝ)^(auPrec p) - Work.Fx.pot (-y) 0 (auNstep p+1)|
        + |Work.Fx.pot (-y) 0 (auNstep p+1) - Real.exp (-y)| := by
    have h := abs_add_le
      ((auH p (-Z) (auNstep p) : ℝ)/(2:ℝ)^(auPrec p) - Work.Fx.pot (-y) 0 (auNstep p+1))
      (Work.Fx.pot (-y) 0 (auNstep p+1) - Real.exp (-y))
    rwa [sub_add_sub_cancel] at h
  rw [show Real.exp (-((Z:ℝ)/(2:ℝ)^(auPrec p))) = Real.exp (-y) by rw [hy]]
  calc |(auH p (-Z) (auNstep p) : ℝ)/(2:ℝ)^(auPrec p) - Real.exp (-y)|
      ≤ |(auH p (-Z) (auNstep p) : ℝ)/(2:ℝ)^(auPrec p) - Work.Fx.pot (-y) 0 (auNstep p+1)|
        + |Work.Fx.pot (-y) 0 (auNstep p+1) - Real.exp (-y)| := htri
    _ ≤ (2/(2:ℝ)^(auPrec p)) * Real.exp y + 1/(2:ℝ)^(2*p+160) := add_le_add hAB hBC
    _ ≤ 1/(2:ℝ)^p + 1/(2:ℝ)^p := add_le_add hA hB
    _ = 2/(2:ℝ)^p := by ring

end Work.Resample
