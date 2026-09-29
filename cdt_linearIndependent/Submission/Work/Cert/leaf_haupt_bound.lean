import Mathlib
import Submission.Work.Cert.LeafAux

/-! # The elementary Hauptmodul bound of the arc certificate

From Jacobi's identity `h(q)·B(q)^8 = -256·q·A(q)^8` (`Work.Cert.ThetaIdentity`) and the
certified enclosures `‖A(q)‖ ≤ Aup/S`, `‖B(q)‖ ≥ Blo/S`, `‖q‖ ≤ m/S` we get the crude bound
`S·‖h(q)‖² ≤ 65536·m²·Aup¹⁶/(Blo¹⁶·S)` which the leaf soundness proof feeds into the
`expLo` test. -/

namespace Work.Cert

theorem leaf_haupt_bound (hI : Work.Cert.ThetaIdentity) {Aup Blo m : ℤ} (hBlo : 0 < Blo) (q : ℂ)
    (hq1 : ‖q‖ < 1) (hA : ‖Work.Cert.thetaA q‖ ≤ (Aup : ℝ) / (Work.Cert.S : ℝ))
    (hB : (Blo : ℝ) / (Work.Cert.S : ℝ) ≤ ‖Work.Cert.thetaB q‖)
    (hm : ‖q‖ ≤ (m : ℝ) / (Work.Cert.S : ℝ)) :
    (Work.Cert.S : ℝ) * ‖Submission.CDTPlan.hauptH q‖ ^ 2
      ≤ 65536 * (m : ℝ) ^ 2 * (Aup : ℝ) ^ 16 / ((Blo : ℝ) ^ 16 * (Work.Cert.S : ℝ)) := by
  have hS : (0 : ℝ) < (Work.Cert.S : ℝ) := by exact_mod_cast Work.Cert.S_pos
  have hBR : (0 : ℝ) < (Blo : ℝ) := by exact_mod_cast hBlo
  have hBq : 0 < ‖Work.Cert.thetaB q‖ := lt_of_lt_of_le (by positivity) hB
  have hMS : 0 ≤ (m : ℝ) / (Work.Cert.S : ℝ) := le_trans (norm_nonneg q) hm
  have hAS : 0 ≤ (Aup : ℝ) / (Work.Cert.S : ℝ) := le_trans (norm_nonneg _) hA
  have hBS : 0 ≤ (Blo : ℝ) / (Work.Cert.S : ℝ) := div_nonneg hBR.le hS.le
  -- Jacobi's identity, in norms
  have hkey : ‖Submission.CDTPlan.hauptH q‖ * ‖Work.Cert.thetaB q‖ ^ 8
      = 256 * ‖q‖ * ‖Work.Cert.thetaA q‖ ^ 8 := by
    have h := congrArg norm (hI q hq1)
    simpa [norm_mul, norm_pow, norm_neg] using h
  have hdiv : ‖Submission.CDTPlan.hauptH q‖
      = 256 * ‖q‖ * ‖Work.Cert.thetaA q‖ ^ 8 / ‖Work.Cert.thetaB q‖ ^ 8 := by
    rw [eq_div_iff (pow_ne_zero 8 (ne_of_gt hBq))]
    exact hkey
  have hnum : 256 * ‖q‖ * ‖Work.Cert.thetaA q‖ ^ 8
      ≤ 256 * ((m : ℝ) / (Work.Cert.S : ℝ)) * (((Aup : ℝ) / (Work.Cert.S : ℝ)) ^ 8) := by
    have hA8 : ‖Work.Cert.thetaA q‖ ^ 8 ≤ ((Aup : ℝ) / (Work.Cert.S : ℝ)) ^ 8 :=
      pow_le_pow_left₀ (norm_nonneg _) hA 8
    have h1 : 256 * ‖q‖ ≤ 256 * ((m : ℝ) / (Work.Cert.S : ℝ)) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    have h2 : 0 ≤ (256 : ℝ) * ((m : ℝ) / (Work.Cert.S : ℝ)) :=
      mul_nonneg (by norm_num) hMS
    exact mul_le_mul h1 hA8 (pow_nonneg (norm_nonneg _) 8) h2
  have hden : ((Blo : ℝ) / (Work.Cert.S : ℝ)) ^ 8 ≤ ‖Work.Cert.thetaB q‖ ^ 8 :=
    pow_le_pow_left₀ hBS hB 8
  have hh : ‖Submission.CDTPlan.hauptH q‖
      ≤ 256 * ((m : ℝ) / (Work.Cert.S : ℝ)) * ((Aup : ℝ) / (Work.Cert.S : ℝ)) ^ 8
        / ((Blo : ℝ) / (Work.Cert.S : ℝ)) ^ 8 := by
    rw [hdiv]
    exact div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) hMS) (pow_nonneg hAS 8)) hnum
      (pow_pos (div_pos hBR hS) 8) hden
  have hT : (Work.Cert.S : ℝ) *
      (256 * ((m : ℝ) / (Work.Cert.S : ℝ)) * ((Aup : ℝ) / (Work.Cert.S : ℝ)) ^ 8
        / ((Blo : ℝ) / (Work.Cert.S : ℝ)) ^ 8) ^ 2
      = 65536 * (m : ℝ) ^ 2 * (Aup : ℝ) ^ 16 / ((Blo : ℝ) ^ 16 * (Work.Cert.S : ℝ)) := by
    field_simp
    ring
  calc (Work.Cert.S : ℝ) * ‖Submission.CDTPlan.hauptH q‖ ^ 2
      ≤ (Work.Cert.S : ℝ) *
          (256 * ((m : ℝ) / (Work.Cert.S : ℝ)) * ((Aup : ℝ) / (Work.Cert.S : ℝ)) ^ 8
            / ((Blo : ℝ) / (Work.Cert.S : ℝ)) ^ 8) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) hS.le
    _ = 65536 * (m : ℝ) ^ 2 * (Aup : ℝ) ^ 16 / ((Blo : ℝ) ^ 16 * (Work.Cert.S : ℝ)) := hT

end Work.Cert
