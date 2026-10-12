import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.bulk_tau_arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

theorem bulkTauLogRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ρ μ : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) (hρ : 0 < ρ)
    (hreg : Work.BoseB6Est.FsI1Regime (Work.BoseBogFS.bogKernel v R ρ μ)
      (_root_.BoseGases.a v) R ρ μ
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hcond : Work.BoseBogFS.chiTC * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 1 / 2)
    (hT : 4 * Work.BoseBogFS.bogC1 v ρ μ ≤ Work.BoseBogFS.bogT v R μ) :
    36 * Work.BoseBogFS.bogC1 v ρ μ
        * (Real.log (Work.BoseBogFS.bogT v R μ)
            - Real.log (4 * Work.BoseBogFS.bogC1 v ρ μ))
      ≤ (36 * 10 ^ 8 + 1) * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  -- The scalar row already proved in `bulk_tau_arith`: with `C = chiTC`,
  -- `c₁·B_β²·(1 + log(T/(4c₁))) + c₁³·B_β² ≤ 10⁸·ε`, where `B_β = bogBb R ℓ chiTC ≥ 8π > 6`.
  have harith := Work.BoseBogFS.bulk_tau_arith (v := v) (R := R) (ρ := ρ) (μ := μ)
    (C := Work.BoseBogFS.chiTC) hR hav hρ Work.BoseBogFS.chiTC_nonneg hcond hreg
  set c1 := Work.BoseBogFS.bogC1 v ρ μ with hc1
  set T := Work.BoseBogFS.bogT v R μ with hTdef
  set Bb := Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC with hBb
  set E := Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ with hE
  have hc1pos : 0 < c1 := by
    rw [hreg.hc1val]
    have h1 : 0 < ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl *
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ :=
      inv_pos.mpr (mul_pos hreg.hKl hreg.hs)
    have h2 : 0 < Real.sqrt (μ / ρ) := Real.sqrt_pos.mpr (div_pos hreg.hμ hρ)
    positivity
  have h4c1pos : 0 < 4 * c1 := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le h4c1pos hT
  -- `log T − log (4c₁) = log(T/(4c₁))`, and the latter is nonnegative by `hT`.
  have hL : Real.log T - Real.log (4 * c1) = Real.log (T / (4 * c1)) :=
    (Real.log_div (ne_of_gt hTpos) (ne_of_gt h4c1pos)).symm
  have hLnn : 0 ≤ Real.log (T / (4 * c1)) :=
    Real.log_nonneg ((one_le_div h4c1pos).mpr hT)
  have hEnn : 0 ≤ E := by
    rw [hE]
    exact hreg.lhyEps_nonneg
  -- `B_β ≥ 8π > 6`, hence `B_β² ≥ 36`.
  have hBbsq : 36 ≤ Bb ^ 2 := by
    have hBb_ge : 8 * Real.pi ≤ Bb := by
      rw [hBb, Work.BoseBogFS.bogBb]
      have hnn : 0 ≤ Work.BoseBogFS.chiTC * (R / Work.BoseFixR.ell v μ) ^ 2 :=
        mul_nonneg Work.BoseBogFS.chiTC_nonneg (sq_nonneg _)
      nlinarith [Real.pi_pos, hnn]
    have h24 : (24 : ℝ) ≤ Bb := by nlinarith [hBb_ge, Real.pi_gt_three]
    nlinarith [h24, sq_nonneg (Bb - 24)]
  have h1 : 36 * c1 * Real.log (T / (4 * c1))
      ≤ c1 * Bb ^ 2 * (1 + Real.log (T / (4 * c1))) := by
    have hk : (0:ℝ) ≤ c1 * (Bb ^ 2 - 36) * (1 + Real.log (T / (4 * c1))) :=
      mul_nonneg (mul_nonneg hc1pos.le (by linarith)) (by linarith)
    have h36 : (0:ℝ) ≤ 36 * c1 := by linarith
    nlinarith [hk, h36]
  have h2 : c1 * Bb ^ 2 * (1 + Real.log (T / (4 * c1)))
      ≤ c1 * Bb ^ 2 * (1 + Real.log (T / (4 * c1))) + c1 ^ 3 * Bb ^ 2 := by
    have : (0:ℝ) ≤ c1 ^ 3 * Bb ^ 2 := by positivity
    linarith
  have h3 : (10 : ℝ) ^ 8 * E ≤ (36 * 10 ^ 8 + 1) * E := by nlinarith [hEnn]
  rw [hL]
  linarith [h1, h2, harith, h3]

end Work.BoseBogFS
