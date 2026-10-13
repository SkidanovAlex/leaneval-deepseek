import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The nine piece bounds assemble into the bound for the right-nested sum `Rsum`. -/
theorem sharpN0_sums {α Ci : ℝ} {g g' h : ℝ → ℝ → ℝ} (hα : 0 < α) (hCi : 0 < Ci)
    (CF Cdz Cw : ℝ) (hCF : 0 < CF) (hCdz : 0 < Cdz) (hCw : 0 < Cw)
    (h1 : Work.Spaces.HkMem α 4 (P1 α g h)
      ∧ Work.FTS.Nonlin.Xn α (P1 α g h) ≤ kA1 α Ci * TOf α g g' h)
    (h2 : Work.Spaces.HkMem α 4 (P2 α g' h)
      ∧ Work.FTS.Nonlin.Xn α (P2 α g' h) ≤ kA2 α Ci * TOf α g g' h)
    (h3 : Work.Spaces.HkMem α 4 (P3 α h)
      ∧ Work.FTS.Nonlin.Xn α (P3 α h) ≤ kA3 α Ci CF * TOf α g g' h)
    (h4 : Work.Spaces.HkMem α 4 (P4 α g h)
      ∧ Work.FTS.Nonlin.Xn α (P4 α g h) ≤ kA4 α Ci * TOf α g g' h)
    (h5 : Work.Spaces.HkMem α 4 (P5 α g' h)
      ∧ Work.FTS.Nonlin.Xn α (P5 α g' h) ≤ kA5 α Ci * TOf α g g' h)
    (h6 : Work.Spaces.HkMem α 4 (P6 α h)
      ∧ Work.FTS.Nonlin.Xn α (P6 α h) ≤ kA6 α Ci Cdz * TOf α g g' h)
    (h7 : Work.Spaces.HkMem α 4 (P7 α g h)
      ∧ Work.FTS.Nonlin.Xn α (P7 α g h) ≤ kA7 α Ci * TOf α g g' h)
    (h8 : Work.Spaces.HkMem α 4 (P8 α g' h)
      ∧ Work.FTS.Nonlin.Xn α (P8 α g' h) ≤ kA8 α Ci * TOf α g g' h)
    (h9 : Work.Spaces.HkMem α 4 (P9 α h)
      ∧ Work.FTS.Nonlin.Xn α (P9 α h) ≤ kA9 α Ci Cw * TOf α g g' h)
    (hs1 : Work.FTS.EllipticEst.SmoothOpen (P1 α g h))
    (hs2 : Work.FTS.EllipticEst.SmoothOpen (P2 α g' h))
    (hs3 : Work.FTS.EllipticEst.SmoothOpen (P3 α h))
    (hs4 : Work.FTS.EllipticEst.SmoothOpen (P4 α g h))
    (hs5 : Work.FTS.EllipticEst.SmoothOpen (P5 α g' h))
    (hs6 : Work.FTS.EllipticEst.SmoothOpen (P6 α h))
    (hs7 : Work.FTS.EllipticEst.SmoothOpen (P7 α g h))
    (hs8 : Work.FTS.EllipticEst.SmoothOpen (P8 α g' h))
    (hs9 : Work.FTS.EllipticEst.SmoothOpen (P9 α h))
    : Work.Spaces.HkMem α 4 (Rsum α g g' h) ∧ Work.FTS.EllipticEst.SmoothOpen (Rsum α g g' h)
      ∧ Work.FTS.Nonlin.Xn α (Rsum α g g' h) ≤ 1024 * ksum α Ci CF Cdz Cw * TOf α g g' h := by

  have hT : 0 ≤ TOf α g g' h := TOf_nonneg α g g' h
  have hK0 : 0 ≤ ksum α Ci CF Cdz Cw := ksum_nonneg hα hCi hCF hCdz hCw
  have h1' : Work.FTS.Nonlin.Xn α (P1 α g h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h1.2 (mul_le_mul_of_nonneg_right (kA1_le_ksum hα hCi hCF hCdz hCw) hT)
  have h2' : Work.FTS.Nonlin.Xn α (P2 α g' h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h2.2 (mul_le_mul_of_nonneg_right (kA2_le_ksum hα hCi hCF hCdz hCw) hT)
  have h3' : Work.FTS.Nonlin.Xn α (P3 α h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h3.2 (mul_le_mul_of_nonneg_right (kA3_le_ksum hα hCi hCF hCdz hCw) hT)
  have h4' : Work.FTS.Nonlin.Xn α (P4 α g h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h4.2 (mul_le_mul_of_nonneg_right (kA4_le_ksum hα hCi hCF hCdz hCw) hT)
  have h5' : Work.FTS.Nonlin.Xn α (P5 α g' h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h5.2 (mul_le_mul_of_nonneg_right (kA5_le_ksum hα hCi hCF hCdz hCw) hT)
  have h6' : Work.FTS.Nonlin.Xn α (P6 α h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h6.2 (mul_le_mul_of_nonneg_right (kA6_le_ksum hα hCi hCF hCdz hCw) hT)
  have h7' : Work.FTS.Nonlin.Xn α (P7 α g h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h7.2 (mul_le_mul_of_nonneg_right (kA7_le_ksum hα hCi hCF hCdz hCw) hT)
  have h8' : Work.FTS.Nonlin.Xn α (P8 α g' h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h8.2 (mul_le_mul_of_nonneg_right (kA8_le_ksum hα hCi hCF hCdz hCw) hT)
  have h9' : Work.FTS.Nonlin.Xn α (P9 α h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h9.2 (mul_le_mul_of_nonneg_right (kA9_le_ksum hα hCi hCF hCdz hCw) hT)
  set R9 : ℝ → ℝ → ℝ := P9 α h with hR9
  set R8 : ℝ → ℝ → ℝ := P8 α g' h + R9 with hR8
  set R7 : ℝ → ℝ → ℝ := P7 α g h + R8 with hR7
  set R6 : ℝ → ℝ → ℝ := P6 α h + R7 with hR6
  set R5 : ℝ → ℝ → ℝ := P5 α g' h + R6 with hR5
  set R4 : ℝ → ℝ → ℝ := P4 α g h + R5 with hR4
  set R3 : ℝ → ℝ → ℝ := P3 α h + R4 with hR3
  set R2 : ℝ → ℝ → ℝ := P2 α g' h + R3 with hR2
  set R1 : ℝ → ℝ → ℝ := P1 α g h + R2 with hR1
  set B9 : ℝ := ksum α Ci CF Cdz Cw with hB9
  set B8 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B9) with hB8
  set B7 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B8) with hB7
  set B6 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B7) with hB6
  set B5 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B6) with hB5
  set B4 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B5) with hB4
  set B3 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B4) with hB3
  set B2 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B3) with hB2
  set B1 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B2) with hB1
  have hR9sm : Work.FTS.EllipticEst.SmoothOpen R9 := by rw [hR9]; exact hs9
  have hR9mem : Work.Spaces.HkMem α 4 R9 := by rw [hR9]; exact h9.1
  have hR9x : Work.FTS.Nonlin.Xn α R9 ≤ B9 * TOf α g g' h := by
    rw [hR9, hB9]; exact h9'
  have hR8sm : Work.FTS.EllipticEst.SmoothOpen R8 := by
    rw [hR8]; exact Work.FTS.NonlinRows.smoothOpen_add hs8 hR9sm
  have hR8mem : Work.Spaces.HkMem α 4 R8 := by
    rw [hR8]; exact Work.FTS.EllipticEst.HkMem_add_open hs8 hR9sm h8.1 hR9mem
  have hR8x : Work.FTS.Nonlin.Xn α R8 ≤ B8 * TOf α g g' h := by
    rw [hR8, hB8]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs8 hR9sm h8.1 hR9mem
    calc Work.FTS.Nonlin.Xn α (P8 α g' h + R9)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P8 α g' h) + Work.FTS.Nonlin.Xn α R9) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B9 * TOf α g g' h) := by linarith [h8', hR9x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B9)) * TOf α g g' h := by ring
  have hR7sm : Work.FTS.EllipticEst.SmoothOpen R7 := by
    rw [hR7]; exact Work.FTS.NonlinRows.smoothOpen_add hs7 hR8sm
  have hR7mem : Work.Spaces.HkMem α 4 R7 := by
    rw [hR7]; exact Work.FTS.EllipticEst.HkMem_add_open hs7 hR8sm h7.1 hR8mem
  have hR7x : Work.FTS.Nonlin.Xn α R7 ≤ B7 * TOf α g g' h := by
    rw [hR7, hB7]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs7 hR8sm h7.1 hR8mem
    calc Work.FTS.Nonlin.Xn α (P7 α g h + R8)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P7 α g h) + Work.FTS.Nonlin.Xn α R8) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B8 * TOf α g g' h) := by linarith [h7', hR8x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B8)) * TOf α g g' h := by ring
  have hR6sm : Work.FTS.EllipticEst.SmoothOpen R6 := by
    rw [hR6]; exact Work.FTS.NonlinRows.smoothOpen_add hs6 hR7sm
  have hR6mem : Work.Spaces.HkMem α 4 R6 := by
    rw [hR6]; exact Work.FTS.EllipticEst.HkMem_add_open hs6 hR7sm h6.1 hR7mem
  have hR6x : Work.FTS.Nonlin.Xn α R6 ≤ B6 * TOf α g g' h := by
    rw [hR6, hB6]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs6 hR7sm h6.1 hR7mem
    calc Work.FTS.Nonlin.Xn α (P6 α h + R7)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P6 α h) + Work.FTS.Nonlin.Xn α R7) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B7 * TOf α g g' h) := by linarith [h6', hR7x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B7)) * TOf α g g' h := by ring
  have hR5sm : Work.FTS.EllipticEst.SmoothOpen R5 := by
    rw [hR5]; exact Work.FTS.NonlinRows.smoothOpen_add hs5 hR6sm
  have hR5mem : Work.Spaces.HkMem α 4 R5 := by
    rw [hR5]; exact Work.FTS.EllipticEst.HkMem_add_open hs5 hR6sm h5.1 hR6mem
  have hR5x : Work.FTS.Nonlin.Xn α R5 ≤ B5 * TOf α g g' h := by
    rw [hR5, hB5]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs5 hR6sm h5.1 hR6mem
    calc Work.FTS.Nonlin.Xn α (P5 α g' h + R6)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P5 α g' h) + Work.FTS.Nonlin.Xn α R6) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B6 * TOf α g g' h) := by linarith [h5', hR6x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B6)) * TOf α g g' h := by ring
  have hR4sm : Work.FTS.EllipticEst.SmoothOpen R4 := by
    rw [hR4]; exact Work.FTS.NonlinRows.smoothOpen_add hs4 hR5sm
  have hR4mem : Work.Spaces.HkMem α 4 R4 := by
    rw [hR4]; exact Work.FTS.EllipticEst.HkMem_add_open hs4 hR5sm h4.1 hR5mem
  have hR4x : Work.FTS.Nonlin.Xn α R4 ≤ B4 * TOf α g g' h := by
    rw [hR4, hB4]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs4 hR5sm h4.1 hR5mem
    calc Work.FTS.Nonlin.Xn α (P4 α g h + R5)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P4 α g h) + Work.FTS.Nonlin.Xn α R5) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B5 * TOf α g g' h) := by linarith [h4', hR5x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B5)) * TOf α g g' h := by ring
  have hR3sm : Work.FTS.EllipticEst.SmoothOpen R3 := by
    rw [hR3]; exact Work.FTS.NonlinRows.smoothOpen_add hs3 hR4sm
  have hR3mem : Work.Spaces.HkMem α 4 R3 := by
    rw [hR3]; exact Work.FTS.EllipticEst.HkMem_add_open hs3 hR4sm h3.1 hR4mem
  have hR3x : Work.FTS.Nonlin.Xn α R3 ≤ B3 * TOf α g g' h := by
    rw [hR3, hB3]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs3 hR4sm h3.1 hR4mem
    calc Work.FTS.Nonlin.Xn α (P3 α h + R4)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P3 α h) + Work.FTS.Nonlin.Xn α R4) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B4 * TOf α g g' h) := by linarith [h3', hR4x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B4)) * TOf α g g' h := by ring
  have hR2sm : Work.FTS.EllipticEst.SmoothOpen R2 := by
    rw [hR2]; exact Work.FTS.NonlinRows.smoothOpen_add hs2 hR3sm
  have hR2mem : Work.Spaces.HkMem α 4 R2 := by
    rw [hR2]; exact Work.FTS.EllipticEst.HkMem_add_open hs2 hR3sm h2.1 hR3mem
  have hR2x : Work.FTS.Nonlin.Xn α R2 ≤ B2 * TOf α g g' h := by
    rw [hR2, hB2]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs2 hR3sm h2.1 hR3mem
    calc Work.FTS.Nonlin.Xn α (P2 α g' h + R3)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P2 α g' h) + Work.FTS.Nonlin.Xn α R3) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B3 * TOf α g g' h) := by linarith [h2', hR3x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B3)) * TOf α g g' h := by ring
  have hR1sm : Work.FTS.EllipticEst.SmoothOpen R1 := by
    rw [hR1]; exact Work.FTS.NonlinRows.smoothOpen_add hs1 hR2sm
  have hR1mem : Work.Spaces.HkMem α 4 R1 := by
    rw [hR1]; exact Work.FTS.EllipticEst.HkMem_add_open hs1 hR2sm h1.1 hR2mem
  have hR1x : Work.FTS.Nonlin.Xn α R1 ≤ B1 * TOf α g g' h := by
    rw [hR1, hB1]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs1 hR2sm h1.1 hR2mem
    calc Work.FTS.Nonlin.Xn α (P1 α g h + R2)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P1 α g h) + Work.FTS.Nonlin.Xn α R2) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B2 * TOf α g g' h) := by linarith [h1', hR2x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B2)) * TOf α g g' h := by ring
  have hB1le : B1 ≤ 1024 * ksum α Ci CF Cdz Cw := by
    rw [hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8, hB9]
    nlinarith [hK0]
  have hR1eq : R1 = Rsum α g g' h := by
    rw [hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, Rsum]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hR1eq]; exact hR1mem
  · rw [← hR1eq]; exact hR1sm
  · rw [← hR1eq]
    exact le_trans hR1x (mul_le_mul_of_nonneg_right hB1le hT)

end Work.FTS.GalFields.RHS
