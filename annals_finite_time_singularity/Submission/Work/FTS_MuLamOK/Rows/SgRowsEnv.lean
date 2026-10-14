import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.sg_open
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS_MuLamOK.Rows

set_option maxHeartbeats 1600000

theorem SgRowsEnv (Cs : ℝ) : ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f Φs : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.VocabO.StarPkgo α Cs Φs →
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1sg α Φs f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2sg α Φs f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3sg α Φs f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) := by
  obtain ⟨CU, hCUpos, hCUb⟩ := Work.FTS.NonlinRows.Rl1.starUopBound
  have hCU0 : 0 ≤ CU := hCUpos.le
  have hP0 : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  have hM0 : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hMC0 : 0 ≤ max Cs 0 + max Cs 0 * CU := by
    have := mul_nonneg hM0 hCU0
    linarith
  set Kc : ℝ := 1 + 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU) with hKcdef
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    nlinarith [hP0, hMC0]
  have hKc0 : 0 ≤ Kc := hKcpos.le
  have hbig : 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU) ≤ Kc := by
    rw [hKcdef]; linarith
  -- ## elementary arithmetic: an `α`-linear coefficient `c ≤ 12·A` is absorbed
  have hcoef : ∀ c : ℝ, 0 ≤ c → c ≤ 12 * (max Cs 0 + max Cs 0 * CU) →
      c * Real.sqrt (Real.pi / 2) ≤ 12 * Real.sqrt (Real.pi / 2)
        * (max Cs 0 + max Cs 0 * CU) := by
    intro c _hc0 hcle
    calc c * Real.sqrt (Real.pi / 2)
        ≤ 12 * (max Cs 0 + max Cs 0 * CU) * Real.sqrt (Real.pi / 2) :=
          mul_le_mul_of_nonneg_right hcle hP0
      _ = 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU) := by ring
  have h6 : (6 : ℝ) * max Cs 0 ≤ 12 * (max Cs 0 + max Cs 0 * CU) := by
    nlinarith [hM0, hCU0, mul_nonneg hM0 hCU0]
  have h3 : 3 * CU * max Cs 0 ≤ 12 * (max Cs 0 + max Cs 0 * CU) := by
    nlinarith [hM0, hCU0, mul_nonneg hM0 hCU0]
  refine ⟨Kc, hKcpos, ?_⟩
  intro α f Φs hα hα1 hso hmem hStar
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  -- ## `α^k·|f| ≤ Env α f` for `k = 1, 2`
  have hαle : α ≤ Real.sqrt α := by
    have hα2 : α ^ 2 ≤ α := by nlinarith [hα.le, hα1]
    calc α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα.le).symm
      _ ≤ Real.sqrt α := Real.sqrt_le_sqrt hα2
  have hαX : α * Work.FTS.Nonlin.Xn α f ≤ Work.FTS.NonlinRows.Rl1.Env α f := by
    have h1 : α * Work.FTS.Nonlin.Xn α f
        ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α f :=
      mul_le_mul_of_nonneg_right hαle hX0
    have h2 : Real.sqrt α * Work.FTS.Nonlin.Xn α f
        ≤ Work.FTS.NonlinRows.Rl1.Env α f := by
      rw [Work.FTS.NonlinRows.Rl1.Env]
      have h3' : 0 ≤ α ^ 2 := sq_nonneg α
      have h4 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
      linarith
    exact h1.trans h2
  have hα2X : α ^ 2 * Work.FTS.Nonlin.Xn α f ≤ Work.FTS.NonlinRows.Rl1.Env α f := by
    have h1 : α ^ 2 * Work.FTS.Nonlin.Xn α f ≤ α * Work.FTS.Nonlin.Xn α f := by
      refine mul_le_mul_of_nonneg_right ?_ hX0
      nlinarith [hα.le, hα1]
    exact h1.trans hαX
  have keyA : ∀ c : ℝ, 0 ≤ c → c ≤ 12 * (max Cs 0 + max Cs 0 * CU) →
      c * α * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f
        ≤ Kc * Work.FTS.NonlinRows.Rl1.Env α f := by
    intro c hc0 hcle
    have h1 := hcoef c hc0 hcle
    calc c * α * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f
        = (c * Real.sqrt (Real.pi / 2)) * (α * Work.FTS.Nonlin.Xn α f) := by ring
      _ ≤ (12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU))
            * (α * Work.FTS.Nonlin.Xn α f) :=
          mul_le_mul h1 le_rfl (mul_nonneg hα.le hX0) (by positivity)
      _ ≤ Kc * Work.FTS.NonlinRows.Rl1.Env α f :=
          mul_le_mul hbig hαX (mul_nonneg hα.le hX0) hKc0
  have keyB : ∀ c : ℝ, 0 ≤ c → c ≤ 12 * (max Cs 0 + max Cs 0 * CU) →
      c * α ^ 2 * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f
        ≤ Kc * Work.FTS.NonlinRows.Rl1.Env α f := by
    intro c hc0 hcle
    have h1 := hcoef c hc0 hcle
    calc c * α ^ 2 * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f
        = (c * Real.sqrt (Real.pi / 2)) * (α ^ 2 * Work.FTS.Nonlin.Xn α f) := by ring
      _ ≤ (12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU))
            * (α ^ 2 * Work.FTS.Nonlin.Xn α f) :=
          mul_le_mul h1 le_rfl (mul_nonneg (sq_nonneg α) hX0) (by positivity)
      _ ≤ Kc * Work.FTS.NonlinRows.Rl1.Env α f :=
          mul_le_mul hbig hα2X (mul_nonneg (sq_nonneg α) hX0) hKc0
  -- ## the three rows
  refine ⟨?_, ?_, ?_⟩
  · refine (Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.row1sg_open
        (Cs := Cs) (f := f) (Φs := Φs) hα hso hmem hStar).trans
      (ENNReal.ofReal_le_ofReal (keyA (6 * max Cs 0) (mul_nonneg (by norm_num) hM0) h6))
  · refine (Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.row2sg_open (α := α)
        (MU := CU * max Cs 0 * α) (f := f) (Φs := Φs) hα hα1
        (mul_nonneg (mul_nonneg hCU0 hM0) hα.le)
        (fun z θ hz hθ => hCUb hα hα1 hStar z hz θ hθ) hso hmem).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [show 3 * (CU * max Cs 0 * α) * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f
        = (3 * CU * max Cs 0) * α * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f
        from by ring]
    exact keyA (3 * CU * max Cs 0) (mul_nonneg (mul_nonneg (by norm_num) hCU0) hM0) h3
  · refine (Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.row3sg_open
        (Cs := Cs) (f := f) (Φs := Φs) hα hso hmem hStar).trans
      (ENNReal.ofReal_le_ofReal (keyB (6 * max Cs 0) (mul_nonneg (by norm_num) hM0) h6))

end Work.FTS_MuLamOK.Rows

end
