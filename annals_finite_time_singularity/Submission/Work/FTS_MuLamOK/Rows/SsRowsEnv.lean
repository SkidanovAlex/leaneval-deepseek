import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.Rl1.ssBounds
import Submission.Work.FTS.NonlinRows.Rl1.tools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLamOK.Rows

theorem SsRowsEnv (Cs : ℝ) : ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f Φs : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.VocabO.StarPkgo α Cs Φs →
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1ss α Φs)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2ss α Φs)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3ss α Φs)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4ss α)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5ss α)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) := by
  -- The five `ss` pieces do not involve the datum, so no `GalClass`/`HkMem` hypothesis is
  -- needed: only the pointwise bounds `Rl1.ss_N1_pt … ss_N5_pt`, the abstract `r`-step
  -- `rl1Pieces.rowStep` and the `𝒰(Φ̃_*)`-bound `Rl1.starUopBound`.  The five constants
  -- `480·max Cs 0`, `320·CU·max Cs 0`, `480·max Cs 0`, `160`, `480` (at `α²`, resp. `α³ ≤ α²`)
  -- are all `≤ (480 + 320·CU)·(1 + max Cs 0) =: K`, and `α² ≤ Env α f` always.
  obtain ⟨CU, hCUpos, hCUb⟩ := Work.FTS.NonlinRows.Rl1.starUopBound
  have hCU0 : (0 : ℝ) ≤ CU := hCUpos.le
  have hm : (0 : ℝ) ≤ max Cs 0 := le_max_right Cs 0
  have h1m : (0 : ℝ) ≤ 1 + max Cs 0 := by linarith
  refine ⟨(480 + 320 * CU) * (1 + max Cs 0),
    mul_pos (by linarith) (by linarith), ?_⟩
  intro α f Φs hα hα1 hs
  have hKnn : (0 : ℝ) ≤ (480 + 320 * CU) * (1 + max Cs 0) :=
    mul_nonneg (by linarith) h1m
  -- `α² ≤ Env α f`
  have hEnv : α ^ 2 ≤ Work.FTS.NonlinRows.Rl1.Env α f := by
    rw [Work.FTS.NonlinRows.Rl1.Env]
    have h1 : (0 : ℝ) ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α f :=
      mul_nonneg (Real.sqrt_nonneg α) (Work.Spaces.HkNorm_nonneg α 4 f)
    have h2 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
    linarith
  have hα3 : α ^ 3 ≤ α ^ 2 := pow_le_pow_of_le_one hα.le hα1 (by norm_num : 2 ≤ 3)
  -- the two generic comparisons `C·α² ≤ K·Env`, `C·α³ ≤ K·Env`
  have key : ∀ {C : ℝ}, 0 ≤ C → C ≤ (480 + 320 * CU) * (1 + max Cs 0) →
      C * α ^ 2 ≤ (480 + 320 * CU) * (1 + max Cs 0)
        * Work.FTS.NonlinRows.Rl1.Env α f := by
    intro C _ hCle
    have h1 : C * α ^ 2 ≤ (480 + 320 * CU) * (1 + max Cs 0) * α ^ 2 :=
      mul_le_mul_of_nonneg_right hCle (sq_nonneg α)
    have h2 : (480 + 320 * CU) * (1 + max Cs 0) * α ^ 2
        ≤ (480 + 320 * CU) * (1 + max Cs 0) * Work.FTS.NonlinRows.Rl1.Env α f :=
      mul_le_mul_of_nonneg_left hEnv hKnn
    linarith
  have key3 : ∀ {C : ℝ}, 0 ≤ C → C ≤ (480 + 320 * CU) * (1 + max Cs 0) →
      C * α ^ 3 ≤ (480 + 320 * CU) * (1 + max Cs 0)
        * Work.FTS.NonlinRows.Rl1.Env α f := by
    intro C _ hCle
    have h1 : C * α ^ 3 ≤ (480 + 320 * CU) * (1 + max Cs 0) * α ^ 3 :=
      mul_le_mul_of_nonneg_right hCle (pow_nonneg hα.le 3)
    have h2 : (480 + 320 * CU) * (1 + max Cs 0) * α ^ 3
        ≤ (480 + 320 * CU) * (1 + max Cs 0) * α ^ 2 :=
      mul_le_mul_of_nonneg_left hα3 hKnn
    have h3 : (480 + 320 * CU) * (1 + max Cs 0) * α ^ 2
        ≤ (480 + 320 * CU) * (1 + max Cs 0) * Work.FTS.NonlinRows.Rl1.Env α f :=
      mul_le_mul_of_nonneg_left hEnv hKnn
    linarith
  -- coefficient comparisons
  have hcoef1 : (480 : ℝ) * max Cs 0 ≤ (480 + 320 * CU) * (1 + max Cs 0) :=
    mul_le_mul (by linarith) (by linarith) hm (by linarith)
  have hcoef2 : (320 : ℝ) * CU * max Cs 0 ≤ (480 + 320 * CU) * (1 + max Cs 0) := by
    have h1 : (320 : ℝ) * CU ≤ 480 + 320 * CU := by linarith
    have h2' : (320 : ℝ) * CU * max Cs 0 ≤ (320 * CU) * (1 + max Cs 0) :=
      mul_le_mul_of_nonneg_left (by linarith : max Cs 0 ≤ 1 + max Cs 0)
        (by linarith : (0 : ℝ) ≤ 320 * CU)
    have h3 : (320 : ℝ) * CU * (1 + max Cs 0)
        ≤ (480 + 320 * CU) * (1 + max Cs 0) :=
      mul_le_mul_of_nonneg_right h1 h1m
    linarith
  have hcoef4 : (160 : ℝ) ≤ (480 + 320 * CU) * (1 + max Cs 0) := by
    have h1 : (160 : ℝ) ≤ 480 + 320 * CU := by linarith
    have h2 : (160 : ℝ) * 1 ≤ 160 * (1 + max Cs 0) :=
      mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 1 + max Cs 0) (by norm_num)
    have h3 : (160 : ℝ) * (1 + max Cs 0) ≤ (480 + 320 * CU) * (1 + max Cs 0) :=
      mul_le_mul_of_nonneg_right h1 h1m
    linarith
  have hcoef5 : (480 : ℝ) ≤ (480 + 320 * CU) * (1 + max Cs 0) := by
    have h1 : (480 : ℝ) ≤ 480 + 320 * CU := by linarith
    have h2 : (480 : ℝ) * 1 ≤ 480 * (1 + max Cs 0) :=
      mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 1 + max Cs 0) (by norm_num)
    have h3 : (480 : ℝ) * (1 + max Cs 0) ≤ (480 + 320 * CU) * (1 + max Cs 0) :=
      mul_le_mul_of_nonneg_right h1 h1m
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `N₁^{ss} = 2ℛ(Φ̃_*)F_*`
    have hC1 : (0 : ℝ) ≤ 120 * max Cs 0 * α ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hm) (sq_nonneg α)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N1ss α Φs) (C := 120 * max Cs 0 * α ^ 2) hC1
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => Work.FTS.NonlinRows.Rl1.ss_N1_pt hα hα1 hs r hr θ hθ))
    have h1 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1ss α Φs)
        ≤ ENNReal.ofReal (4 * (120 * max Cs 0 * α ^ 2)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have he : (4 : ℝ) * (120 * max Cs 0 * α ^ 2) = 480 * max Cs 0 * α ^ 2 := by ring
    rw [he]
    exact key (mul_nonneg (by norm_num) hm) hcoef1
  · -- `N₂^{ss} = -2𝒰(Φ̃_*)∂_θF_*`
    have hMU : (0 : ℝ) ≤ CU * max Cs 0 * α :=
      mul_nonneg (mul_nonneg hCU0 hm) hα.le
    have hU : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
        |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
          ≤ CU * max Cs 0 * α :=
      fun z θ hz hθI => hCUb (α := α) (Cs := Cs) (Φs := Φs) hα hα1 hs z hz θ hθI
    have hC2 : (0 : ℝ) ≤ 80 * (CU * max Cs 0 * α) * α ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hMU) (sq_nonneg α)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N2ss α Φs) (C := 80 * (CU * max Cs 0 * α) * α ^ 2) hC2
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => Work.FTS.NonlinRows.Rl1.ss_N2_pt (Cs := Cs) hα hα1 hMU hU r hr θ hθ))
    have h2 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2ss α Φs)
        ≤ ENNReal.ofReal (4 * (80 * (CU * max Cs 0 * α) * α ^ 2)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    have he : (4 : ℝ) * (80 * (CU * max Cs 0 * α) * α ^ 2)
        = 320 * CU * max Cs 0 * α ^ 3 := by ring
    rw [he]
    exact key3 (mul_nonneg (mul_nonneg (by norm_num) hCU0) hm) hcoef2
  · -- `N₃^{ss} = -2α𝒱(Φ̃_*)D_zF_*`
    have hC3 : (0 : ℝ) ≤ 120 * max Cs 0 * α ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) hm) (pow_nonneg hα.le 3)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N3ss α Φs) (C := 120 * max Cs 0 * α ^ 3) hC3
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => Work.FTS.NonlinRows.Rl1.ss_N3_pt hα hα1 hs r hr θ hθ))
    have h3 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3ss α Φs)
        ≤ ENNReal.ofReal (4 * (120 * max Cs 0 * α ^ 3)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
    have he : (4 : ℝ) * (120 * max Cs 0 * α ^ 3) = 480 * max Cs 0 * α ^ 3 := by ring
    rw [he]
    exact key3 (mul_nonneg (by norm_num) hm) hcoef1
  · -- `N₄^{ss} = -(1/2)sin2θ FK(F_*) ∂_θF_*`
    have hC4 : (0 : ℝ) ≤ 40 * α ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hα.le 3)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N4ss α) (C := 40 * α ^ 3) hC4
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => Work.FTS.NonlinRows.Rl1.ss_N4_pt hα hα1 r hr θ hθ))
    have h4 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4ss α)
        ≤ ENNReal.ofReal (4 * (40 * α ^ 3)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h4.trans (ENNReal.ofReal_le_ofReal ?_)
    have he : (4 : ℝ) * (40 * α ^ 3) = 160 * α ^ 3 := by ring
    rw [he]
    exact key3 (by norm_num) hcoef4
  · -- `N₅^{ss} = -sin²θ FK(F_*) F_*`
    have hC5 : (0 : ℝ) ≤ 120 * α ^ 2 := mul_nonneg (by norm_num) (sq_nonneg α)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N5ss α) (C := 120 * α ^ 2) hC5
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => Work.FTS.NonlinRows.Rl1.ss_N5_pt hα hα1 r hr θ hθ))
    have h5 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5ss α)
        ≤ ENNReal.ofReal (4 * (120 * α ^ 2)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h5.trans (ENNReal.ofReal_le_ofReal ?_)
    have he : (4 : ℝ) * (120 * α ^ 2) = 480 * α ^ 2 := by ring
    rw [he]
    exact key (by norm_num) hcoef5

end Work.FTS_MuLamOK.Rows
