import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.Eisenstein_atZero
import Submission.Work.Asymptotics.norm_Eisenstein_imagAxis_atZero
import Submission.Work.Asymptotics.norm_theta_imagAxis_atZero
import Submission.Work.Asymptotics.norm_L_imagAxis_atZero

namespace Work.Asymptotics

set_option maxHeartbeats 1600000

open scoped MatrixGroups Manifold

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane

def M8mat (J : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![J, 0, 1; -2 * J, -2, 0; 1, 0, 0]

/-- The matrix `!![-3456,0,0; 0,1,-1; 0,1728-jτ,jτ]` of `Υ_-^{(8)}`. -/
def Mmmat (jτ : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-(2 * (1728 : ℂ)), 0, 0; 0, 1, -1; 0, (1728 : ℂ) - jτ, jτ]

/-- The column bounds `(2‖J‖+1, 2, 1)` for `M_+^{(8)}`. -/
def colP (J : ℂ) : Fin 3 → ℝ := ![2 * ‖J‖ + 1, 2, 1]

/-- The column bounds `(2·1728, 1729+‖jτ‖, 1+‖jτ‖)` for `M_-^{(8)}`. -/
def colM (jτ : ℂ) : Fin 3 → ℝ := ![(2 : ℝ) * 1728, 1729 + ‖jτ‖, 1 + ‖jτ‖]

/-! ## The entries of the cleared coefficient matrices -/

lemma UpsilonPlusClear_entry (τ z : UpperHalfPlane) (i j : Fin 3) :
    Work.Kernels.UpsilonPlusClear 8 τ z i j =
      ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ *
        (Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] i) τ) *
        M8mat (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) i j *
        Work.Kernels.fk (![12, 10, 8] j) z := by
  simp only [Work.Kernels.UpsilonPlusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, M8mat,
    if_true, Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  ring

lemma UpsilonMinusClear_entry (τ z : UpperHalfPlane) (i j : Fin 3) :
    Work.Kernels.UpsilonMinusClear 8 τ z i j =
      ((2 : ℂ) * (1728 : ℂ) * (Real.pi : ℂ))⁻¹ *
        (Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] i) τ) *
        Mmmat (Work.Kernels.jInvariantFun τ) i j *
        Work.Kernels.fk (![10, 8, 6] j) z := by
  simp only [Work.Kernels.UpsilonMinusClear, Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Mmmat,
    Work.Kernels.c1728, if_true, Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.of_apply]
  ring_nf

/-! ## Column bounds, and the values of `f_k` at the relevant integers -/

lemma M8mat_col0 (J : ℂ) : ∀ i : Fin 3, ‖M8mat J i 0‖ ≤ 2 * ‖J‖ + 1 := by
  intro i
  fin_cases i <;> norm_num [M8mat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val] <;> linarith [norm_nonneg J]

lemma M8mat_col1 (J : ℂ) : ∀ i : Fin 3, ‖M8mat J i 1‖ ≤ 2 := by
  intro i
  fin_cases i <;> norm_num [M8mat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val]

lemma M8mat_col2 (J : ℂ) : ∀ i : Fin 3, ‖M8mat J i 2‖ ≤ 1 := by
  intro i
  fin_cases i <;> norm_num [M8mat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val]

lemma Mmmat_col0 (jτ : ℂ) : ∀ i : Fin 3, ‖Mmmat jτ i 0‖ ≤ 2 * 1728 := by
  intro i
  fin_cases i <;> norm_num [Mmmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val]

lemma Mmmat_col1 (jτ : ℂ) : ∀ i : Fin 3, ‖Mmmat jτ i 1‖ ≤ 1729 + ‖jτ‖ := by
  intro i
  fin_cases i
  · norm_num [Mmmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]
    linarith [norm_nonneg jτ]
  · norm_num [Mmmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]
    linarith [norm_nonneg jτ]
  · norm_num [Mmmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]
    calc ‖(1728 : ℂ) - jτ‖ ≤ ‖(1728 : ℂ)‖ + ‖jτ‖ := norm_sub_le _ _
      _ = 1728 + ‖jτ‖ := by simp
      _ ≤ 1729 + ‖jτ‖ := by linarith

lemma Mmmat_col2 (jτ : ℂ) : ∀ i : Fin 3, ‖Mmmat jτ i 2‖ ≤ 1 + ‖jτ‖ := by
  intro i
  fin_cases i
  · norm_num [Mmmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]
    try linarith [norm_nonneg jτ]
  · norm_num [Mmmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]
    try linarith [norm_nonneg jτ]
  · norm_num [Mmmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]
    try linarith [norm_nonneg jτ]

lemma norm_M8mat_le_colP (J : ℂ) : ∀ i j : Fin 3, ‖M8mat J i j‖ ≤ colP J j := by
  intro i j
  fin_cases j
  · exact M8mat_col0 J i
  · exact M8mat_col1 J i
  · exact M8mat_col2 J i

lemma norm_Mmmat_le_colM (jτ : ℂ) : ∀ i j : Fin 3, ‖Mmmat jτ i j‖ ≤ colM jτ j := by
  intro i j
  fin_cases j
  · exact Mmmat_col0 jτ i
  · exact Mmmat_col1 jτ i
  · exact Mmmat_col2 jτ i

lemma fk_twelve (z : UpperHalfPlane) : Work.Kernels.fk (12 : ℤ) z = Work.Kernels.DeltaFun z := by
  simp [Work.Kernels.fk]
lemma fk_ten (z : UpperHalfPlane) : Work.Kernels.fk (10 : ℤ) z = Work.Kernels.E10Fun z := by
  simp [Work.Kernels.fk]
lemma fk_eight (z : UpperHalfPlane) : Work.Kernels.fk (8 : ℤ) z = Work.Kernels.E8Fun z := by
  simp [Work.Kernels.fk]
lemma fk_six (z : UpperHalfPlane) : Work.Kernels.fk (6 : ℤ) z = Work.Kernels.E6Fun z := by
  simp [Work.Kernels.fk]
lemma fk_four (z : UpperHalfPlane) : Work.Kernels.fk (4 : ℤ) z = Work.Kernels.E4Fun z := by
  simp [Work.Kernels.fk]
lemma fk_two (z : UpperHalfPlane) :
    Work.Kernels.fk (2 : ℤ) z = Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z := by
  simp [Work.Kernels.fk]
lemma fk_zero (z : UpperHalfPlane) : Work.Kernels.fk (0 : ℤ) z = 1 := by
  simp [Work.Kernels.fk]

lemma DeltaFun_mul_fk_two (τ : UpperHalfPlane) :
    Work.Kernels.DeltaFun τ * Work.Kernels.fk (2 : ℤ) τ = Work.Kernels.E14Fun τ := by
  rw [fk_two, mul_div_assoc']
  exact mul_div_cancel_left₀ (Work.Kernels.E14Fun τ)
    (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)

lemma DeltaFun_mul_fk_four (τ : UpperHalfPlane) :
    Work.Kernels.DeltaFun τ * Work.Kernels.fk (4 : ℤ) τ
      = Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ := by
  rw [fk_four]

lemma DeltaFun_mul_fk_six (τ : UpperHalfPlane) :
    Work.Kernels.DeltaFun τ * Work.Kernels.fk (6 : ℤ) τ
      = Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ := by
  rw [fk_six]

lemma DeltaFun_mul_fk_zero (τ : UpperHalfPlane) :
    Work.Kernels.DeltaFun τ * Work.Kernels.fk (0 : ℤ) τ = Work.Kernels.DeltaFun τ := by
  rw [fk_zero, mul_one]

/-! ## Evaluation of the vector indices and of the `col` bounds -/

lemma vec642_zero : ![6, 4, 2] (0 : Fin 3) = (6 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma vec642_one : ![6, 4, 2] (1 : Fin 3) = (4 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma vec642_two : ![6, 4, 2] (2 : Fin 3) = (2 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma vec128_zero : ![12, 10, 8] (0 : Fin 3) = (12 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma vec128_one : ![12, 10, 8] (1 : Fin 3) = (10 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma vec128_two : ![12, 10, 8] (2 : Fin 3) = (8 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma vec420_zero : ![4, 2, 0] (0 : Fin 3) = (4 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma vec420_one : ![4, 2, 0] (1 : Fin 3) = (2 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma vec420_two : ![4, 2, 0] (2 : Fin 3) = (0 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma vec1086_zero : ![10, 8, 6] (0 : Fin 3) = (10 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma vec1086_one : ![10, 8, 6] (1 : Fin 3) = (8 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma vec1086_two : ![10, 8, 6] (2 : Fin 3) = (6 : ℤ) := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]

lemma colP_zero (J : ℂ) : colP J 0 = 2 * ‖J‖ + 1 := by
  simp [colP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma colP_one (J : ℂ) : colP J 1 = 2 := by
  simp [colP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma colP_two (J : ℂ) : colP J 2 = 1 := by
  simp [colP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma colM_zero (jτ : ℂ) : colM jτ 0 = 2 * 1728 := by
  simp [colM, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma colM_one (jτ : ℂ) : colM jτ 1 = 1729 + ‖jτ‖ := by
  simp [colM, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]
lemma colM_two (jτ : ℂ) : colM jτ 2 = 1 + ‖jτ‖ := by
  simp [colM, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val]

lemma phitVec_zero (z : UpperHalfPlane) : Work.Kernels.phitVec z 0 = (z : ℂ) ^ 2 := rfl
lemma phitVec_one (z : UpperHalfPlane) :
    Work.Kernels.phitVec z 1 = (z : ℂ) ^ 2 * Work.Kernels.E2S z := rfl
lemma phitVec_two (z : UpperHalfPlane) :
    Work.Kernels.phitVec z 2 = (z : ℂ) ^ 2 * (Work.Kernels.E2S z) ^ 2 := rfl

lemma psitVec_zero (ℓ : Work.Kernels.LogLambdaData) (z : UpperHalfPlane) :
    Work.Kernels.psitVec ℓ z 0 = ℓ.L z := rfl
lemma psitVec_one (ℓ : Work.Kernels.LogLambdaData) (z : UpperHalfPlane) :
    Work.Kernels.psitVec ℓ z 1 = Work.Kernels.WFun z := rfl
lemma psitVec_two (ℓ : Work.Kernels.LogLambdaData) (z : UpperHalfPlane) :
    Work.Kernels.psitVec ℓ z 2 = Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2 := rfl

lemma imagAxis_coe (t : ℝ) (ht : 0 < t) :
    ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl

lemma norm_imagAxis (t : ℝ) (ht : 0 < t) :
    ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)‖ = t := by
  show ‖((t : ℂ) * Complex.I)‖ = t
  rw [norm_mul, Complex.norm_I, mul_one]
  have h : ‖((t : ℂ))‖ = |t| := RCLike.norm_ofReal t
  rw [h, abs_of_pos ht]

/-! ## Continuity of the building blocks and bounds on closed balls -/

private lemma continuous_jInvariantFun :
    Continuous (fun τ : UpperHalfPlane => Work.Kernels.jInvariantFun τ) := by
  have h4 : Continuous (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ) :=
    Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1.continuous
  have hΔ : Continuous (fun τ : UpperHalfPlane => Work.Kernels.DeltaFun τ) :=
    Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.continuous
  have h : Work.Kernels.jInvariantFun =
      fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ := by
    funext τ; rfl
  rw [h]
  exact (h4.pow 3).div hΔ (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)

lemma continuous_UFun : Continuous (fun τ : UpperHalfPlane => Work.Kernels.UFun τ) :=
  (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4

lemma continuous_WFun : Continuous (fun τ : UpperHalfPlane => Work.Kernels.WFun τ) :=
  (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4

lemma continuous_VFun : Continuous (fun τ : UpperHalfPlane => Work.Kernels.VFun τ) :=
  (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4

lemma continuous_xi2Fun : Continuous (fun τ : UpperHalfPlane => Work.Kernels.xi2Fun τ) := by
  have h : Work.Kernels.xi2Fun =
      fun τ : UpperHalfPlane => Work.Kernels.UFun τ + Work.Kernels.WFun τ := by
    funext τ; rfl
  rw [h]; exact continuous_UFun.add continuous_WFun

lemma continuous_psi2 (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : UpperHalfPlane => Work.Kernels.psi2 ℓ τ) := by
  have h : (fun τ : UpperHalfPlane => Work.Kernels.psi2 ℓ τ) =
      fun τ => Work.Kernels.xi2Fun τ * ℓ.L τ +
        (-(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) * ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi2Fun τ * ℓ.L τ +
        (SlashAction.map (2:ℤ) ModularGroup.S Work.Kernels.xi2Fun) τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi2Fun_slash_S τ]
  rw [h]
  exact (continuous_xi2Fun.mul ℓ.holo.continuous).add
    ((continuous_UFun.add continuous_VFun).neg.mul ℓ.holo_S.continuous)

lemma continuous_psi4 (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : UpperHalfPlane => Work.Kernels.psi4 ℓ τ) := by
  have hξ4 : Continuous (fun τ : UpperHalfPlane => Work.Kernels.xi4Fun τ) := by
    have h' : Work.Kernels.xi4Fun = fun τ : UpperHalfPlane =>
        Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2 := by
      funext τ; rfl
    rw [h']; exact ((continuous_UFun.pow 2).add (continuous_WFun.pow 2)).sub
      ((continuous_VFun.pow 2).const_mul 2)
  have h : (fun τ : UpperHalfPlane => Work.Kernels.psi4 ℓ τ) =
      fun τ => Work.Kernels.xi4Fun τ * ℓ.L τ +
        (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2) *
          ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi4Fun τ * ℓ.L τ +
        (SlashAction.map (4:ℤ) ModularGroup.S Work.Kernels.xi4Fun) τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi4S_apply τ]
  rw [h]
  exact (hξ4.mul ℓ.holo.continuous).add
    (((continuous_UFun.pow 2).add (continuous_VFun.pow 2)).sub
      ((continuous_WFun.pow 2).const_mul 2) |>.mul ℓ.holo_S.continuous)

/-- A continuous complex-valued function is bounded on a closed ball. -/
lemma bound_on_ball {τ₀ : UpperHalfPlane} {R : ℝ} {f : UpperHalfPlane → ℂ} (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → ‖f τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (x := τ₀) (r := R)).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun τ hτ => le_trans (hC τ hτ) (le_max_left _ _)⟩

/-- A continuous real-valued function is bounded above on a closed ball. -/
lemma bound_on_ball_real {τ₀ : UpperHalfPlane} {R : ℝ} {f : UpperHalfPlane → ℝ}
    (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → f τ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (x := τ₀) (r := R)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun τ hτ => ?_⟩
  have h := hC τ hτ
  rw [Real.norm_eq_abs] at h
  exact le_trans (le_abs_self _) (le_trans h (le_max_left _ _))

/-- The uniform lower bound `δ ≤ ‖Δ τ‖` on a closed ball, together with the uniform upper
bound `‖j τ‖ ≤ Aj` (the compactness input of both cusp estimates). -/
lemma exists_delta_Aj {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R) :
    ∃ δ Aj : ℝ, 0 < δ ∧ 0 ≤ Aj ∧
      (∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → δ ≤ ‖Work.Kernels.DeltaFun τ‖) ∧
      (∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → ‖Work.Kernels.jInvariantFun τ‖ ≤ Aj) := by
  obtain ⟨τm, hτm_mem, hτm_min⟩ :=
    (isCompact_closedBall (x := τ₀) (r := R)).exists_isMinOn
      ⟨τ₀, Metric.mem_closedBall_self hR.le⟩
      ((Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.continuous.norm).continuousOn)
  obtain ⟨Aj, hAj0, hAj⟩ := bound_on_ball (τ₀ := τ₀) (R := R) continuous_jInvariantFun
  exact ⟨‖Work.Kernels.DeltaFun τm‖, Aj,
    norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τm), hAj0,
    fun τ hτ => hτm_min hτ, hAj⟩

/-! ## Generic arithmetic helpers (kept as separate lemmas so that the big kernel terms
never enter the unification problems) -/

lemma mul_le_mul_three {a a' b b' c c' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (ha'0 : 0 ≤ a') (hb'0 : 0 ≤ b') :
    a * b * c ≤ a' * b' * c' :=
  mul_le_mul (mul_le_mul ha hb hb0 ha'0) hc hc0 (mul_nonneg ha'0 hb'0)

lemma mul_le_mul_four {a a' b b' c c' d d' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (hd : d ≤ d') (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (ha'0 : 0 ≤ a') (hb'0 : 0 ≤ b') (hc'0 : 0 ≤ c') :
    a * b * c * d ≤ a' * b' * c' * d' :=
  mul_le_mul (mul_le_mul_three ha hb hc hb0 hc0 ha'0 hb'0) hd hd0
    (mul_nonneg (mul_nonneg ha'0 hb'0) hc'0)

lemma norm_sub_ge_half {v w : ℂ} {c A t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (hw : c * Real.exp (2 * Real.pi / t) ≤ ‖w‖) (hv : ‖v‖ ≤ A)
    (hA : 2 * A ≤ c * Real.exp (2 * Real.pi / t)) :
    c / 2 * Real.exp (2 * Real.pi / t) ≤ ‖v - w‖ := by
  have h := norm_sub_norm_le w v
  rw [norm_sub_rev] at h
  have h2 : c / 2 * Real.exp (2 * Real.pi / t) ≤ c * Real.exp (2 * Real.pi / t) - A := by
    nlinarith [hA]
  linarith

lemma algebra_cancel {δ cΔ cj t : ℝ} (ht : 0 < t) :
    δ * cΔ * cj / 2 * (t ^ 12)⁻¹ =
      δ * (cΔ * (t ^ 12)⁻¹ * Real.exp (-(2 * Real.pi / t))) *
        (cj / 2 * Real.exp (2 * Real.pi / t)) := by
  rw [show Real.exp (2 * Real.pi / t) = (Real.exp (-(2 * Real.pi / t)))⁻¹ by
        rw [← Real.exp_neg]; ring_nf]
  field_simp

lemma inv_pow_le_inv_pow {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    (t ^ m)⁻¹ ≤ (t ^ n)⁻¹ := by
  have h : t ^ n ≤ t ^ m := pow_le_pow_of_le_one ht.le ht1 hmn
  have := one_div_le_one_div_of_le (a := t ^ n) (b := t ^ m) (pow_pos ht n) h
  simpa only [one_div] using this

lemma exp_neg_div_le_one {t : ℝ} (ht : 0 < t) :
    Real.exp (-(2 * Real.pi / t)) ≤ 1 :=
  Real.exp_le_one_iff.mpr (by
    have h : 0 < 2 * Real.pi / t := div_pos (by positivity) ht
    linarith)

lemma sum_fk642_eq (τ : UpperHalfPlane) :
    (∑ i : Fin 3, ‖Work.Kernels.phiVec τ i‖ *
        ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] i) τ‖) =
      ‖Work.Kernels.phiVec τ 0‖ * ‖Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ‖ +
      ‖Work.Kernels.phiVec τ 1‖ * ‖Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ‖ +
      ‖Work.Kernels.phiVec τ 2‖ * ‖Work.Kernels.E14Fun τ‖ := by
  rw [Fin.sum_univ_three, vec642_zero, vec642_one, vec642_two,
    DeltaFun_mul_fk_six, DeltaFun_mul_fk_four, DeltaFun_mul_fk_two]

lemma sum_fk420_eq (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    (∑ i : Fin 3, ‖Work.Kernels.psiVec ℓ τ i‖ *
        ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] i) τ‖) =
      ‖Work.Kernels.psiVec ℓ τ 0‖ * ‖Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ‖ +
      ‖Work.Kernels.psiVec ℓ τ 1‖ * ‖Work.Kernels.E14Fun τ‖ +
      ‖Work.Kernels.psiVec ℓ τ 2‖ * ‖Work.Kernels.DeltaFun τ‖ := by
  rw [Fin.sum_univ_three, vec420_zero, vec420_one, vec420_two,
    DeltaFun_mul_fk_four, DeltaFun_mul_fk_two, DeltaFun_mul_fk_zero]


lemma continuous_scale_kba : Continuous (fun τ : UpperHalfPlane => Work.Kernels.scale τ) := by
  have h : (fun τ : UpperHalfPlane => Work.Kernels.scale τ) =
      fun τ : UpperHalfPlane => 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := by
    funext τ; rfl
  rw [h]
  refine (continuous_const.add ?_).add ?_
  · exact UpperHalfPlane.continuous_im.inv₀ (fun τ => ne_of_gt τ.im_pos)
  · exact UpperHalfPlane.continuous_coe.norm

lemma scale_imagAxis (t : ℝ) (ht : 0 < t) :
    Work.Kernels.scale (Work.Kernels.imagAxis t ht) = 1 + t⁻¹ + t := by
  have h1 : (Work.Kernels.imagAxis t ht).im = t := by
    show ((t : ℂ) * Complex.I).im = t
    simp
  have h2 : ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)‖ = t := norm_imagAxis t ht
  simp only [Work.Kernels.scale, h1, h2]

lemma imagAxis_im (t : ℝ) (ht : 0 < t) : (Work.Kernels.imagAxis t ht).im = t := by
  show ((t : ℂ) * Complex.I).im = t
  simp

lemma norm_sub_ge_half' {v w : ℂ} {c A t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (hw : c * Real.exp (2 * Real.pi * t) ≤ ‖w‖) (hv : ‖v‖ ≤ A)
    (hA : 2 * A ≤ c * Real.exp (2 * Real.pi * t)) :
    c / 2 * Real.exp (2 * Real.pi * t) ≤ ‖v - w‖ := by
  have h := norm_sub_norm_le w v
  rw [norm_sub_rev] at h
  have h2 : c / 2 * Real.exp (2 * Real.pi * t) ≤ c * Real.exp (2 * Real.pi * t) - A := by
    nlinarith [hA]
  linarith


lemma UpsilonPlusClear_norm_le (τ z : UpperHalfPlane) (i j : Fin 3) :
    ‖Work.Kernels.UpsilonPlusClear 8 τ z i j‖ ≤
      ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹‖ *
        ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![6, 4, 2] i) τ‖ *
        colP (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) j *
        ‖Work.Kernels.fk (![12, 10, 8] j) z‖ := by
  rw [UpsilonPlusClear_entry, norm_mul, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_M8mat_le_colP _ i j) (by positivity)) (norm_nonneg _)

lemma UpsilonMinusClear_norm_le (τ z : UpperHalfPlane) (i j : Fin 3) :
    ‖Work.Kernels.UpsilonMinusClear 8 τ z i j‖ ≤
      ‖((2 : ℂ) * (1728 : ℂ) * (Real.pi : ℂ))⁻¹‖ *
        ‖Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4, 2, 0] i) τ‖ *
        colM (Work.Kernels.jInvariantFun τ) j *
        ‖Work.Kernels.fk (![10, 8, 6] j) z‖ := by
  rw [UpsilonMinusClear_entry, norm_mul, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_Mmmat_le_colM _ i j) (by positivity)) (norm_nonneg _)


/-! ## The kernel is bounded near the cusp `t → 0` -/

lemma continuous_E2Fun : Continuous (fun τ : UpperHalfPlane => Work.Kernels.E2Fun τ) :=
  Work.Kernels.ClassicalFacts.E2Fun_mem_InP.1.continuous

lemma continuous_E14Fun : Continuous (fun τ : UpperHalfPlane => Work.Kernels.E14Fun τ) := by
  have h : Work.Kernels.E14Fun =
      fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ := by
    funext τ; rfl
  rw [h]
  exact ((Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1.continuous).pow 2).mul
    Work.Kernels.ClassicalFacts.E6Fun_mem_InP.1.continuous

lemma continuous_phiVec0 : Continuous (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 0) := by
  have h : (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 0) = fun τ : UpperHalfPlane => (τ : ℂ) := by
    funext τ; rfl
  rw [h]; exact UpperHalfPlane.continuous_coe

lemma continuous_phiVec1 : Continuous (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 1) := by
  have h : (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 1) =
      fun τ : UpperHalfPlane => (τ : ℂ) * Work.Kernels.E2Fun τ - 3 * Complex.I / (Real.pi : ℂ) := by
    funext τ; rfl
  rw [h]
  exact (UpperHalfPlane.continuous_coe.mul continuous_E2Fun).sub continuous_const

lemma continuous_phiVec2 : Continuous (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 2) := by
  have h : (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 2) =
      fun τ : UpperHalfPlane => (τ : ℂ) * Work.Kernels.E2Fun τ ^ 2 -
        (6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun τ := by
    funext τ; rfl
  rw [h]
  exact (UpperHalfPlane.continuous_coe.mul (continuous_E2Fun.pow 2)).sub
    (continuous_const.mul continuous_E2Fun)

lemma continuous_psiVec0 (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : UpperHalfPlane => Work.Kernels.psiVec ℓ τ 0) := by
  have h : (fun τ : UpperHalfPlane => Work.Kernels.psiVec ℓ τ 0) = fun _ => (1 : ℂ) := by
    funext τ; rfl
  rw [h]; exact continuous_const

lemma continuous_psiVec1 (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : UpperHalfPlane => Work.Kernels.psiVec ℓ τ 1) := by
  have h : (fun τ : UpperHalfPlane => Work.Kernels.psiVec ℓ τ 1) =
      fun τ => Work.Kernels.psi2 ℓ τ := by funext τ; rfl
  rw [h]; exact continuous_psi2 ℓ

lemma continuous_psiVec2 (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : UpperHalfPlane => Work.Kernels.psiVec ℓ τ 2) := by
  have h : (fun τ : UpperHalfPlane => Work.Kernels.psiVec ℓ τ 2) =
      fun τ => Work.Kernels.psi4 ℓ τ := by funext τ; rfl
  rw [h]; exact continuous_psi4 ℓ


end

end Work.Asymptotics
