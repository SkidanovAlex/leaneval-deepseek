import Mathlib
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.cuspAtomLimits

set_option linter.unusedVariables false

/-!
# The uniform cusp bound for the `K_-` numerator

This module is import-compatible with `Submission.Work.Asymptotics.KPlusXiDefs` (it does not
import `Submission.Work.Asymptotics.KMinusCuspBallBound` or
`Submission.Work.Asymptotics.KernelBoundAux`); the only external ingredients are the cusp
estimates of `Submission.Work.Asymptotics.KMinusCuspBallLimit`, the atoms of
`Submission.Work.Asymptotics.cuspAtomLimits` and the definition of `Ncusp` in
`Submission.Work.Asymptotics.KMinusCuspBallDefs`.
-/

namespace Work.Asymptotics

open UpperHalfPlane

set_option maxHeartbeats 1600000

noncomputable section

/-! ## Uniform cusp estimates with explicit constants

`Work.Asymptotics.CuspEst f k` (from `KMinusCuspBallLimit`) records that
`‖f z‖ ≤ C * tpar z ^ k` for all large `Im z`, with an unspecified constant `C`.  For the
contour argument on a compact `K ⊆ 𝒟` the constant must be bounded uniformly over `τ` in a
closed ball, so we carry the constants explicitly in `CuspEstU`: the estimate
`CuspEstU S F k H C` says `‖F τ z‖ ≤ C * tpar z ^ k` for every `τ ∈ S` and every `z` with
`H ≤ z.im`, with a single pair `(H, C)`.

The `z`-dependence of `Ncusp` is a combination of the cusp atoms, whose estimates for fixed `τ`
are already proved (`CuspEstU.ofCuspEst` turns those into uniform ones, since they do not
depend on `τ`); the only `τ`-dependence is through the coefficients `Alpha ℓ d i τ` and
`j(τ)`, which are bounded on a closed ball by continuity (`alpha_j_closedBall_bound`). -/

/-- `CuspEstU S F k H C`: `‖F τ z‖ ≤ C * tpar z ^ k` for all `τ ∈ S` and all `z` with
`H ≤ z.im`. -/
def CuspEstU (S : Set ℍ) (F : ℍ → ℍ → ℂ) (k : ℕ) (H C : ℝ) : Prop :=
  0 < C ∧ ∀ τ ∈ S, ∀ z : ℍ, H ≤ z.im → ‖F τ z‖ ≤ C * Work.Residues.tpar z ^ k

lemma CuspEstU.mono_exp {S : Set ℍ} {F : ℍ → ℍ → ℂ} {k k' : ℕ} (hk : k' ≤ k) {H C : ℝ}
    (h : CuspEstU S F k H C) : CuspEstU S F k' H C := by
  obtain ⟨hC, hb⟩ := h
  refine ⟨hC, fun τ hτ z hz => ?_⟩
  refine le_trans (hb τ hτ z hz) (mul_le_mul_of_nonneg_left ?_ hC.le)
  exact pow_le_pow_of_le_one (Work.Residues.tpar_nonneg z) (Work.Residues.tpar_le_one z) hk

lemma CuspEstU.congr {S : Set ℍ} {F G : ℍ → ℍ → ℂ} {k : ℕ} {H C : ℝ}
    (h : ∀ τ z : ℍ, F τ z = G τ z) (hF : CuspEstU S F k H C) : CuspEstU S G k H C := by
  obtain ⟨hC, hb⟩ := hF
  exact ⟨hC, fun τ hτ z hz => by rw [← h τ z]; exact hb τ hτ z hz⟩

lemma CuspEstU.add {S : Set ℍ} {F G : ℍ → ℍ → ℂ} {k : ℕ} {H₁ C₁ H₂ C₂ : ℝ}
    (h₁ : CuspEstU S F k H₁ C₁) (h₂ : CuspEstU S G k H₂ C₂) :
    CuspEstU S (fun τ z => F τ z + G τ z) k (max H₁ H₂) (C₁ + C₂) := by
  obtain ⟨hC₁, hb₁⟩ := h₁
  obtain ⟨hC₂, hb₂⟩ := h₂
  refine ⟨by linarith, fun τ hτ z hz => ?_⟩
  have hz₁ : H₁ ≤ z.im := le_trans (le_max_left _ _) hz
  have hz₂ : H₂ ≤ z.im := le_trans (le_max_right _ _) hz
  have ht : (0 : ℝ) ≤ Work.Residues.tpar z ^ k := pow_nonneg (Work.Residues.tpar_nonneg z) k
  calc ‖F τ z + G τ z‖ ≤ ‖F τ z‖ + ‖G τ z‖ := norm_add_le _ _
    _ ≤ C₁ * Work.Residues.tpar z ^ k + C₂ * Work.Residues.tpar z ^ k :=
        add_le_add (hb₁ τ hτ z hz₁) (hb₂ τ hτ z hz₂)
    _ = (C₁ + C₂) * Work.Residues.tpar z ^ k := by ring

lemma CuspEstU.neg {S : Set ℍ} {F : ℍ → ℍ → ℂ} {k : ℕ} {H C : ℝ}
    (h : CuspEstU S F k H C) : CuspEstU S (fun τ z => -F τ z) k H C := by
  obtain ⟨hC, hb⟩ := h
  exact ⟨hC, fun τ hτ z hz => by rw [norm_neg]; exact hb τ hτ z hz⟩

lemma CuspEstU.sub {S : Set ℍ} {F G : ℍ → ℍ → ℂ} {k : ℕ} {H₁ C₁ H₂ C₂ : ℝ}
    (h₁ : CuspEstU S F k H₁ C₁) (h₂ : CuspEstU S G k H₂ C₂) :
    CuspEstU S (fun τ z => F τ z - G τ z) k (max H₁ H₂) (C₁ + C₂) :=
  (h₁.add h₂.neg).congr (fun _ _ => by ring)

lemma CuspEstU.mul {S : Set ℍ} {F G : ℍ → ℍ → ℂ} {k₁ k₂ : ℕ} {H₁ C₁ H₂ C₂ : ℝ}
    (h₁ : CuspEstU S F k₁ H₁ C₁) (h₂ : CuspEstU S G k₂ H₂ C₂) :
    CuspEstU S (fun τ z => F τ z * G τ z) (k₁ + k₂) (max H₁ H₂) (C₁ * C₂) := by
  obtain ⟨hC₁, hb₁⟩ := h₁
  obtain ⟨hC₂, hb₂⟩ := h₂
  refine ⟨mul_pos hC₁ hC₂, fun τ hτ z hz => ?_⟩
  have hz₁ : H₁ ≤ z.im := le_trans (le_max_left _ _) hz
  have hz₂ : H₂ ≤ z.im := le_trans (le_max_right _ _) hz
  have ht₁ : (0 : ℝ) ≤ Work.Residues.tpar z ^ k₁ := pow_nonneg (Work.Residues.tpar_nonneg z) k₁
  calc ‖F τ z * G τ z‖ = ‖F τ z‖ * ‖G τ z‖ := norm_mul _ _
    _ ≤ (C₁ * Work.Residues.tpar z ^ k₁) * (C₂ * Work.Residues.tpar z ^ k₂) :=
        mul_le_mul (hb₁ τ hτ z hz₁) (hb₂ τ hτ z hz₂) (norm_nonneg _) (mul_nonneg hC₁.le ht₁)
    _ = (C₁ * C₂) * Work.Residues.tpar z ^ (k₁ + k₂) := by ring

/-- Multiplication by a coefficient function bounded on `S`. -/
lemma CuspEstU.constmul {S : Set ℍ} {c : ℍ → ℂ} {B : ℝ} {F : ℍ → ℍ → ℂ} {k : ℕ} {H C : ℝ}
    (hc : ∀ τ ∈ S, ‖c τ‖ ≤ B) (hB : 0 ≤ B) (h : CuspEstU S F k H C) :
    CuspEstU S (fun τ z => c τ * F τ z) k H ((B + 1) * C) := by
  obtain ⟨hC, hb⟩ := h
  refine ⟨by positivity, fun τ hτ z hz => ?_⟩
  rw [norm_mul]
  have ht : (0 : ℝ) ≤ Work.Residues.tpar z ^ k := pow_nonneg (Work.Residues.tpar_nonneg z) k
  calc ‖c τ‖ * ‖F τ z‖ ≤ B * (C * Work.Residues.tpar z ^ k) :=
        mul_le_mul (hc τ hτ) (hb τ hτ z hz) (norm_nonneg _) hB
    _ ≤ (B + 1) * C * Work.Residues.tpar z ^ k := by nlinarith [ht, hC.le, hB]

/-- A constant coefficient, with exponent `0`. -/
lemma CuspEstU.const (S : Set ℍ) (c : ℂ) {H : ℝ} :
    CuspEstU S (fun _ _ : ℍ => c) 0 H (‖c‖ + 1) :=
  ⟨by positivity, fun τ _ z _ => by
    have h1 : ‖((fun _ _ : ℍ => c) τ z)‖ = ‖c‖ := rfl
    simp only [pow_zero, mul_one]
    rw [h1]
    linarith [norm_nonneg c]⟩

/-- The `τ`-fixed cusp estimates for functions independent of `τ` are uniform. -/
lemma CuspEstU.ofCuspEst {S : Set ℍ} {f : ℍ → ℂ} {k : ℕ} (h : CuspEst f k) :
    ∃ H C : ℝ, CuspEstU S (fun _ z => f z) k H C := by
  obtain ⟨H, C, hC, hb⟩ := h
  exact ⟨H, C, hC, fun _ _ z hz => hb z hz⟩

/-! ## Boundedness on a closed ball -/

/-- A continuous function is bounded on a closed ball. -/
lemma bound_closedBall_of_continuous {f : ℍ → ℂ} (hf : Continuous f) (τ₀ : ℍ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, dist τ τ₀ ≤ R → ‖f τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall τ₀ R).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max C 0 + 1, by positivity, fun τ hτ =>
    le_trans (hC τ hτ) (by linarith [le_max_left C (0 : ℝ)])⟩

lemma continuous_UFun_ub : Continuous (fun τ : ℍ => Work.Kernels.UFun τ) :=
  (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4

lemma continuous_WFun_ub : Continuous (fun τ : ℍ => Work.Kernels.WFun τ) :=
  (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4

lemma continuous_VFun_ub : Continuous (fun τ : ℍ => Work.Kernels.VFun τ) :=
  (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4

lemma continuous_xi2Fun_ub : Continuous (fun τ : ℍ => Work.Kernels.xi2Fun τ) := by
  have h : Work.Kernels.xi2Fun = fun τ : ℍ => Work.Kernels.UFun τ + Work.Kernels.WFun τ := rfl
  rw [h]; exact continuous_UFun_ub.add continuous_WFun_ub

lemma continuous_xi4Fun_ub : Continuous (fun τ : ℍ => Work.Kernels.xi4Fun τ) := by
  have h : Work.Kernels.xi4Fun = fun τ : ℍ =>
      Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2 := rfl
  rw [h]
  exact ((continuous_UFun_ub.pow 2).add (continuous_WFun_ub.pow 2)).sub
    ((continuous_VFun_ub.pow 2).const_mul 2)

lemma continuous_psi2_ub (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) := by
  have h : (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) = fun τ : ℍ =>
      Work.Kernels.xi2Fun τ * ℓ.L τ +
        (-(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) * ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi2Fun τ * ℓ.L τ +
        (SlashAction.map (2 : ℤ) ModularGroup.S Work.Kernels.xi2Fun) τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi2Fun_slash_S τ]
  rw [h]
  exact (continuous_xi2Fun_ub.mul ℓ.holo.continuous).add
    (((continuous_UFun_ub.add continuous_VFun_ub).neg).mul ℓ.holo_S.continuous)

lemma continuous_psi4_ub (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) := by
  have h : (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) = fun τ : ℍ =>
      Work.Kernels.xi4Fun τ * ℓ.L τ +
        (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 -
          2 * Work.Kernels.WFun τ ^ 2) * ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi4Fun τ * ℓ.L τ +
        (SlashAction.map (4 : ℤ) ModularGroup.S Work.Kernels.xi4Fun) τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi4S_apply τ]
  rw [h]
  exact (continuous_xi4Fun_ub.mul ℓ.holo.continuous).add
    ((((continuous_UFun_ub.pow 2).add (continuous_VFun_ub.pow 2)).sub
      ((continuous_WFun_ub.pow 2).const_mul 2)).mul ℓ.holo_S.continuous)

lemma continuous_E4Fun_ub : Continuous (fun τ : ℍ => Work.Kernels.E4Fun τ) :=
  (ModularForm.holo' ModularForm.E₄).continuous

lemma continuous_E6Fun_ub : Continuous (fun τ : ℍ => Work.Kernels.E6Fun τ) :=
  (ModularForm.holo' ModularForm.E₆).continuous

lemma continuous_DeltaFun_ub : Continuous (fun τ : ℍ => Work.Kernels.DeltaFun τ) :=
  (CuspForm.holo' CuspForm.discriminant).continuous

lemma continuous_jInvariantFun_ub : Continuous (fun τ : ℍ => Work.Kernels.jInvariantFun τ) :=
  ((continuous_E4Fun_ub.pow 3).div continuous_DeltaFun_ub
    (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ))

lemma continuous_fk_two_ub : Continuous (fun τ : ℍ => Work.Kernels.fk 2 τ) := by
  have h : (fun τ : ℍ => Work.Kernels.fk 2 τ) = fun τ : ℍ =>
      Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ := by
    funext τ; rw [fk_two_eq]
  rw [h]
  exact ((continuous_E4Fun_ub.pow 2).mul continuous_E6Fun_ub).div continuous_DeltaFun_ub
    (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)

/-- The coordinates of `ψ⃗` are bounded on a closed ball. -/
lemma psiVec_closedBall_bound (ℓ : Work.Kernels.LogLambdaData) (τ₀ : ℍ) (R : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ τ : ℍ, dist τ τ₀ ≤ R → ∀ i : Fin 3,
      ‖Work.Kernels.psiVec ℓ τ i‖ ≤ B := by
  obtain ⟨B2, hB2, h2⟩ := bound_closedBall_of_continuous (continuous_psi2_ub ℓ) τ₀ R
  obtain ⟨B4, hB4, h4⟩ := bound_closedBall_of_continuous (continuous_psi4_ub ℓ) τ₀ R
  refine ⟨max 1 (max B2 B4), lt_of_lt_of_le one_pos (le_max_left _ _), fun τ hτ i => ?_⟩
  fin_cases i
  · simp only [Work.Kernels.psiVec]
    exact le_trans (le_of_eq (norm_one)) (le_max_left _ _)
  · simp only [Work.Kernels.psiVec]
    exact le_trans (h2 τ hτ) (le_trans (le_max_left B2 B4) (le_max_right 1 (max B2 B4)))
  · simp only [Work.Kernels.psiVec]
    exact le_trans (h4 τ hτ) (le_trans (le_max_right B2 B4) (le_max_right 1 (max B2 B4)))

/-- **`τ`-coefficient bounds on a closed ball.**  The coefficients `Alpha ℓ d i τ` of the
cusp numerator and `j(τ)` are bounded on the closed ball `dist τ τ₀ ≤ R`. -/
lemma alpha_j_closedBall_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ₀ : ℍ) (R : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ τ : ℍ, dist τ τ₀ ≤ R →
      (∀ i : Fin 3, ‖Alpha ℓ d i τ‖ ≤ B) ∧ ‖Work.Kernels.jInvariantFun τ‖ ≤ B := by
  obtain ⟨Bψ, hBψ, hψ⟩ := psiVec_closedBall_bound ℓ τ₀ R
  obtain ⟨B4, hB4, h4⟩ := bound_closedBall_of_continuous continuous_E4Fun_ub τ₀ R
  obtain ⟨B6, hB6, h6⟩ := bound_closedBall_of_continuous continuous_E6Fun_ub τ₀ R
  obtain ⟨BD, hBD, hD⟩ := bound_closedBall_of_continuous continuous_DeltaFun_ub τ₀ R
  obtain ⟨B2, hB2, h2⟩ := bound_closedBall_of_continuous continuous_fk_two_ub τ₀ R
  obtain ⟨Bj₀, hBj₀, hj₀⟩ := bound_closedBall_of_continuous continuous_jInvariantFun_ub τ₀ R
  set Bfk : ℝ := 1 + B4 + B6 + B2 + BD + B4 * B6 + B4 * B4 with hBfk
  have hBfkpos : 0 < Bfk := by rw [hBfk]; positivity
  have h1le : (1 : ℝ) ≤ Bfk := by
    rw [hBfk]; nlinarith [hB4.le, hB6.le, hB2.le, hBD.le, mul_nonneg hB4.le hB6.le]
  have hB4le : B4 ≤ Bfk := by
    rw [hBfk]; nlinarith [hB4.le, hB6.le, hB2.le, hBD.le, mul_nonneg hB4.le hB6.le]
  have hB2le : B2 ≤ Bfk := by
    rw [hBfk]; nlinarith [hB4.le, hB6.le, hB2.le, hBD.le, mul_nonneg hB4.le hB6.le]
  have hBDle : BD ≤ Bfk := by
    rw [hBfk]; nlinarith [hB4.le, hB6.le, hB2.le, hBD.le, mul_nonneg hB4.le hB6.le]
  have hB46le : B4 * B6 ≤ Bfk := by
    rw [hBfk]; nlinarith [hB4.le, hB6.le, hB2.le, hBD.le, mul_nonneg hB4.le hB6.le]
  have hB44le : B4 ^ 2 ≤ Bfk := by
    rw [hBfk, sq]; nlinarith [hB4.le, hB6.le, hB2.le, hBD.le, mul_nonneg hB4.le hB6.le]
  have hfk : ∀ τ : ℍ, dist τ τ₀ ≤ R → ∀ i : Fin 3,
      ‖Work.Kernels.fk (vlen d i) τ‖ ≤ Bfk := by
    intro τ hτ i
    rcases hd with rfl | rfl
    · fin_cases i <;> simp only [Fin.reduceFinMk]
      · have hv : Work.Kernels.fk (vlen 8 0) τ = Work.Kernels.E4Fun τ := by
          simp [vlen, Work.Kernels.fk]
        rw [hv]; exact le_trans (h4 τ hτ) hB4le
      · have hv : Work.Kernels.fk (vlen 8 1) τ =
            Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ := by simp [vlen, Work.Kernels.fk]
        rw [hv]; exact le_trans (h2 τ hτ) hB2le
      · have hv : Work.Kernels.fk (vlen 8 2) τ = 1 := by simp [vlen, Work.Kernels.fk]
        rw [hv, norm_one]; exact h1le
    · fin_cases i <;> simp only [Fin.reduceFinMk]
      · have hv : Work.Kernels.fk (vlen 24 0) τ = Work.Kernels.DeltaFun τ := by
          simp [vlen, Work.Kernels.fk]
        rw [hv]; exact le_trans (hD τ hτ) hBDle
      · have hv : Work.Kernels.fk (vlen 24 1) τ = Work.Kernels.E10Fun τ := by
          simp [vlen, Work.Kernels.fk]
        rw [hv]
        have heq : Work.Kernels.E10Fun τ = Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ := rfl
        rw [heq, norm_mul]
        exact le_trans (mul_le_mul (h4 τ hτ) (h6 τ hτ) (norm_nonneg _) hB4.le) hB46le
      · have hv : Work.Kernels.fk (vlen 24 2) τ = Work.Kernels.E8Fun τ := by
          simp [vlen, Work.Kernels.fk]
        rw [hv]
        have heq : Work.Kernels.E8Fun τ = Work.Kernels.E4Fun τ ^ 2 := rfl
        rw [heq, norm_pow]
        exact le_trans (pow_le_pow_left₀ (norm_nonneg _) (h4 τ hτ) 2) hB44le
  refine ⟨Bψ * Bfk + Bj₀ + 1, by positivity, fun τ hτ => ⟨fun i => ?_, ?_⟩⟩
  · show ‖Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (vlen d i) τ‖ ≤ Bψ * Bfk + Bj₀ + 1
    rw [norm_mul]
    have h1 : ‖Work.Kernels.psiVec ℓ τ i‖ * ‖Work.Kernels.fk (vlen d i) τ‖ ≤ Bψ * Bfk :=
      mul_le_mul (hψ τ hτ i) (hfk τ hτ i) (norm_nonneg _) hBψ.le
    linarith [hBj₀.le, hBψ.le, hBfkpos.le, h1]
  · have h1 := hj₀ τ hτ
    have h2 : (0 : ℝ) ≤ Bψ * Bfk := mul_nonneg hBψ.le hBfkpos.le
    linarith

/-! ## Uniform estimates for the cusp atoms -/

lemma cuspEstU_eA (ℓ : Work.Kernels.LogLambdaData) {S : Set ℍ} :
    ∃ H C : ℝ, CuspEstU S (fun τ z => eA τ z) 2 H C := by
  obtain ⟨H, C, hC, hb⟩ := cuspEst_eA ℓ ⟨Complex.I, by norm_num [Complex.I_im]⟩
  exact ⟨H, C, hC, fun _ _ z hz => hb z hz⟩

lemma cuspEstU_eE {S : Set ℍ} :
    ∃ H C : ℝ, CuspEstU S (fun τ z => eE τ z) 2 H C := by
  obtain ⟨H, C, hC, hb⟩ := cuspEst_eE ⟨Complex.I, by norm_num [Complex.I_im]⟩
  exact ⟨H, C, hC, fun _ _ z hz => hb z hz⟩

lemma cuspEstU_eU (ℓ : Work.Kernels.LogLambdaData) {S : Set ℍ} :
    ∃ H C : ℝ, CuspEstU S (fun _ z => eU ℓ z) 3 H C := by
  obtain ⟨H, C, hC, hb⟩ := cuspEst_eU ℓ
  exact ⟨H, C, hC, fun _ _ z hz => hb z hz⟩

lemma cuspEstU_eV {S : Set ℍ} :
    ∃ H C : ℝ, CuspEstU S (fun _ z => eV z) 3 H C := by
  obtain ⟨H, C, hC, hb⟩ := cuspEst_eV
  exact ⟨H, C, hC, fun _ _ z hz => hb z hz⟩

lemma cuspEstU_eW {S : Set ℍ} :
    ∃ H C : ℝ, CuspEstU S (fun _ z => eW z) 3 H C := by
  obtain ⟨H, C, hC, hb⟩ := cuspEst_eW
  exact ⟨H, C, hC, fun _ _ z hz => hb z hz⟩

/-- `(j(τ) - j(z))E² + 1 = O(t²)`, uniformly for `τ` in a set on which `j` is bounded. -/
lemma cuspEstU_eB {S : Set ℍ} {Bj : ℝ} (hBj : 0 ≤ Bj)
    (hj : ∀ τ ∈ S, ‖Work.Kernels.jInvariantFun τ‖ ≤ Bj) :
    ∃ H C : ℝ, CuspEstU S (fun τ z => eB τ z) 2 H C := by
  obtain ⟨Hj, Cj, hCj, hbj⟩ := cuspEst_Ept_sq_mul_jInvariantFun_sub_one
  obtain ⟨Hp, Cp, hp⟩ := CuspEstU.ofCuspEst (S := S) (cuspEst_Ept_pow 2)
  have hjE : CuspEstU S (fun τ z => Work.Kernels.jInvariantFun τ * Work.Residues.Ept z ^ 2)
      2 Hp ((Bj + 1) * Cp) :=
    hp.constmul (B := Bj) hj hBj
  have hneg : CuspEstU S
      (fun _ z => -(Work.Residues.Ept z ^ 2 * Work.Kernels.jInvariantFun z - 1)) 2 Hj Cj :=
    ⟨hCj, fun τ _ z hz => by rw [norm_neg]; exact hbj z hz⟩
  refine ⟨max Hp Hj, (Bj + 1) * Cp + Cj, ?_⟩
  refine (hjE.add hneg).congr (fun τ z => ?_)
  simp only [eB]
  ring

/-! ## The uniform `d = 8` estimate -/

/-- **Uniform `d = 8` estimate.**  `T₈ = O(t)` with constants valid on a closed ball. -/
theorem cuspEstU_T8 (ℓ : Work.Kernels.LogLambdaData) {S : Set ℍ} {Bα Bj : ℝ}
    (hBα : 0 < Bα) (hBj : 0 ≤ Bj)
    (hα : ∀ τ ∈ S, ∀ i : Fin 3, ‖Alpha ℓ 8 i τ‖ ≤ Bα)
    (hj : ∀ τ ∈ S, ‖Work.Kernels.jInvariantFun τ‖ ≤ Bj) :
    ∃ H C : ℝ, CuspEstU S (fun τ z => T8 ℓ τ z) 1 H C := by
  obtain ⟨HL, CL, hL⟩ := CuspEstU.ofCuspEst (S := S) (cuspEst_E10Fun.mul (cuspEst_LS ℓ))
  obtain ⟨H8, C8, h8⟩ := CuspEstU.ofCuspEst (S := S) (cuspEst_E8Fun.mul cuspEst_VFun.neg)
  obtain ⟨H6, C6, h6⟩ :=
    CuspEstU.ofCuspEst (S := S) (cuspEst_E6Fun.mul cuspEst_UFun_sq_sub_WFun_sq)
  have h30 : ∀ τ ∈ S, ‖(-3456 : ℂ) * Alpha ℓ 8 0 τ‖ ≤ 3456 * Bα := by
    intro τ hτ
    rw [norm_mul, show ‖(-3456 : ℂ)‖ = 3456 by norm_num]
    exact mul_le_mul_of_nonneg_left (hα τ hτ 0) (by norm_num)
  have h31 : ∀ τ ∈ S,
      ‖Alpha ℓ 8 1 τ + Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ)‖
        ≤ Bα + Bα * (1728 + Bj) := by
    intro τ hτ
    have hsub : ‖(1728 : ℂ) - Work.Kernels.jInvariantFun τ‖ ≤ 1728 + Bj := by
      have h1 := norm_sub_le (1728 : ℂ) (Work.Kernels.jInvariantFun τ)
      rw [show ‖((1728 : ℂ))‖ = 1728 by norm_num] at h1
      linarith [h1, hj τ hτ]
    have hmul : ‖Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ)‖
        ≤ Bα * (1728 + Bj) := by
      rw [norm_mul]
      exact mul_le_mul (hα τ hτ 2) hsub (norm_nonneg _) hBα.le
    calc ‖Alpha ℓ 8 1 τ + Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ)‖
        ≤ ‖Alpha ℓ 8 1 τ‖ + ‖Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ)‖ :=
          norm_add_le _ _
      _ ≤ Bα + Bα * (1728 + Bj) := add_le_add (hα τ hτ 1) hmul
  have h32 : ∀ τ ∈ S,
      ‖-(Alpha ℓ 8 1 τ) + Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ‖ ≤ Bα + Bα * Bj := by
    intro τ hτ
    have hmul : ‖Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ‖ ≤ Bα * Bj := by
      rw [norm_mul]
      exact mul_le_mul (hα τ hτ 2) (hj τ hτ) (norm_nonneg _) hBα.le
    calc ‖-(Alpha ℓ 8 1 τ) + Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ‖
        ≤ ‖-(Alpha ℓ 8 1 τ)‖ + ‖Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ‖ := norm_add_le _ _
      _ ≤ Bα + Bα * Bj := add_le_add (by simpa using hα τ hτ 1) hmul
  have hT0 := hL.constmul h30 (by positivity)
  have hT1 := h8.constmul h31 (by positivity)
  have hT2 := h6.constmul h32 (by positivity)
  exact ⟨_, _, ((hT0.add hT1).add hT2).congr (fun τ z => by
    simp only [T8, ulen8_zero, ulen8_one, ulen8_two, fk_ten_eq, fk_eight_eq, fk_six_eq]
    ring)⟩

/-! ## The uniform `d = 24` estimate -/

lemma norm_natCast_mul_le {B : ℝ} {c : ℂ} (n : ℕ) (hc : ‖c‖ ≤ B) :
    ‖(n : ℂ) * c‖ ≤ n * B := by
  rw [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hc (by positivity)

lemma norm_add_sub_le3 {a b c : ℂ} : ‖a + b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  refine le_trans (norm_sub_le _ _) ?_
  exact add_le_add (norm_add_le _ _) le_rfl

lemma norm_neg_natCast_mul_le {B : ℝ} {c : ℂ} (n : ℕ) (hc : ‖c‖ ≤ B) :
    ‖(-(n : ℂ)) * c‖ ≤ n * B := by
  rw [norm_mul, norm_neg, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hc (by positivity)

/-- **Uniform `d = 24` estimate.**  `T₂₄ · E² = O(t³)` with constants valid on a closed ball. -/
theorem cuspEstU_T24_mul_Ept_sq (ℓ : Work.Kernels.LogLambdaData) {S : Set ℍ} {Bα Bj : ℝ}
    (hBα : 0 < Bα) (hBj : 0 ≤ Bj)
    (hα : ∀ τ ∈ S, ∀ i : Fin 3, ‖Alpha ℓ 24 i τ‖ ≤ Bα)
    (hj : ∀ τ ∈ S, ‖Work.Kernels.jInvariantFun τ‖ ≤ Bj) :
    ∃ H C : ℝ, CuspEstU S (fun τ z => T24 ℓ τ z * Work.Residues.Ept z ^ 2) 3 H C := by
  obtain ⟨Ha, Ca, ha⟩ := cuspEstU_eA ℓ (S := S)
  obtain ⟨Hb, Cb, hb⟩ := cuspEstU_eB (S := S) hBj hj
  obtain ⟨He, Ce, he⟩ := cuspEstU_eE (S := S)
  obtain ⟨Hu, Cu, hu⟩ := cuspEstU_eU ℓ (S := S)
  obtain ⟨Hv, Cv, hv⟩ := cuspEstU_eV (S := S)
  obtain ⟨Hw, Cw, hw⟩ := cuspEstU_eW (S := S)
  obtain ⟨H1, C1, hE1⟩ := CuspEstU.ofCuspEst (S := S) cuspEst_Ept
  obtain ⟨H2, C2, hE2⟩ := CuspEstU.ofCuspEst (S := S) (cuspEst_Ept_pow 2)
  obtain ⟨H3, C3, hE3⟩ := CuspEstU.ofCuspEst (S := S) (cuspEst_Ept_pow 3)
  have hone_a : CuspEstU S (fun τ z => 1 + eA τ z) 0 (max 0 Ha) ((‖(1 : ℂ)‖ + 1) + Ca) :=
    (CuspEstU.const S 1 (H := 0)).add (ha.mono_exp (Nat.zero_le 2))
  have hone_b : CuspEstU S (fun τ z => 1 - eB τ z) 0 (max 0 Hb) ((‖(1 : ℂ)‖ + 1) + Cb) :=
    (CuspEstU.const S 1 (H := 0)).sub (hb.mono_exp (Nat.zero_le 2))
  have hone_e : CuspEstU S (fun τ z => 1 + eE τ z) 0 (max 0 He) ((‖(1 : ℂ)‖ + 1) + Ce) :=
    (CuspEstU.const S 1 (H := 0)).add (he.mono_exp (Nat.zero_le 2))
  have hna : ∀ τ ∈ S, ‖(55296 : ℂ) * Alpha ℓ 24 0 τ‖ ≤ 55296 * Bα :=
    fun τ hτ => norm_natCast_mul_le 55296 (hα τ hτ 0)
  have hnu : ∀ τ ∈ S, ‖(3456 : ℂ) * Alpha ℓ 24 0 τ‖ ≤ 3456 * Bα :=
    fun τ hτ => norm_natCast_mul_le 3456 (hα τ hτ 0)
  have hnv : ∀ τ ∈ S,
      ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ‖ ≤ 3460 * Bα := by
    intro τ hτ
    have k0 := norm_neg_natCast_mul_le 3456 (hα τ hτ 0)
    have k1 := norm_natCast_mul_le 2 (hα τ hτ 1)
    have k2 := norm_natCast_mul_le 2 (hα τ hτ 2)
    calc ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ‖
        ≤ ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ‖ + ‖2 * Alpha ℓ 24 1 τ‖ + ‖2 * Alpha ℓ 24 2 τ‖ :=
          norm_add_sub_le3
      _ ≤ 3456 * Bα + 2 * Bα + 2 * Bα := add_le_add (add_le_add k0 k1) k2
      _ ≤ 3460 * Bα := by linarith
  have hnb : ∀ τ ∈ S,
      ‖(16 : ℂ) * ((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)‖
        ≤ 16 * (3460 * Bα) := by
    intro τ hτ
    calc ‖(16 : ℂ) * ((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)‖
        ≤ 16 * ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ‖ :=
          norm_natCast_mul_le 16 le_rfl
      _ ≤ 16 * (3460 * Bα) := mul_le_mul_of_nonneg_left (hnv τ hτ) (by norm_num)
  have hne : ∀ τ ∈ S, ‖(32 : ℂ) * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ)‖ ≤ 32 * (2 * Bα) := by
    intro τ hτ
    have hsub : ‖Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ‖ ≤ 2 * Bα := by
      calc ‖Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ‖ ≤ ‖Alpha ℓ 24 2 τ‖ + ‖Alpha ℓ 24 1 τ‖ := norm_sub_le _ _
        _ ≤ 2 * Bα := by linarith [hα τ hτ 2, hα τ hτ 1]
    calc ‖(32 : ℂ) * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ)‖
        ≤ 32 * ‖Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ‖ := norm_natCast_mul_le 32 le_rfl
      _ ≤ 32 * (2 * Bα) := mul_le_mul_of_nonneg_left hsub (by norm_num)
  have hn6 : ∀ τ ∈ S, ‖Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ‖ ≤ 2 * Bα := by
    intro τ hτ
    calc ‖Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ‖ ≤ ‖Alpha ℓ 24 2 τ‖ + ‖Alpha ℓ 24 1 τ‖ := norm_sub_le _ _
      _ ≤ 2 * Bα := by linarith [hα τ hτ 2, hα τ hτ 1]
  have hn45 : ∀ τ ∈ S,
      ‖(Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
        + 1728 * Alpha ℓ 24 2 τ‖ ≤ 2 * Bα * Bj + 1728 * Bα := by
    intro τ hτ
    have h12 : ‖Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ‖ ≤ 2 * Bα := by
      calc ‖Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ‖ ≤ ‖Alpha ℓ 24 1 τ‖ + ‖Alpha ℓ 24 2 τ‖ := norm_sub_le _ _
        _ ≤ 2 * Bα := by linarith [hα τ hτ 1, hα τ hτ 2]
    have h1 : ‖(Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ‖
        ≤ (2 * Bα) * Bj := by
      rw [norm_mul]
      exact mul_le_mul h12 (hj τ hτ) (norm_nonneg _) (by positivity)
    have h2 : ‖(1728 : ℂ) * Alpha ℓ 24 2 τ‖ ≤ 1728 * Bα :=
      norm_natCast_mul_le 1728 (hα τ hτ 2)
    calc ‖(Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
          + 1728 * Alpha ℓ 24 2 τ‖
        ≤ ‖(Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ‖
            + ‖(1728 : ℂ) * Alpha ℓ 24 2 τ‖ := norm_add_le _ _
      _ ≤ (2 * Bα) * Bj + 1728 * Bα := add_le_add h1 h2
      _ ≤ 2 * Bα * Bj + 1728 * Bα := by linarith
  have hn4 : ∀ τ ∈ S,
      ‖(16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
        + 1728 * Alpha ℓ 24 2 τ)‖ ≤ 16 * (2 * Bα * Bj + 1728 * Bα) := by
    intro τ hτ
    calc ‖(16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
          + 1728 * Alpha ℓ 24 2 τ)‖
        ≤ 16 * ‖(Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
          + 1728 * Alpha ℓ 24 2 τ‖ := norm_natCast_mul_le 16 le_rfl
      _ ≤ 16 * (2 * Bα * Bj + 1728 * Bα) := mul_le_mul_of_nonneg_left (hn45 τ hτ) (by norm_num)
  have h1 : CuspEstU S (fun τ z =>
      (55296 * Alpha ℓ 24 0 τ * eA τ z
        - 16 * (-3456 * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ) * eB τ z
        + 32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z) * Work.Residues.Ept z) 3 _ _ :=
    (((ha.constmul hna (by positivity)).sub
        (hb.constmul hnb (by positivity))).add
      (he.constmul hne (by positivity))).mul hE1
  have h2 : CuspEstU S (fun τ z =>
      3456 * Alpha ℓ 24 0 τ * eU ℓ z * (1 + eA τ z)) 3 _ _ :=
    (hu.constmul hnu (by positivity)).mul hone_a
  have h3 : CuspEstU S (fun τ z =>
      (-3456 * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ) * eV z
        * (1 - eB τ z)) 3 _ _ :=
    (hv.constmul hnv (by positivity)).mul hone_b
  have h4 : CuspEstU S (fun τ z =>
      16 * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
        + 1728 * Alpha ℓ 24 2 τ) * Work.Residues.Ept z ^ 3) 3 _ _ :=
    hE3.constmul hn4 (by positivity)
  have h5 : CuspEstU S (fun τ z =>
      ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
        + 1728 * Alpha ℓ 24 2 τ) * eV z * Work.Residues.Ept z ^ 2) 5 _ _ :=
    (hv.constmul hn45 (by positivity)).mul hE2
  have h7 : CuspEstU S (fun τ z =>
      ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
        + 1728 * Alpha ℓ 24 2 τ) * eV z * Work.Residues.Ept z ^ 2) 3 _ _ :=
    h5.mono_exp (by norm_num)
  have h6 : CuspEstU S (fun τ z =>
      (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * (1 + eE τ z)) 3 _ _ :=
    (hw.constmul hn6 (by positivity)).mul hone_e
  have hRHS : CuspEstU S (fun τ z =>
      (55296 * Alpha ℓ 24 0 τ * eA τ z
          - 16 * (-3456 * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ) * eB τ z
          + 32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z) * Work.Residues.Ept z
        - 3456 * Alpha ℓ 24 0 τ * eU ℓ z * (1 + eA τ z)
        + (-3456 * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ) * eV z
            * (1 - eB τ z)
        - 16 * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
              + 1728 * Alpha ℓ 24 2 τ) * Work.Residues.Ept z ^ 3
        - ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
              + 1728 * Alpha ℓ 24 2 τ) * eV z * Work.Residues.Ept z ^ 2
        + (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * (1 + eE τ z)) 3 _ _ :=
    ((((h1.sub h2).add h3).sub h4).sub h7).add h6
  exact ⟨_, _, hRHS.congr (fun τ z => by
    refine Eq.symm ?_
    have h := T24_cancellation (Alpha ℓ 24 0 τ) (Alpha ℓ 24 1 τ) (Alpha ℓ 24 2 τ)
      (Work.Kernels.jInvariantFun τ) (Work.Residues.Ept z) (eA τ z) (eB τ z) (eE τ z)
      (eU ℓ z) (eV z) (eW z)
    rw [← h]
    simp only [T24, eA, eB, eE, eU, eV, eW]
    ring)⟩

/-! ## The uniform cusp bound on a closed ball -/

/-- **Uniform cusp bound for the `K_-` numerator `Ncusp` on a closed ball.**

The proved result `Work.Asymptotics.KMinusCuspBallLimit` (for a *fixed* `τ`) says
`Ecusp z · Ncusp ℓ d τ z → 0` as `Im z → ∞`, which by the (proved) cusp-atom analysis
(`cuspEst_Ncusp`) means `Ncusp ℓ d τ z = O(‖Ecusp z‖) = O(exp (−π Im z))` with constants
depending on `τ`.  What the CKMRV contour argument on a compact `K ⊆ 𝒟` needs is the *uniform*
version on a closed ball:

  `∃ H C, 0 < C ∧ ∀ τ z, dist τ τ₀ ≤ R → H ≤ z.im → ‖Ncusp ℓ d τ z‖ ≤ C * exp (−π z.im)`.

The proof re-runs the cusp analysis of `cuspEst_Ncusp` with the `τ`-dependence tracked: the
`z`-factors are estimated uniformly by `CuspEstU` (the `τ`-fixed estimates of
`KMinusCuspBallLimit` for `eA, eE, eU, eV, eW`, together with `cuspEstU_eB`, which uses the
boundedness of `j(τ)` on the ball), while the `τ`-coefficients `Alpha ℓ d i τ` are bounded on
the ball by `alpha_j_closedBall_bound`. -/
theorem Ncusp_bound_ball (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R) :
    ∃ H C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), dist τ τ₀ ≤ R → H ≤ z.im →
      ‖Work.Asymptotics.Ncusp ℓ d τ z‖ ≤ C * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨B, hBpos, hB⟩ := alpha_j_closedBall_bound ℓ d hd τ₀ R
  have hmem : ∀ τ : ℍ, dist τ τ₀ ≤ R → τ ∈ Metric.closedBall τ₀ R :=
    fun τ hτ => by simpa [Metric.mem_closedBall] using hτ
  have hα : ∀ τ ∈ Metric.closedBall τ₀ R, ∀ i : Fin 3, ‖Alpha ℓ d i τ‖ ≤ B :=
    fun τ hτ i => (hB τ (by simpa [Metric.mem_closedBall] using hτ)).1 i
  have hJ : ∀ τ ∈ Metric.closedBall τ₀ R, ‖Work.Kernels.jInvariantFun τ‖ ≤ B :=
    fun τ hτ => (hB τ (by simpa [Metric.mem_closedBall] using hτ)).2
  have htpar : ∀ z : ℍ, Work.Residues.tpar z = Real.exp (-(Real.pi * z.im)) :=
    fun z => rfl
  rcases hd with rfl | rfl
  · obtain ⟨H, C, hbd⟩ := cuspEstU_T8 ℓ hBpos hBpos.le hα hJ
    refine ⟨H, ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * C + 1,
      by nlinarith [hbd.1, norm_nonneg ((2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹)],
      fun τ z hτ hz => ?_⟩
    have hb : ‖T8 ℓ τ z‖ ≤ C * Work.Residues.tpar z := by
      simpa using hbd.2 τ (hmem τ hτ) z hz
    rw [Ncusp_eight_expansion ℓ τ z, norm_mul]
    calc ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ‖T8 ℓ τ z‖
        ≤ ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (C * Work.Residues.tpar z) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ ≤ (‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * C + 1) * Work.Residues.tpar z := by
          rw [show ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (C * Work.Residues.tpar z)
              = (‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * C) * Work.Residues.tpar z by ring]
          exact mul_le_mul_of_nonneg_right (by linarith) (Work.Residues.tpar_nonneg z)
      _ = (‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * C + 1) *
            Real.exp (-(Real.pi * z.im)) := by rw [htpar z]
  · obtain ⟨H, C, hbd⟩ := cuspEstU_T24_mul_Ept_sq ℓ hBpos hBpos.le hα hJ
    refine ⟨H, ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * C + 1,
      by nlinarith [hbd.1, norm_nonneg ((2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹)],
      fun τ z hτ hz => ?_⟩
    have hb := hbd.2 τ (hmem τ hτ) z hz
    have hE2 : ‖Work.Residues.Ept z ^ 2‖ = Work.Residues.tpar z ^ 2 := by
      rw [norm_pow, Work.Residues.norm_Ept]; rfl
    have hT : ‖T24 ℓ τ z‖ ≤ C * Work.Residues.tpar z := by
      have h1 : ‖T24 ℓ τ z‖ * Work.Residues.tpar z ^ 2 ≤ C * Work.Residues.tpar z ^ 3 := by
        rw [← hE2, ← norm_mul]
        exact hb
      have h2 : (0 : ℝ) < Work.Residues.tpar z ^ 2 := pow_pos (Work.Residues.tpar_pos z) 2
      refine le_of_mul_le_mul_right ?_ h2
      rw [show C * Work.Residues.tpar z * Work.Residues.tpar z ^ 2
          = C * Work.Residues.tpar z ^ 3 by ring]
      exact h1
    rw [Ncusp_twentyfour_expansion ℓ τ z, norm_mul]
    calc ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ‖T24 ℓ τ z‖
        ≤ ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (C * Work.Residues.tpar z) :=
          mul_le_mul_of_nonneg_left hT (norm_nonneg _)
      _ ≤ (‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * C + 1) * Work.Residues.tpar z := by
          rw [show ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (C * Work.Residues.tpar z)
              = (‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * C) * Work.Residues.tpar z by ring]
          exact mul_le_mul_of_nonneg_right (by linarith) (Work.Residues.tpar_nonneg z)
      _ = (‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * C + 1) *
            Real.exp (-(Real.pi * z.im)) := by rw [htpar z]

end

end Work.Asymptotics
