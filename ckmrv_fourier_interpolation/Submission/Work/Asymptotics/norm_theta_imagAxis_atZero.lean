import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Residues.ThetaDecay

/-!
# The theta quartics near the cusp `t → 0` on the imaginary axis

This file records the growth of the three theta quartics

`U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴`

at the cusp `τ → 0` along the imaginary axis `τ = it`:

`‖U(it)‖ = O(t⁻⁴)`,  `‖V(it)‖ = O(t⁻²)`,  `‖W(it)‖ = O(t⁻²)`  as `t → 0⁺`.

These are the exponents `d/2 - k` (with `d = 8`, resp. `24`) of the CKMRV kernels: with `U`,
`W` bounded by `C·t⁻⁴` and `V`, `W` by `C·t⁻²` the product expansions of the clearing
factors in `K_±^{(d)}` give the required growth of the kernels at the cusp `τ = 0`.

## The argument

The pointwise transformation laws of the quartics under the modular involution
`S : τ ↦ -1/τ` (CKMRV (2.11), proved in `Work.Kernels.KernelFacts`),

`U(S•τ) = -τ² U(τ)`, `W(S•τ) = -τ² V(τ)`, `V(S•τ) = -τ² W(τ)`,

turn the cusp `τ = 0` into the cusp `i∞`: `S•(it) = i/t`, and `1/t ≥ 1` for `t ≤ 1`.
There the decay of `Work.Residues.ThetaDecay` applies,

`U(τ) - 1 = O(e^{-π Im τ})`, `W(τ) - 1 = O(e^{-π Im τ})`, `V(τ) = O(e^{-π Im τ})`,

so that `U(i/t)`, `W(i/t)` are bounded by an absolute constant while
`V(i/t) ≤ C e^{-π/t}`.  Since `‖U(S•τ)‖ = |τ|² ‖U(τ)‖` this gives
`‖U(it)‖ ≤ C t⁻²`, and `t ≤ 1` upgrades `t⁻² ≤ t⁻⁴`.
-/

namespace Work.Asymptotics

open UpperHalfPlane

/-- **`S` on the imaginary axis.** The involution `S : z ↦ -1/z` sends `it` to `i/t`
(this is the change of variable that converts the cusp `t → 0` into the cusp `t → ∞`). -/
private lemma thetaImagAxis_S_smul (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • Work.Kernels.imagAxis t ht
      = Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  show (-((t : ℂ) * Complex.I))⁻¹ = ((t⁻¹ : ℝ) : ℂ) * Complex.I
  rw [inv_neg, mul_inv, Complex.inv_I]
  push_cast
  ring

/-- The imaginary part of `imagAxis t ht` is `t`. -/
private lemma thetaImagAxis_im (t : ℝ) (ht : 0 < t) :
    (Work.Kernels.imagAxis t ht).im = t := by
  simp [Work.Kernels.imagAxis]

/-- **Transfer of an `S`-law to the cusp `t → 0`.**  If `F(S•τ) = -τ² G(τ)` and `F` is
bounded by `M` at `i/t`, then `G(it) ≤ t⁻² M`. -/
private lemma norm_le_of_S_law_atZero {F G : ℍ → ℂ} {M t : ℝ} (ht : 0 < t)
    (hlaw : ∀ τ : ℍ, F (ModularGroup.S • τ) = -((τ : ℂ) ^ 2) * G τ)
    (hF : ‖F (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))‖ ≤ M) :
    ‖G (Work.Kernels.imagAxis t ht)‖ ≤ (t ^ 2)⁻¹ * M := by
  have h := hlaw (Work.Kernels.imagAxis t ht)
  rw [thetaImagAxis_S_smul t ht] at h
  have hcoe : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl
  have hnormτ : ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)‖ = t := by
    rw [hcoe]; simp [abs_of_pos ht]
  have h2 : ‖(((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) ^ 2)‖ = t ^ 2 := by
    rw [norm_pow, hnormτ]
  have hnorm : ‖F (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))‖
      = t ^ 2 * ‖G (Work.Kernels.imagAxis t ht)‖ := by
    rw [h, norm_mul, norm_neg, h2]
  have ht2 : (0 : ℝ) < t ^ 2 := pow_pos ht 2
  have hsolve : ‖G (Work.Kernels.imagAxis t ht)‖
      = (t ^ 2)⁻¹ * ‖F (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))‖ := by
    rw [hnorm, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht2), one_mul]
  rw [hsolve]
  exact mul_le_mul_of_nonneg_left hF (by positivity)

/-- `t⁻² ≤ t⁻⁴` for `0 < t ≤ 1`. -/
private lemma inv_sq_le_inv_pow_four {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (t ^ 2)⁻¹ ≤ (t ^ 4)⁻¹ := by
  rw [inv_le_inv₀ (pow_pos ht 2) (pow_pos ht 4)]
  have h2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.le ht1
  calc t ^ 4 = t ^ 2 * t ^ 2 := by ring
    _ ≤ 1 * t ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = t ^ 2 := one_mul _

/-- A function which is `1 + O(e^{-π Im τ})` at `i∞` is bounded by `1 + C` at `i/t`,
for `0 < t ≤ 1`. -/
private lemma norm_le_one_add_of_sub_le {F : ℍ → ℂ} {C t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hC : 0 ≤ C)
    (h : ∀ τ : ℍ, 1 ≤ τ.im → ‖F τ - 1‖ ≤ C * Real.exp (-(Real.pi * τ.im))) :
    ‖F (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))‖ ≤ 1 + C := by
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have him : 1 ≤ (Work.Kernels.imagAxis t⁻¹ hti).im := by
    rw [thetaImagAxis_im]; exact (one_le_inv₀ ht).mpr ht1
  have hdec := h _ him
  have hexp : Real.exp (-(Real.pi * (Work.Kernels.imagAxis t⁻¹ hti).im)) ≤ 1 := by
    rw [Real.exp_le_one_iff, thetaImagAxis_im]
    nlinarith [Real.pi_pos, hti]
  have h1 : ‖F (Work.Kernels.imagAxis t⁻¹ hti) - 1‖ ≤ C := by
    calc ‖F (Work.Kernels.imagAxis t⁻¹ hti) - 1‖
        ≤ C * Real.exp (-(Real.pi * (Work.Kernels.imagAxis t⁻¹ hti).im)) := hdec
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hexp hC
      _ = C := mul_one C
  calc ‖F (Work.Kernels.imagAxis t⁻¹ hti)‖
      = ‖(F (Work.Kernels.imagAxis t⁻¹ hti) - 1) + 1‖ := by ring_nf
    _ ≤ ‖F (Work.Kernels.imagAxis t⁻¹ hti) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ C + 1 := by rw [norm_one]; linarith
    _ = 1 + C := by ring

/-- A function which is `O(e^{-π Im τ})` at `i∞` is bounded by `C` at `i/t`, for
`0 < t ≤ 1`. -/
private lemma norm_le_of_decay {F : ℍ → ℂ} {C t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C)
    (h : ∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-(Real.pi * τ.im))) :
    ‖F (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))‖ ≤ C := by
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have him : 1 ≤ (Work.Kernels.imagAxis t⁻¹ hti).im := by
    rw [thetaImagAxis_im]; exact (one_le_inv₀ ht).mpr ht1
  have hdec := h _ him
  have hexp : Real.exp (-(Real.pi * (Work.Kernels.imagAxis t⁻¹ hti).im)) ≤ 1 := by
    rw [Real.exp_le_one_iff, thetaImagAxis_im]
    nlinarith [Real.pi_pos, hti]
  calc ‖F (Work.Kernels.imagAxis t⁻¹ hti)‖
      ≤ C * Real.exp (-(Real.pi * (Work.Kernels.imagAxis t⁻¹ hti).im)) := hdec
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hexp hC
    _ = C := mul_one C

/-- **The theta quartics near `t = 0` on the imaginary axis.**  There are constants such that
for `0 < t ≤ 1`
`‖U(it)‖ ≤ C t⁻⁴`, `‖V(it)‖ ≤ C t⁻²` and `‖W(it)‖ ≤ C t⁻²`,
where `U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴`. -/
theorem norm_theta_imagAxis_atZero :
    (∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
        ‖Work.Kernels.UFun (Work.Kernels.imagAxis t ht)‖ ≤ C * (t ^ 4)⁻¹) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
        ‖Work.Kernels.VFun (Work.Kernels.imagAxis t ht)‖ ≤ C * (t ^ 2)⁻¹) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
        ‖Work.Kernels.WFun (Work.Kernels.imagAxis t ht)‖ ≤ C * (t ^ 2)⁻¹) := by
  obtain ⟨CU, hCU, hUdec⟩ := Work.Residues.UFun_decay
  obtain ⟨CW, hCW, hWdec⟩ := Work.Residues.WFun_decay
  obtain ⟨CV, hCV, hVdec⟩ := Work.Residues.VFun_decay
  refine ⟨⟨1 + CU, by linarith, ?_⟩, ⟨1 + CW, by linarith, ?_⟩, ⟨CV, hCV, ?_⟩⟩
  · -- `U(S•τ) = -τ² U(τ)`: reduce to the boundedness of `U` at `i/t`
    intro t ht ht1
    have hb := norm_le_one_add_of_sub_le (F := Work.Kernels.UFun) ht ht1 hCU.le hUdec
    have h := norm_le_of_S_law_atZero (F := Work.Kernels.UFun) (G := Work.Kernels.UFun)
      (M := 1 + CU) ht (fun τ => Work.Kernels.KernelFacts.UFun_S_smul τ) hb
    calc ‖Work.Kernels.UFun (Work.Kernels.imagAxis t ht)‖
        ≤ (t ^ 2)⁻¹ * (1 + CU) := h
      _ ≤ (t ^ 4)⁻¹ * (1 + CU) :=
          mul_le_mul_of_nonneg_right (inv_sq_le_inv_pow_four ht ht1) (by linarith)
      _ = (1 + CU) * (t ^ 4)⁻¹ := by ring
  · -- `W(S•τ) = -τ² V(τ)`: reduce to the boundedness of `W` at `i/t`
    intro t ht ht1
    have hb := norm_le_one_add_of_sub_le (F := Work.Kernels.WFun) ht ht1 hCW.le hWdec
    have h := norm_le_of_S_law_atZero (F := Work.Kernels.WFun) (G := Work.Kernels.VFun)
      (M := 1 + CW) ht (fun τ => Work.Kernels.KernelFacts.WFun_S_smul τ) hb
    calc ‖Work.Kernels.VFun (Work.Kernels.imagAxis t ht)‖
        ≤ (t ^ 2)⁻¹ * (1 + CW) := h
      _ = (1 + CW) * (t ^ 2)⁻¹ := by ring
  · -- `V(S•τ) = -τ² W(τ)`: reduce to the exponential decay of `V` at `i/t`
    intro t ht ht1
    have hb := norm_le_of_decay (F := Work.Kernels.VFun) ht ht1 hCV.le hVdec
    have h := norm_le_of_S_law_atZero (F := Work.Kernels.VFun) (G := Work.Kernels.WFun)
      (M := CV) ht (fun τ => Work.Kernels.KernelFacts.VFun_S_smul τ) hb
    calc ‖Work.Kernels.WFun (Work.Kernels.imagAxis t ht)‖
        ≤ (t ^ 2)⁻¹ * CV := h
      _ = CV * (t ^ 2)⁻¹ := by ring

end Work.Asymptotics
