import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Residues.LogLambdaBound

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup ModularForm

/-- **`S` on the imaginary axis, in the direction needed at the cusp `t → 0`.**
`S • (i/t) = it`: the involution `S : z ↦ -1/z` sends the large imaginary part `1/t` back to
the small one `t`.  (This is the reverse direction of `Work.Asymptotics.imagAxis_smul_S`.) -/
private lemma imagAxis_S_smul_inv (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) = Work.Kernels.imagAxis t ht := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  show (-(((t⁻¹ : ℝ) : ℂ) * Complex.I))⁻¹ = (t : ℂ) * Complex.I
  rw [inv_neg, mul_inv, Complex.inv_I]
  push_cast
  rw [inv_inv]
  ring

/-- **Boundedness of `𝓛 = ℓ.L` at the cusp `t → 0`.**  The transformation law
`ℓ.slash_S : ℓ.L ∣[(0:ℤ)] ModularGroup.S = ℓ.L_S` reads `ℓ.L (-1/τ) = ℓ.L_S τ`, so for
`t ≤ 1` we have `ℓ.L (it) = ℓ.L_S (i/t)`, and `Work.Residues.LogLambdaBound` gives
`‖ℓ.L_S τ‖ ≤ C e^{-π im τ}` for `im τ ≥ 1`.  Hence `𝓛(it)` is bounded (indeed exponentially
small) as `t → 0`. -/
theorem norm_L_imagAxis_atZero (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖ℓ.L (Work.Kernels.imagAxis t ht)‖ ≤ C := by
  obtain ⟨-, C_S, hCpos, hCS⟩ := Work.Residues.LogLambdaBound ℓ
  refine ⟨C_S, hCpos, ?_⟩
  intro t ht ht1
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  -- the `S`-law specialized at `i/t`
  have hslash : ℓ.L (ModularGroup.S • Work.Kernels.imagAxis t⁻¹ hti)
      = ℓ.L_S (Work.Kernels.imagAxis t⁻¹ hti) := by
    have h := congr_fun ℓ.slash_S (Work.Kernels.imagAxis t⁻¹ hti)
    rw [Work.Kernels.slash_apply'] at h
    simpa using h
  rw [← imagAxis_S_smul_inv t ht, hslash]
  -- the imaginary part of `i/t` is `1/t ≥ 1`
  have him : (Work.Kernels.imagAxis t⁻¹ hti).im = t⁻¹ := by simp [Work.Kernels.imagAxis]
  have him1 : 1 ≤ (Work.Kernels.imagAxis t⁻¹ hti).im := by
    rw [him]; exact (one_le_inv₀ ht).mpr ht1
  have hb := hCS _ him1
  rw [him] at hb
  have hexp : Real.exp (-(Real.pi * t⁻¹)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hti]
  calc ‖ℓ.L_S (Work.Kernels.imagAxis t⁻¹ hti)‖
      ≤ C_S * Real.exp (-(Real.pi * t⁻¹)) := hb
    _ ≤ C_S * 1 := mul_le_mul_of_nonneg_left hexp hCpos.le
    _ = C_S := mul_one C_S

end Work.Asymptotics
