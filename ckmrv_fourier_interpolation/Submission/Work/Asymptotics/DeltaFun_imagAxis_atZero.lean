import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atTop

namespace Work.Asymptotics

/-- **`S` on the imaginary axis.**  The Möbius inversion `S : z ↦ -1/z` sends `it` to
`i/t`; this is the change of variable that converts the cusp `t → ∞` into the cusp
`t → 0`. -/
lemma imagAxis_smul_S (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • Work.Kernels.imagAxis t ht
      = Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  show (-((t : ℂ) * Complex.I))⁻¹ = ((t⁻¹ : ℝ) : ℂ) * Complex.I
  rw [inv_neg, mul_inv, Complex.inv_I]
  push_cast
  ring

/-- **The cusp asymptotics of `Δ` at `t → 0` on the imaginary axis**, obtained from
`Work.Asymptotics.DeltaFun_imagAxis_atTop` by the modular transformation law
`Δ(-1/τ) = τ^12 Δ(τ)` (applied at `τ = it`, so that `it` and `i/t` are related by `S`):
`Δ(it)` is comparable to `t^{-12} e^{-2π/t}` for `t` small.  This is the half of the divisor
estimate that governs the CKMRV contour integral near `t = 0`. -/
theorem DeltaFun_imagAxis_atZero :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 0 < T ∧
      ∀ (t : ℝ) (ht : 0 < t), t ≤ T →
        c * ((t : ℝ) ^ 12)⁻¹ * Real.exp (-(2 * Real.pi / t)) ≤
          ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ∧
        ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ≤
          C * ((t : ℝ) ^ 12)⁻¹ * Real.exp (-(2 * Real.pi / t)) := by
  obtain ⟨c, C, T, hc, hC, hT, hb⟩ := DeltaFun_imagAxis_atTop
  refine ⟨c, C, T⁻¹, hc, hC, inv_pos.mpr hT, ?_⟩
  intro t ht htT
  have hs : 0 < t⁻¹ := inv_pos.mpr ht
  -- `1/t ≥ T`, so the cusp estimate at infinity applies at `i/t`
  have hge : T ≤ t⁻¹ := (le_inv_comm₀ hT ht).mpr htT
  obtain ⟨hlo, hhi⟩ := hb t⁻¹ hs hge
  -- the modular transformation law `Δ(S • it) = (it)^12 Δ(it)`
  have hS := Work.Kernels.KernelFacts.kpc_smul_S_of_slash
    (F := Work.Kernels.DeltaFun) Work.Kernels.KernelFacts.kpc_Delta_slash_S
    (Work.Kernels.imagAxis t ht)
  rw [imagAxis_smul_S t ht] at hS
  have hnormτ12 :
      ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) ^ (12 : ℤ)‖ = t ^ 12 := by
    rw [norm_zpow]
    have hnormτ : ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)‖ = t := by
      simp [Work.Kernels.imagAxis, abs_of_pos ht]
    rw [hnormτ, zpow_ofNat]
  have hnorm : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hs)‖
      = t ^ 12 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
    rw [hS, norm_mul, hnormτ12]
  have ht12pos : (0 : ℝ) < t ^ 12 := pow_pos ht 12
  -- solve for `‖Δ(it)‖`
  have hDinv : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
      = (t ^ 12)⁻¹ * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hs)‖ := by
    rw [hnorm, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht12pos), one_mul]
  have hexp : Real.exp (-(2 * Real.pi * t⁻¹)) = Real.exp (-(2 * Real.pi / t)) := by
    rw [div_eq_mul_inv]
  constructor
  · calc c * (t ^ 12)⁻¹ * Real.exp (-(2 * Real.pi / t))
        = (t ^ 12)⁻¹ * (c * Real.exp (-(2 * Real.pi * t⁻¹))) := by rw [hexp]; ring
      _ ≤ (t ^ 12)⁻¹ * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hs)‖ :=
          mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr ht12pos.le)
      _ = ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := hDinv.symm
  · calc ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
        = (t ^ 12)⁻¹ * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hs)‖ := hDinv
      _ ≤ (t ^ 12)⁻¹ * (C * Real.exp (-(2 * Real.pi * t⁻¹))) :=
          mul_le_mul_of_nonneg_left hhi (inv_nonneg.mpr ht12pos.le)
      _ = C * (t ^ 12)⁻¹ * Real.exp (-(2 * Real.pi / t)) := by rw [hexp]; ring

end Work.Asymptotics
