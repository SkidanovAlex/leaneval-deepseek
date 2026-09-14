import Mathlib.Analysis.Distribution.Sobolev

namespace Commons.Analysis.Sobolev

open FourierTransform TemperedDistribution
open scoped SchwartzMap Laplacian

/-- Fourier multipliers are additive in the symbol. -/
theorem fourierMultiplierCLM_add {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [NormedSpace ℂ F] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F (g₁ + g₂) = fourierMultiplierCLM F g₁ + fourierMultiplierCLM F g₂ := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_add hg₁ hg₂]

theorem memSobolev_one_of_laplacian_memSobolev_neg_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u : TemperedDistribution E ℂ)
    (hu : TemperedDistribution.MemSobolev 0 2 u)
    (hΔ : TemperedDistribution.MemSobolev (-1) 2 (Laplacian.laplacian u)) :
    TemperedDistribution.MemSobolev 1 2 u := by
  set Sm : E → ℂ := fun x ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2)) with hSm
  set Sn : E → ℂ := fun x ↦ Complex.ofReal (‖x‖ ^ 2) with hSn
  set c : ℂ := -((2 * Real.pi : ℂ) ^ 2) with hc_def
  have hSmG : Sm.HasTemperateGrowth := by rw [hSm]; fun_prop
  have hSnG : Sn.HasTemperateGrowth := by rw [hSn]; fun_prop
  have hSnSmG : (Sn * Sm).HasTemperateGrowth := hSnG.mul hSmG
  -- pointwise identity: the symbol of `besselPotential 1` is `Sm + Sn * Sm`
  have hpt : (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))) = Sm + Sn * Sm := by
    rw [hSm, hSn]
    funext x
    simp only [Pi.add_apply, Pi.mul_apply]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
    congr 1
    have hpos : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
    exact (calc (1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) + ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2)
          = (1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) := by ring
        _ = (1 + ‖x‖ ^ 2) ^ (1 : ℝ) * (1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) := by rw [Real.rpow_one]
        _ = (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) + (-1 : ℝ) / 2) := by rw [Real.rpow_add hpos]
        _ = (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) := by congr 1; norm_num).symm
  have hB1 : besselPotential E ℂ 1 =
      fourierMultiplierCLM ℂ (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))) :=
    rfl
  have hBm : besselPotential E ℂ (-1) = fourierMultiplierCLM ℂ Sm := by rw [hSm]; rfl
  have hkey : besselPotential E ℂ 1 u = fourierMultiplierCLM ℂ Sm u
      + fourierMultiplierCLM ℂ (Sn * Sm) u := by
    rw [hB1, hpt, fourierMultiplierCLM_add hSmG hSnSmG, add_apply]
  -- the Laplacian is (minus) a nonzero multiple of the multiplier with symbol `Sn`
  have hLap : Laplacian.laplacian u = c • fourierMultiplierCLM ℂ Sn u := by
    rw [hc_def, hSn, TemperedDistribution.laplacian_eq_fourierMultiplierCLM u]
    show ((↑(-(((2 : ℝ) * Real.pi) ^ 2)) : ℂ)) • fourierMultiplierCLM ℂ
        (fun x : E ↦ Complex.ofReal (‖x‖ ^ 2)) u
      = (-((2 * Real.pi : ℂ) ^ 2)) • fourierMultiplierCLM ℂ
        (fun x : E ↦ Complex.ofReal (‖x‖ ^ 2)) u
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by rw [hc_def]; norm_num
  have hSnEq : fourierMultiplierCLM ℂ Sn u = c⁻¹ • Laplacian.laplacian u := by
    calc fourierMultiplierCLM ℂ Sn u = c⁻¹ • (c • fourierMultiplierCLM ℂ Sn u) :=
          (inv_smul_smul₀ hc _).symm
      _ = c⁻¹ • Laplacian.laplacian u := by rw [hLap]
  have hS2 : fourierMultiplierCLM ℂ (Sn * Sm) u =
      c⁻¹ • besselPotential E ℂ (-1) (Laplacian.laplacian u) := by
    rw [← fourierMultiplierCLM_fourierMultiplierCLM_apply hSnG hSmG u, hSnEq, map_smul, ← hBm]
  -- Sobolev membership of the pieces
  have hYmem : MemSobolev 0 2 (besselPotential E ℂ (-1) (Laplacian.laplacian u)) :=
    (TemperedDistribution.memSobolev_besselPotential_iff (s := 0) (r := -1) (p := 2)
      (f := Laplacian.laplacian u)).mpr (by simpa using hΔ)
  have hSmbdd : ∃ C, ∀ x, ‖Sm x‖ ≤ C := by
    refine ⟨1, fun x ↦ ?_⟩
    rw [hSm]
    have hnn : (0 : ℝ) ≤ (1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) := by positivity
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by norm_num)
  have h1 : MemSobolev 0 2 (fourierMultiplierCLM ℂ Sm u) :=
    hu.fourierMultiplierCLM_of_bounded hSmG hSmbdd
  have h2 : MemSobolev 0 2 (fourierMultiplierCLM ℂ (Sn * Sm) u) := by
    rw [hS2]
    exact hYmem.smul c⁻¹
  have h3 : MemSobolev 0 2 (besselPotential E ℂ 1 u) := by
    rw [hkey]
    exact h1.add h2
  simpa using (TemperedDistribution.memSobolev_besselPotential_iff (s := 0) (r := 1) (p := 2)
    (f := u)).mp h3

end Commons.Analysis.Sobolev