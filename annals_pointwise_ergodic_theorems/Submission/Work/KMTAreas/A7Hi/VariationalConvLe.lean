import Mathlib
import Submission.Work.KMTAreas.A7Hi.variationalNorm_tsum_le
import Submission.Port.Aesm

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **The base (`α = 0`) bound: convolution with an `ℓ¹`-kernel does not increase the
`ℓᵖ(ℤ; Vʳ)`-norm.**  This is the piece of the `F_l` decomposition
`T_M = Σ_i D_i − (l−1)C` (§12) that survives the frequency-`0` collapse: at the shared frequency
`α = 0` every decimation `D_i` reduces to the same `m`-convolution `C`, and `C` has kernel
`cw m` of `ℓ¹`-mass `≤ B`, so `C` is bounded by `B` on `ℓᵖ(ℤ; Vʳ)` — with no use of the band, of
the arithmetic, or of `l`.  The `α ≠ 0` windows, where `T_M` coincides with a single `D_i`, are
handled by the coset engine `CosetL1MassLe`.

Proof (per review): pointwise `Vʳ(Σ_j k j · u n (x−j)) ≤ Σ_j ‖k j‖·Vʳ(u·(x−j))` by
`variationalNorm_tsum_mul_le`; then monotonicity of `eLpNorm` and the `Lᵖ` triangle inequality
(`eLpNorm_tsum_le`, `1 < p`) with the translation-invariance of counting measure on `ℤ`. -/
theorem VariationalConvLe (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℤ → ℂ), Summable (fun j : ℤ => ‖k j‖) → ∀ (u : ℕ → ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' j : ℤ, k j * u n (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * ∑' j : ℤ, ‖k j‖) * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  -- The kernel mass `∑'_j ‖k j‖ₑ` is the sharp constant; `C = 1` suffices.
  refine ⟨1, one_pos, ?_⟩
  intro k hk u
  -- Step 1: the pointwise Young inequality for the variational norm, the `j`-sum written as an
  -- integral against the counting measure so that the discrete convolution appears literally.
  have hstep : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => ∑' j : ℤ, k j * u n (x - j))
      ≤ ∫⁻ y : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n (x - y))
          * ‖k y‖ₑ ∂MeasureTheory.Measure.count := by
    intro x
    refine (variationalNorm_tsum_le r hr k (fun j n => u n (x - j))).trans ?_
    rw [MeasureTheory.lintegral_count]
    exact ENNReal.tsum_le_tsum (fun j => le_of_eq (mul_comm _ _))
  -- Step 2: monotonicity of `eLpNorm`.
  have h2 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => ∑' j : ℤ, k j * u n (x - j))) (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∫⁻ y : ℤ,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n (x - y))
            * ‖k y‖ₑ ∂MeasureTheory.Measure.count)
        (ENNReal.ofReal p) MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => hstep x)
  -- Step 3: `eLpNorm` of the `ℓ¹`-kernel over the counting measure is its `ℓ¹`-mass.
  have ha1 : MeasureTheory.eLpNorm (fun y : ℤ => ‖k y‖ₑ) (ENNReal.ofReal 1)
        MeasureTheory.Measure.count
      = ∑' j : ℤ, ‖k j‖ₑ := by
    rw [ENNReal.ofReal_one, MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm),
      MeasureTheory.lintegral_count]
    simp
  -- Step 4: Young's convolution inequality `ℓ¹ ∗ ℓᵖ → ℓᵖ` on `ℤ` (here `p = q = p`, `r = 1`).
  have hyoung := Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal
      (G := ℤ) (μ := MeasureTheory.Measure.count)
      (K := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
      (Φ := fun y : ℤ => ‖k y‖ₑ) (p := 1) (q := p) (r := p)
      le_rfl (le_of_lt hp) (by ring)
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
  rw [ha1, mul_comm] at hyoung
  -- Step 5: the `ℝ≥0∞`-mass of the kernel is the `ofReal` of its real `ℓ¹`-mass.
  have hS : (∑' j : ℤ, ‖k j‖ₑ) = ENNReal.ofReal (1 * ∑' j : ℤ, ‖k j‖) := by
    rw [one_mul, ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hk]
    simp
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, k j * u n (x - j))) (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∫⁻ y : ℤ,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n (x - y))
            * ‖k y‖ₑ ∂MeasureTheory.Measure.count)
        (ENNReal.ofReal p) MeasureTheory.Measure.count := h2
    _ ≤ (∑' j : ℤ, ‖k j‖ₑ) * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count := hyoung
    _ = ENNReal.ofReal (1 * ∑' j : ℤ, ‖k j‖) * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        rw [hS]

end Work.KMTAreas.A7Hi
