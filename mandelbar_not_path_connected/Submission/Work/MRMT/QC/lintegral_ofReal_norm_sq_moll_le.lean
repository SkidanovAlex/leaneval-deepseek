/-
The L²-contraction property of mollification against a normalised nonnegative kernel.

* `enorm_eq_ofReal_norm` — the extended norm of a complex number is `ENNReal.ofReal` of its norm;
* `lintegral_mul_sq_le` — Cauchy–Schwarz for `ℝ≥0∞`-valued functions,
  `(∫ G·H)² ≤ (∫ G)·(∫ G·H²)`;
* `lintegral_ofReal_norm_sq_moll_le` — the requested bound
  `∫⁻ z, ofReal ‖ρ ⋆ f z‖² ≤ ∫⁻ z, ofReal ‖f z‖²`
  for a nonnegative kernel `ρ` with `∫ ρ = 1`.  The proof is Jensen/Cauchy–Schwarz for the
  weighted average `(ρ ⋆ f) z = ∫ y, ρ y • f (z - y)` followed by Tonelli and the translation
  invariance of Lebesgue measure.
-/
import Mathlib
import Submission.Work.MRMT.Weyl.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.QC

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

noncomputable section

/-- The extended norm of a complex number is `ENNReal.ofReal` of its norm. -/
theorem enorm_eq_ofReal_norm (x : ℂ) : ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
  rw [← Real.enorm_eq_ofReal (norm_nonneg x)]
  simp [enorm_eq_nnnorm]

/-- **Cauchy–Schwarz for `ℝ≥0∞`-valued functions**:
`(∫ G·H)² ≤ (∫ G)·(∫ G·H²)`. -/
theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {G H : α → ℝ≥0∞}
    (hG : AEMeasurable G μ) (hH : AEMeasurable H μ) :
    (∫⁻ y, G y * H y ∂μ) ^ 2 ≤ (∫⁻ y, G y ∂μ) * ∫⁻ y, G y * H y ^ 2 ∂μ := by
  have hsq : ∀ A : ℝ≥0∞, (A ^ (1/2:ℝ)) ^ 2 = A := fun A => by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num
  have hpq : (2:ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  set F : α → ℝ≥0∞ := fun y => G y ^ (1/2:ℝ) with hF
  set K : α → ℝ≥0∞ := fun y => H y * G y ^ (1/2:ℝ) with hK
  have hFm : AEMeasurable F μ := by rw [hF]; exact hG.pow_const _
  have hKm : AEMeasurable K μ := by rw [hK]; exact hH.mul (hG.pow_const _)
  have hFK : ∫⁻ y, F y * K y ∂μ = ∫⁻ y, G y * H y ∂μ := by
    refine lintegral_congr fun y => ?_
    simp only [hF, hK]
    calc G y ^ (1/2:ℝ) * (H y * G y ^ (1/2:ℝ))
        = (G y ^ (1/2:ℝ))^2 * H y := by rw [pow_two]; ring
      _ = G y * H y := by rw [hsq]
  have hFF : ∫⁻ y, F y ^ (2:ℝ) ∂μ = ∫⁻ y, G y ∂μ := by
    refine lintegral_congr fun y => ?_
    simp only [hF, ENNReal.rpow_two]
    exact hsq (G y)
  have hKK : ∫⁻ y, K y ^ (2:ℝ) ∂μ = ∫⁻ y, G y * H y ^ 2 ∂μ := by
    refine lintegral_congr fun y => ?_
    simp only [hK]
    rw [ENNReal.mul_rpow_of_nonneg (H y) (G y ^ (1/2:ℝ)) (by norm_num), ENNReal.rpow_two,
      ENNReal.rpow_two, hsq (G y)]
    ring
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (f := F) (g := K) hFm hKm
  simp only [Pi.mul_apply] at h
  rw [hFK, hFF, hKK] at h
  have h2 : (∫⁻ y, G y * H y ∂μ)^2
      ≤ ((∫⁻ y, G y ∂μ)^(1/2:ℝ) * (∫⁻ y, G y * H y^2 ∂μ)^(1/2:ℝ))^2 :=
    pow_le_pow_left' h 2
  rwa [mul_pow, hsq, hsq] at h2

theorem lintegral_ofReal_norm_sq_moll_le {f : ℂ → ℂ} {ρ : ℂ → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hρnn : ∀ x, 0 ≤ ρ x) (hρint : ∫ x, ρ x = 1)
    (hρm : MeasureTheory.AEStronglyMeasurable ρ (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    ∫⁻ z, ENNReal.ofReal (‖Work.MRMT.Weyl.moll ρ f z‖ ^ 2)
      ≤ ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) := by
  -- `ρ` is integrable, since its integral is `1`
  have hρint_meas : Integrable ρ (volume : Measure ℂ) := by
    by_contra h
    rw [integral_undef h] at hρint
    exact one_ne_zero hρint.symm
  set G : ℂ → ℝ≥0∞ := fun y => ‖ρ y‖ₑ with hGdef
  set K : ℂ → ℝ≥0∞ := fun w => ‖f w‖ₑ ^ 2 with hKdef
  have hGm : AEMeasurable G (volume : Measure ℂ) := hρm.enorm
  have hKm : AEMeasurable K (volume : Measure ℂ) := (hf.enorm).pow_const 2
  have hGlin : ∫⁻ y, G y ∂(volume : Measure ℂ) = 1 := by
    rw [hGdef]
    rw [lintegral_congr fun y => Real.enorm_eq_ofReal (hρnn y)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hρint_meas
      (Filter.Eventually.of_forall hρnn), hρint]
    simp
  -- pointwise (in `z`) Cauchy–Schwarz / Jensen bound
  have hpt : ∀ z, ENNReal.ofReal (‖Work.MRMT.Weyl.moll ρ f z‖ ^ 2)
      ≤ ∫⁻ y, G y * K (z - y) ∂(volume : Measure ℂ) := by
    intro z
    have hHm : AEMeasurable (fun y => ‖f (z - y)‖ₑ) (volume : Measure ℂ) :=
      (hf.enorm).comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure ℂ) z)
    have hCS := lintegral_mul_sq_le (μ := (volume : Measure ℂ)) (G := G)
      (H := fun y => ‖f (z - y)‖ₑ) hGm hHm
    have h1 : ‖Work.MRMT.Weyl.moll ρ f z‖ₑ
        ≤ ∫⁻ y, G y * ‖f (z - y)‖ₑ ∂(volume : Measure ℂ) := by
      rw [Work.MRMT.Weyl.moll_apply]
      refine (enorm_integral_le_lintegral_enorm (μ := (volume : Measure ℂ))
        (fun y => ((ρ y : ℝ) : ℂ) * f (z - y))).trans_eq ?_
      refine lintegral_congr fun y => ?_
      rw [enorm_mul]
      congr 1
      simp only [hGdef]
      rw [enorm_eq_nnnorm, Complex.nnnorm_real, enorm_eq_nnnorm]
    have hof : ENNReal.ofReal (‖Work.MRMT.Weyl.moll ρ f z‖ ^ 2)
        = ‖Work.MRMT.Weyl.moll ρ f z‖ₑ ^ 2 := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), enorm_eq_ofReal_norm]
    rw [hof]
    calc ‖Work.MRMT.Weyl.moll ρ f z‖ₑ ^ 2
        ≤ (∫⁻ y, G y * ‖f (z - y)‖ₑ ∂(volume : Measure ℂ)) ^ 2 :=
          pow_le_pow_left' h1 2
      _ ≤ (∫⁻ y, G y ∂(volume : Measure ℂ))
            * ∫⁻ y, G y * ‖f (z - y)‖ₑ ^ 2 ∂(volume : Measure ℂ) := hCS
      _ = 1 * ∫⁻ y, G y * K (z - y) ∂(volume : Measure ℂ) := by rw [hGlin]
      _ = ∫⁻ y, G y * K (z - y) ∂(volume : Measure ℂ) := one_mul _
  -- the right-hand side, in terms of `K`
  have hRHS : ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂(volume : Measure ℂ)
      = ∫⁻ z, K z ∂(volume : Measure ℂ) := by
    refine lintegral_congr fun z => ?_
    simp only [hKdef]
    rw [ENNReal.ofReal_pow (norm_nonneg (f z)), enorm_eq_ofReal_norm]
  have hmeas1 : AEMeasurable (Function.uncurry fun z y : ℂ => G y * K (z - y))
      ((volume : Measure ℂ).prod volume) :=
    (hGm.comp_snd).mul (hKm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure ℂ) (volume : Measure ℂ)))
  have hmeas2 : AEMeasurable (Function.uncurry fun y z : ℂ => G y * K z)
      ((volume : Measure ℂ).prod volume) :=
    (hGm.comp_fst).mul (hKm.comp_snd)
  have hmain : ∫⁻ z, ENNReal.ofReal (‖Work.MRMT.Weyl.moll ρ f z‖ ^ 2) ∂(volume : Measure ℂ)
      ≤ ∫⁻ z, K z ∂(volume : Measure ℂ) := by
    calc ∫⁻ z, ENNReal.ofReal (‖Work.MRMT.Weyl.moll ρ f z‖ ^ 2) ∂(volume : Measure ℂ)
        ≤ ∫⁻ z, ∫⁻ y, G y * K (z - y) ∂(volume : Measure ℂ) ∂(volume : Measure ℂ) :=
          lintegral_mono hpt
      _ = ∫⁻ y, ∫⁻ z, G y * K (z - y) ∂(volume : Measure ℂ) ∂(volume : Measure ℂ) :=
          lintegral_lintegral_swap hmeas1
      _ = ∫⁻ y, ∫⁻ z, G y * K z ∂(volume : Measure ℂ) ∂(volume : Measure ℂ) := by
          refine lintegral_congr fun y => ?_
          rw [lintegral_sub_right_eq_self (fun z => G y * K z) y]
      _ = ∫⁻ p : ℂ × ℂ, G p.1 * K p.2 ∂((volume : Measure ℂ).prod volume) :=
          lintegral_lintegral hmeas2
      _ = (∫⁻ y, G y ∂(volume : Measure ℂ)) * ∫⁻ z, K z ∂(volume : Measure ℂ) :=
          lintegral_prod_mul hGm hKm
      _ = ∫⁻ z, K z ∂(volume : Measure ℂ) := by rw [hGlin, one_mul]
  rw [hRHS]
  exact hmain

end

end Work.MRMT.QC
