/-
Copyright: `Work.MRMT` (mandelbar) subproject, Ahlfors--Bers theory.

# Post-composition by an affine map, and normalisation of quasiconformal maps

If `f` is quasiconformal on `U` with complex dilatation `μ`, then so is `z ↦ c * f z + d`
for every `c ≠ 0`: post-composition by a conformal (here affine) map multiplies both
Wirtinger derivatives by the same non-zero factor `c`, hence leaves the quotient
`∂̄/∂` — the complex dilatation — unchanged.  The point of the file is the bookkeeping
that makes this statement available at the level of the *definitions* of `IsQCOn`:
the Fréchet definition of `dz`, `dzbar` (junk value `0` where `f` is not real
differentiable) is preserved *everywhere*, and the weak-derivative and `L²_loc` clauses
transport by linearity, using that `∫ ∂φ = ∫ ∂̄φ = 0` for test functions.

The application (the reason the file exists) is `exists_normalized_of_qc_homeo`: a
quasiconformal homeomorphism of `ℂ` with dilatation `μ` can be normalised by
`z ↦ (φ z - φ 0)/(φ 1 - φ 0)` so as to fix `0` and `1`, without changing `μ`.
-/
import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

namespace Work.MRMT.AhlforsBers

open Work.MRMT

/-! ## Integrals of the Wirtinger derivatives of a compactly supported smooth function -/

/-- Integration by parts against the constant test function `1`: the integral of a
directional derivative `v ↦ fderiv ℝ G · v` of a compactly supported `C¹` function vanishes. -/
theorem integral_fderiv_apply_eq_zero {n : WithTop ℕ∞} (G : ℂ → ℂ) (hc : ContDiff ℝ n G)
    (hn : n ≠ 0) (hs : HasCompactSupport G) (v : ℂ) : ∫ z, fderiv ℝ G z v = 0 := by
  have hdiff : Differentiable ℝ G := hc.differentiable hn
  have hcont : Continuous fun z => fderiv ℝ G z v :=
    (hc.continuous_fderiv hn).clm_apply continuous_const
  have hint1 : Integrable (fun z => fderiv ℝ G z v) :=
    hcont.integrable_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) v)
  have hintG : Integrable G := hc.continuous.integrable_of_hasCompactSupport hs
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := G) (g := fun _ : ℂ => (1 : ℂ)) (v := v) (by simpa using hint1) (by simp)
    (by simpa using hintG) (fun x _ => hdiff x) (fun x _ => differentiableAt_const 1)
  simpa using h

/-- For a compactly supported smooth `G` the integral of `∂G` vanishes. -/
theorem integral_dz_eq_zero {n : WithTop ℕ∞} (G : ℂ → ℂ) (hc : ContDiff ℝ n G)
    (hn : n ≠ 0) (hs : HasCompactSupport G) : ∫ z, dz G z = 0 := by
  have h1 := integral_fderiv_apply_eq_zero G hc hn hs 1
  have hI := integral_fderiv_apply_eq_zero G hc hn hs Complex.I
  have hcont1 : Continuous fun z => fderiv ℝ G z (1 : ℂ) :=
    (hc.continuous_fderiv hn).clm_apply continuous_const
  have hcontI : Continuous fun z => fderiv ℝ G z Complex.I :=
    (hc.continuous_fderiv hn).clm_apply continuous_const
  have hint1 : Integrable (fun z => fderiv ℝ G z (1 : ℂ)) :=
    hcont1.integrable_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) (1 : ℂ))
  have hintI : Integrable (fun z => fderiv ℝ G z Complex.I) :=
    hcontI.integrable_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) Complex.I)
  have hF : ∫ z, (fderiv ℝ G z 1 - Complex.I * fderiv ℝ G z Complex.I) = 0 := by
    rw [integral_sub hint1 (hintI.const_mul Complex.I), integral_const_mul, h1, hI]
    simp
  calc ∫ z, dz G z
      = ∫ z, (fderiv ℝ G z 1 - Complex.I * fderiv ℝ G z Complex.I) * (2 : ℂ)⁻¹ := by
        simp only [dz, div_eq_mul_inv]
    _ = (∫ z, (fderiv ℝ G z 1 - Complex.I * fderiv ℝ G z Complex.I)) * (2 : ℂ)⁻¹ :=
        integral_mul_const _ _
    _ = 0 := by rw [hF, zero_mul]

/-- For a compactly supported smooth `G` the integral of `∂̄G` vanishes. -/
theorem integral_dzbar_eq_zero {n : WithTop ℕ∞} (G : ℂ → ℂ) (hc : ContDiff ℝ n G)
    (hn : n ≠ 0) (hs : HasCompactSupport G) : ∫ z, dzbar G z = 0 := by
  have h1 := integral_fderiv_apply_eq_zero G hc hn hs 1
  have hI := integral_fderiv_apply_eq_zero G hc hn hs Complex.I
  have hcont1 : Continuous fun z => fderiv ℝ G z (1 : ℂ) :=
    (hc.continuous_fderiv hn).clm_apply continuous_const
  have hcontI : Continuous fun z => fderiv ℝ G z Complex.I :=
    (hc.continuous_fderiv hn).clm_apply continuous_const
  have hint1 : Integrable (fun z => fderiv ℝ G z (1 : ℂ)) :=
    hcont1.integrable_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) (1 : ℂ))
  have hintI : Integrable (fun z => fderiv ℝ G z Complex.I) :=
    hcontI.integrable_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) Complex.I)
  have hF : ∫ z, (fderiv ℝ G z 1 + Complex.I * fderiv ℝ G z Complex.I) = 0 := by
    rw [integral_add hint1 (hintI.const_mul Complex.I), integral_const_mul, h1, hI]
    simp
  calc ∫ z, dzbar G z
      = ∫ z, (fderiv ℝ G z 1 + Complex.I * fderiv ℝ G z Complex.I) * (2 : ℂ)⁻¹ := by
        simp only [dzbar, div_eq_mul_inv]
    _ = (∫ z, (fderiv ℝ G z 1 + Complex.I * fderiv ℝ G z Complex.I)) * (2 : ℂ)⁻¹ :=
        integral_mul_const _ _
    _ = 0 := by rw [hF, zero_mul]

/-- `∂φ` is integrable for every test function `φ`. -/
theorem integrable_dz_test (φ : 𝓓(⊤, ℂ)) : Integrable (dz (φ : ℂ → ℂ)) := by
  have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ : ℂ → ℂ) := φ.contDiff
  have hn : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hcs : HasCompactSupport (φ : ℂ → ℂ) := φ.hasCompactSupport
  have hcont1 : Continuous fun z => fderiv ℝ (φ : ℂ → ℂ) z (1 : ℂ) :=
    (hc.continuous_fderiv hn).clm_apply continuous_const
  have hcontI : Continuous fun z => fderiv ℝ (φ : ℂ → ℂ) z Complex.I :=
    (hc.continuous_fderiv hn).clm_apply continuous_const
  have hi1 : Integrable (fun z => fderiv ℝ (φ : ℂ → ℂ) z (1 : ℂ)) :=
    hcont1.integrable_of_hasCompactSupport (hcs.fderiv_apply (𝕜 := ℝ) (1 : ℂ))
  have hiI : Integrable (fun z => fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
    hcontI.integrable_of_hasCompactSupport (hcs.fderiv_apply (𝕜 := ℝ) Complex.I)
  have hcomb : Integrable (fun z =>
      (2 : ℂ)⁻¹ * (fderiv ℝ (φ : ℂ → ℂ) z 1 - Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I)) :=
    (hi1.sub (hiI.const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
  convert hcomb using 1
  funext z
  rw [dz, div_eq_mul_inv]
  ring

/-- `∂̄φ` is integrable for every test function `φ`. -/
theorem integrable_dzbar_test (φ : 𝓓(⊤, ℂ)) : Integrable (dzbar (φ : ℂ → ℂ)) := by
  have hc : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (φ : ℂ → ℂ) := φ.contDiff
  have hn : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hcs : HasCompactSupport (φ : ℂ → ℂ) := φ.hasCompactSupport
  have hcont1 : Continuous fun z => fderiv ℝ (φ : ℂ → ℂ) z (1 : ℂ) :=
    (hc.continuous_fderiv hn).clm_apply continuous_const
  have hcontI : Continuous fun z => fderiv ℝ (φ : ℂ → ℂ) z Complex.I :=
    (hc.continuous_fderiv hn).clm_apply continuous_const
  have hi1 : Integrable (fun z => fderiv ℝ (φ : ℂ → ℂ) z (1 : ℂ)) :=
    hcont1.integrable_of_hasCompactSupport (hcs.fderiv_apply (𝕜 := ℝ) (1 : ℂ))
  have hiI : Integrable (fun z => fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
    hcontI.integrable_of_hasCompactSupport (hcs.fderiv_apply (𝕜 := ℝ) Complex.I)
  have hcomb : Integrable (fun z =>
      (2 : ℂ)⁻¹ * (fderiv ℝ (φ : ℂ → ℂ) z 1 + Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I)) :=
    (hi1.add (hiI.const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
  convert hcomb using 1
  funext z
  rw [dzbar, div_eq_mul_inv]
  ring

/-! ## The pointwise identities -/

/-- `∂(c·f + d) = c·∂f` *everywhere*, with the convention that `∂` takes the junk value `0`
where the function is not real differentiable. -/
theorem dz_const_mul_add (c d : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    dz (fun w => c * f w + d) z = c * dz f z := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    have hfun : (fun w => (0 : ℂ) * f w + d) = fun _ => d := by funext w; simp
    have hzero : dz (fun _ : ℂ => d) z = 0 := by
      rw [dz]
      simp
    rw [hfun, hzero, zero_mul]
  · by_cases hd : DifferentiableAt ℝ f z
    · rw [dz, dz, fderiv_add_const (𝕜 := ℝ) d, fderiv_const_mul (𝕜 := ℝ) hd c]
      simp only [smul_apply, smul_eq_mul]
      ring
    · have hnd : ¬ DifferentiableAt ℝ (fun w => c * f w + d) z := by
        intro h
        apply hd
        have h2 : DifferentiableAt ℝ (fun w => c * f w + d - d) z := h.sub_const d
        have h3 : DifferentiableAt ℝ (fun w => c⁻¹ * (c * f w + d - d)) z :=
          h2.const_mul c⁻¹
        have heq : (fun w => c⁻¹ * (c * f w + d - d)) = f := by
          funext w
          rw [add_sub_cancel_right, inv_mul_cancel_left₀ hc]
        rw [heq] at h3
        exact h3
      rw [dz, dz, fderiv_zero_of_not_differentiableAt hnd,
        fderiv_zero_of_not_differentiableAt hd]
      simp

/-- `∂̄(c·f + d) = c·∂̄f` *everywhere* (companion of `dz_const_mul_add`). -/
theorem dzbar_const_mul_add (c d : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    dzbar (fun w => c * f w + d) z = c * dzbar f z := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    have hfun : (fun w => (0 : ℂ) * f w + d) = fun _ => d := by funext w; simp
    have hzero : dzbar (fun _ : ℂ => d) z = 0 := by
      rw [dzbar]
      simp
    rw [hfun, hzero, zero_mul]
  · by_cases hd : DifferentiableAt ℝ f z
    · rw [dzbar, dzbar, fderiv_add_const (𝕜 := ℝ) d, fderiv_const_mul (𝕜 := ℝ) hd c]
      simp only [smul_apply, smul_eq_mul]
      ring
    · have hnd : ¬ DifferentiableAt ℝ (fun w => c * f w + d) z := by
        intro h
        apply hd
        have h2 : DifferentiableAt ℝ (fun w => c * f w + d - d) z := h.sub_const d
        have h3 : DifferentiableAt ℝ (fun w => c⁻¹ * (c * f w + d - d)) z :=
          h2.const_mul c⁻¹
        have heq : (fun w => c⁻¹ * (c * f w + d - d)) = f := by
          funext w
          rw [add_sub_cancel_right, inv_mul_cancel_left₀ hc]
        rw [heq] at h3
        exact h3
      rw [dzbar, dzbar, fderiv_zero_of_not_differentiableAt hnd,
        fderiv_zero_of_not_differentiableAt hd]
      simp

/-! ## Transport of the weak derivatives -/

/-- Weak `∂`-derivatives transport under `z ↦ c * f z + d`. -/
theorem isDzDerivOn_const_mul_add {f g : ℂ → ℂ} {U : Set ℂ} (h : IsDzDerivOn f g U)
    (c d : ℂ) : IsDzDerivOn (fun z => c * f z + d) (fun z => c * g z) U := by
  obtain ⟨hf, hgl, hrel⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have h1 : LocallyIntegrableOn (fun z => c * f z) U := hf.smul c
    have h2 : LocallyIntegrableOn (fun _ : ℂ => d) U := locallyIntegrableOn_const d
    have h3 := h1.add h2
    convert h3 using 1
  · exact hgl.smul c
  · intro φ hφ
    obtain ⟨hI1, hI2, hInt⟩ := hrel φ hφ
    have hdz : Integrable (dz (φ : ℂ → ℂ)) := integrable_dz_test φ
    have hA : Integrable (fun z => c * (f z * dz (φ : ℂ → ℂ) z)) := hI1.const_mul c
    have hB : Integrable (fun z => d * dz (φ : ℂ → ℂ) z) := hdz.const_mul d
    refine ⟨?_, ?_, ?_⟩
    · refine (hA.add hB).congr (Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply]
      ring
    · refine (hI2.const_mul c).congr (Eventually.of_forall fun z => ?_)
      simp only
      ring
    · have hdz0 : ∫ z, dz (φ : ℂ → ℂ) z = 0 :=
        integral_dz_eq_zero _ φ.contDiff (by simp) φ.hasCompactSupport
      have heq : (fun z => (c * f z + d) * dz (φ : ℂ → ℂ) z) =
          fun z => c * (f z * dz (φ : ℂ → ℂ) z) + d * dz (φ : ℂ → ℂ) z := by
        funext z; ring
      have hcg : ∫ z, (c * g z) * (φ : ℂ → ℂ) z = c * ∫ z, g z * (φ : ℂ → ℂ) z := by
        rw [← integral_const_mul c (fun z => g z * (φ : ℂ → ℂ) z)]
        exact integral_congr_ae (Eventually.of_forall fun z => by ring)
      rw [heq, integral_add hA hB, integral_const_mul, integral_const_mul, hInt, hdz0,
        mul_zero, add_zero, hcg]
      ring

/-- Weak `∂̄`-derivatives transport under `z ↦ c * f z + d`. -/
theorem isDbarDerivOn_const_mul_add {f g : ℂ → ℂ} {U : Set ℂ} (h : IsDbarDerivOn f g U)
    (c d : ℂ) : IsDbarDerivOn (fun z => c * f z + d) (fun z => c * g z) U := by
  obtain ⟨hf, hgl, hrel⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have h1 : LocallyIntegrableOn (fun z => c * f z) U := hf.smul c
    have h2 : LocallyIntegrableOn (fun _ : ℂ => d) U := locallyIntegrableOn_const d
    have h3 := h1.add h2
    convert h3 using 1
  · exact hgl.smul c
  · intro φ hφ
    obtain ⟨hI1, hI2, hInt⟩ := hrel φ hφ
    have hdz : Integrable (dzbar (φ : ℂ → ℂ)) := integrable_dzbar_test φ
    have hA : Integrable (fun z => c * (f z * dzbar (φ : ℂ → ℂ) z)) := hI1.const_mul c
    have hB : Integrable (fun z => d * dzbar (φ : ℂ → ℂ) z) := hdz.const_mul d
    refine ⟨?_, ?_, ?_⟩
    · refine (hA.add hB).congr (Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply]
      ring
    · refine (hI2.const_mul c).congr (Eventually.of_forall fun z => ?_)
      simp only
      ring
    · have hdz0 : ∫ z, dzbar (φ : ℂ → ℂ) z = 0 :=
        integral_dzbar_eq_zero _ φ.contDiff (by simp) φ.hasCompactSupport
      have heq : (fun z => (c * f z + d) * dzbar (φ : ℂ → ℂ) z) =
          fun z => c * (f z * dzbar (φ : ℂ → ℂ) z) + d * dzbar (φ : ℂ → ℂ) z := by
        funext z; ring
      have hcg : ∫ z, (c * g z) * (φ : ℂ → ℂ) z = c * ∫ z, g z * (φ : ℂ → ℂ) z := by
        rw [← integral_const_mul c (fun z => g z * (φ : ℂ → ℂ) z)]
        exact integral_congr_ae (Eventually.of_forall fun z => by ring)
      rw [heq, integral_add hA hB, integral_const_mul, integral_const_mul, hInt, hdz0,
        mul_zero, add_zero, hcg]
      ring

/-! ## Transport of the `L²_loc` condition -/

theorem memL2LocOn_const_mul {f : ℂ → ℂ} {U : Set ℂ} (h : MemL2LocOn f U) (c : ℂ) :
    MemL2LocOn (fun z => c * f z) U := by
  intro K hK
  have hfK : Integrable (fun z => ‖f z‖ ^ 2) (volume.restrict (K ∩ U)) := h K hK
  change Integrable (fun z => ‖c * f z‖ ^ 2) (volume.restrict (K ∩ U))
  refine (hfK.const_mul (‖c‖ ^ 2)).congr (Eventually.of_forall fun z => ?_)
  simp only [norm_mul, mul_pow]

theorem memL2LocOn_add_const {f : ℂ → ℂ} {U : Set ℂ} (h : MemL2LocOn f U) (d : ℂ)
    (hm : AEStronglyMeasurable f (volume.restrict U)) : MemL2LocOn (fun z => f z + d) U := by
  intro K hK
  have hfin : (volume : Measure ℂ) (K ∩ U) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) hK.measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict (K ∩ U)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hfin⟩
  have hfK : Integrable (fun z => ‖f z‖ ^ 2) (volume.restrict (K ∩ U)) := h K hK
  have hmK : AEStronglyMeasurable f (volume.restrict (K ∩ U)) :=
    hm.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)
  have hbound : Integrable (fun z => 2 * ‖f z‖ ^ 2 + 2 * ‖d‖ ^ 2) (volume.restrict (K ∩ U)) :=
    (hfK.const_mul 2).add (integrable_const _)
  refine Integrable.mono' hbound ?_ ?_
  · exact (by fun_prop : Continuous fun w : ℂ => ‖w + d‖ ^ 2).comp_aestronglyMeasurable hmK
  · filter_upwards with z
    have h1 : ‖f z + d‖ ≤ ‖f z‖ + ‖d‖ := norm_add_le _ _
    have h2 : ‖f z + d‖ ^ 2 ≤ (‖f z‖ + ‖d‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (‖f z‖ + ‖d‖) ^ 2 ≤ 2 * ‖f z‖ ^ 2 + 2 * ‖d‖ ^ 2 := by
      nlinarith [sq_nonneg (‖f z‖ - ‖d‖)]
    have h4 : ‖‖f z + d‖ ^ 2‖ = ‖f z + d‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h4]
    exact h2.trans h3

theorem memL2LocOn_const_mul_add {f : ℂ → ℂ} {U : Set ℂ} (h : MemL2LocOn f U) (c d : ℂ)
    (hm : AEStronglyMeasurable f (volume.restrict U)) :
    MemL2LocOn (fun z => c * f z + d) U := by
  have hm' : AEStronglyMeasurable (fun z => c * f z) (volume.restrict U) :=
    (by fun_prop : Continuous fun w : ℂ => c * w).comp_aestronglyMeasurable hm
  exact memL2LocOn_add_const (memL2LocOn_const_mul h c) d hm'

/-! ## Transport of the homeomorphism clause -/

theorem isHomeomorphOn_const_mul_add {f : ℂ → ℂ} {U : Set ℂ} (h : IsHomeomorphOn f U)
    {c d : ℂ} (hc : c ≠ 0) : IsHomeomorphOn (fun z => c * f z + d) U := by
  obtain ⟨hcont, ginv, hginvcont, hleft, hright⟩ := h
  have hdiv : ∀ z : ℂ, (c * f z + d - d) / c = f z := by
    intro z
    rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hc]
  refine ⟨?_, fun w => ginv ((w - d) / c), ?_, ?_, ?_⟩
  · exact ((continuous_const.continuousOn).mul hcont).add continuousOn_const
  · refine hginvcont.comp ?_ ?_
    · exact ((continuous_id.sub continuous_const).div_const c).continuousOn
    · rintro w ⟨z, hz, rfl⟩
      simp only
      rw [hdiv z]
      exact ⟨z, hz, rfl⟩
  · intro x hx
    simp only
    rw [hdiv x, hleft x hx]
  · rintro y ⟨x, hx, rfl⟩
    simp only
    rw [hdiv x, hright (f x) ⟨x, hx, rfl⟩]

/-! ## Transport of the whole structure -/

theorem hasW12LocOn_const_mul_add {f : ℂ → ℂ} {U : Set ℂ} (h : HasW12LocOn f U) (c d : ℂ) :
    HasW12LocOn (fun z => c * f z + d) U := by
  obtain ⟨hL2, gz, gzbar, hdz, hdbar, hgzL2, hgzbarL2, hgzag, hgzbarag⟩ := h
  have hm : AEStronglyMeasurable f (volume.restrict U) := hdz.1.aestronglyMeasurable
  refine ⟨memL2LocOn_const_mul_add hL2 c d hm, fun z => c * gz z, fun z => c * gzbar z,
    isDzDerivOn_const_mul_add hdz c d, isDbarDerivOn_const_mul_add hdbar c d,
    memL2LocOn_const_mul hgzL2 c, memL2LocOn_const_mul hgzbarL2 c, ?_, ?_⟩
  · filter_upwards [hgzag] with z hz
    rw [hz, dz_const_mul_add]
  · filter_upwards [hgzbarag] with z hz
    rw [hz, dzbar_const_mul_add]

/-- **Post-composition by an affine map preserves quasiconformality and its dilatation.** -/
theorem isQCOn_const_mul_add {f : ℂ → ℂ} {U : Set ℂ} {μ : ℂ → ℂ} (h : IsQCOn f U μ)
    {c d : ℂ} (hc : c ≠ 0) : IsQCOn (fun z => c * f z + d) U μ := by
  obtain ⟨hU, hhom, hW, hk, hrel⟩ := h
  refine ⟨hU, isHomeomorphOn_const_mul_add hhom hc, hasW12LocOn_const_mul_add hW c d, hk, ?_⟩
  filter_upwards [hrel] with z hz hzU
  rw [dzbar_const_mul_add, dz_const_mul_add, hz hzU]
  ring

/-! ## Application: normalisation at `0` and `1` -/

/-- Normalising a quasiconformal map by `z ↦ (φ z - φ 0)/(φ 1 - φ 0)` does not change its
complex dilatation. -/
theorem isQCOn_normalized {φ : ℂ → ℂ} {μ : ℂ → ℂ} (h : IsQCOn φ Set.univ μ)
    (h01 : φ 1 ≠ φ 0) : IsQCOn (fun z => (φ z - φ 0) / (φ 1 - φ 0)) Set.univ μ := by
  have hne : φ 1 - φ 0 ≠ 0 := sub_ne_zero.mpr h01
  have h' := isQCOn_const_mul_add h (c := (φ 1 - φ 0)⁻¹)
    (d := -(φ 0) * (φ 1 - φ 0)⁻¹) (inv_ne_zero hne)
  convert h' using 1
  funext z
  field_simp
  ring

/-- A quasiconformal homeomorphism `φ` of `ℂ` with dilatation `μ` gives a normalized
quasiconformal solution `f` with `f 0 = 0` and `f 1 = 1`, and the same dilatation `μ`. -/
theorem exists_normalized_of_qc_homeo (μ : Beltrami) (φ : ℂ ≃ₜ ℂ)
    (hφ : IsQCOn (φ : ℂ → ℂ) Set.univ ↑μ) :
    ∃ f : ℂ → ℂ, IsQuasiconformal f ↑μ ∧ FixesZeroOne f := by
  have h01 : (φ : ℂ → ℂ) 1 ≠ (φ : ℂ → ℂ) 0 := by
    intro h
    have h' : (1 : ℂ) = 0 := φ.injective h
    norm_num at h'
  have hne : (φ : ℂ → ℂ) 1 - (φ : ℂ → ℂ) 0 ≠ 0 := sub_ne_zero.mpr h01
  refine ⟨fun z => ((φ : ℂ → ℂ) z - φ 0) / ((φ : ℂ → ℂ) 1 - φ 0),
    ⟨⟨isQCOn_normalized hφ h01, ?_⟩, ?_, ?_⟩⟩
  · intro w
    obtain ⟨z, hz⟩ := φ.surjective ((φ : ℂ → ℂ) 0 + w * ((φ : ℂ → ℂ) 1 - φ 0))
    refine ⟨z, ?_⟩
    simp only
    rw [hz, add_sub_cancel_left, mul_div_cancel_right₀ _ hne]
  · simp
  · field_simp

end Work.MRMT.AhlforsBers
