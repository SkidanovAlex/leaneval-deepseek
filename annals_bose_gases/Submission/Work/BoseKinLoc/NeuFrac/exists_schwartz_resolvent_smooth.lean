import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The resolvent multiplier `(‖p‖²+c)⁻¹` on smooth compactly supported data

For a smooth compactly supported real function `ψ` on `ℝ³` and `c > 0` there is a
real-valued Schwartz function `W` with

`kinFT W p = (‖p‖² + c)⁻¹ · kinFT ψ p`.

`W` is `(-Δ + c)⁻¹ ψ`: with `kinFT u p = 𝓕 u ((2π)⁻¹ • p)` the p-convention Fourier
transform (`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`), the resolvent symbol
`p ↦ (‖p‖² + c)⁻¹` corresponds in frequency space to multiplication by

`ξ ↦ c⁻¹ (1 + ‖(2π/√c) • ξ‖²)⁻¹`,

which is of temperate growth (so that Mathlib's `SchwartzMap.smulLeftCLM` applies to
Schwartz functions).  Reality of `W = 𝓕⁻ (m · 𝓕 ψ)` follows from the conjugate symmetry
`𝓕 ψ (-v) = conj (𝓕 ψ v)` that holds because `ψ` is real valued.
-/

noncomputable section

open scoped ContDiff FourierTransform
open MeasureTheory

namespace Work.BoseKinLoc.NeuFrac

/-- The Fourier character is conjugate to its value at the negated argument. -/
theorem conj_fourierChar (a : ℝ) :
    (starRingEnd ℂ) (Real.fourierChar a : ℂ) = (Real.fourierChar (-a) : ℂ) := by
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]

/-- Complex conjugation commutes with the Fourier transform, at the cost of reflecting
the frequency argument. -/
theorem conj_fourier {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    (g : V → ℂ) (v : V) :
    (starRingEnd ℂ) (𝓕 g v) = 𝓕⁻ (fun y => (starRingEnd ℂ) (g y)) v := by
  rw [Real.fourierInv_eq, Real.fourier_eq]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with y
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, map_mul, conj_fourierChar]
  ring_nf

/-- Complex conjugation commutes with the inverse Fourier transform, at the cost of
reflecting the frequency argument. -/
theorem conj_fourierInv {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    (u : V → ℂ) (x : V) :
    (starRingEnd ℂ) (𝓕⁻ u x) = 𝓕 (fun y => (starRingEnd ℂ) (u y)) x := by
  rw [Real.fourierInv_eq, Real.fourier_eq]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with y
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, map_mul, conj_fourierChar]

/-- A real-valued function has a conjugate-symmetric Fourier transform. -/
theorem fourier_neg_eq_conj_ofReal {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    (f : V → ℝ) (v : V) :
    𝓕 (fun y => (f y : ℂ)) (-v) = (starRingEnd ℂ) (𝓕 (fun y => (f y : ℂ)) v) := by
  have hfun : (fun y : V => (starRingEnd ℂ) ((f y : ℂ))) = fun y => (f y : ℂ) := by
    funext y
    exact Complex.conj_ofReal (f y)
  rw [conj_fourier, hfun, Real.fourierInv_eq_fourier_neg]

/-- A conjugate-symmetric function has a real inverse Fourier transform. -/
theorem im_fourierInv_eq_zero_of_symm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    (u : V → ℂ) (hu : ∀ v, u (-v) = (starRingEnd ℂ) (u v)) (x : V) :
    (𝓕⁻ u x).im = 0 := by
  have hfun : (fun y : V => (starRingEnd ℂ) (u y)) = fun y => u (-y) := by
    funext y
    exact (hu y).symm
  have key : 𝓕⁻ u x = (starRingEnd ℂ) (𝓕⁻ u x) := by
    rw [conj_fourierInv, hfun, ← Real.fourierInv_eq_fourier_comp_neg]
  have := congrArg Complex.im key
  simp only [Complex.conj_im] at this
  linarith

/-- The resolvent multiplier `ξ ↦ (c + ‖2π ξ‖²)⁻¹`, written in a form that is manifestly
of temperate growth: `c⁻¹ (1 + ‖(2π/√c) • ξ‖²)⁻¹`. -/
noncomputable def resolvMult (c : ℝ) : EuclideanSpace ℝ (Fin 3) → ℂ :=
  fun ξ => ((c⁻¹ * (1 + ‖(2 * Real.pi / Real.sqrt c) • ξ‖ ^ 2) ^ (-1 : ℝ) : ℝ) : ℂ)

theorem hasTemperateGrowth_resolvMult (c : ℝ) :
    Function.HasTemperateGrowth (resolvMult c) := by
  have hinner : Function.HasTemperateGrowth
      (fun v : EuclideanSpace ℝ (Fin 3) => (1 + ‖v‖ ^ 2) ^ (-1 : ℝ)) :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow (EuclideanSpace ℝ (Fin 3)) (-1)
  have hscale : Function.HasTemperateGrowth
      (fun ξ : EuclideanSpace ℝ (Fin 3) => (2 * Real.pi / Real.sqrt c) • ξ) := by fun_prop
  have hM : Function.HasTemperateGrowth
      (fun ξ : EuclideanSpace ℝ (Fin 3) =>
        c⁻¹ * (1 + ‖(2 * Real.pi / Real.sqrt c) • ξ‖ ^ 2) ^ (-1 : ℝ)) :=
    (Function.HasTemperateGrowth.const c⁻¹).mul (hinner.comp hscale)
  exact Function.Complex.hasTemperateGrowth_ofReal.comp hM

theorem resolvMult_neg (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    resolvMult c (-ξ) = resolvMult c ξ := by
  simp only [resolvMult, smul_neg, norm_neg]

theorem resolvMult_conj (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    (starRingEnd ℂ) (resolvMult c ξ) = resolvMult c ξ := by
  rw [resolvMult, Complex.conj_ofReal]

theorem resolvMult_apply_inv_smul (c : ℝ) (hc : 0 < c)
    (p : EuclideanSpace ℝ (Fin 3)) :
    resolvMult c ((2 * Real.pi)⁻¹ • p) = ((‖p‖ ^ 2 + c)⁻¹ : ℂ) := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hcoef : (2 * Real.pi / Real.sqrt c) * (2 * Real.pi)⁻¹ = (Real.sqrt c)⁻¹ := by
    field_simp
  have hnorm : ‖(2 * Real.pi / Real.sqrt c) • ((2 * Real.pi)⁻¹ • p)‖ ^ 2
      = c⁻¹ * ‖p‖ ^ 2 := by
    rw [smul_smul, hcoef]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsc)]
    rw [mul_pow, inv_pow, Real.sq_sqrt hc.le]
  have hreal : c⁻¹ * (1 + ‖(2 * Real.pi / Real.sqrt c) • ((2 * Real.pi)⁻¹ • p)‖ ^ 2) ^ (-1 : ℝ)
      = (‖p‖ ^ 2 + c)⁻¹ := by
    rw [hnorm, Real.rpow_neg_one]
    field_simp
    ring
  simp only [resolvMult]
  exact_mod_cast hreal

theorem exists_schwartz_resolvent_smooth (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hcs : HasCompactSupport ψ) {c : ℝ} (hc : 0 < c) :
    ∃ W : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ,
      (∀ x, (W x).im = 0) ∧
      (∀ p, Submission.BoseGases.kinFT (W : EuclideanSpace ℝ (Fin 3) → ℂ) p
        = ((‖p‖ ^ 2 + c)⁻¹ : ℂ) *
            Submission.BoseGases.kinFT (fun y => (ψ y : ℂ)) p) := by
  have hψcs : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin 3) => (ψ y : ℂ)) :=
    hcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hψcd : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 3) => (ψ y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hψ
  let ψc : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
    HasCompactSupport.toSchwartzMap hψcs hψcd
  have hψc : (ψc : EuclideanSpace ℝ (Fin 3) → ℂ) = fun y => (ψ y : ℂ) := rfl
  set X : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (resolvMult c) (𝓕 ψc) with hX
  set W : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ := 𝓕⁻ X with hW
  refine ⟨W, ?_, ?_⟩
  · intro x
    rw [hW, SchwartzMap.fourierInv_coe]
    refine im_fourierInv_eq_zero_of_symm _ ?_ x
    intro v
    rw [hX]
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_resolvMult c),
        SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_resolvMult c),
        SchwartzMap.fourier_coe, hψc]
    rw [smul_eq_mul, smul_eq_mul, map_mul, resolvMult_neg,
        fourier_neg_eq_conj_ofReal ψ v, resolvMult_conj]
  · intro p
    have hF : 𝓕 (W : EuclideanSpace ℝ (Fin 3) → ℂ) = (X : EuclideanSpace ℝ (Fin 3) → ℂ) := by
      rw [hW, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
    calc Submission.BoseGases.kinFT (W : EuclideanSpace ℝ (Fin 3) → ℂ) p
        = 𝓕 (W : EuclideanSpace ℝ (Fin 3) → ℂ) ((2 * Real.pi)⁻¹ • p) :=
            Work.SmallBoxBridge.Resolve.kinFT_eq_fourier _ _
      _ = (X : EuclideanSpace ℝ (Fin 3) → ℂ) ((2 * Real.pi)⁻¹ • p) := by rw [hF]
      _ = ((‖p‖ ^ 2 + c)⁻¹ : ℂ) *
            Submission.BoseGases.kinFT (fun y => (ψ y : ℂ)) p := by
            rw [hX]
            rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_resolvMult c),
                smul_eq_mul, resolvMult_apply_inv_smul c hc p]
            congr 1
            rw [SchwartzMap.fourier_coe, hψc]
            exact (Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
              (fun y : EuclideanSpace ℝ (Fin 3) => (ψ y : ℂ)) p).symm

end Work.BoseKinLoc.NeuFrac
