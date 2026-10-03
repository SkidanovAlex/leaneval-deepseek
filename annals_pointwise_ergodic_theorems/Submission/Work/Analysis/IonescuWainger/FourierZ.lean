/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.IonescuWainger.Pset

/-!
# The Fourier transform on `ℤ` and Fourier multipliers on `ℓ²(ℤ)`

The dual of `ℤ` is the circle `ℝ/ℤ = Circle`.  We record the isometric isomorphism
`𝓕_ℤ : ℓ²(ℤ) ≃ L²(ℝ/ℤ)` given by Mathlib's Hilbert basis `fourierBasis`, and define the
Fourier multiplier `T_m` with a bounded measurable symbol `m` on the circle, acting on
`ℓ²(ℤ)`.  This is the ambient setting for the Ionescu–Wainger Fourier projections of
Krause–Mirek–Tao, Appendix A and §5.

## Main definitions

* `Work.Analysis.IonescuWainger.L2Z` — `ℓ²(ℤ; ℂ)` as Mathlib's `lp` space;
* `Work.Analysis.IonescuWainger.fourierZ` — the Fourier transform `ℓ²(ℤ) ≃ L²(ℝ/ℤ)`;
* `Work.Analysis.IonescuWainger.circleMulOp` — multiplication of `L²(ℝ/ℤ)` by `L^∞(ℝ/ℤ)`;
* `Work.Analysis.IonescuWainger.multiplier` — the Fourier multiplier `T_m` on `ℓ²(ℤ)`;
* `Work.Analysis.IonescuWainger.multiplierOf` — `T_m` for a bounded measurable `m : Circle → ℂ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

open MeasureTheory

/-- `ℓ²(ℤ; ℂ)`, realised as Mathlib's `lp` space. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℂ) 2

/-- Haar measure on the frequency circle `ℝ/ℤ`, of total mass `1`. -/
noncomputable abbrev circleMeasure : Measure Circle := AddCircle.haarAddCircle (T := 1)

/-- The Fourier transform `𝓕_ℤ : ℓ²(ℤ) → L²(ℝ/ℤ)`, the isometric isomorphism sending the
sequence `f` to the function `ξ ↦ ∑' n, f n • e(n ξ)` on the circle. -/
noncomputable def fourierZ : L2Z ≃ₗᵢ[ℂ] Lp ℂ 2 circleMeasure :=
  (fourierBasis (T := 1)).repr.symm

theorem fourierZ_hasSum (f : L2Z) :
    HasSum (fun n : ℤ => f n • fourierLp (T := 1) 2 n) (fourierZ f) := by
  simpa only [fourierZ, coe_fourierBasis] using
    HilbertBasis.hasSum_repr_symm (fourierBasis (T := 1)) f

/-- Multiplication of `L²(ℝ/ℤ)` by an element of `L^∞(ℝ/ℤ)` (Hölder with exponents
`∞, 2, 2`). -/
noncomputable def circleMulOp (m : Lp ℂ ⊤ circleMeasure) :
    Lp ℂ 2 circleMeasure →L[ℂ] Lp ℂ 2 circleMeasure :=
  LinearMap.mkContinuous
    { toFun := fun g => m • g
      map_add' := fun g₁ g₂ => Lp.add_smul m g₁ g₂
      map_smul' := fun c g => (Lp.smul_comm c m g).symm }
    ‖m‖ fun g => Lp.norm_smul_le m g

@[simp]
theorem circleMulOp_apply (m : Lp ℂ ⊤ circleMeasure) (g : Lp ℂ 2 circleMeasure) :
    circleMulOp m g = m • g := rfl

theorem norm_circleMulOp_le (m : Lp ℂ ⊤ circleMeasure) : ‖circleMulOp m‖ ≤ ‖m‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- The Fourier multiplier `T_m` on `ℓ²(ℤ)` with symbol `m ∈ L^∞(ℝ/ℤ)`: for `f ∈ ℓ²(ℤ)`,
`𝓕_ℤ (T_m f) = m · 𝓕_ℤ f`. -/
noncomputable def multiplier (m : Lp ℂ ⊤ circleMeasure) : L2Z →L[ℂ] L2Z :=
  (fourierZ.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((circleMulOp m).comp fourierZ.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The characterising property of `T_m`: it acts on the Fourier side by multiplication by the
symbol. -/
theorem fourierZ_multiplier (m : Lp ℂ ⊤ circleMeasure) (f : L2Z) :
    fourierZ (multiplier m f) = m • fourierZ f := by
  show fourierZ (fourierZ.symm (circleMulOp m (fourierZ f))) = m • fourierZ f
  rw [LinearIsometryEquiv.apply_symm_apply, circleMulOp_apply]

theorem norm_multiplier_le (m : Lp ℂ ⊤ circleMeasure) : ‖multiplier m‖ ≤ ‖m‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => by
    calc ‖multiplier m f‖ = ‖fourierZ (multiplier m f)‖ := (fourierZ.norm_map _).symm
      _ = ‖m • fourierZ f‖ := by rw [fourierZ_multiplier]
      _ ≤ ‖m‖ * ‖fourierZ f‖ := Lp.norm_smul_le (p := ⊤) (q := 2) (r := 2) m (fourierZ f)
      _ = ‖m‖ * ‖f‖ := by rw [fourierZ.norm_map]

/-- The Fourier multiplier with a bounded measurable symbol `m : ℝ/ℤ → ℂ`. -/
noncomputable def multiplierOf (m : Circle → ℂ) (hm : MemLp m ⊤ circleMeasure) :
    L2Z →L[ℂ] L2Z :=
  multiplier (hm.toLp m)

theorem fourierZ_multiplierOf (m : Circle → ℂ) (hm : MemLp m ⊤ circleMeasure) (f : L2Z) :
    fourierZ (multiplierOf m hm f) = hm.toLp m • fourierZ f :=
  fourierZ_multiplier (hm.toLp m) f

/-- A multiplier whose symbol has `eLpNorm ≤ C` (`∞`-norm `≤ C`) has operator norm at most `C`. -/
theorem norm_multiplierOf_le {m : Circle → ℂ} (hm : MemLp m ⊤ circleMeasure)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : eLpNorm m ⊤ circleMeasure ≤ ENNReal.ofReal C) :
    ‖multiplierOf m hm‖ ≤ C := by
  refine le_trans (norm_multiplier_le _) ?_
  rw [Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal hC0 ?_
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp hm)]
  exact hC

end Work.Analysis.IonescuWainger
