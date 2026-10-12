import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.Work.SmallBoxBridge.Bridge
import Submission.Work.SmallBoxModeParseval
import Submission.Work.SmallBoxSpectral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-288 — the WINDOW-GENERIC mode layer

`Submission/Work/SmallBoxPairMode.qMode` and `Submission/Work/SmallBoxKineticP.kinPWord` are
written for ONE window: the corpus's `chiScale ℓ` (an `L²`-normalised radial bump supported in
`ball(0,ℓ/2) ⊆ acube ℓ`).  This module re-develops the mode layer for an ARBITRARY real window
`χ : ℝ³ → ℝ`:

    winChat χ ℓ p       = ∫_{acube ℓ} χ(y) e^{−i⟨p,y⟩} dy            (the χ-mean)
    winQMode χ ℓ p y    = χ(y) e^{−i⟨p,y⟩} − ℓ^{−3} winChat χ ℓ p    (the Q_B-projected mode)
    winQModeRe/Im       = its real / imaginary parts
    winKinPWord χ s c Φ = (2π)^{−3} ∫_p [‖p‖−c]₊² (P_{u_p} + P_{v_p}) dp

with `u_p + i v_p = winQMode χ s p` and `modeP` (window-FREE in the mode) from
`SmallBoxKineticP`.

## What this buys

* **Compatibility**: `chiScale` is the special case — `winQMode (chiScale ℓ) ℓ p = qMode ℓ p`
  and `winKinPWord (chiScale s) s c Φ = kinPWord s c Φ` (both `rfl`), so every statement below
  specialises to the corpus's objects.

* **The window-scaling law** (the reason D1's kinetic word is RIGID): the mode, and hence the
  word, is homogeneous of degree 2 in the window,

      winQMode (fun y => c * χ y) ℓ p     = c • winQMode χ ℓ p
      winKinPWord (fun y => c * χ y) s c' Φ = c² * winKinPWord χ s c' Φ.

  D1's word therefore cannot be renormalised independently of the window: any change of the
  window multiplies the word by a FACTOR, and the position-space pairing kernel
  `wPairC s (g0 v h) = chiScale(x)·WS₁(x−y)·chiScale(y)`
  (`Submission/Work/QDecompSimpler.q4PairWord`) is multiplied by the SAME factor — so the pair
  (word, pairing) can never be re-balanced.  See `WinObstruction.lean` for the resulting no-go.

* **Nonnegativity** of the windowed word (`winKinPWord_nonneg`).
-/

noncomputable section

open MeasureTheory Metric Filter
open Classical
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxA0

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1 The window-generic mode -/

/-- The χ-mean of the momentum mode `χ(y)e^{-i⟨p,y⟩}` over the box `acube ℓ`. -/
noncomputable def winChat (χ : ℝ³ → ℝ) (ℓ : ℝ) (p : ℝ³) : ℂ :=
  ∫ y in acube ℓ, (χ y : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))

/-- The `Q_B`-projected χ-momentum mode `g_p(y) = χ(y)e^{-i⟨p,y⟩} − |B|^{-1}c_p`. -/
noncomputable def winQMode (χ : ℝ³ → ℝ) (ℓ : ℝ) (p y : ℝ³) : ℂ :=
  (χ y : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
    - ((ℓ ^ 3)⁻¹ : ℂ) * winChat χ ℓ p

/-- Real part of the windowed mode. -/
noncomputable def winQModeRe (χ : ℝ³ → ℝ) (ℓ : ℝ) (p : ℝ³) : ℝ³ → ℝ :=
  fun y => (winQMode χ ℓ p y).re

/-- Imaginary part of the windowed mode. -/
noncomputable def winQModeIm (χ : ℝ³ → ℝ) (ℓ : ℝ) (p : ℝ³) : ℝ³ → ℝ :=
  fun y => (winQMode χ ℓ p y).im

/-- The window-generic D1 kinetic word `(2π)^{-3}∫_p [‖p‖−c]₊² (P_{u_p}+P_{v_p})`. -/
noncomputable def winKinPWord (χ : ℝ³ → ℝ) (s c : ℝ) {n : ℕ} (Φ : X (n + 1) → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ ^ 3 * ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
    (modeP s (winQModeRe χ s p) Φ + modeP s (winQModeIm χ s p) Φ)

/-! ## 2 Compatibility with the corpus's `chiScale` window -/

@[simp] lemma winChat_chiScale (ℓ : ℝ) (p : ℝ³) :
    winChat (chiScale ℓ) ℓ p = modeChat ℓ p := rfl

@[simp] lemma winQMode_chiScale (ℓ : ℝ) (p y : ℝ³) :
    winQMode (chiScale ℓ) ℓ p y = qMode ℓ p y := rfl

@[simp] lemma winQModeRe_chiScale (ℓ : ℝ) (p : ℝ³) :
    winQModeRe (chiScale ℓ) ℓ p = qModeRe ℓ p := rfl

@[simp] lemma winQModeIm_chiScale (ℓ : ℝ) (p : ℝ³) :
    winQModeIm (chiScale ℓ) ℓ p = qModeIm ℓ p := rfl

@[simp] lemma winKinPWord_chiScale {s c : ℝ} {n : ℕ} (Φ : X (n + 1) → ℝ) :
    winKinPWord (chiScale s) s c Φ = kinPWord s c Φ := rfl

/-! ## 3 The window-scaling law (degree 2 in the window) -/

/-- The χ-mean is ℂ-linear (degree 1) in the window. -/
lemma winChat_smul (χ : ℝ³ → ℝ) (c ℓ : ℝ) (p : ℝ³) :
    winChat (fun y => c * χ y) ℓ p = (c : ℂ) * winChat χ ℓ p := by
  unfold winChat
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Complex.ofReal_mul]
  ring

/-- The mode is ℂ-linear (degree 1) in the window. -/
lemma winQMode_smul (χ : ℝ³ → ℝ) (c ℓ : ℝ) (p y : ℝ³) :
    winQMode (fun z => c * χ z) ℓ p y = (c : ℂ) * winQMode χ ℓ p y := by
  unfold winQMode
  rw [winChat_smul]
  simp only [Complex.ofReal_mul]
  ring

lemma winQModeRe_smul (χ : ℝ³ → ℝ) (c ℓ : ℝ) (p : ℝ³) :
    winQModeRe (fun z => c * χ z) ℓ p = c • winQModeRe χ ℓ p := by
  funext y
  simp only [winQModeRe, Pi.smul_apply, smul_eq_mul]
  rw [winQMode_smul, Complex.mul_re]
  simp

lemma winQModeIm_smul (χ : ℝ³ → ℝ) (c ℓ : ℝ) (p : ℝ³) :
    winQModeIm (fun z => c * χ z) ℓ p = c • winQModeIm χ ℓ p := by
  funext y
  simp only [winQModeIm, Pi.smul_apply, smul_eq_mul]
  rw [winQMode_smul, Complex.mul_im]
  simp

/-- `boxOp s 1` is ℝ-linear in the mode. -/
lemma boxOp_one_smul_mode {s : ℝ} {N : ℕ} (c : ℝ) (g : ℝ³ → ℝ) (Ψ : X N → ℝ) (x : X N) :
    boxOp s (fun _ => (1 : ℝ)) (fun z => c * g z) Ψ x
      = c * boxOp s (fun _ => (1 : ℝ)) g Ψ x := by
  unfold boxOp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz : (∫ z in acube s, (c * g z) * Ψ (Function.update x i z))
      = c * ∫ z in acube s, g z * Ψ (Function.update x i z) := by
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  rw [hz]
  ring

/-- `modeP` is quadratic (degree 2) in the mode. -/
lemma modeP_smul_mode {s : ℝ} {n : ℕ} (c : ℝ) (g : ℝ³ → ℝ) (Φ : X (n + 1) → ℝ) :
    modeP s (fun z => c * g z) Φ = c ^ 2 * modeP s g Φ := by
  unfold modeP
  have h1 : (∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) (fun z => c * g z) Φ x) ^ 2)
      = ∫ x in abox (n + 1) s, (c * boxOp s (fun _ => (1 : ℝ)) g Φ x) ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only []
      rw [boxOp_one_smul_mode])
  rw [h1]
  have h2 : (∫ x in abox (n + 1) s, (c * boxOp s (fun _ => (1 : ℝ)) g Φ x) ^ 2)
      = c ^ 2 * ∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Φ x) ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [h2]
  ring

/-- `modeP` is quadratic in the mode (pointwise-scalar form, used with `•`). -/
lemma modeP_smul_function {s : ℝ} {n : ℕ} (c : ℝ) (g : ℝ³ → ℝ) (Φ : X (n + 1) → ℝ) :
    modeP s (c • g) Φ = c ^ 2 * modeP s g Φ := by
  rw [show (c • g) = fun z => c * g z from
    funext fun z => by rw [Pi.smul_apply, smul_eq_mul]]
  exact modeP_smul_mode c g Φ

/-- **The window-scaling law**: the D1 word is homogeneous of degree 2 in the window. -/
theorem winKinPWord_smul (χ : ℝ³ → ℝ) (c s c' : ℝ) {n : ℕ} (Φ : X (n + 1) → ℝ) :
    winKinPWord (fun z => c * χ z) s c' Φ = c ^ 2 * winKinPWord χ s c' Φ := by
  unfold winKinPWord
  rw [show (∫ p : ℝ³, fsKinCoeff c' ‖p‖ *
        (modeP s (winQModeRe (fun z => c * χ z) s p) Φ
          + modeP s (winQModeIm (fun z => c * χ z) s p) Φ))
      = ∫ p : ℝ³, c ^ 2 * (fsKinCoeff c' ‖p‖ *
        (modeP s (winQModeRe χ s p) Φ + modeP s (winQModeIm χ s p) Φ)) from by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only []
    rw [winQModeRe_smul, winQModeIm_smul, modeP_smul_function, modeP_smul_function]
    ring]
  rw [MeasureTheory.integral_const_mul]
  ring

/-! ## 4 Nonnegativity -/

lemma winKinPWord_nonneg (χ : ℝ³ → ℝ) {s c : ℝ} (hs : 0 < s) {n : ℕ} (Φ : X (n + 1) → ℝ) :
    0 ≤ winKinPWord χ s c Φ := by
  unfold winKinPWord
  refine mul_nonneg (by positivity) ?_
  refine integral_nonneg fun p => ?_
  exact mul_nonneg (fsKinCoeff_nonneg c ‖p‖)
    (add_nonneg (modeP_nonneg hs _ Φ) (modeP_nonneg hs _ Φ))

/-! ## 5 Continuity of the windowed mode -/

/-- The windowed mode is continuous in `y` for a continuous window. -/
lemma continuous_winQMode {χ : ℝ³ → ℝ} (hχc : Continuous χ) (ℓ : ℝ) (p : ℝ³) :
    Continuous (fun y : ℝ³ => winQMode χ ℓ p y) := by
  unfold winQMode
  exact ((Complex.continuous_ofReal.comp hχc).mul
    (Complex.continuous_exp.comp ((continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))).neg))).sub
    continuous_const

/-! ## 6 The mode multiplication table -/

/-- **The `Q_B`-projected mode multiplication table** `g_p(y)·g_{−p}(z)`: the four-term
expansion of `(χ(y)e^{−i⟨p,y⟩} − |B|^{−1}c_p)(χ(z)e^{i⟨p,z⟩} − |B|^{−1}c_{−p})`. -/
theorem winQMode_mul {χ : ℝ³ → ℝ} {ℓ : ℝ} (p y z : ℝ³) :
    winQMode χ ℓ p y * winQMode χ ℓ (-p) z
      = (χ y : ℂ) * (χ z : ℂ) * Complex.exp (Complex.I * ((inner ℝ p (z - y) : ℝ) : ℂ))
        - ((ℓ ^ 3)⁻¹ : ℂ) * winChat χ ℓ p * (χ z : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ p z : ℝ) : ℂ))
        - ((ℓ ^ 3)⁻¹ : ℂ) * winChat χ ℓ (-p) * (χ y : ℂ)
            * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        + ((ℓ ^ 3)⁻¹ : ℂ) * ((ℓ ^ 3)⁻¹ : ℂ) * winChat χ ℓ p * winChat χ ℓ (-p) := by
  have hy : Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * Complex.exp (Complex.I * ((inner ℝ p z : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((inner ℝ p (z - y) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [inner_sub_right]
    push_cast
    ring
  have hz : Complex.exp (-(Complex.I * ((inner ℝ (-p) z : ℝ) : ℂ)))
      = Complex.exp (Complex.I * ((inner ℝ p z : ℝ) : ℂ)) := by
    rw [inner_neg_left]
    push_cast
    ring_nf
  simp only [winQMode, winChat]
  rw [hz, hy.symm]
  ring

/-! ## 7 Mean vanishing of the projected mode -/

/-- **`∫_{acube} g_p = 0`**: the `Q_B`-projection is mean-free. -/
theorem integral_winQMode_eq_zero {χ : ℝ³ → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hχc : Continuous χ)
    (p : ℝ³) :
    ∫ y in acube ℓ, winQMode χ ℓ p y = 0 := by
  have h1 : ∫ y in acube ℓ, (χ y : ℂ)
      * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) = winChat χ ℓ p := rfl
  have h2 : ∫ y in acube ℓ, ((ℓ ^ 3)⁻¹ : ℂ) * winChat χ ℓ p
      = (ℓ ^ 3 : ℝ) • (((ℓ ^ 3)⁻¹ : ℂ) * winChat χ ℓ p) := by
    rw [MeasureTheory.integral_const, real_volume_acube ℓ hℓ.le]
  have hmode : (fun y : ℝ³ => (χ y : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))))
      = fun y : ℝ³ => winQMode χ ℓ p y + ((ℓ ^ 3)⁻¹ : ℂ) * winChat χ ℓ p := by
    funext y; simp only [winQMode]; ring
  have hInt1 : IntegrableOn
      (fun y : ℝ³ => (χ y : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))))
      (acube ℓ) volume := by
    rw [hmode]
    exact ContinuousOn.integrableOn_compact (acube_compact hℓ)
      ((continuous_winQMode hχc ℓ p).continuousOn.add continuousOn_const)
  have hInt2 : IntegrableOn (fun y : ℝ³ => ((ℓ ^ 3)⁻¹ : ℂ) * winChat χ ℓ p) (acube ℓ) volume :=
    integrableOn_const (hs := ne_of_lt (acube_lt_top ℓ hℓ.le))
  simp only [winQMode]
  rw [MeasureTheory.integral_sub hInt1 hInt2, h1, h2]
  have hcast : (((ℓ ^ 3 : ℝ)) : ℂ) = ((ℓ : ℂ)) ^ 3 := by push_cast; ring
  rw [Algebra.smul_def]
  push_cast
  have hne : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
  field_simp
  simp

/-! ## 8 The Bessel (commutator) bound for an arbitrary window -/

/-- **`∫_{acube}(Re² + Im²) ≤ ∫_{acube} χ²`** — FS's `[b_p,b_p†] ≤ n₀|B|^{−1}∫χ_B²` input, for an
arbitrary continuous window: the `Q_B`-projection removes the mean-square `ℓ^{−3}‖c_p‖²`, so the
window's mass `∫χ²` is the only datum. -/
lemma integral_winQMode_normSq {χ : ℝ³ → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hχc : Continuous χ)
    (p : ℝ³) :
    (∫ y in acube ℓ, (winQModeRe χ ℓ p y) ^ 2)
        + (∫ y in acube ℓ, (winQModeIm χ ℓ p y) ^ 2)
      = (∫ y in acube ℓ, (χ y) ^ 2) - (ℓ ^ 3)⁻¹ * ‖winChat χ ℓ p‖ ^ 2 := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top ℓ hℓ.le⟩
  set m : ℂ := ((ℓ ^ 3)⁻¹ : ℂ) * winChat χ ℓ p with hm
  have hsplit : winQMode χ ℓ p = fun y : ℝ³ => (χ y : ℂ)
      * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) - m := by
    funext y; rw [winQMode]
  have hct : Continuous (fun y : ℝ³ => (χ y : ℂ)
      * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) :=
    (Complex.continuous_ofReal.comp hχc).mul
      (Complex.continuous_exp.comp ((continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))).neg))
  have hsum : (∫ y in acube ℓ, (winQModeRe χ ℓ p y) ^ 2)
      + (∫ y in acube ℓ, (winQModeIm χ ℓ p y) ^ 2)
      = ∫ y in acube ℓ, ‖winQMode χ ℓ p y‖ ^ 2 := by
    rw [← integral_add]
    · exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
        simp only []
        rw [Complex.sq_norm, Complex.normSq_apply, winQModeRe, winQModeIm]; ring)
    · exact ContinuousOn.integrableOn_compact (acube_compact hℓ)
        (((Complex.continuous_re.comp (continuous_winQMode hχc ℓ p)).pow 2).continuousOn)
    · exact ContinuousOn.integrableOn_compact (acube_compact hℓ)
        (((Complex.continuous_im.comp (continuous_winQMode hχc ℓ p)).pow 2).continuousOn)
  rw [hsum]
  have hnormSq_full : ∀ y : ℝ³, Complex.normSq ((χ y : ℂ)
      * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) = (χ y) ^ 2 := by
    intro y
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    have hw : (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))).re = 0 := by
      simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im]
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, hw, Real.exp_zero, one_pow]
    ring
  have hpoint : ∀ y : ℝ³, ‖winQMode χ ℓ p y‖ ^ 2
      = ((χ y) ^ 2 + Complex.normSq m)
        - 2 * (((χ y : ℂ)
            * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) * star m).re := by
    intro y
    rw [Complex.sq_norm, hsplit, Complex.normSq_sub, hnormSq_full]
    simp only [Complex.star_def]
  have hdecomp : (∫ y in acube ℓ, ‖winQMode χ ℓ p y‖ ^ 2)
      = (∫ y in acube ℓ, ((χ y) ^ 2 + Complex.normSq m))
        - (∫ y in acube ℓ, 2 * (((χ y : ℂ)
            * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) * star m).re) := by
    rw [show (∫ y in acube ℓ, ‖winQMode χ ℓ p y‖ ^ 2)
        = ∫ y in acube ℓ, (((χ y) ^ 2 + Complex.normSq m)
            - 2 * (((χ y : ℂ)
                * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) * star m).re) from
      integral_congr_ae (Filter.Eventually.of_forall fun y => hpoint y)]
    rw [integral_sub (f := fun y : ℝ³ => (χ y) ^ 2 + Complex.normSq m)
      (g := fun y : ℝ³ => 2 * (((χ y : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) * star m).re)
      ((ContinuousOn.integrableOn_compact (acube_compact hℓ)
        (((hχc.pow 2).add continuous_const).continuousOn)) )
      (ContinuousOn.integrableOn_compact (acube_compact hℓ)
        (((Complex.continuous_re.comp (hct.mul continuous_const)).const_mul 2).continuousOn))]
  rw [hdecomp, integral_add (f := fun y : ℝ³ => (χ y) ^ 2)
    (g := fun _ : ℝ³ => Complex.normSq m)
    (ContinuousOn.integrableOn_compact (acube_compact hℓ) ((hχc.pow 2).continuousOn))
    (integrable_const _), integral_const_mul]
  have hI4 : Integrable (fun y : ℝ³ => (χ y : ℂ)
      * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * star m)
      ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ContinuousOn.integrableOn_compact (acube_compact hℓ) (hct.mul continuous_const).continuousOn
  have hosc : (∫ y in acube ℓ, (((χ y : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) * star m).re)
      = (winChat χ ℓ p * star m).re := by
    have h1 : (∫ y in acube ℓ, (((χ y : ℂ)
          * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) * star m).re)
        = (∫ y in acube ℓ, (χ y : ℂ)
            * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * star m).re :=
      Complex.reCLM.integral_comp_comm (φ := fun y : ℝ³ => (χ y : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * star m) hI4
    rw [h1, MeasureTheory.integral_mul_const]
    rfl
  rw [hosc]
  rw [MeasureTheory.integral_const, real_volume_acube ℓ hℓ.le, smul_eq_mul]
  have hr : ((ℓ ^ 3)⁻¹ : ℂ) = ((((ℓ ^ 3 : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; ring
  have hstar_inv : star (((ℓ ^ 3)⁻¹ : ℂ)) = ((ℓ ^ 3)⁻¹ : ℂ) := by
    rw [hr, Complex.star_def, Complex.conj_ofReal]
  have hsm : star m = ((ℓ ^ 3)⁻¹ : ℂ) * star (winChat χ ℓ p) := by
    rw [hm, star_mul, hstar_inv, mul_comm]
  have hnm : Complex.normSq m = (((ℓ ^ 3 : ℝ))⁻¹ * ((ℓ ^ 3 : ℝ))⁻¹)
      * ‖winChat χ ℓ p‖ ^ 2 := by
    rw [hm, Complex.normSq_mul, hr, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
  have hcs : (winChat χ ℓ p * star m).re = ((ℓ ^ 3 : ℝ))⁻¹ * ‖winChat χ ℓ p‖ ^ 2 := by
    have hcc : (winChat χ ℓ p * star (winChat χ ℓ p)).re = ‖winChat χ ℓ p‖ ^ 2 := by
      simp only [Complex.star_def]
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hci : (winChat χ ℓ p * star (winChat χ ℓ p)).im = 0 := by
      simp only [Complex.star_def]
      rw [Complex.mul_conj, Complex.ofReal_im]
    rw [hsm]
    have hassoc : winChat χ ℓ p * (((ℓ ^ 3)⁻¹ : ℂ) * star (winChat χ ℓ p))
        = ((ℓ ^ 3)⁻¹ : ℂ) * (winChat χ ℓ p * star (winChat χ ℓ p)) := by ring
    rw [hassoc, hr, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hcc, hci]
    ring
  rw [hcs, hnm]
  have hℓ3ne : (ℓ ^ 3 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- the Bessel form `‖g_p‖² ≤ ∫χ²`. -/
lemma integral_winQMode_normSq_le {χ : ℝ³ → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hχc : Continuous χ)
    (p : ℝ³) :
    (∫ y in acube ℓ, (winQModeRe χ ℓ p y) ^ 2)
        + (∫ y in acube ℓ, (winQModeIm χ ℓ p y) ^ 2)
      ≤ ∫ y in acube ℓ, (χ y) ^ 2 := by
  rw [integral_winQMode_normSq hℓ hχc p]
  have h : 0 ≤ (ℓ ^ 3)⁻¹ * ‖winChat χ ℓ p‖ ^ 2 := by positivity
  linarith

/-! ## 9 The word sees only the window's restriction to the box -/

/-- `modeP` depends only on the mode's restriction to `acube s` (all its integrals are over the
cube). -/
lemma modeP_congr_acube {s : ℝ} {n : ℕ} {g g' : ℝ³ → ℝ}
    (h : ∀ z ∈ acube s, g z = g' z) (Φ : X (n + 1) → ℝ) :
    modeP s g Φ = modeP s g' Φ := by
  unfold modeP
  congr 1
  refine setIntegral_congr_fun (abox_measurable (n + 1) s) fun x _ => ?_
  have hbox : boxOp s (fun _ => (1 : ℝ)) g Φ x = boxOp s (fun _ => (1 : ℝ)) g' Φ x := by
    unfold boxOp
    refine Finset.sum_congr rfl fun i _ => ?_
    have hz : (∫ z in acube s, g z * Φ (Function.update x i z))
        = ∫ z in acube s, g' z * Φ (Function.update x i z) :=
      setIntegral_congr_fun (acube_measurable s) fun z hz => by rw [h z hz]
    rw [hz]
  rw [hbox]

/-- The window restricted to the cube: `winRestrict χ s z = χ z` on `acube s`, `0` off it. -/
noncomputable def winRestrict (χ : ℝ³ → ℝ) (s : ℝ) : ℝ³ → ℝ := fun z => if z ∈ acube s then χ z else 0

lemma winRestrict_of_mem {χ : ℝ³ → ℝ} {s : ℝ} {z : ℝ³} (hz : z ∈ acube s) :
    winRestrict χ s z = χ z := by
  simp only [winRestrict, if_pos hz]

/-- **The D1 word is determined by the window's restriction to the cube.**  Since `boxOp`'s
integral runs over `acube s` only, replacing the window by `winRestrict χ s` does not change
`winKinPWord`.  (So a window `≡ 1` on the cube DEFINES the same word as the indicator
`1_{acube s}` — no re-normalisation of the window can change it.) -/
theorem winKinPWord_restrict_acube {χ : ℝ³ → ℝ} {s c : ℝ} {n : ℕ} (Φ : X (n + 1) → ℝ) :
    winKinPWord χ s c Φ = winKinPWord (winRestrict χ s) s c Φ := by
  have hchat : ∀ p : ℝ³, winChat (winRestrict χ s) s p = winChat χ s p := by
    intro p
    unfold winChat
    refine setIntegral_congr_fun (acube_measurable s) fun z hz => ?_
    rw [winRestrict_of_mem hz]
  have hmod : ∀ p : ℝ³, ∀ z ∈ acube s,
      winQModeRe (winRestrict χ s) s p z = winQModeRe χ s p z := by
    intro p z hz
    simp only [winQModeRe, winQMode, hchat p, winRestrict_of_mem hz]
  have him : ∀ p : ℝ³, ∀ z ∈ acube s,
      winQModeIm (winRestrict χ s) s p z = winQModeIm χ s p z := by
    intro p z hz
    simp only [winQModeIm, winQMode, hchat p, winRestrict_of_mem hz]
  unfold winKinPWord
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only []
  have h1 : modeP s (winQModeRe (winRestrict χ s) s p) Φ = modeP s (winQModeRe χ s p) Φ :=
    modeP_congr_acube (fun z hz => hmod p z hz) Φ
  have h2 : modeP s (winQModeIm (winRestrict χ s) s p) Φ = modeP s (winQModeIm χ s p) Φ :=
    modeP_congr_acube (fun z hz => him p z hz) Φ
  rw [h1, h2]
lemma winChat_eq_of_eqOn_acube {χ χ' : ℝ³ → ℝ} {s : ℝ}
    (h : ∀ z ∈ acube s, χ z = χ' z) (p : ℝ³) : winChat χ s p = winChat χ' s p := by
  unfold winChat
  refine setIntegral_congr_fun (acube_measurable s) fun z hz => by rw [h z hz]

/-- **RIGIDITY: the D1 word depends only on the window's values on `acube s`.**  In particular
every window that is `≡ 1` on the cube defines the SAME word (that of the indicator `1_{acube s}`),
so no re-normalisation of a `≡ 1` window can change the word — and by
`not_continuous_eq_one_on_box_supported_in_box` such a window cannot be supported inside the
cube, while by `winKinPWord_chiScale` the corpus's `chiScale` (supported inside) is not `≡ 1`. -/
theorem winKinPWord_eq_of_eqOn_acube {χ χ' : ℝ³ → ℝ} {s c : ℝ}
    (h : ∀ z ∈ acube s, χ z = χ' z) {n : ℕ} (Φ : X (n + 1) → ℝ) :
    winKinPWord χ s c Φ = winKinPWord χ' s c Φ := by
  have hchat : ∀ p : ℝ³, winChat χ s p = winChat χ' s p := fun p => winChat_eq_of_eqOn_acube h p
  have hmod : ∀ p : ℝ³, ∀ z ∈ acube s,
      winQModeRe χ s p z = winQModeRe χ' s p z := by
    intro p z hz
    simp only [winQModeRe, winQMode, hchat p, h z hz]
  have him : ∀ p : ℝ³, ∀ z ∈ acube s,
      winQModeIm χ s p z = winQModeIm χ' s p z := by
    intro p z hz
    simp only [winQModeIm, winQMode, hchat p, h z hz]
  unfold winKinPWord
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only []
  have h1 : modeP s (winQModeRe χ s p) Φ = modeP s (winQModeRe χ' s p) Φ :=
    modeP_congr_acube (fun z hz => hmod p z hz) Φ
  have h2 : modeP s (winQModeIm χ s p) Φ = modeP s (winQModeIm χ' s p) Φ :=
    modeP_congr_acube (fun z hz => him p z hz) Φ
  rw [h1, h2]
/-- **All windows `≡ 1` on the cube give the SAME word** (that of the constant-one window).
This is the sharp form of the rigidity: the `χ_b ≡ 1` lane cannot be tuned by re-normalising the
window. -/
theorem winKinPWord_eq_const_one_of_eq_one_on_box {χ : ℝ³ → ℝ} {s c : ℝ}
    (h : ∀ z : ℝ³, z ∈ acube s → χ z = 1) {n : ℕ} (Φ : X (n + 1) → ℝ) :
    winKinPWord χ s c Φ = winKinPWord (fun _ => (1 : ℝ)) s c Φ :=
  winKinPWord_eq_of_eqOn_acube (fun z hz => by rw [h z hz]) Φ

end Work.SmallBoxA0
