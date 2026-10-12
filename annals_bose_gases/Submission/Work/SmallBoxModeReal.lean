import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxPairIdent
import Submission.Work.SmallBoxTauComm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-279 — the REAL-mode reduction of the D1 Bogoliubov step

FS `lm:appbogolubov` diagonalises the per-`p` operator

    h(p) = 𝒜(p)(b_p†b_p + b_{−p}†b_{−p}) + ℬ(p)(b_p†b_{−p}† + b_{−p}b_p),
    b_p† = |B|^{−1}a†(g_p)a(1),  g_p = Q_B(χ_B e^{−ipx}),

with Bogoliubov's method (`thm:bogolubov-complete`) applied to the pair
`(b_p, b_{−p})`.  The modes are COMPLEX (`g_{−p} = conj g_p`), which in the
corpus's bilinear slot calculus is awkward.  This module records the
reduction that makes the step elementary:

write `u_p := Re g_p`, `v_p := Im g_p` (REAL modes), so that
`g_p = u_p + i v_p` and `g_{−p} = u_p − i v_p`.  Then, with
`X_u := bDag u = |B|^{−1}a†(u)a(1)` and `x_u := bAnn u = |B|^{−1}a†(1)a(u)`,
the pairing combination `b_p†b_{−p}† + b_{−p}b_p` is
`X_u² + X_v² + x_u² + x_v²` and the diagonal combination
`b_p†b_p + b_{−p}†b_{−p}` is `2(X_u x_u + X_v x_v)` — the cross terms
`±i(…)` cancel pairwise.  So the quadratic form of `h(p)` IS the sum of the
two REAL same-mode Bogoliubov problems attached to `u_p` and `v_p`; the
corpus's `tau_two_mode_bound` (session 273) applies to each.

## Contents

* the real/imaginary modes `qModeRe`, `qModeIm`, the decomposition, the
  mean-vanishing `∫u = ∫v = 0`, and the norm identity
  `∫(u²+v²) = ∫χ_B² − |B|^{−1}‖c_p‖² ≤ ∫χ_B²` (FS's `∫χ_B²`);
* the complex-mode annihilation operator `bAnn` (`= |B|^{−1}a†(1)a(g)`),
  with the two-slot kernel formula `bAnn_double`;
* `bogoliubov_perP`: FS's per-`p` Bogoliubov lower bound in the corpus's
  real-mode language.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1 The real and imaginary parts of the D1 mode -/

/-- the REAL part of FS's mode `g_p = Q_B(χ_B e^{-ipx})`. -/
noncomputable def qModeRe (ℓ : ℝ) (p : ℝ³) : ℝ³ → ℝ := fun y => (qMode ℓ p y).re

/-- the IMAGINARY part of FS's mode `g_p = Q_B(χ_B e^{-ipx})`. -/
noncomputable def qModeIm (ℓ : ℝ) (p : ℝ³) : ℝ³ → ℝ := fun y => (qMode ℓ p y).im

lemma qMode_eq_re_add_im (ℓ : ℝ) (p y : ℝ³) :
    qMode ℓ p y = (qModeRe ℓ p y : ℂ) + Complex.I * (qModeIm ℓ p y : ℂ) := by
  simp only [qModeRe, qModeIm]
  rw [mul_comm Complex.I ((qMode ℓ p y).im : ℂ)]
  exact (Complex.re_add_im _).symm

lemma continuous_qModeRe {ℓ : ℝ} (p : ℝ³) : Continuous (qModeRe ℓ p) :=
  Complex.continuous_re.comp (continuous_qMode p)

lemma continuous_qModeIm {ℓ : ℝ} (p : ℝ³) : Continuous (qModeIm ℓ p) :=
  Complex.continuous_im.comp (continuous_qMode p)

/-- `∫_{a B} u_p = 0` (the `Q_B`-projection is box-mean-free). -/
lemma integral_qModeRe_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (p : ℝ³) :
    ∫ y in acube ℓ, qModeRe ℓ p y = 0 := by
  have h := integral_qMode_eq_zero hℓ p
  have hrint : ∫ y in acube ℓ, (qMode ℓ p y).re = (∫ y in acube ℓ, qMode ℓ p y).re := by
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.integral_comp_comm (φ := fun y => qMode ℓ p y)
        (μ := (volume : Measure ℝ³).restrict (acube ℓ))
        (ContinuousOn.integrableOn_compact (acube_compact hℓ) (continuous_qMode p).continuousOn))
  simpa [qModeRe] using (hrint.trans (by rw [h]; simp))

/-- `∫_{a B} v_p = 0`. -/
lemma integral_qModeIm_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (p : ℝ³) :
    ∫ y in acube ℓ, qModeIm ℓ p y = 0 := by
  have h := integral_qMode_eq_zero hℓ p
  have himint : ∫ y in acube ℓ, (qMode ℓ p y).im = (∫ y in acube ℓ, qMode ℓ p y).im := by
    simpa only [Complex.imCLM_apply] using
      (Complex.imCLM.integral_comp_comm (φ := fun y => qMode ℓ p y)
        (μ := (volume : Measure ℝ³).restrict (acube ℓ))
        (ContinuousOn.integrableOn_compact (acube_compact hℓ) (continuous_qMode p).continuousOn))
  simpa [qModeIm] using (himint.trans (by rw [h]; simp))

/-- the pointwise norm-square decomposition `‖g_p(y)‖² = u_p(y)² + v_p(y)²`. -/
lemma normSq_qMode (ℓ : ℝ) (p y : ℝ³) :
    ‖qMode ℓ p y‖ ^ 2 = (qModeRe ℓ p y) ^ 2 + (qModeIm ℓ p y) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [qModeRe, qModeIm]
  ring

/-! ## 2 The norm identity (FS's `∫χ_B²`) -/

lemma normSq_fullMode (ℓ : ℝ) (p y : ℝ³) :
    Complex.normSq ((chiScale ℓ y : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) = (chiScale ℓ y) ^ 2 := by
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  have h : ‖Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [Complex.normSq_eq_norm_sq, h]
  ring

/-- `star` fixes `|B|^{−1} = (ℓ³)^{−1}` (a real number). -/
lemma star_boxInv (ℓ : ℝ) : star ((ℓ ^ 3)⁻¹ : ℂ) = ((ℓ ^ 3)⁻¹ : ℂ) := by
  rw [show ((ℓ ^ 3)⁻¹ : ℂ) = ((((ℓ ^ 3 : ℝ))⁻¹ : ℝ) : ℂ) from by push_cast; ring]
  simp

/-- **the norm identity**: `∫(u_p²+v_p²) = ∫χ_B² − |B|^{−1}‖c_p‖²`; in particular
`‖g_p‖² ≤ ∫χ_B²` (Bessel), which is the `∫χ_B²` of FS's commutator bound. -/
lemma integral_qMode_normSq {ℓ : ℝ} (hℓ : 0 < ℓ) (p : ℝ³) :
    (∫ y in acube ℓ, (qModeRe ℓ p y) ^ 2) + (∫ y in acube ℓ, (qModeIm ℓ p y) ^ 2)
      = (∫ y in acube ℓ, (chiScale ℓ y) ^ 2)
        - (ℓ ^ 3)⁻¹ * ‖modeChat ℓ p‖ ^ 2 := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top ℓ hℓ.le⟩
  set m : ℂ := ((ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ p with hm
  have hsplit : qMode ℓ p = fun y : ℝ³ => (chiScale ℓ y : ℂ)
      * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) - m := by
    funext y; rw [qMode]
  have hct : Continuous (fun y : ℝ³ => (chiScale ℓ y : ℂ)
      * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) := by
    refine (Complex.continuous_ofReal.comp (chiScale_continuous ℓ)).mul ?_
    refine Complex.continuous_exp.comp ?_
    exact (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))).neg
  have hsum : (∫ y in acube ℓ, (qModeRe ℓ p y) ^ 2) + (∫ y in acube ℓ, (qModeIm ℓ p y) ^ 2)
      = ∫ y in acube ℓ, ‖qMode ℓ p y‖ ^ 2 := by
    rw [← integral_add]
    · exact integral_congr_ae (Filter.Eventually.of_forall fun y => (normSq_qMode ℓ p y).symm)
    · exact ContinuousOn.integrableOn_compact (acube_compact hℓ)
        ((continuous_qModeRe p).pow 2).continuousOn
    · exact ContinuousOn.integrableOn_compact (acube_compact hℓ)
        ((continuous_qModeIm p).pow 2).continuousOn
  rw [hsum]
  have hI1 : Integrable (fun y : ℝ³ => (chiScale ℓ y) ^ 2)
      ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ContinuousOn.integrableOn_compact (acube_compact hℓ)
      ((chiScale_continuous ℓ).pow 2).continuousOn
  have hI2 : Integrable (fun _ : ℝ³ => Complex.normSq m)
      ((volume : Measure ℝ³).restrict (acube ℓ)) := integrable_const _
  have hI3 : Integrable (fun y : ℝ³ => 2 * ((chiScale ℓ y : ℂ)
      * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * star m).re)
      ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ContinuousOn.integrableOn_compact (acube_compact hℓ)
      (((Complex.continuous_re.comp (hct.mul continuous_const)).const_mul 2).continuousOn)
  have hpoint : ∀ y : ℝ³, ‖qMode ℓ p y‖ ^ 2
      = ((chiScale ℓ y) ^ 2 + Complex.normSq m)
        - 2 * (((chiScale ℓ y : ℂ)
            * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) * star m).re := by
    intro y
    rw [Complex.sq_norm, hsplit, Complex.normSq_sub, normSq_fullMode]
    simp only [Complex.star_def]
  have hdecomp : (∫ y in acube ℓ, ‖qMode ℓ p y‖ ^ 2)
      = (∫ y in acube ℓ, ((chiScale ℓ y) ^ 2 + Complex.normSq m))
        - (∫ y in acube ℓ, 2 * ((chiScale ℓ y : ℂ)
            * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * star m).re) := by
    rw [show (∫ y in acube ℓ, ‖qMode ℓ p y‖ ^ 2)
        = ∫ y in acube ℓ, (((chiScale ℓ y) ^ 2 + Complex.normSq m)
            - 2 * (((chiScale ℓ y : ℂ)
                * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) * star m).re) from
      integral_congr_ae (Filter.Eventually.of_forall fun y => hpoint y)]
    rw [integral_sub (f := fun y : ℝ³ => (chiScale ℓ y) ^ 2 + Complex.normSq m)
      (g := fun y : ℝ³ => 2 * ((chiScale ℓ y : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * star m).re)
      (hI1.add hI2) hI3]
  rw [hdecomp, integral_add (f := fun y : ℝ³ => (chiScale ℓ y) ^ 2)
    (g := fun _ : ℝ³ => Complex.normSq m) hI1 hI2, integral_const_mul]
  have hI4 : Integrable (fun y : ℝ³ => (chiScale ℓ y : ℂ)
      * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * star m)
      ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ContinuousOn.integrableOn_compact (acube_compact hℓ) (hct.mul continuous_const).continuousOn
  have hosc : (∫ y in acube ℓ, ((chiScale ℓ y : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * star m).re)
      = (modeChat ℓ p * star m).re := by
    have h1 : (∫ y in acube ℓ, ((chiScale ℓ y : ℂ)
          * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * star m).re)
        = (∫ y in acube ℓ, (chiScale ℓ y : ℂ)
            * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * star m).re :=
      Complex.reCLM.integral_comp_comm (φ := fun y : ℝ³ => (chiScale ℓ y : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * star m) hI4
    rw [h1, MeasureTheory.integral_mul_const]
    rfl
  rw [hosc]
  rw [MeasureTheory.integral_const, real_volume_acube ℓ hℓ.le, smul_eq_mul]
  have hr : ((ℓ ^ 3)⁻¹ : ℂ) = ((((ℓ ^ 3 : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; ring
  have hsm : star m = ((ℓ ^ 3)⁻¹ : ℂ) * star (modeChat ℓ p) := by
    rw [hm, star_mul, star_boxInv, mul_comm]
  have hnm : Complex.normSq m = (((ℓ ^ 3 : ℝ))⁻¹ * ((ℓ ^ 3 : ℝ))⁻¹)
      * ‖modeChat ℓ p‖ ^ 2 := by
    rw [hm, Complex.normSq_mul, hr, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
  have hcs : (modeChat ℓ p * star m).re = ((ℓ ^ 3 : ℝ))⁻¹ * ‖modeChat ℓ p‖ ^ 2 := by
    have hcc : (modeChat ℓ p * star (modeChat ℓ p)).re = ‖modeChat ℓ p‖ ^ 2 := by
      simp only [Complex.star_def]
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hci : (modeChat ℓ p * star (modeChat ℓ p)).im = 0 := by
      simp only [Complex.star_def]
      rw [Complex.mul_conj, Complex.ofReal_im]
    rw [hsm]
    have hassoc : modeChat ℓ p * (((ℓ ^ 3)⁻¹ : ℂ) * star (modeChat ℓ p))
        = ((ℓ ^ 3)⁻¹ : ℂ) * (modeChat ℓ p * star (modeChat ℓ p)) := by ring
    rw [hassoc, hr, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hcc, hci]
    ring
  rw [hcs, hnm]
  have hℓ3ne : (ℓ ^ 3 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- the Bessel form `‖g_p‖² ≤ ∫χ_B²` (FS's `∫χ_B²` in the commutator bound). -/
lemma integral_qMode_normSq_le {ℓ : ℝ} (hℓ : 0 < ℓ) (p : ℝ³) :
    (∫ y in acube ℓ, (qModeRe ℓ p y) ^ 2) + (∫ y in acube ℓ, (qModeIm ℓ p y) ^ 2)
      ≤ ∫ y in acube ℓ, (chiScale ℓ y) ^ 2 := by
  rw [integral_qMode_normSq hℓ p]
  have h : 0 ≤ (ℓ ^ 3)⁻¹ * ‖modeChat ℓ p‖ ^ 2 := by positivity
  linarith

/-! ## 3 The complex mode operator `bAnn = |B|^{−1}a†(1)a(g)` and the per-`p` Bogoliubov bound -/

/-- FS's annihilation mode operator `b_g = |B|^{−1}a†(1)a(g) = |B|^{−1/2}τ_g` in the
corpus's position-slot language (sesquilinear convention: the annihilation profile
is conjugated).  For real `g` it is `|B|^{−1/2}` times
`SmallBoxTauModes.tauAnn`. -/
noncomputable def bAnn (ℓ : ℝ) {N : ℕ} (g : ℝ³ → ℂ) (Ψ : X N → ℂ) (x : X N) : ℂ :=
  boxInv ℓ * ∑ i : Fin N, ∫ z in acube ℓ, star (g z) * Ψ (Function.update x i z)

lemma bAnn_apply {N : ℕ} (ℓ : ℝ) (g : ℝ³ → ℂ) (Ψ : X N → ℂ) (x : X N) :
    bAnn ℓ g Ψ x = boxInv ℓ * ∑ i : Fin N, ∫ z in acube ℓ,
      star (g z) * Ψ (Function.update x i z) := rfl

/-- the `z`-fibre of `star (g z) * Ψ (x_{i←z})` is continuous on the cube. -/
lemma continuous_star_mode_fibre {N : ℕ} (g : ℝ³ → ℂ) (hg : Continuous g)
    (Ψ : X N → ℂ) (hΨ : Continuous Ψ) (x : X N) (i : Fin N) :
    Continuous fun z : ℝ³ => star (g z) * Ψ (Function.update x i z) :=
  (continuous_star.comp hg).mul
    (hΨ.comp ((continuous_const : Continuous fun _ : ℝ³ => x).update i continuous_id))

/-- `bAnn` is LINEAR in the mode (the conjugation is inside the definition). -/
lemma bAnn_add {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (g₁ g₂ : ℝ³ → ℂ) (Ψ : X N → ℂ)
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hΨ : Continuous Ψ) :
    bAnn ℓ (fun z => g₁ z + g₂ z) Ψ = bAnn ℓ g₁ Ψ + bAnn ℓ g₂ Ψ := by
  funext x
  have key : ∀ i : Fin N,
      (∫ z in acube ℓ, star ((g₁ z + g₂ z)) * Ψ (Function.update x i z))
        = (∫ z in acube ℓ, star (g₁ z) * Ψ (Function.update x i z))
          + (∫ z in acube ℓ, star (g₂ z) * Ψ (Function.update x i z)) := by
    intro i
    rw [show (fun z : ℝ³ => star ((g₁ z + g₂ z)) * Ψ (Function.update x i z))
        = fun z : ℝ³ => star (g₁ z) * Ψ (Function.update x i z)
          + star (g₂ z) * Ψ (Function.update x i z) by
      funext z; rw [star_add, add_mul]]
    rw [integral_add (ContinuousOn.integrableOn_compact (acube_compact hℓ)
        (continuous_star_mode_fibre g₁ hg₁ Ψ hΨ x i).continuousOn)
      (ContinuousOn.integrableOn_compact (acube_compact hℓ)
        (continuous_star_mode_fibre g₂ hg₂ Ψ hΨ x i).continuousOn)]
  simp only [bAnn_apply, key, Pi.add_apply, Finset.sum_add_distrib, mul_add]

/-- `bAnn` is ANTILINEAR in the mode: `bAnn (c • g) = star c • bAnn g`. -/
lemma bAnn_smul {N : ℕ} {ℓ : ℝ} (_hℓ : 0 < ℓ) (c : ℂ) (g : ℝ³ → ℂ) (Ψ : X N → ℂ)
    (_hg : Continuous g) (_hΨ : Continuous Ψ) :
    bAnn ℓ (fun z => c * g z) Ψ = star c • bAnn ℓ g Ψ := by
  funext x
  have key : ∀ i : Fin N,
      (∫ z in acube ℓ, star (c * g z) * Ψ (Function.update x i z))
        = star c * (∫ z in acube ℓ, star (g z) * Ψ (Function.update x i z)) := by
    intro i
    rw [show (fun z : ℝ³ => star (c * g z) * Ψ (Function.update x i z))
        = fun z : ℝ³ => star c * (star (g z) * Ψ (Function.update x i z)) by
      funext z; rw [star_mul]; ring]
    rw [MeasureTheory.integral_const_mul]
  simp only [bAnn_apply, key, Pi.smul_apply]
  rw [← Finset.mul_sum]
  ring

/-- **FS's per-`p` Bogoliubov lower bound** (`lm:appbogolubov`'s Bogoliubov step)
in the corpus's REAL-mode language: since `g_p = u_p + i v_p` with `u_p = Re g_p`,
`v_p = Im g_p`, the quadratic form of `h(p)` is the sum of the two REAL same-mode
Bogoliubov problems for `u_p` and `v_p` (the cross terms `±i(…)` cancel pairwise),
and each is bounded by `tau_two_mode_bound` with the commutator input
`∫(u_p²+v_p²) = ‖g_p‖² ≤ ∫χ_B²`. -/
theorem bogoliubov_perP {n : ℕ} {s A B : ℝ} (hs : 0 < s) {p : ℝ³}
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) (hA : 0 < A) (hB : |B| ≤ A) :
    - ((A - Real.sqrt (A ^ 2 - B ^ 2)) / 2)
        * (((∫ z in acube s, (qModeRe s p z) ^ 2) + (∫ z in acube s, (qModeIm s p z) ^ 2))
            * ((n : ℝ) + 1) * (∫ x in abox (n + 1) s, (Ψ x) ^ 2))
      ≤ A * ((∫ x in abox (n + 1) s, (tauAnn s (qModeRe s p) Ψ x) ^ 2)
              + (∫ x in abox (n + 1) s, (tauAnn s (qModeIm s p) Ψ x) ^ 2))
        + B * ((∫ x in abox (n + 1) s,
                (tauAnn s (qModeRe s p) Ψ x) * (tauDag s (qModeRe s p) Ψ x))
              + (∫ x in abox (n + 1) s,
                (tauAnn s (qModeIm s p) Ψ x) * (tauDag s (qModeIm s p) Ψ x))) := by
  have hu := tau_two_mode_bound (s := s) (n := n) (g := qModeRe s p) (g' := qModeRe s p)
    (Ψ := Ψ) hs (continuous_qModeRe (ℓ := s) p) (continuous_qModeRe (ℓ := s) p) hΨ hA hB
  have hv := tau_two_mode_bound (s := s) (n := n) (g := qModeIm s p) (g' := qModeIm s p)
    (Ψ := Ψ) hs (continuous_qModeIm (ℓ := s) p) (continuous_qModeIm (ℓ := s) p) hΨ hA hB
  have hsq_u : (∫ z in acube s, qModeRe s p z * qModeRe s p z)
      = ∫ z in acube s, (qModeRe s p z) ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  have hsq_v : (∫ z in acube s, qModeIm s p z * qModeIm s p z)
      = ∫ z in acube s, (qModeIm s p z) ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  have hRu : (∫ x in abox (n + 1) s, (tauDag s (qModeRe s p) Ψ x) * (tauAnn s (qModeRe s p) Ψ x))
      = ∫ x in abox (n + 1) s, (tauAnn s (qModeRe s p) Ψ x) * (tauDag s (qModeRe s p) Ψ x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hRv : (∫ x in abox (n + 1) s, (tauDag s (qModeIm s p) Ψ x) * (tauAnn s (qModeIm s p) Ψ x))
      = ∫ x in abox (n + 1) s, (tauAnn s (qModeIm s p) Ψ x) * (tauDag s (qModeIm s p) Ψ x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hsq_u] at hu
  rw [hsq_v] at hv
  rw [hRu] at hu
  rw [hRv] at hv
  have hX : (((∫ z in acube s, (qModeRe s p z) ^ 2) + (∫ z in acube s, (qModeIm s p z) ^ 2))
        * ((n : ℝ) + 1) * (∫ x in abox (n + 1) s, (Ψ x) ^ 2))
      = ((∫ z in acube s, (qModeRe s p z) ^ 2) * ((n : ℝ) + 1)
          * (∫ x in abox (n + 1) s, (Ψ x) ^ 2))
        + ((∫ z in acube s, (qModeIm s p z) ^ 2) * ((n : ℝ) + 1)
          * (∫ x in abox (n + 1) s, (Ψ x) ^ 2)) := by ring
  rw [hX]
  nlinarith [hu, hv]

/-- the FS-flavoured form of `bogoliubov_perP`: the commutator input is bounded by
`∫χ_B²` (Bessel), which is exactly the `∫χ_B²` appearing in FS's
`[b_p,b_p†] ≤ n_0|B|^{−1}∫χ_B²`. -/
theorem bogoliubov_perP_chi {n : ℕ} {s A B : ℝ} (hs : 0 < s) {p : ℝ³}
    {Ψ : X (n + 1) → ℝ} (hΨ : Continuous Ψ) (hA : 0 < A) (hB : |B| ≤ A) :
    - ((A - Real.sqrt (A ^ 2 - B ^ 2)) / 2)
        * ((∫ z in acube s, (chiScale s z) ^ 2) * ((n : ℝ) + 1)
            * (∫ x in abox (n + 1) s, (Ψ x) ^ 2))
      ≤ A * ((∫ x in abox (n + 1) s, (tauAnn s (qModeRe s p) Ψ x) ^ 2)
              + (∫ x in abox (n + 1) s, (tauAnn s (qModeIm s p) Ψ x) ^ 2))
        + B * ((∫ x in abox (n + 1) s,
                (tauAnn s (qModeRe s p) Ψ x) * (tauDag s (qModeRe s p) Ψ x))
              + (∫ x in abox (n + 1) s,
                (tauAnn s (qModeIm s p) Ψ x) * (tauDag s (qModeIm s p) Ψ x))) := by
  have h := bogoliubov_perP (s := s) hs (p := p) hΨ hA hB
  have hle := integral_qMode_normSq_le (ℓ := s) hs p
  have hK : 0 ≤ ((n : ℝ) + 1) * (∫ x in abox (n + 1) s, (Ψ x) ^ 2) := by
    have h2 : (0 : ℝ) ≤ ∫ x in abox (n + 1) s, (Ψ x) ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    positivity
  have hcoef : 0 ≤ (A - Real.sqrt (A ^ 2 - B ^ 2)) / 2 := by
    have h1 : Real.sqrt (A ^ 2 - B ^ 2) ≤ A := by
      rw [Real.sqrt_le_left (le_of_lt hA)]
      nlinarith [abs_le.mp hB]
    linarith
  have hmul : ((A - Real.sqrt (A ^ 2 - B ^ 2)) / 2)
        * (((∫ z in acube s, (qModeRe s p z) ^ 2) + (∫ z in acube s, (qModeIm s p z) ^ 2))
            * ((n : ℝ) + 1) * (∫ x in abox (n + 1) s, (Ψ x) ^ 2))
      ≤ ((A - Real.sqrt (A ^ 2 - B ^ 2)) / 2)
        * ((∫ z in acube s, (chiScale s z) ^ 2) * ((n : ℝ) + 1)
            * (∫ x in abox (n + 1) s, (Ψ x) ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hcoef
    have h1 : (((∫ z in acube s, (qModeRe s p z) ^ 2) + (∫ z in acube s, (qModeIm s p z) ^ 2))
          * ((n : ℝ) + 1)) ≤ (∫ z in acube s, (chiScale s z) ^ 2) * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hle (by positivity)
    have h2 : (0 : ℝ) ≤ ∫ x in abox (n + 1) s, (Ψ x) ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    exact mul_le_mul_of_nonneg_right h1 h2
  linarith [h, hmul]

/-! ## 4 Mode linearity of `bDag` (needed for the pair `(p,−p)` reduction) -/

/-- `bDag` is ℂ-LINEAR in the mode. -/
lemma bDag_add_mode {N : ℕ} (ℓ : ℝ) (g₁ g₂ : ℝ³ → ℂ) (Ψ : X N → ℂ) :
    bDag ℓ (fun z => g₁ z + g₂ z) Ψ = bDag ℓ g₁ Ψ + bDag ℓ g₂ Ψ := by
  funext x
  simp only [bDag_apply, Pi.add_apply]
  have hsum : (∑ i : Fin N, (g₁ (x i) + g₂ (x i)) * ∫ z in acube ℓ, Ψ (Function.update x i z))
      = (∑ i : Fin N, g₁ (x i) * ∫ z in acube ℓ, Ψ (Function.update x i z))
        + ∑ i : Fin N, g₂ (x i) * ∫ z in acube ℓ, Ψ (Function.update x i z) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum, mul_add]

/-- `bDag` is ℂ-linear: `bDag (c • g) = c • bDag g`. -/
lemma bDag_smul_mode {N : ℕ} (ℓ : ℝ) (c : ℂ) (g : ℝ³ → ℂ) (Ψ : X N → ℂ) :
    bDag ℓ (fun z => c * g z) Ψ = c • bDag ℓ g Ψ := by
  funext x
  simp only [bDag_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ i : Fin N, (c * g (x i)) * ∫ z in acube ℓ, Ψ (Function.update x i z))
      = c * ∑ i : Fin N, g (x i) * ∫ z in acube ℓ, Ψ (Function.update x i z) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)]
  ring

/-- `bAnn` mode antilinearity in the `star`-free form used by the pair reduction:
`bAnn (u + I • v) = bAnn u - I • bAnn v`. -/
lemma bAnn_complex_decomp {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (u v : ℝ³ → ℝ) (Ψ : X N → ℂ)
    (hu : Continuous u) (hv : Continuous v) (hΨ : Continuous Ψ) :
    bAnn ℓ (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) Ψ
      = bAnn ℓ (fun z => (u z : ℂ)) Ψ - Complex.I • bAnn ℓ (fun z => (v z : ℂ)) Ψ := by
  have h1 := bAnn_add hℓ (fun z : ℝ³ => (u z : ℂ)) (fun z : ℝ³ => Complex.I * (v z : ℂ)) Ψ
    (Complex.continuous_ofReal.comp hu)
    (continuous_const.mul (Complex.continuous_ofReal.comp hv)) hΨ
  have hL : (fun z : ℝ³ => (u z : ℂ) + Complex.I * (v z : ℂ))
      = fun z : ℝ³ => (u z : ℂ) + (fun z : ℝ³ => Complex.I * (v z : ℂ)) z := rfl
  rw [hL, h1]
  rw [bAnn_smul hℓ Complex.I (fun z => (v z : ℂ)) Ψ (Complex.continuous_ofReal.comp hv) hΨ]
  rw [show star Complex.I = -Complex.I from by simp, neg_smul, sub_eq_add_neg]


/-! ## 5 The unified complex mode operator `cOp f h = a†(f)a(h)` -/

/-- The complex sesquilinear one-body mode operator `a†(f)a(h)` in the corpus's
position-slot language (`star` on the annihilation profile).  Unifies
`bDag` (`h = 1`) and `bAnn` (`f = 1`), and gives the mode number operator
`cOp g g = a†(g)a(g)`. -/
noncomputable def cOp (ℓ : ℝ) {N : ℕ} (f h : ℝ³ → ℂ) (Ψ : X N → ℂ) (x : X N) : ℂ :=
  ∑ i : Fin N, f (x i) * ∫ z in acube ℓ, star (h z) * Ψ (Function.update x i z)

lemma bDag_eq_cOp {N : ℕ} (ℓ : ℝ) (g : ℝ³ → ℂ) (Ψ : X N → ℂ) (x : X N) :
    bDag ℓ g Ψ x = boxInv ℓ * cOp ℓ g (fun _ => (1 : ℂ)) Ψ x := by
  simp only [bDag_apply, cOp, star_one, one_mul]

lemma bAnn_eq_cOp {N : ℕ} (ℓ : ℝ) (g : ℝ³ → ℂ) (Ψ : X N → ℂ) (x : X N) :
    bAnn ℓ g Ψ x = boxInv ℓ * cOp ℓ (fun _ => (1 : ℂ)) g Ψ x := by
  simp only [bAnn_apply, cOp, one_mul]

lemma cOp_add_left {N : ℕ} (ℓ : ℝ) (f₁ f₂ h : ℝ³ → ℂ) (Ψ : X N → ℂ) :
    cOp ℓ (fun z => f₁ z + f₂ z) h Ψ = cOp ℓ f₁ h Ψ + cOp ℓ f₂ h Ψ := by
  funext x
  simp only [cOp, Pi.add_apply]
  have hsum : (∑ i : Fin N, (f₁ (x i) + f₂ (x i)) *
        ∫ z in acube ℓ, star (h z) * Ψ (Function.update x i z))
      = (∑ i : Fin N, f₁ (x i) * ∫ z in acube ℓ, star (h z) * Ψ (Function.update x i z))
        + ∑ i : Fin N, f₂ (x i) * ∫ z in acube ℓ, star (h z) * Ψ (Function.update x i z) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum]

lemma cOp_smul_left {N : ℕ} (ℓ : ℝ) (c : ℂ) (f h : ℝ³ → ℂ) (Ψ : X N → ℂ) :
    cOp ℓ (fun z => c * f z) h Ψ = c • cOp ℓ f h Ψ := by
  funext x
  simp only [cOp, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ i : Fin N, (c * f (x i)) *
        ∫ z in acube ℓ, star (h z) * Ψ (Function.update x i z))
      = c * ∑ i : Fin N, f (x i) *
          ∫ z in acube ℓ, star (h z) * Ψ (Function.update x i z) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)]

/-- `cOp` is LINEAR in the annihilation profile (the `star` is inside). -/
lemma cOp_add_right {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (f h₁ h₂ : ℝ³ → ℂ) (Ψ : X N → ℂ)
    (hh₁ : Continuous h₁) (hh₂ : Continuous h₂) (hΨ : Continuous Ψ) :
    cOp ℓ f (fun z => h₁ z + h₂ z) Ψ = cOp ℓ f h₁ Ψ + cOp ℓ f h₂ Ψ := by
  funext x
  simp only [cOp, Pi.add_apply]
  have key : ∀ i : Fin N,
      (∫ z in acube ℓ, star (h₁ z + h₂ z) * Ψ (Function.update x i z))
        = (∫ z in acube ℓ, star (h₁ z) * Ψ (Function.update x i z))
          + (∫ z in acube ℓ, star (h₂ z) * Ψ (Function.update x i z)) := by
    intro i
    rw [show (fun z : ℝ³ => star (h₁ z + h₂ z) * Ψ (Function.update x i z))
        = fun z : ℝ³ => star (h₁ z) * Ψ (Function.update x i z)
          + star (h₂ z) * Ψ (Function.update x i z) by
      funext z; rw [star_add, add_mul]]
    rw [integral_add (ContinuousOn.integrableOn_compact (acube_compact hℓ)
        (continuous_star_mode_fibre h₁ hh₁ Ψ hΨ x i).continuousOn)
      (ContinuousOn.integrableOn_compact (acube_compact hℓ)
        (continuous_star_mode_fibre h₂ hh₂ Ψ hΨ x i).continuousOn)]
  simp only [key, Finset.sum_add_distrib, mul_add]

/-- `cOp` is antilinear in the annihilation profile. -/
lemma cOp_smul_right {N : ℕ} {ℓ : ℝ} (_hℓ : 0 < ℓ) (c : ℂ) (f h : ℝ³ → ℂ) (Ψ : X N → ℂ) :
    cOp ℓ f (fun z => c * h z) Ψ = star c • cOp ℓ f h Ψ := by
  funext x
  simp only [cOp, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ i : Fin N, f (x i) * ∫ z in acube ℓ, star (c * h z) * Ψ (Function.update x i z))
      = star c * ∑ i : Fin N, f (x i) *
          ∫ z in acube ℓ, star (h z) * Ψ (Function.update x i z) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (fun z : ℝ³ => star (c * h z) * Ψ (Function.update x i z))
        = fun z : ℝ³ => star c * (star (h z) * Ψ (Function.update x i z)) by
      funext z; rw [star_mul]; ring]
    rw [MeasureTheory.integral_const_mul]
    ring]


/-! ## 6 The creation commutativity `[bDag u, bDag v] = 0` -/

/-- the order of the two cube integrations can be swapped for a complex-valued
continuous kernel. -/
lemma cube_iter_swap_order {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ³ → ℝ³ → ℂ}
    (hF : Continuous fun p : ℝ³ × ℝ³ => F p.1 p.2) :
    (∫ z in acube ℓ, ∫ w in acube ℓ, F z w) = ∫ z in acube ℓ, ∫ w in acube ℓ, F w z := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top ℓ hℓ.le⟩
  have hInt : Integrable (Function.uncurry F)
      (((volume : Measure ℝ³).restrict (acube ℓ)).prod
        ((volume : Measure ℝ³).restrict (acube ℓ))) := by
    obtain ⟨C, hC⟩ := ((acube_compact hℓ).prod (acube_compact hℓ)).exists_bound_of_continuousOn
      hF.continuousOn
    refine Integrable.of_bound hF.aestronglyMeasurable (max C 0) ?_
    filter_upwards [ae_mem_cube_prod hℓ] with p hp
    exact le_trans (hC p ⟨hp.1, hp.2⟩) (le_max_left _ _)
  exact integral_integral_swap hInt

/-- the symmetry of the two-slot kernel `K i j = ∫_z∫_w Ψ(x_{j←w,i←z})` in `(i,j)`. -/
lemma cube_iter_pair_swap_symm {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {Ψ : X N → ℂ} (hΨ : Continuous Ψ) (x : X N) :
    (∫ z in acube ℓ, ∫ w in acube ℓ, Ψ (Function.update (Function.update x j w) i z))
      = ∫ z in acube ℓ, ∫ w in acube ℓ,
          Ψ (Function.update (Function.update x i w) j z) := by
  have hc : Continuous fun p : ℝ³ × ℝ³ =>
      Ψ (Function.update (Function.update x i p.2) j p.1) :=
    hΨ.comp (((continuous_const (y := x)).update i continuous_snd).update j continuous_fst)
  rw [cube_iter_swap_order hℓ (F := fun z w : ℝ³ =>
    Ψ (Function.update (Function.update x i w) j z)) hc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  exact congrArg Ψ (Function.update_comm hij z w x).symm

/-- **the creation commutativity** `bDag u (bDag v Ψ) = bDag v (bDag u Ψ)` for two
box-mean-free modes — the `[X_u,X_v] = 0` needed for the pair `(p,−p)` reduction. -/
theorem bDag_dag_comm {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (g g' : ℝ³ → ℂ) (Ψ : X N → ℂ)
    (hg : Continuous g) (hg' : Continuous g') (hΨ : Continuous Ψ)
    (hgm : ∫ z in acube ℓ, g z = 0) (hg'm : ∫ z in acube ℓ, g' z = 0) (x : X N) :
    bDag ℓ g (bDag ℓ g' Ψ) x = bDag ℓ g' (bDag ℓ g Ψ) x := by
  rw [bDag_double hℓ g g' Ψ hg' hΨ hg'm, bDag_double hℓ g' g Ψ hg hΨ hgm]
  congr 1
  exact (show (∑ i, ∑ j ∈ Finset.univ.erase i, g' (x i) * g (x j) *
        ∫ z in acube ℓ, ∫ w in acube ℓ, Ψ (Function.update (Function.update x j w) i z))
      = ∑ i, ∑ j ∈ Finset.univ.erase i, g (x i) * g' (x j) *
        ∫ z in acube ℓ, ∫ w in acube ℓ, Ψ (Function.update (Function.update x j w) i z) from by
    calc (∑ i, ∑ j ∈ Finset.univ.erase i, g' (x i) * g (x j) *
          ∫ z in acube ℓ, ∫ w in acube ℓ, Ψ (Function.update (Function.update x j w) i z))
        = ∑ i, ∑ j ∈ Finset.univ.erase i, g (x j) * g' (x i) *
            ∫ z in acube ℓ, ∫ w in acube ℓ, Ψ (Function.update (Function.update x j w) i z) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      _ = ∑ i, ∑ j ∈ Finset.univ.erase i, g (x i) * g' (x j) *
            ∫ z in acube ℓ, ∫ w in acube ℓ, Ψ (Function.update (Function.update x i w) j z) :=
          sum_erase_swap (fun i j : Fin N => g (x j) * g' (x i) *
            ∫ z in acube ℓ, ∫ w in acube ℓ, Ψ (Function.update (Function.update x j w) i z))
      _ = ∑ i, ∑ j ∈ Finset.univ.erase i, g (x i) * g' (x j) *
            ∫ z in acube ℓ, ∫ w in acube ℓ, Ψ (Function.update (Function.update x j w) i z) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j hj => ?_))
          have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
          rw [cube_iter_pair_swap_symm hℓ hij hΨ x]).symm

/-! ## 7 Linearity of `cOp` in the state -/

lemma cOp_add_state {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (f h : ℝ³ → ℂ) (Ψ₁ Ψ₂ : X N → ℂ)
    (hh : Continuous h) (hΨ₁ : Continuous Ψ₁) (hΨ₂ : Continuous Ψ₂) :
    cOp ℓ f h (Ψ₁ + Ψ₂) = cOp ℓ f h Ψ₁ + cOp ℓ f h Ψ₂ := by
  funext x
  simp only [cOp, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : Continuous fun z : ℝ³ => star (h z) * Ψ₁ (Function.update x i z) :=
    continuous_star_mode_fibre h hh Ψ₁ hΨ₁ x i
  have h2 : Continuous fun z : ℝ³ => star (h z) * Ψ₂ (Function.update x i z) :=
    continuous_star_mode_fibre h hh Ψ₂ hΨ₂ x i
  rw [show (fun z : ℝ³ => star (h z) * (Ψ₁ (Function.update x i z) + Ψ₂ (Function.update x i z)))
      = fun z : ℝ³ => star (h z) * Ψ₁ (Function.update x i z)
        + star (h z) * Ψ₂ (Function.update x i z) by
    funext z; rw [mul_add]]
  rw [integral_add (ContinuousOn.integrableOn_compact (acube_compact hℓ) h1.continuousOn)
    (ContinuousOn.integrableOn_compact (acube_compact hℓ) h2.continuousOn), mul_add]

lemma cOp_smul_state {N : ℕ} {ℓ : ℝ} (_hℓ : 0 < ℓ) (f h : ℝ³ → ℂ) (c : ℂ) (Ψ : X N → ℂ) :
    cOp ℓ f h (c • Ψ) = c • cOp ℓ f h Ψ := by
  funext x
  simp only [cOp, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (fun z : ℝ³ => star (h z) * (c * Ψ (Function.update x i z)))
      = fun z : ℝ³ => c * (star (h z) * Ψ (Function.update x i z)) by
    funext z; ring]
  rw [MeasureTheory.integral_const_mul]
  ring



/-! ## 8 The D1 pair identities and the mode-operator algebra

`cOp_pair_diagonal` (identity (B)) and `cOp_pair_offdiag` (identity (A)) are the
structural statements behind `bogoliubov_perP`: the complex pair `(p,−p)` splits
into the two REAL same-mode Bogoliubov problems attached to `u = Re g_p` and
`v = Im g_p`.  `bAnn_double`/`bAnn_comm` supply the annihilation commutativity
`[x_u,x_v] = 0` (the creation counterpart `[X_u,X_v] = 0` is `bDag_dag_comm`).
-/

lemma cOp_continuous_state {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} {f h : ℝ³ → ℂ}
    (hf : Continuous f) (hh : Continuous h) {Ψ : X N → ℂ} (hΨ : Continuous Ψ) :
    Continuous (cOp ℓ f h Ψ) := by
  have hterm : ∀ i : Fin N, Continuous fun x : X N =>
      f (x i) * ∫ z in acube ℓ, star (h z) * Ψ (Function.update x i z) := by
    intro i
    refine (hf.comp (continuous_apply i)).mul ?_
    refine continuous_parametric_integral_of_continuous
      (f := fun (x : X N) (z : ℝ³) => star (h z) * Ψ (Function.update x i z)) ?_ ?_
    · exact (hh.comp continuous_snd).star.mul
        (hΨ.comp (continuous_fst.update i continuous_snd))
    · exact acube_compact hℓ
  change Continuous fun x : X N =>
      ∑ i : Fin N, f (x i) * ∫ z in acube ℓ, star (h z) * Ψ (Function.update x i z)
  exact continuous_finsetSum _ (fun i _ => hterm i)

lemma cOp_add_smul_state {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (f h : ℝ³ → ℂ) (A B : X N → ℂ) (c : ℂ)
    (hh : Continuous h) (hA : Continuous A) (hB : Continuous B) :
    cOp ℓ f h (A + c • B) = cOp ℓ f h A + c • cOp ℓ f h B := by
  rw [cOp_add_state hℓ f h A (c • B) hh hA (hB.const_smul c),
      cOp_smul_state hℓ f h c B]

/-- identity (B): the diagonal pairing in the real-mode form. -/
theorem cOp_pair_diagonal {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (u v : ℝ³ → ℝ)
    (hu : Continuous u) (hv : Continuous v) {Ψ : X N → ℂ} (hΨ : Continuous Ψ) :
    cOp ℓ (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) Ψ)
      + cOp ℓ (fun z => (u z : ℂ) - Complex.I * (v z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ) - Complex.I * (v z : ℂ)) Ψ)
    = (2 : ℂ) • (cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ))
          (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ)
        + cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ))
          (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ)) := by
  have hun : Continuous fun z : ℝ³ => (u z : ℂ) := Complex.continuous_ofReal.comp hu
  have hvn : Continuous fun z : ℝ³ => (v z : ℂ) := Complex.continuous_ofReal.comp hv
  have hIv : Continuous fun z : ℝ³ => Complex.I * (v z : ℂ) := continuous_const.mul hvn
  have h1 : Continuous fun _ : ℝ³ => (1 : ℂ) := continuous_const
  have hCu : Continuous (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ) :=
    cOp_continuous_state hℓ h1 hun hΨ
  have hCv : Continuous (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ) :=
    cOp_continuous_state hℓ h1 hvn hΨ
  have hAu : ∀ X : X N → ℂ,
      cOp ℓ (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) (fun _ => (1 : ℂ)) X
        = cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) X
          + Complex.I • cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) X := by
    intro X
    rw [cOp_add_left, cOp_smul_left]
  have hBu : ∀ X : X N → ℂ,
      cOp ℓ (fun z => (u z : ℂ) - Complex.I * (v z : ℂ)) (fun _ => (1 : ℂ)) X
        = cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) X
          + (-Complex.I) • cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) X := by
    intro X
    rw [show (fun z : ℝ³ => (u z : ℂ) - Complex.I * (v z : ℂ))
        = fun z => (u z : ℂ) + (-Complex.I) * (v z : ℂ) from by funext z; ring]
    rw [cOp_add_left, cOp_smul_left]
  have hRg : cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) Ψ
      = cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ
        + (-Complex.I) • cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ := by
    rw [cOp_add_right hℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ))
          (fun z => Complex.I * (v z : ℂ)) Ψ hun hIv hΨ,
        cOp_smul_right hℓ Complex.I (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ]
    rw [show star Complex.I = -Complex.I from by rw [Complex.star_def, Complex.conj_I]]
  have hRg' : cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ) - Complex.I * (v z : ℂ)) Ψ
      = cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ
        + Complex.I • cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ := by
    rw [show (fun z : ℝ³ => (u z : ℂ) - Complex.I * (v z : ℂ))
        = fun z => (u z : ℂ) + (-Complex.I) * (v z : ℂ) from by funext z; ring]
    rw [cOp_add_right hℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ))
          (fun z => (-Complex.I) * (v z : ℂ)) Ψ hun (continuous_const.mul hvn) hΨ,
        cOp_smul_right hℓ (-Complex.I) (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ]
    rw [show star (-Complex.I) = Complex.I from by
      rw [Complex.star_def, map_neg, Complex.conj_I, neg_neg]]
  rw [hAu, hRg, hBu, hRg']
  rw [cOp_add_smul_state hℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ)
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ) (-Complex.I) h1 hCu hCv,
      cOp_add_smul_state hℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ)
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ) (-Complex.I) h1 hCu hCv,
      cOp_add_smul_state hℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ)
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ) Complex.I h1 hCu hCv,
      cOp_add_smul_state hℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ)
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ) Complex.I h1 hCu hCv]
  simp only [smul_add, smul_smul]
  rw [show Complex.I * (-Complex.I) = (1 : ℂ) from by rw [mul_neg, Complex.I_mul_I, neg_neg],
      show (-Complex.I) * Complex.I = (1 : ℂ) from by rw [neg_mul, Complex.I_mul_I, neg_neg]]
  simp only [one_smul]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma integral_star_eq_zero_of_integral_eq_zero {ℓ : ℝ} {g : ℝ³ → ℂ}
    (hg : ∫ z in acube ℓ, g z = 0) : ∫ z in acube ℓ, star (g z) = 0 := by
  rw [Complex.star_def, integral_conj, hg, map_zero]

lemma bAnn_double {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (g g' : ℝ³ → ℂ) (Ψ : X N → ℂ)
    (hg : Continuous g) (hg' : Continuous g') (hΨ : Continuous Ψ)
    (hgm : ∫ z in acube ℓ, g z = 0) (x : X N) :
    bAnn ℓ g (bAnn ℓ g' Ψ) x = boxInv ℓ ^ 2 * ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
      ∫ z in acube ℓ, ∫ w in acube ℓ, star (g z) * star (g' w) *
        Ψ (Function.update (Function.update x j w) i z) := by
  have key : ∀ i : Fin N,
      (∫ z in acube ℓ, star (g z) * bAnn ℓ g' Ψ (Function.update x i z))
        = boxInv ℓ * ∑ j ∈ Finset.univ.erase i, ∫ z in acube ℓ, ∫ w in acube ℓ,
            star (g z) * star (g' w) * Ψ (Function.update (Function.update x j w) i z) := by
    intro i
    have hcontA : Continuous fun z : ℝ³ => ∑ j ∈ Finset.univ.erase i,
        ∫ w in acube ℓ, star (g' w) * Ψ (Function.update (Function.update x i z) j w) := by
      refine continuous_finsetSum _ (fun j _ => ?_)
      refine continuous_parametric_integral_of_continuous (f := fun (z : ℝ³) (w : ℝ³) =>
        star (g' w) * Ψ (Function.update (Function.update x i z) j w)) ?_ (acube_compact hℓ)
      fun_prop
    have hcontB : Continuous fun z : ℝ³ =>
        ∫ w in acube ℓ, star (g' w) * Ψ (Function.update (Function.update x i z) i w) := by
      refine continuous_parametric_integral_of_continuous (f := fun (z : ℝ³) (w : ℝ³) =>
        star (g' w) * Ψ (Function.update (Function.update x i z) i w)) ?_ (acube_compact hℓ)
      fun_prop
    have h1 : (∫ z in acube ℓ, star (g z) * bAnn ℓ g' Ψ (Function.update x i z))
        = ∫ z in acube ℓ, boxInv ℓ * (star (g z) * (∑ j ∈ Finset.univ.erase i,
              ∫ w in acube ℓ, star (g' w) * Ψ (Function.update (Function.update x i z) j w)))
            + boxInv ℓ * (star (g z) * (∫ w in acube ℓ, star (g' w) *
                Ψ (Function.update (Function.update x i z) i w))) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only []
      rw [bAnn_apply, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      ring
    rw [h1]
    rw [MeasureTheory.integral_add
      (f := fun z : ℝ³ => boxInv ℓ * (star (g z) * (∑ j ∈ Finset.univ.erase i,
        ∫ w in acube ℓ, star (g' w) * Ψ (Function.update (Function.update x i z) j w))))
      (g := fun z : ℝ³ => boxInv ℓ * (star (g z) * (∫ w in acube ℓ, star (g' w) *
        Ψ (Function.update (Function.update x i z) i w))))
      (ContinuousOn.integrableOn_compact (acube_compact hℓ)
        (((continuous_const.mul ((continuous_star.comp hg).mul hcontA))).continuousOn))
      (ContinuousOn.integrableOn_compact (acube_compact hℓ)
        (((continuous_const.mul ((continuous_star.comp hg).mul hcontB))).continuousOn))]
    have hB : (∫ z in acube ℓ, boxInv ℓ * (star (g z) * (∫ w in acube ℓ, star (g' w) *
          Ψ (Function.update (Function.update x i z) i w)))) = 0 := by
      rw [MeasureTheory.integral_const_mul]
      rw [show (fun z : ℝ³ => star (g z) * (∫ w in acube ℓ, star (g' w) *
            Ψ (Function.update (Function.update x i z) i w)))
          = fun z : ℝ³ => star (g z) * (∫ w in acube ℓ, star (g' w) *
              Ψ (Function.update x i w)) by
        funext z
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        simp only []
        rw [Function.update_idem]]
      rw [MeasureTheory.integral_mul_const, integral_star_eq_zero_of_integral_eq_zero hgm,
        zero_mul, mul_zero]
    rw [hB, add_zero]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [show (fun z : ℝ³ => star (g z) * (∑ j ∈ Finset.univ.erase i,
          ∫ w in acube ℓ, star (g' w) * Ψ (Function.update (Function.update x i z) j w)))
        = fun z : ℝ³ => ∑ j ∈ Finset.univ.erase i, star (g z) *
            (∫ w in acube ℓ, star (g' w) * Ψ (Function.update (Function.update x i z) j w)) by
      funext z; rw [Finset.mul_sum]]
    rw [MeasureTheory.integral_finsetSum (s := Finset.univ.erase i)
      (f := fun j (z : ℝ³) => star (g z) *
        ∫ w in acube ℓ, star (g' w) * Ψ (Function.update (Function.update x i z) j w))]
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
      rw [show (fun z : ℝ³ => star (g z) * (∫ w in acube ℓ, star (g' w) *
            Ψ (Function.update (Function.update x i z) j w)))
          = fun z : ℝ³ => star (g z) * (∫ w in acube ℓ, star (g' w) *
              Ψ (Function.update (Function.update x j w) i z)) by
        funext z
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        simp only []
        rw [Function.update_comm hij z w x]]
      rw [show (∫ z in acube ℓ, star (g z) * (∫ w in acube ℓ, star (g' w) *
            Ψ (Function.update (Function.update x j w) i z)))
          = ∫ z in acube ℓ, ∫ w in acube ℓ, star (g z) * (star (g' w) *
              Ψ (Function.update (Function.update x j w) i z)) from by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only []
        rw [MeasureTheory.integral_const_mul]]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only []
      ring
    · intro j _
      exact ContinuousOn.integrableOn_compact (acube_compact hℓ)
        (((continuous_star.comp hg).mul (continuous_parametric_integral_of_continuous
          (f := fun (z : ℝ³) (w : ℝ³) => star (g' w) *
            Ψ (Function.update (Function.update x i z) j w)) (by fun_prop)
          (acube_compact hℓ))).continuousOn)
  rw [bAnn_apply]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  rw [← Finset.mul_sum]
  ring

lemma bAnn_comm {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (g g' : ℝ³ → ℂ) (Ψ : X N → ℂ)
    (hg : Continuous g) (hg' : Continuous g') (hΨ : Continuous Ψ)
    (hgm : ∫ z in acube ℓ, g z = 0) (hg'm : ∫ z in acube ℓ, g' z = 0) (x : X N) :
    bAnn ℓ g (bAnn ℓ g' Ψ) x = bAnn ℓ g' (bAnn ℓ g Ψ) x := by
  have hstep : ∀ i : Fin N, ∀ j ∈ Finset.univ.erase i,
      (∫ z in acube ℓ, ∫ w in acube ℓ, star (g z) * star (g' w) *
        Ψ (Function.update (Function.update x i w) j z))
      = ∫ z in acube ℓ, ∫ w in acube ℓ, star (g' z) * star (g w) *
        Ψ (Function.update (Function.update x j w) i z) := by
    intro i j hj
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    have hcont : Continuous fun p : ℝ³ × ℝ³ => star (g p.2) * star (g' p.1) *
        Ψ (Function.update (Function.update x i p.1) j p.2) := by fun_prop
    rw [← cube_iter_swap_order hℓ (F := fun z w : ℝ³ => star (g w) * star (g' z) *
        Ψ (Function.update (Function.update x i z) j w)) hcont]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    rw [show Function.update (Function.update x i z) j w
        = Function.update (Function.update x j w) i z from Function.update_comm hij z w x]
    ring
  have hsum_eq : (∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        (∫ z in acube ℓ, ∫ w in acube ℓ, star (g z) * star (g' w) *
          Ψ (Function.update (Function.update x j w) i z)))
      = ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        (∫ z in acube ℓ, ∫ w in acube ℓ, star (g' z) * star (g w) *
          Ψ (Function.update (Function.update x j w) i z)) := by
    calc (∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
            (∫ z in acube ℓ, ∫ w in acube ℓ, star (g z) * star (g' w) *
              Ψ (Function.update (Function.update x j w) i z)))
        = ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
            (∫ z in acube ℓ, ∫ w in acube ℓ, star (g z) * star (g' w) *
              Ψ (Function.update (Function.update x i w) j z)) :=
          sum_erase_swap (fun i j : Fin N => ∫ z in acube ℓ, ∫ w in acube ℓ,
            star (g z) * star (g' w) * Ψ (Function.update (Function.update x j w) i z))
      _ = ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
            (∫ z in acube ℓ, ∫ w in acube ℓ, star (g' z) * star (g w) *
              Ψ (Function.update (Function.update x j w) i z)) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => hstep i j hj
  rw [bAnn_double hℓ g g' Ψ hg hg' hΨ hgm x, bAnn_double hℓ g' g Ψ hg' hg hΨ hg'm x]
  exact congrArg (fun t => boxInv ℓ ^ 2 * t) hsum_eq

lemma boxInv_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) : boxInv ℓ ≠ 0 := by
  rw [boxInv, ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
  exact pow_ne_zero 3 hℓ.ne'

/-- creation commutativity in the `cOp` normalisation. -/
lemma cOp_comm_l {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (u v : ℝ³ → ℝ) {Ψ : X N → ℂ}
    (hu : Continuous u) (hv : Continuous v) (hΨ : Continuous Ψ)
    (hum : ∫ z in acube ℓ, (u z : ℂ) = 0) (hvm : ∫ z in acube ℓ, (v z : ℂ) = 0) :
    cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ)
      = cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) Ψ) := by
  have huC : Continuous fun z : ℝ³ => (u z : ℂ) := Complex.continuous_ofReal.comp hu
  have hvC : Continuous fun z : ℝ³ => (v z : ℂ) := Complex.continuous_ofReal.comp hv
  have h1 : Continuous fun _ : ℝ³ => (1 : ℂ) := continuous_const
  have hbv : bDag ℓ (fun z => (v z : ℂ)) Ψ
      = boxInv ℓ • cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ :=
    funext fun y => bDag_eq_cOp ℓ (fun z => (v z : ℂ)) Ψ y
  have hbu : bDag ℓ (fun z => (u z : ℂ)) Ψ
      = boxInv ℓ • cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) Ψ :=
    funext fun y => bDag_eq_cOp ℓ (fun z => (u z : ℂ)) Ψ y
  have key1 : cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ))
        (bDag ℓ (fun z => (v z : ℂ)) Ψ)
      = boxInv ℓ • cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ) := by
    rw [hbv, cOp_smul_state hℓ]
  have key2 : cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ))
        (bDag ℓ (fun z => (u z : ℂ)) Ψ)
      = boxInv ℓ • cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) Ψ) := by
    rw [hbu, cOp_smul_state hℓ]
  funext x
  have h := bDag_dag_comm hℓ (fun z => (u z : ℂ)) (fun z => (v z : ℂ)) Ψ
    huC hvC hΨ hum hvm x
  simp only [bDag_eq_cOp] at h
  rw [key1, key2] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [← mul_assoc, ← mul_assoc] at h
  exact mul_left_cancel₀ (mul_ne_zero (boxInv_ne_zero hℓ) (boxInv_ne_zero hℓ)) h

/-- annihilation commutativity in the `cOp` normalisation. -/
lemma cOp_comm_r {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (u v : ℝ³ → ℝ) {Ψ : X N → ℂ}
    (hu : Continuous u) (hv : Continuous v) (hΨ : Continuous Ψ)
    (hum : ∫ z in acube ℓ, (u z : ℂ) = 0) (hvm : ∫ z in acube ℓ, (v z : ℂ) = 0) :
    cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ))
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ)
      = cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ))
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ) := by
  have huC : Continuous fun z : ℝ³ => (u z : ℂ) := Complex.continuous_ofReal.comp hu
  have hvC : Continuous fun z : ℝ³ => (v z : ℂ) := Complex.continuous_ofReal.comp hv
  have h1 : Continuous fun _ : ℝ³ => (1 : ℂ) := continuous_const
  have hbv : bAnn ℓ (fun z => (v z : ℂ)) Ψ
      = boxInv ℓ • cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ :=
    funext fun y => bAnn_eq_cOp ℓ (fun z => (v z : ℂ)) Ψ y
  have hbu : bAnn ℓ (fun z => (u z : ℂ)) Ψ
      = boxInv ℓ • cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ :=
    funext fun y => bAnn_eq_cOp ℓ (fun z => (u z : ℂ)) Ψ y
  have key1 : cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ))
        (bAnn ℓ (fun z => (v z : ℂ)) Ψ)
      = boxInv ℓ • cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ))
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ) := by
    rw [hbv, cOp_smul_state hℓ]
  have key2 : cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ))
        (bAnn ℓ (fun z => (u z : ℂ)) Ψ)
      = boxInv ℓ • cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ))
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ) := by
    rw [hbu, cOp_smul_state hℓ]
  funext x
  have h := bAnn_comm hℓ (fun z => (u z : ℂ)) (fun z => (v z : ℂ)) Ψ
    huC hvC hΨ hum hvm x
  simp only [bAnn_eq_cOp] at h
  rw [key1, key2] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [← mul_assoc, ← mul_assoc] at h
  exact mul_left_cancel₀ (mul_ne_zero (boxInv_ne_zero hℓ) (boxInv_ne_zero hℓ)) h

theorem cOp_pair_offdiag {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (u v : ℝ³ → ℝ) {Ψ : X N → ℂ}
    (hu : Continuous u) (hv : Continuous v) (hΨ : Continuous Ψ)
    (hum : ∫ z in acube ℓ, (u z : ℂ) = 0) (hvm : ∫ z in acube ℓ, (v z : ℂ) = 0) :
    cOp ℓ (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun z => (u z : ℂ) - Complex.I * (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ)
      + cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ) - Complex.I * (v z : ℂ))
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) Ψ)
    = (cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ))
          (cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) Ψ)
        + cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ))
          (cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ))
      + (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ))
          (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ)
        + cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ))
          (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ)) := by
  have huC : Continuous fun z : ℝ³ => (u z : ℂ) := Complex.continuous_ofReal.comp hu
  have hvC : Continuous fun z : ℝ³ => (v z : ℂ) := Complex.continuous_ofReal.comp hv
  have h1 : Continuous fun _ : ℝ³ => (1 : ℂ) := continuous_const
  have hIvn : Continuous fun z : ℝ³ => Complex.I * (v z : ℂ) := continuous_const.mul hvC
  have hAu : Continuous (cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) Ψ) :=
    cOp_continuous_state hℓ huC h1 hΨ
  have hAv : Continuous (cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ) :=
    cOp_continuous_state hℓ hvC h1 hΨ
  have hA : Continuous (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ) :=
    cOp_continuous_state hℓ h1 huC hΨ
  have hB : Continuous (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ) :=
    cOp_continuous_state hℓ h1 hvC hΨ
  have eLp : ∀ X : X N → ℂ,
      cOp ℓ (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) (fun _ => (1 : ℂ)) X
        = cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) X
          + Complex.I • cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) X := by
    intro X; rw [cOp_add_left, cOp_smul_left]
  have eLm : ∀ X : X N → ℂ,
      cOp ℓ (fun z => (u z : ℂ) - Complex.I * (v z : ℂ)) (fun _ => (1 : ℂ)) X
        = cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) X
          + (-Complex.I) • cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) X := by
    intro X
    rw [show (fun z : ℝ³ => (u z : ℂ) - Complex.I * (v z : ℂ))
        = fun z => (u z : ℂ) + (-Complex.I) * (v z : ℂ) from by funext z; ring]
    rw [cOp_add_left, cOp_smul_left]
  have eRp : ∀ X : X N → ℂ, Continuous X →
      cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) X
        = cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) X
          + (-Complex.I) • cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) X := by
    intro X hX
    rw [cOp_add_right hℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ))
          (fun z => Complex.I * (v z : ℂ)) X huC hIvn hX,
        cOp_smul_right hℓ Complex.I (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) X]
    rw [show star Complex.I = -Complex.I from by rw [Complex.star_def, Complex.conj_I]]
  have eRm : ∀ X : X N → ℂ, Continuous X →
      cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ) - Complex.I * (v z : ℂ)) X
        = cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) X
          + Complex.I • cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) X := by
    intro X hX
    rw [show (fun z : ℝ³ => (u z : ℂ) - Complex.I * (v z : ℂ))
        = fun z => (u z : ℂ) + (-Complex.I) * (v z : ℂ) from by funext z; ring]
    rw [cOp_add_right hℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ))
          (fun z => (-Complex.I) * (v z : ℂ)) X huC (continuous_const.mul hvC) hX,
        cOp_smul_right hℓ (-Complex.I) (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) X]
    rw [show star (-Complex.I) = Complex.I from by
      rw [Complex.star_def, map_neg, Complex.conj_I, neg_neg]]
  rw [eLp, eLm,
      eRm (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) Ψ)
        (cOp_continuous_state hℓ h1 (huC.add hIvn) hΨ),
      eRp Ψ hΨ]
  rw [cOp_add_smul_state hℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) Ψ)
        (cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ) (-Complex.I) h1 hAu hAv,
      cOp_add_smul_state hℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ))
        (cOp ℓ (fun z => (u z : ℂ)) (fun _ => (1 : ℂ)) Ψ)
        (cOp ℓ (fun z => (v z : ℂ)) (fun _ => (1 : ℂ)) Ψ) (-Complex.I) h1 hAu hAv,
      cOp_add_smul_state hℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ))
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ)
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ) (-Complex.I) huC hA hB,
      cOp_add_smul_state hℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ))
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (u z : ℂ)) Ψ)
        (cOp ℓ (fun _ => (1 : ℂ)) (fun z => (v z : ℂ)) Ψ) (-Complex.I) hvC hA hB]
  rw [cOp_comm_l hℓ u v hu hv hΨ hum hvm, cOp_comm_r hℓ u v hu hv hΨ hum hvm]
  simp only [smul_add, smul_smul,
    show Complex.I * (-Complex.I) = (1 : ℂ) from by rw [mul_neg, Complex.I_mul_I, neg_neg],
    one_smul]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end BoseGases
end Submission
