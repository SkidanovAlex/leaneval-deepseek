import Mathlib
import Submission.Work.Drive.N2Lead.mobiusGeomDefs
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.twistToolkit
import Submission.Work.Drive.N2Lead.mobiusArcDefs
import Submission.Work.Drive.N2.saddleModelPsi

/-!
# The two untwisted model arcs of the upper level of the Möbius saddle

The toolkit for `Work.Drive.N2Lead.mobius_upperArcs`: see the docstring of the theorem there.
This file develops the elementary calculus the statement needs:

* the transition-function facts (`ST t + ST (1 - t) = 1`, `ST (1/2) = 1/2`, monotonicity at
  `1/2`, `deriv ST (1/2) = 2`);
* the coordinate form of the two slab twists applied to the model arcs (`uaA`, `uaB`, `uaTh`,
  `uaX`, `uaPsi`), i.e. the planar geometry of
  `α w = X w · cos`, `β` as in the statement;
* the estimates on `Re √` and `Im √` (the `σ' · Re ρ + Im ρ > 0` estimate) and the sign analysis.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Polynomial

noncomputable section

open Work.Drive.N2

/-! ## 1. The transition function `Real.smoothTransition` -/

lemma st_add_one_sub (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  have hden : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  have h2 : Real.smoothTransition (1 - x)
      = expNegInvGlue (1 - x) / (expNegInvGlue x + expNegInvGlue (1 - x)) := by
    simp only [Real.smoothTransition]
    rw [show expNegInvGlue (1 - (1 - x)) = expNegInvGlue x from by congr 1; ring, add_comm]
  rw [Real.smoothTransition, h2, ← add_div, div_self hden]

lemma st_half : Real.smoothTransition (1 / 2) = 1 / 2 := by
  have h := st_add_one_sub (1 / 2)
  norm_num at h
  linarith

lemma expNegInvGlue_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    expNegInvGlue x < expNegInvGlue y := by
  rw [expNegInvGlue, expNegInvGlue, if_neg (not_le.mpr hx),
    if_neg (not_le.mpr (hx.trans hxy)), Real.exp_lt_exp]
  have hl : y⁻¹ < x⁻¹ := by simpa using one_div_lt_one_div_of_lt hx hxy
  linarith

lemma st_lt_half_of_lt {x : ℝ} (h : x < 1 / 2) : Real.smoothTransition x < 1 / 2 := by
  have hden : (0:ℝ) < expNegInvGlue x + expNegInvGlue (1 - x) :=
    Real.smoothTransition.pos_denom x
  have hlt : expNegInvGlue x < expNegInvGlue (1 - x) := by
    rcases le_or_gt x 0 with hx | hx
    · have h1 : expNegInvGlue x = 0 := expNegInvGlue.zero_of_nonpos hx
      have h2 : 0 < expNegInvGlue (1 - x) := expNegInvGlue.pos_of_pos (by linarith)
      linarith
    · exact expNegInvGlue_lt hx (by linarith)
  rw [Real.smoothTransition, div_lt_iff₀ hden]
  linarith

lemma st_half_lt_of_lt {x : ℝ} (h : 1 / 2 < x) : 1 / 2 < Real.smoothTransition x := by
  have h1 := st_lt_half_of_lt (x := 1 - x) (by linarith)
  have h2 := st_add_one_sub x
  linarith

lemma st_lt_half_iff {x : ℝ} : Real.smoothTransition x < 1 / 2 ↔ x < 1 / 2 := by
  constructor
  · intro h
    rcases lt_trichotomy x (1 / 2) with hx | hx | hx
    · exact hx
    · rw [hx, st_half] at h; exact absurd h (lt_irrefl _)
    · exact absurd h (not_lt.mpr (le_of_lt (st_half_lt_of_lt hx)))
  · exact st_lt_half_of_lt

lemma st_half_lt_iff {x : ℝ} : 1 / 2 < Real.smoothTransition x ↔ 1 / 2 < x := by
  constructor
  · intro h
    rcases lt_trichotomy x (1 / 2) with hx | hx | hx
    · exact absurd h (not_lt.mpr (le_of_lt (st_lt_half_of_lt hx)))
    · rw [hx, st_half] at h; exact absurd h (lt_irrefl _)
    · exact hx
  · exact st_half_lt_of_lt

lemma st_deriv_nonneg (x : ℝ) : 0 ≤ deriv Real.smoothTransition x :=
  Monotone.deriv_nonneg (g := Real.smoothTransition) (x := x) Real.smoothTransition.monotone

theorem st_deriv_half : deriv Real.smoothTransition (1 / 2) = 2 := by
  have hg : HasDerivAt expNegInvGlue (4 * expNegInvGlue (1 / 2)) (1 / 2) := by
    have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) (1 / 2)
    convert h using 1
    · ext x; simp
    · norm_num
  have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) (1 / 2) := by
    have h : HasDerivAt (fun x : ℝ => (1:ℝ) - x) (0 - 1) (1 / 2) := by
      have h1 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 (1 / 2) := hasDerivAt_const _ _
      have h2 : HasDerivAt (fun x : ℝ => x) 1 (1 / 2) := hasDerivAt_id _
      exact h1.sub h2
    simpa using h
  have hg2 : HasDerivAt expNegInvGlue (4 * expNegInvGlue (1 / 2)) (1 - 1 / 2) := by
    rw [show (1:ℝ) - 1 / 2 = 1 / 2 by norm_num]; exact hg
  have hcomp : HasDerivAt (fun x : ℝ => expNegInvGlue (1 - x))
      (-4 * expNegInvGlue (1 / 2)) (1 / 2) := by
    have h := hg2.comp (1 / 2) hsub
    simpa [Function.comp_def] using h
  have hden : HasDerivAt (fun x : ℝ => expNegInvGlue x + expNegInvGlue (1 - x))
      (4 * expNegInvGlue (1 / 2) + (-4 * expNegInvGlue (1 / 2))) (1 / 2) := hg.add hcomp
  have hne : expNegInvGlue (1 / 2) + expNegInvGlue (1 - 1 / 2) ≠ 0 := by
    have h1 : 0 < expNegInvGlue (1 / 2) := expNegInvGlue.pos_of_pos (by norm_num)
    have h2 : 0 < expNegInvGlue (1 - 1 / 2) := expNegInvGlue.pos_of_pos (by norm_num)
    linarith
  have hquot := hg.div hden hne
  have hd : deriv (fun x : ℝ => expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x)))
        (1 / 2)
      = ((4 * expNegInvGlue (1 / 2) * (expNegInvGlue (1 / 2) + expNegInvGlue (1 - 1 / 2)) -
        expNegInvGlue (1 / 2) * (4 * expNegInvGlue (1 / 2) + -4 * expNegInvGlue (1 / 2))) /
      (expNegInvGlue (1 / 2) + expNegInvGlue (1 - 1 / 2)) ^ 2) := hquot.deriv
  have hfun : (fun x : ℝ => expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x)))
      = Real.smoothTransition := rfl
  rw [← hfun, hd]
  rw [show expNegInvGlue (1 - 1 / 2) = expNegInvGlue (1 / 2) by norm_num]
  have hgpos : (0:ℝ) < expNegInvGlue (1 / 2) := expNegInvGlue.pos_of_pos (by norm_num)
  rw [div_eq_iff (by positivity : (expNegInvGlue (1 / 2) + expNegInvGlue (1 / 2)) ^ 2 ≠ 0)]
  ring

/-- `deriv Real.smoothTransition 0 = 0`: the transition function is flat at the left end (its
derivative is continuous and vanishes on `(-∞, 0)`). -/
lemma st_deriv_zero : deriv Real.smoothTransition 0 = 0 := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    ContDiff.continuous_deriv (Real.smoothTransition.contDiff (n := ⊤)) (by simp)
  have hleft : deriv Real.smoothTransition =ᶠ[𝓝[<] (0:ℝ)] (fun _ => (0:ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [Filter.EventuallyEq.deriv_eq h, deriv_const]
  have htend : Tendsto (deriv Real.smoothTransition) (𝓝[<] (0:ℝ)) (𝓝 0) :=
    Tendsto.congr' hleft.symm tendsto_const_nhds
  exact tendsto_nhds_unique (l := 𝓝[<] (0:ℝ))
    (hcont.continuousAt.tendsto.mono_left inf_le_left) htend

/-- `deriv Real.smoothTransition 1 = 0`: the transition function is flat at the right end. -/
lemma st_deriv_one : deriv Real.smoothTransition 1 = 0 := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    ContDiff.continuous_deriv (Real.smoothTransition.contDiff (n := ⊤)) (by simp)
  have hright : deriv Real.smoothTransition =ᶠ[𝓝[>] (1:ℝ)] (fun _ => (0:ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1:ℝ)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [Filter.EventuallyEq.deriv_eq h, deriv_const]
  have htend : Tendsto (deriv Real.smoothTransition) (𝓝[>] (1:ℝ)) (𝓝 0) :=
    Tendsto.congr' hright.symm tendsto_const_nhds
  exact tendsto_nhds_unique (l := 𝓝[>] (1:ℝ))
    (hcont.continuousAt.tendsto.mono_left inf_le_left) htend

/-- The transition-function value is above/below `1/2` according to the argument. -/
lemma st_arg_neg {A b : ℝ} (hA : A ≠ 0) :
    Real.smoothTransition ((A + b) / (2 * A)) = 1 - Real.smoothTransition ((A - b) / (2 * A)) := by
  have h1 := st_add_one_sub ((A + b) / (2 * A))
  have h2 : 1 - (A + b) / (2 * A) = (A - b) / (2 * A) := by field_simp; ring
  rw [h2] at h1
  linarith

/-! ## 2. The model arc functions of the upper level

`uaRho η δ s w = √(ζ w)` with `ζ w = σ (s,w) + i w`, and the twisted coordinates. -/

/-- The level coordinate `σ (s, w)` of the saddle model. -/
noncomputable def uaSig (η δ s : ℝ) (w : ℝ) : ℝ := modelSigma η δ s w

/-- The model arc point in the chart coordinate: `ρ w = √(σ (s,w) + i w)`. -/
noncomputable def uaRho (η δ s : ℝ) (w : ℝ) : ℂ := Complex.sqrt (modelZeta η δ s w)

/-- The real part `Re ρ`. -/
noncomputable def uaA (η δ s : ℝ) (w : ℝ) : ℝ := (mobiusRho η δ s w).re

/-- The imaginary part `Im ρ` (odd, of the sign of `w`). -/
noncomputable def uaB (η δ s : ℝ) (w : ℝ) : ℝ := (mobiusRho η δ s w).im

/-- The twist angle of the horizontal slab twist on the arc. -/
noncomputable def uaTh (η δ s a' : ℝ) (w : ℝ) : ℝ :=
  Real.pi * Real.smoothTransition ((a' - uaB η δ s w) / (2 * a'))

/-- The `x`-coordinate of both twisted arcs. -/
noncomputable def uaX (η δ s a' : ℝ) (w : ℝ) : ℝ := uaA η δ s w * Real.cos (uaTh η δ s a' w)

/-- The twist angle of the vertical slab twist on the arc. -/
noncomputable def uaPsi (η δ s a' ε : ℝ) (w : ℝ) : ℝ :=
  Real.pi * Real.smoothTransition ((uaX η δ s a' w + ε) / (2 * ε))

lemma uaSig_eq (η δ s w : ℝ) : uaSig η δ s w = Work.Drive.N2.saddleSigma η δ (s, w) := rfl

lemma uaRho_eq_mobiusRho (η δ s w : ℝ) : uaRho η δ s w = mobiusRho η δ s w := rfl

lemma uaRho_eq_sqrt (η δ s w : ℝ) : uaRho η δ s w = Complex.sqrt (modelZeta η δ s w) := rfl

lemma uaB_eq_modelArcIm (η δ s w : ℝ) : uaB η δ s w = modelArcIm η δ s w :=
  rfl

lemma mobiusRho_eq_sqrt (η δ s w : ℝ) : mobiusRho η δ s w = Complex.sqrt (modelZeta η δ s w) :=
  rfl

lemma uaX_eq (η δ s a' w : ℝ) :
    uaX η δ s a' w = uaA η δ s w * Real.cos (uaTh η δ s a' w) := rfl

lemma uaPsi_eq (η δ s a' ε w : ℝ) :
    uaPsi η δ s a' ε w
      = Real.pi * Real.smoothTransition ((uaX η δ s a' w + ε) / (2 * ε)) := rfl

/-! ## 3. The coordinate form of the two slab twists -/

lemma twistY_apply_cE3_zero (a' : ℝ) (z : ℂ) :
    (twistY a' (-1) (cE3 z)) 0
      = z.re * Real.cos (Real.pi * Real.smoothTransition ((a' - z.im) / (2 * a'))) := by
  simp [twistY, rot02]

lemma twistY_apply_cE3_one (a' : ℝ) (z : ℂ) : (twistY a' (-1) (cE3 z)) 1 = z.im := by
  simp [twistY, rot02]

lemma twistY_apply_cE3_two (a' : ℝ) (z : ℂ) :
    (twistY a' (-1) (cE3 z)) 2
      = -z.re * Real.sin (Real.pi * Real.smoothTransition ((a' - z.im) / (2 * a'))) := by
  simp [twistY, rot02]

lemma twistX_apply_zero (ε : ℝ) (v : E3) : (twistX ε (-1) v) 0 = v 0 := by
  simp [twistX, rot12]

lemma twistX_apply_one (ε : ℝ) (v : E3) :
    (twistX ε (-1) v) 1 = v 1 * Real.cos (Real.pi * Real.smoothTransition ((v 0 + ε) / (2 * ε)))
      + v 2 * Real.sin (Real.pi * Real.smoothTransition ((v 0 + ε) / (2 * ε))) := by
  simp [twistX, rot12, Real.cos_neg, Real.sin_neg]

/-- The transition function reflected in `1/2`. -/
lemma st_neg_arg {A b : ℝ} (hA : 0 < A) :
    Real.smoothTransition ((A + b) / (2 * A)) = 1 - Real.smoothTransition ((A - b) / (2 * A)) :=
  st_arg_neg hA.ne'

/-- The cosine of the reflected twist angle: `cos θ (A + b) = - cos θ (A - b)`. -/
lemma cos_st_neg_arg {A b : ℝ} (hA : 0 < A) :
    Real.cos (Real.pi * Real.smoothTransition ((A + b) / (2 * A)))
      = -Real.cos (Real.pi * Real.smoothTransition ((A - b) / (2 * A))) := by
  rw [st_neg_arg hA,
    show Real.pi * (1 - Real.smoothTransition ((A - b) / (2 * A)))
      = Real.pi - Real.pi * Real.smoothTransition ((A - b) / (2 * A)) from by ring,
    Real.cos_pi_sub]

/-- The sine of the reflected twist angle: `sin θ (A + b) = sin θ (A - b)`. -/
lemma sin_st_neg_arg {A b : ℝ} (hA : 0 < A) :
    Real.sin (Real.pi * Real.smoothTransition ((A + b) / (2 * A)))
      = Real.sin (Real.pi * Real.smoothTransition ((A - b) / (2 * A))) := by
  rw [st_neg_arg hA,
    show Real.pi * (1 - Real.smoothTransition ((A - b) / (2 * A)))
      = Real.pi - Real.pi * Real.smoothTransition ((A - b) / (2 * A)) from by ring,
    Real.sin_pi_sub]

/-! ### The algebraic identities for `ρ`

`Re ρ = √((‖ζ‖ + σ)/2)`, `Im ρ = ±√((‖ζ‖ - σ)/2)`, `2 Re ρ Im ρ = w`. -/

lemma uaSig_eq_modelSigma (η δ s w : ℝ) : uaSig η δ s w = modelSigma η δ s w := rfl

lemma modelSigma_eq_uaSig (η δ s w : ℝ) : modelSigma η δ s w = uaSig η δ s w := rfl

lemma uaA_eq_sqrt (η δ s w : ℝ) :
    uaA η δ s w = Real.sqrt ((‖modelZeta η δ s w‖ + uaSig η δ s w) / 2) := by
  rw [uaA, mobiusRho_eq_sqrt, Complex.sqrt_eq_real_add_ite, modelZeta_re, modelZeta_im,
    modelSigma_eq_uaSig]
  split_ifs <;> simp [Complex.mul_I_re, Complex.mul_I_im]

lemma uaB_eq_sqrt (η δ s w : ℝ) :
    uaB η δ s w = (if 0 ≤ w then 1 else -1)
      * Real.sqrt ((‖modelZeta η δ s w‖ - uaSig η δ s w) / 2) := by
  rw [uaB, mobiusRho_eq_sqrt, Complex.sqrt_eq_real_add_ite, modelZeta_re, modelZeta_im,
    modelSigma_eq_uaSig]
  split_ifs <;> simp [Complex.mul_I_re, Complex.mul_I_im, Real.sqrt_div]

/-- The plateau `saddleM δ` takes its values in `[0,1]`. -/
lemma saddleM_mem_Icc (δ w : ℝ) : saddleM δ w ∈ Set.Icc (0:ℝ) 1 := by
  rw [saddleM, saddleMu]
  refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (Real.smoothTransition.le_one _)),
    mul_le_one₀ (Real.smoothTransition.le_one _)
      (sub_nonneg.mpr (Real.smoothTransition.le_one _))
      (sub_le_self _ (Real.smoothTransition.nonneg _))⟩

lemma uaSig_eq_affine (η δ s w : ℝ) : uaSig η δ s w = s + saddleM δ w * (-η - s) :=
  modelSigma_eq η δ s w

section ModelBounds

variable {η δ s : ℝ}

lemma uaSig_le_s {η δ s : ℝ} (hη : 0 < η) (hs : 0 < s) (w : ℝ) : uaSig η δ s w ≤ s := by
  have hM := (saddleM_mem_Icc δ w).1
  rw [uaSig_eq_affine]
  have : saddleM δ w * (-η - s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM (by linarith)
  linarith

lemma neg_eta_le_uaSig {η δ s : ℝ} (hη : 0 < η) (hs : 0 < s) (w : ℝ) :
    -η ≤ uaSig η δ s w := by
  have hM := (saddleM_mem_Icc δ w).2
  rw [uaSig_eq_affine]
  nlinarith [hM, hη, hs]

lemma abs_uaSig_le {η δ s : ℝ} (hη : 0 < η) (hs : 0 < s) (hsη : s ≤ η) (w : ℝ) :
    |uaSig η δ s w| ≤ η :=
  abs_le.mpr ⟨neg_eta_le_uaSig hη hs w, le_trans (uaSig_le_s hη hs w) hsη⟩

lemma norm_modelZeta_lt {η δ s : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hs : 0 < s)
    (hsη : s ≤ η) {w : ℝ} (hw : |w| ≤ 2) : ‖modelZeta η δ s w‖ < 21 / 10 := by
  have hN := norm_modelZeta η δ s w
  have hσ : |uaSig η δ s w| ≤ η := abs_uaSig_le hη hs hsη w
  have hσ2 : uaSig η δ s w ^ 2 ≤ η ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hσ 2
  have hw2 : w ^ 2 ≤ 4 := by nlinarith [abs_le.mp hw]
  have hsq : ‖modelZeta η δ s w‖ ^ 2 < (21 / 10 : ℝ) ^ 2 := by
    rw [hN, modelSigma_eq_uaSig, Real.sq_sqrt (show (0:ℝ) ≤ uaSig η δ s w ^ 2 + w ^ 2 by positivity)]
    nlinarith [hσ2, hw2, hη']
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

lemma uaA_plus_pos (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s) (hδ₂ : δ < 1 / 2) (w : ℝ) :
    0 < ‖modelZeta η δ s w‖ + uaSig η δ s w := by
  have hN2 : ‖modelZeta η δ s w‖ ^ 2 = uaSig η δ s w ^ 2 + w ^ 2 := by
    rw [norm_modelZeta, modelSigma_eq_uaSig]
    exact Real.sq_sqrt (by positivity)
  rcases eq_or_ne w 0 with rfl | hw
  · have h0 : uaSig η δ s 0 = s := by
      rw [uaSig_eq_affine, saddleM_zero_of_lt_half hδ hδ₂]
      ring
    rw [h0]
    positivity
  · have hlt : |uaSig η δ s w| < ‖modelZeta η δ s w‖ := by
      have hsq : uaSig η δ s w ^ 2 < ‖modelZeta η δ s w‖ ^ 2 := by
        rw [hN2]; nlinarith [sq_pos_of_ne_zero hw]
      rwa [sq_lt_sq, abs_of_nonneg (norm_nonneg _)] at hsq
    linarith [neg_abs_le (uaSig η δ s w)]

lemma uaA_pos (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s) (hδ₂ : δ < 1 / 2) (w : ℝ) :
    0 < uaA η δ s w := by
  rw [uaA_eq_sqrt]
  exact Real.sqrt_pos.mpr (by linarith [uaA_plus_pos hδ hη hs hδ₂ w])

lemma uaA_sq (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s) (hδ₂ : δ < 1 / 2) (w : ℝ) :
    uaA η δ s w ^ 2 = (‖modelZeta η δ s w‖ + uaSig η δ s w) / 2 := by
  rw [uaA_eq_sqrt]
  exact Real.sq_sqrt (by linarith [uaA_plus_pos hδ hη hs hδ₂ w])

lemma two_mul_uaA_mul_uaB (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s) (hδ₂ : δ < 1 / 2)
    (w : ℝ) : 2 * uaA η δ s w * uaB η δ s w = w := by
  have hN2 : ‖modelZeta η δ s w‖ ^ 2 = uaSig η δ s w ^ 2 + w ^ 2 := by
    rw [norm_modelZeta, modelSigma_eq_uaSig]
    exact Real.sq_sqrt (by positivity)
  have hA : 0 < ‖modelZeta η δ s w‖ + uaSig η δ s w := uaA_plus_pos hδ hη hs hδ₂ w
  have hsq : (‖modelZeta η δ s w‖ + uaSig η δ s w) * (‖modelZeta η δ s w‖ - uaSig η δ s w)
      = w ^ 2 := by nlinarith [hN2]
  have hsqrt : Real.sqrt ((‖modelZeta η δ s w‖ + uaSig η δ s w) / 2)
      * Real.sqrt ((‖modelZeta η δ s w‖ - uaSig η δ s w) / 2) = |w| / 2 := by
    rw [← Real.sqrt_mul (by linarith), show (‖modelZeta η δ s w‖ + uaSig η δ s w) / 2
      * ((‖modelZeta η δ s w‖ - uaSig η δ s w) / 2) = (w / 2) ^ 2 by nlinarith [hsq],
      Real.sqrt_sq_eq_abs, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have key : 2 * Real.sqrt ((‖modelZeta η δ s w‖ + uaSig η δ s w) / 2)
      * Real.sqrt ((‖modelZeta η δ s w‖ - uaSig η δ s w) / 2) = |w| := by
    rw [mul_assoc, hsqrt]; ring
  rw [uaA_eq_sqrt, uaB_eq_sqrt]
  split_ifs with hw
  · rw [one_mul, key, abs_of_nonneg hw]
  · push_neg at hw
    rw [show -1 * Real.sqrt ((‖modelZeta η δ s w‖ - uaSig η δ s w) / 2)
        = -Real.sqrt ((‖modelZeta η δ s w‖ - uaSig η δ s w) / 2) by ring, mul_neg, key,
      abs_of_neg hw]
    ring

lemma uaB_eq_div (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s) (hδ₂ : δ < 1 / 2) (w : ℝ) :
    uaB η δ s w = w / (2 * uaA η δ s w) := by
  have hpos := uaA_pos hδ hη hs hδ₂ w
  have h := two_mul_uaA_mul_uaB hδ hη hs hδ₂ w
  field_simp
  linarith [h]

lemma uaA_neg (η δ s w : ℝ) : uaA η δ s (-w) = uaA η δ s w := by
  simp only [uaA_eq_sqrt, uaSig_eq_modelSigma, modelSigma_even, norm_modelZeta_neg]

lemma uaB_neg (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s) (hδ₂ : δ < 1 / 2) (w : ℝ) :
    uaB η δ s (-w) = - uaB η δ s w := by
  rw [uaB_eq_div hδ hη hs hδ₂, uaB_eq_div hδ hη hs hδ₂, uaA_neg]
  ring

lemma uaB_pos_iff (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s) (hδ₂ : δ < 1 / 2) {w : ℝ} :
    0 < uaB η δ s w ↔ 0 < w := by
  rw [uaB_eq_div hδ hη hs hδ₂]
  have hpos := uaA_pos hδ hη hs hδ₂ w
  constructor
  · intro h; by_contra hw; push_neg at hw
    have : w / (2 * uaA η δ s w) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hw (by linarith)
    linarith
  · intro hw; positivity

lemma uaB_neg_iff (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s) (hδ₂ : δ < 1 / 2) {w : ℝ} :
    uaB η δ s w < 0 ↔ w < 0 := by
  have h := uaB_pos_iff (δ := δ) (η := η) (s := s) (w := -w) hδ hη hs hδ₂
  rw [uaB_neg hδ hη hs hδ₂ w, neg_pos, neg_pos] at h
  exact h

lemma uaB_zero_iff (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s) (hδ₂ : δ < 1 / 2) {w : ℝ} :
    uaB η δ s w = 0 ↔ w = 0 := by
  rw [uaB_eq_div hδ hη hs hδ₂]
  have hpos := uaA_pos hδ hη hs hδ₂ w
  constructor
  · intro h
    have h' := div_eq_zero_iff.mp h
    rcases h' with h'' | h''
    · exact h''
    · linarith
  · intro h; rw [h]; simp

end ModelBounds

/-! ### The derivatives of `uaSig`, `uaA`, `uaB`, `uaX`

The derivative values are collected in the definitions `uaAD`, `uaBD`, `uaXD`; the companion lemmas
`hasDerivAt_uaA`, `hasDerivAt_uaB`, `hasDerivAt_uaX` identify them with the `deriv`s. -/

/-- The derivative of `Re ρ`: `(w + σ' (σ + ‖ζ‖)) / (4 Re ρ ‖ζ‖)`. -/
noncomputable def uaAD (η δ s : ℝ) (w : ℝ) : ℝ :=
  (w + deriv (uaSig η δ s) w * (uaSig η δ s w + ‖modelZeta η δ s w‖)) /
    (4 * uaA η δ s w * ‖modelZeta η δ s w‖)

/-- The derivative of `Im ρ`, from `Im ρ = w / (2 Re ρ)`. -/
noncomputable def uaBD (η δ s : ℝ) (w : ℝ) : ℝ :=
  (uaA η δ s w - w * uaAD η δ s w) / (2 * uaA η δ s w ^ 2)

/-- The derivative of the `x`-coordinate `uaX` of the twisted arcs. -/
noncomputable def uaXD (η δ s a' : ℝ) (w : ℝ) : ℝ :=
  uaAD η δ s w * Real.cos (uaTh η δ s a' w)
    + uaA η δ s w * Real.sin (uaTh η δ s a' w) *
      (Real.pi * deriv Real.smoothTransition ((a' - uaB η δ s w) / (2 * a'))
        * uaBD η δ s w / (2 * a'))

section ModelDeriv

variable {η δ s a' : ℝ}

lemma differentiableAt_uaSig (hδ : 0 < δ) (hδ' : δ < 1 / 10) (w : ℝ) :
    DifferentiableAt ℝ (uaSig η δ s) w := by
  have h2 : (0:ℝ) < 2 - 4 * δ := by linarith
  have hM : DifferentiableAt ℝ (saddleM δ) w :=
    ((contDiff_saddleM hδ h2).differentiable (by simp)).differentiableAt
  have h1 : DifferentiableAt ℝ (fun _ : ℝ => s) w := differentiableAt_const _
  have h3 : DifferentiableAt ℝ (fun _ : ℝ => -η - s) w := differentiableAt_const _
  have h : DifferentiableAt ℝ (fun y : ℝ => s + saddleM δ y * (-η - s)) w :=
    h1.add (hM.mul h3)
  have hfun : (fun y : ℝ => s + saddleM δ y * (-η - s)) = uaSig η δ s := by
    funext y; rw [uaSig_eq_affine]
  rwa [hfun] at h

lemma hasDerivAt_uaSig (hδ : 0 < δ) (hδ' : δ < 1 / 10) (w : ℝ) :
    HasDerivAt (uaSig η δ s) (deriv (uaSig η δ s) w) w :=
  (differentiableAt_uaSig (η := η) (s := s) hδ hδ' w).hasDerivAt

lemma norm_modelZeta_pos (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hs : 0 < s) (w : ℝ) :
    0 < ‖modelZeta η δ s w‖ := by
  have hN2 : ‖modelZeta η δ s w‖ ^ 2 = uaSig η δ s w ^ 2 + w ^ 2 := by
    rw [norm_modelZeta, modelSigma_eq_uaSig]
    exact Real.sq_sqrt (by positivity)
  have hpos : 0 < ‖modelZeta η δ s w‖ ^ 2 := by
    rcases eq_or_ne w 0 with rfl | hw
    · have h0 : uaSig η δ s 0 = s := by
        rw [uaSig_eq_affine, saddleM_zero_of_lt_half hδ hδ₂]
        ring
      rw [hN2, h0]
      nlinarith [hs]
    · rw [hN2]
      nlinarith [sq_pos_of_ne_zero hw, sq_nonneg (uaSig η δ s w)]
  nlinarith [norm_nonneg (modelZeta η δ s w)]

lemma hasDerivAt_modelZeta_norm (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hδ₂ : δ < 1 / 2)
    (hs : 0 < s) (w : ℝ) :
    HasDerivAt (fun y : ℝ => ‖modelZeta η δ s y‖)
      ((uaSig η δ s w * deriv (uaSig η δ s) w + w) / ‖modelZeta η δ s w‖) w := by
  have hNne : ‖modelZeta η δ s w‖ ≠ 0 := (norm_modelZeta_pos (η := η) (s := s) hδ hδ₂ hs w).ne'
  have hfun : (fun y : ℝ => ‖modelZeta η δ s y‖)
      = fun y : ℝ => Real.sqrt (uaSig η δ s y ^ 2 + y ^ 2) := by
    funext y
    rw [norm_modelZeta, modelSigma_eq_uaSig]
  rw [hfun]
  have hσ := hasDerivAt_uaSig (η := η) (s := s) hδ hδ' w
  have hne : uaSig η δ s w ^ 2 + w ^ 2 ≠ 0 := by
    rcases eq_or_ne w 0 with rfl | hw
    · have h2 : (0:ℝ) < 2 - 4 * δ := by linarith
      have h0 : uaSig η δ s 0 = s := by
        rw [uaSig_eq_affine, saddleM_zero hδ (le_of_lt h2)]
        ring
      rw [h0]
      positivity
    · exact ne_of_gt (by nlinarith [sq_pos_of_ne_zero hw, sq_nonneg (uaSig η δ s w)])
  have h1 := ((hσ.pow 2).add ((hasDerivAt_id w).pow 2)).sqrt hne
  refine h1.congr_deriv ?_
  simp only [Pi.add_apply, Pi.pow_apply, id_eq]
  rw [uaSig_eq_modelSigma η δ s w, ← norm_modelZeta η δ s w]
  have hNne : ‖modelZeta η δ s w‖ ≠ 0 := (norm_modelZeta_pos (η := η) (s := s) hδ hδ₂ hs w).ne'
  field_simp
  ring

set_option maxHeartbeats 1000000 in
lemma hasDerivAt_uaA (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hs : 0 < s)
    (hδ₂ : δ < 1 / 2) (w : ℝ) :
    HasDerivAt (uaA η δ s) (uaAD η δ s w) w := by
  have hfun : uaA η δ s = fun y : ℝ => Real.sqrt ((‖modelZeta η δ s y‖ + uaSig η δ s y) / 2) :=
    funext (fun y => uaA_eq_sqrt η δ s y)
  have hpos : 0 < (‖modelZeta η δ s w‖ + uaSig η δ s w) / 2 := by
    linarith [uaA_plus_pos (δ := δ) (η := η) (s := s) hδ hη hs hδ₂ w]
  have hN := hasDerivAt_modelZeta_norm (η := η) (s := s) hδ hδ' hδ₂ hs w
  have hσ := hasDerivAt_uaSig (η := η) (s := s) hδ hδ' w
  have h1 := ((hN.add hσ).div_const 2).sqrt (ne_of_gt hpos)
  rw [hfun]
  refine h1.congr_deriv ?_
  rw [uaAD]
  simp only [Pi.add_apply]
  rw [← uaA_eq_sqrt η δ s w]
  have hApos : 0 < uaA η δ s w := uaA_pos hδ hη hs hδ₂ w
  have hNne : ‖modelZeta η δ s w‖ ≠ 0 := (norm_modelZeta_pos (η := η) (s := s) hδ hδ₂ hs w).ne'
  field_simp
  ring

set_option maxHeartbeats 1000000 in
lemma hasDerivAt_uaB (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hs : 0 < s)
    (hδ₂ : δ < 1 / 2) (w : ℝ) :
    HasDerivAt (uaB η δ s) (uaBD η δ s w) w := by
  have hfun : uaB η δ s = fun y : ℝ => y / (2 * uaA η δ s y) :=
    funext (fun y => uaB_eq_div hδ hη hs hδ₂ y)
  have hApos : 0 < uaA η δ s w := uaA_pos hδ hη hs hδ₂ w
  have hden : (2 * uaA η δ s w) ≠ 0 := by positivity
  have hA := hasDerivAt_uaA (s := s) hδ hδ' hη hs hδ₂ w
  have h1 := (hasDerivAt_id w).div (hA.const_mul 2) hden
  rw [hfun]
  refine h1.congr_deriv ?_
  rw [uaBD, uaAD]
  simp only [id_eq]
  field_simp
  try ring

lemma deriv_uaA_eq (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hs : 0 < s)
    (hδ₂ : δ < 1 / 2) (w : ℝ) : deriv (uaA η δ s) w = uaAD η δ s w :=
  (hasDerivAt_uaA hδ hδ' hη hs hδ₂ w).deriv

lemma deriv_uaB_eq (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hs : 0 < s)
    (hδ₂ : δ < 1 / 2) (w : ℝ) : deriv (uaB η δ s) w = uaBD η δ s w :=
  (hasDerivAt_uaB hδ hδ' hη hs hδ₂ w).deriv

lemma deriv_uaA_neg (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hs : 0 < s)
    (hδ₂ : δ < 1 / 2) (w : ℝ) : deriv (uaA η δ s) (-w) = - deriv (uaA η δ s) w := by
  have h1 : HasDerivAt (fun y : ℝ => uaA η δ s (-y)) (-(uaAD η δ s (-w))) w := by
    have h := (hasDerivAt_uaA hδ hδ' hη hs hδ₂ (-w)).comp w (hasDerivAt_neg' (x := w))
    simpa [Function.comp_def] using h
  have h2 : HasDerivAt (fun y : ℝ => uaA η δ s (-y)) (uaAD η δ s w) w := by
    have h3 : HasDerivAt (uaA η δ s) (uaAD η δ s w) w := hasDerivAt_uaA hδ hδ' hη hs hδ₂ w
    have h4 : (fun y : ℝ => uaA η δ s (-y)) = uaA η δ s := funext (fun y => uaA_neg η δ s y)
    rw [← h4] at h3
    exact h3
  have huniq := h1.unique h2
  rw [deriv_uaA_eq hδ hδ' hη hs hδ₂ (-w), deriv_uaA_eq hδ hδ' hη hs hδ₂ w]
  linarith

lemma deriv_uaB_neg (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η) (hs : 0 < s)
    (hδ₂ : δ < 1 / 2) (w : ℝ) : deriv (uaB η δ s) (-w) = deriv (uaB η δ s) w := by
  have h1 : HasDerivAt (fun y : ℝ => uaB η δ s (-y)) (-(uaBD η δ s (-w))) w := by
    have h := (hasDerivAt_uaB hδ hδ' hη hs hδ₂ (-w)).comp w (hasDerivAt_neg' (x := w))
    simpa [Function.comp_def] using h
  have h2 : HasDerivAt (fun y : ℝ => uaB η δ s (-y)) (-(uaBD η δ s w)) w := by
    have h3 : HasDerivAt (fun y : ℝ => - uaB η δ s y) (-(uaBD η δ s w)) w :=
      (hasDerivAt_uaB hδ hδ' hη hs hδ₂ w).neg
    have h4 : (fun y : ℝ => - uaB η δ s y) = fun y : ℝ => uaB η δ s (-y) :=
      funext (fun y => (uaB_neg hδ hη hs hδ₂ y).symm)
    rw [h4] at h3
    exact h3
  have huniq := h1.unique h2
  rw [deriv_uaB_eq hδ hδ' hη hs hδ₂ (-w), deriv_uaB_eq hδ hδ' hη hs hδ₂ w]
  linarith


/-! ### The range of the twist angle and its value at `0` -/

lemma uaB_zero (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s) (hδ₂ : δ < 1 / 2) :
    uaB η δ s 0 = 0 := by
  rw [uaB_eq_div hδ hη hs hδ₂]
  simp

lemma uaTh_mem {η δ s a' : ℝ} (ha' : 0 < a') (w : ℝ) :
    uaTh η δ s a' w ∈ Set.Icc (0:ℝ) Real.pi := by
  have h1 : 0 ≤ Real.smoothTransition ((a' - uaB η δ s w) / (2 * a')) :=
    Real.smoothTransition.nonneg _
  have h2 : Real.smoothTransition ((a' - uaB η δ s w) / (2 * a')) ≤ 1 :=
    Real.smoothTransition.le_one _
  rw [uaTh]
  exact ⟨mul_nonneg Real.pi_pos.le h1, by nlinarith [Real.pi_pos]⟩

lemma sin_uaTh_nonneg {η δ s a' : ℝ} (ha' : 0 < a') (w : ℝ) :
    0 ≤ Real.sin (uaTh η δ s a' w) :=
  Real.sin_nonneg_of_mem_Icc (uaTh_mem ha' w)

lemma uaTh_zero (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hη : 0 < η) (hs : 0 < s) {a' : ℝ}
    (ha' : 0 < a') : uaTh η δ s a' 0 = Real.pi / 2 := by
  rw [uaTh, uaB_zero (δ := δ) hδ hη hs hδ₂]
  have h : (a' - 0) / (2 * a') = 1 / 2 := by field_simp; ring
  rw [h, st_half]
  ring

end ModelDeriv

/-! ### The coordinates of `β` (the `+ρ` arc) -/

lemma mobiusBeta_zero (η δ s a' ε w : ℝ) :
    (mobiusBeta η δ s a' ε w) 0 = uaX η δ s a' w := by
  rw [mobiusBeta, twistX_apply_zero, twistY_apply_cE3_zero, uaX, uaTh, uaA, uaB]

lemma mobiusBeta_one (η δ s a' ε w : ℝ) :
    (mobiusBeta η δ s a' ε w) 1
      = uaB η δ s w * Real.cos (uaPsi η δ s a' ε w)
        - uaA η δ s w * Real.sin (uaTh η δ s a' w) * Real.sin (uaPsi η δ s a' ε w) := by
  rw [mobiusBeta, twistX_apply_one, twistY_apply_cE3_one, twistY_apply_cE3_two,
    twistY_apply_cE3_zero]
  simp only [uaPsi, uaX, uaTh, uaA, uaB]
  ring

/-! ### The coordinates of `α` (the `-ρ` arc) -/

lemma twistY_neg_rho_zero (η δ s a' w : ℝ) (ha' : 0 < a') :
    (twistY a' (-1) (cE3 (-(mobiusRho η δ s w)))) 0 = uaX η δ s a' w := by
  rw [twistY_apply_cE3_zero, uaX, uaTh, uaA, uaB, Complex.neg_re, Complex.neg_im]
  rw [show a' - -(mobiusRho η δ s w).im = a' + (mobiusRho η δ s w).im from by ring,
    cos_st_neg_arg (b := (mobiusRho η δ s w).im) ha']
  ring

lemma twistY_neg_rho_one (η δ s a' w : ℝ) :
    (twistY a' (-1) (cE3 (-(mobiusRho η δ s w)))) 1 = - uaB η δ s w := by
  rw [twistY_apply_cE3_one, uaB, Complex.neg_im]

lemma twistY_neg_rho_two (η δ s a' w : ℝ) (ha' : 0 < a') :
    (twistY a' (-1) (cE3 (-(mobiusRho η δ s w)))) 2
      = uaA η δ s w * Real.sin (uaTh η δ s a' w) := by
  rw [twistY_apply_cE3_two, uaA, uaTh, uaB, Complex.neg_re, Complex.neg_im]
  rw [show a' - -(mobiusRho η δ s w).im = a' + (mobiusRho η δ s w).im from by ring,
    sin_st_neg_arg (b := (mobiusRho η δ s w).im) ha']
  ring

lemma mobiusAlpha_zero (η δ s a' ε w : ℝ) (ha' : 0 < a') :
    (mobiusAlpha η δ s a' ε w) 0 = uaX η δ s a' w := by
  rw [mobiusAlpha, twistX_apply_zero, twistY_neg_rho_zero η δ s a' w ha']

lemma mobiusAlpha_one (η δ s a' ε w : ℝ) (ha' : 0 < a') :
    (mobiusAlpha η δ s a' ε w) 1
      = - uaB η δ s w * Real.cos (uaPsi η δ s a' ε w)
        + uaA η δ s w * Real.sin (uaTh η δ s a' w) * Real.sin (uaPsi η δ s a' ε w) := by
  rw [mobiusAlpha, twistX_apply_one, twistY_neg_rho_one, twistY_neg_rho_two η δ s a' w ha',
    twistY_neg_rho_zero η δ s a' w ha']
  simp only [uaPsi, uaX, uaTh, uaA, uaB]


end

end Work.Drive.N2Lead
