import Mathlib
import Submission.Work.CKFinal.LineDecay.ContourPoint
import Submission.Work.CKFinal.LineDecay.j_eq_tau_of_lines
import Submission.Work.CKFinal.LineDecay.HatLayer
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Residues.KernelPoleLocation
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Asymptotics.KhatE1.STPure
import Submission.Work.Asymptotics.Tile.tileFarTools
import Submission.Work.Asymptotics.DivisorLowerEAux

/-!
# The two analytic inputs on the imaginary axis

This file supplies, for a *fixed* `τ` on one of the lines `Re τ = ±1/2` with `Im τ ≥ 12`:

* `zcb_not_orbit` : the contour points `i u` (`u > 0`) are never in the `SL(2,ℤ)`-orbit of `τ`,
  hence never poles of `K̂(τ,·)`;
* `khat_axis_continuous` : `u ↦ K̂^{(d)}(τ, i u)` is continuous on `(0,∞)`;
* `axis_divisor_lower` : `‖Δ(i u)(j τ - j(i u))‖` is bounded below on `u ≥ 1/3`;
* `khat_segment_bound` : `K̂^{(d)}(τ,·)` is bounded on the segment `{Im = 1, |Re| ≤ 1}`;
* `Aexp_Ghat_eq` : the `S`-transported cusp model `(𝒢₊ - 𝒢₋)/2` of `K̂` is `Aexp (Ĝ)`.
-/

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory
open scoped Topology Manifold

noncomputable section

variable {τ : UpperHalfPlane}

/-- **No point `i u` (`u > 0`) lies in the orbit of `τ`.**

If it did, then (using the `S`-invariance of `j` for `u < 1`, which replaces `u` by `1/u > 1`) the
`SL(2,ℤ)`-classification `j_eq_tau_of_lines` would force `i u` to be `τ`, `τ - 1` or `τ + 1`,
all of which have imaginary part `≥ 12`, whereas `i u` has imaginary part `u` and `u < 1` in the
second case, or `u` arbitrary in the first. -/
lemma zcb_not_orbit (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 12 ≤ τ.im) {u : ℝ}
    (hu : 0 < u) : Work.Kernels.jInvariantFun (zcb u) ≠ Work.Kernels.jInvariantFun τ := by
  have key : ∀ {v : ℝ}, 1 ≤ v → Work.Kernels.jInvariantFun (zcb v) = Work.Kernels.jInvariantFun τ →
      False := by
    intro v hv hJ
    have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
    obtain h1 | h1 | h1 := j_eq_tau_of_lines τ (zcb v) hre (by linarith)
      (by rw [zcb_re hv0]; norm_num) (by rw [zcb_re hv0]; norm_num)
      (by rw [zcb_im hv0]; exact hv) hJ
    · have hr := congrArg (fun w : ℍ => w.re) h1
      rw [zcb_re hv0] at hr
      rcases hre with h | h <;> rw [h] at hr <;> norm_num at hr
    · have hr := congrArg (fun w : ℍ => w.re) h1
      rw [zcb_re hv0, UpperHalfPlane.vadd_re] at hr
      rcases hre with h | h <;> rw [h] at hr <;> norm_num at hr
    · have hr := congrArg (fun w : ℍ => w.re) h1
      rw [zcb_re hv0, UpperHalfPlane.vadd_re] at hr
      rcases hre with h | h <;> rw [h] at hr <;> norm_num at hr
  intro h
  rcases le_or_gt 1 u with hge | hlt
  · exact key hge h
  · refine key ((one_le_inv₀ hu).mpr hlt.le) ?_
    rw [← S_smul_zcb hu, Work.Kernels.KernelFacts.jInvariantFun_S_smul]
    exact h

/-- **Continuity of the hatted kernel along the imaginary axis.** -/
theorem khat_axis_continuous (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 12 ≤ τ.im) :
    ContinuousOn (fun t : ℝ => Work.Kernels.Khat ℓ d τ (zcb t)) (Set.Ioi 0) := by
  intro t₀ ht₀
  have hzp : Work.Kernels.jInvariantFun (zcb t₀) ≠ Work.Kernels.jInvariantFun τ :=
    zcb_not_orbit hre hy ht₀
  have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => Work.Kernels.Khat ℓ d τ ζ) (zcb t₀) :=
    Work.Residues.mdifferentiableAt_Khat_snd ℓ d hd τ (zcb t₀) hzp
  have hcont : ContinuousAt (fun ζ : ℍ => Work.Kernels.Khat ℓ d τ ζ) (zcb t₀) :=
    hmd.continuousAt
  have hzcb : ContinuousAt zcb t₀ :=
    continuousOn_zcb.continuousAt (isOpen_Ioi.mem_nhds ht₀)
  exact (hcont.comp hzcb).continuousWithinAt

/-- `Δ(z)·j(z) = E₄(z)³`. -/
lemma DeltaFun_mul_jInvariantFun (z : UpperHalfPlane) :
    Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun z = Work.Kernels.E4Fun z ^ 3 := by
  rw [show Work.Kernels.jInvariantFun z
      = Work.Kernels.E4Fun z ^ 3 / Work.Kernels.DeltaFun z from rfl]
  exact mul_div_cancel₀ _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)

/-- The exponential-dominated scalar estimate: if `log (16 K + 1) ≤ 2 π u` then
`K e^{-2πu} ≤ 1/16`. -/
private lemma exp_decay_le (K u : ℝ) (hK : 0 ≤ K)
    (hlog : Real.log (16 * K + 1) ≤ 2 * Real.pi * u) :
    K * Real.exp (-(2 * Real.pi * u)) ≤ 1 / 16 := by
  have h2 : 16 * K + 1 ≤ Real.exp (2 * Real.pi * u) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 16 * K + 1)]
    exact Real.exp_le_exp.mpr hlog
  have h3 : Real.exp (-(2 * Real.pi * u)) ≤ (16 * K + 1)⁻¹ := by
    rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) (by positivity)]
    exact h2
  calc K * Real.exp (-(2 * Real.pi * u)) ≤ K * (16 * K + 1)⁻¹ :=
        mul_le_mul_of_nonneg_left h3 hK
    _ ≤ 1 / 16 := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 16)]
        nlinarith

/-- **The divisor is bounded below on the positive imaginary axis.**

For `τ` on the lines with `Im τ ≥ 12` there is `c > 0` with
`c ≤ ‖Δ(i u)(j τ - j(i u))‖` for all `u ≥ 1/3`.  For large `u` this is because
`Δ(i u)(j τ - j(i u)) = Δ(i u) j τ - E₄(i u)³` and `‖E₄‖ ≥ 1/2` there, so that the first term
(decaying like `e^{-2π u}`) cannot cancel the second; for `u` in the compact range `[1/3, Y]`
it follows from continuity and the non-vanishing of the divisor (no poles on the axis). -/
theorem axis_divisor_lower (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 12 ≤ τ.im) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, 1 / 3 ≤ u →
      c ≤ ‖Work.Kernels.DeltaFun (zcb u)
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (zcb u))‖ := by
  obtain ⟨CD, hCDpos, hΔup⟩ := Work.Asymptotics.delta_upper_third
  have hE4 : ∀ z : ℍ, 3 ≤ z.im → (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖ :=
    Work.FunnelNumerics.E4_funnel_bounds.2
  set Y : ℝ := max 3 (max (1 / 3)
    (Real.log (16 * (CD * ‖Work.Kernels.jInvariantFun τ‖) + 1) / (2 * Real.pi))) with hY
  have hY3 : 3 ≤ Y := le_max_left _ _
  have hY13 : (1 / 3 : ℝ) ≤ Y := le_trans (le_max_left _ _) (le_max_right _ _)
  -- continuity of the divisor along the axis
  have hcont : ContinuousOn (fun u : ℝ => ‖Work.Kernels.DeltaFun (zcb u)
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (zcb u))‖)
      (Set.Icc (1 / 3 : ℝ) Y) := by
    have hc : Continuous (fun w : ℍ => ‖Work.Kernels.DeltaFun w
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun w)‖) := by
      refine Continuous.norm (Continuous.mul ?_ ?_)
      · exact Work.Asymptotics.DivisorLowerE.continuous_DeltaFun
      · exact continuous_const.sub Work.Residues.continuous_jInvariantFun
    refine hc.comp_continuousOn (continuousOn_zcb.mono ?_)
    intro u hu
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) hu.1
  -- the compact part: a positive minimum
  obtain ⟨u₀, hu₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hY13) (hcont.neg)
  have hmin : ∀ u ∈ Set.Icc (1 / 3 : ℝ) Y,
      ‖Work.Kernels.DeltaFun (zcb u₀)
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (zcb u₀))‖
      ≤ ‖Work.Kernels.DeltaFun (zcb u)
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (zcb u))‖ := by
    intro u hu
    exact neg_le_neg_iff.mp (hmax hu)
  have hminpos : 0 < ‖Work.Kernels.DeltaFun (zcb u₀)
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (zcb u₀))‖ := by
    refine norm_pos_iff.mpr (mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _) ?_)
    exact sub_ne_zero.mpr (zcb_not_orbit hre hy (lt_of_lt_of_le (by norm_num) hu₀.1)).symm
  -- the large part
  have hlarge : ∀ u : ℝ, Y ≤ u → (1 / 16 : ℝ) ≤ ‖Work.Kernels.DeltaFun (zcb u)
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (zcb u))‖ := by
    intro u hu
    have hu3 : (3 : ℝ) ≤ u := le_trans hY3 hu
    have hu0 : 0 < u := by linarith
    have hzu : (zcb u).im = u := zcb_im hu0
    have hE4u : (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun (zcb u)‖ :=
      hE4 (zcb u) (by rw [hzu]; exact hu3)
    have hΔu : ‖Work.Kernels.DeltaFun (zcb u)‖ ≤ CD * Real.exp (-(2 * Real.pi * u)) := by
      calc ‖Work.Kernels.DeltaFun (zcb u)‖ ≤ CD * ‖Work.Kernels.qParamFun (zcb u)‖ :=
            hΔup (zcb u) (by rw [hzu]; linarith)
        _ = CD * Real.exp (-(2 * Real.pi * u)) := by
            rw [Work.Asymptotics.norm_qParamFun, hzu]
    have hE43 : (1 / 8 : ℝ) ≤ ‖Work.Kernels.E4Fun (zcb u) ^ 3‖ := by
      rw [norm_pow]
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hE4u 3
      norm_num at this
      linarith
    have hsmall : ‖Work.Kernels.DeltaFun (zcb u) * Work.Kernels.jInvariantFun τ‖ ≤ 1 / 16 := by
      rw [norm_mul]
      refine le_trans (mul_le_mul_of_nonneg_right hΔu (norm_nonneg _)) ?_
      have hK : (0 : ℝ) ≤ CD * ‖Work.Kernels.jInvariantFun τ‖ := by positivity
      have hlog : Real.log (16 * (CD * ‖Work.Kernels.jInvariantFun τ‖) + 1) ≤
          2 * Real.pi * u := by
        have h1 : Real.log (16 * (CD * ‖Work.Kernels.jInvariantFun τ‖) + 1)
            / (2 * Real.pi) ≤ Y :=
          le_trans (le_max_right _ _) (le_max_right _ _)
        have h2 := mul_le_mul_of_nonneg_right (le_trans h1 hu) (by positivity : (0:ℝ) ≤ 2 * Real.pi)
        rw [div_mul_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)] at h2
        calc Real.log (16 * (CD * ‖Work.Kernels.jInvariantFun τ‖) + 1)
            ≤ u * (2 * Real.pi) := h2
          _ = 2 * Real.pi * u := by ring
      calc (CD * Real.exp (-(2 * Real.pi * u))) * ‖Work.Kernels.jInvariantFun τ‖
          = (CD * ‖Work.Kernels.jInvariantFun τ‖) * Real.exp (-(2 * Real.pi * u)) := by ring
        _ ≤ 1 / 16 := exp_decay_le _ u hK hlog
    have hsplit : Work.Kernels.DeltaFun (zcb u)
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (zcb u))
        = Work.Kernels.DeltaFun (zcb u) * Work.Kernels.jInvariantFun τ
          - Work.Kernels.E4Fun (zcb u) ^ 3 := by
      rw [mul_sub, DeltaFun_mul_jInvariantFun (zcb u)]
    rw [hsplit]
    have hrev : ‖Work.Kernels.E4Fun (zcb u) ^ 3‖
        - ‖Work.Kernels.DeltaFun (zcb u) * Work.Kernels.jInvariantFun τ‖
        ≤ ‖Work.Kernels.DeltaFun (zcb u) * Work.Kernels.jInvariantFun τ
            - Work.Kernels.E4Fun (zcb u) ^ 3‖ := by
      have h := abs_norm_sub_norm_le
        (Work.Kernels.DeltaFun (zcb u) * Work.Kernels.jInvariantFun τ)
        (Work.Kernels.E4Fun (zcb u) ^ 3)
      have h2 := neg_le_abs (‖Work.Kernels.DeltaFun (zcb u) * Work.Kernels.jInvariantFun τ‖
        - ‖Work.Kernels.E4Fun (zcb u) ^ 3‖)
      linarith
    linarith
  refine ⟨min (1 / 16) ‖Work.Kernels.DeltaFun (zcb u₀)
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (zcb u₀))‖, ?_, ?_⟩
  · exact lt_min (by norm_num) hminpos
  · intro u hu
    rcases le_or_gt u Y with hle | hlt
    · exact le_trans (min_le_right _ _) (hmin u ⟨hu, hle⟩)
    · exact le_trans (min_le_left _ _) (hlarge u hlt.le)

/-- **No point of the segment `{Im = 1, |Re| ≤ 1}` is a pole of `K̂(τ,·)`.** -/
lemma segment_not_orbit (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 12 ≤ τ.im)
    {x : ℝ} (hx : |x| ≤ 1) :
    Work.Kernels.jInvariantFun ((x : ℝ) +ᵥ zcb 1) ≠ Work.Kernels.jInvariantFun τ := by
  intro h
  have hζim : (((x : ℝ) +ᵥ zcb 1 : ℍ)).im = 1 := by
    rw [UpperHalfPlane.vadd_im, zcb_im one_pos]
  have hx' := abs_le.mp hx
  have hζre1 : (-1 : ℝ) ≤ (((x : ℝ) +ᵥ zcb 1 : ℍ)).re := by
    rw [UpperHalfPlane.vadd_re, zcb_re one_pos, add_zero]; linarith [hx'.1]
  have hζre2 : (((x : ℝ) +ᵥ zcb 1 : ℍ)).re ≤ 1 := by
    rw [UpperHalfPlane.vadd_re, zcb_re one_pos, add_zero]; linarith [hx'.2]
  obtain h1 | h1 | h1 := j_eq_tau_of_lines τ ((x : ℝ) +ᵥ zcb 1) hre (by linarith)
    hζre1 hζre2 (by rw [hζim]) h
  · have him := congrArg (fun w : ℍ => w.im) h1
    rw [hζim] at him
    linarith
  · have him := congrArg (fun w : ℍ => w.im) h1
    rw [hζim, UpperHalfPlane.vadd_im] at him
    linarith
  · have him := congrArg (fun w : ℍ => w.im) h1
    rw [hζim, UpperHalfPlane.vadd_im] at him
    linarith

/-- **Continuity of the hatted kernel on the segment `{Im = 1, |Re| ≤ 1}`** in the first
variable. -/
theorem khat_segment_continuous (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 12 ≤ τ.im) :
    ContinuousOn (fun x : ℝ => Work.Kernels.Khat ℓ d τ ((x : ℝ) +ᵥ zcb 1))
      (Set.Icc (-1 : ℝ) 1) := by
  have hvadd : Continuous (fun x : ℝ => (x : ℝ) +ᵥ zcb 1) := by
    rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
    change Continuous (fun x : ℝ => UpperHalfPlane.coe ((x : ℝ) +ᵥ zcb 1))
    have hcoe : (fun x : ℝ => UpperHalfPlane.coe ((x : ℝ) +ᵥ zcb 1))
        = fun x : ℝ => (x : ℂ) + ((zcb 1 : ℍ) : ℂ) := by
      funext x
      rw [UpperHalfPlane.coe_vadd]
    rw [hcoe]
    exact Complex.continuous_ofReal.add continuous_const
  intro x₀ hx₀
  have hx₁ : |x₀| ≤ 1 := abs_le.mpr ⟨hx₀.1, hx₀.2⟩
  have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => Work.Kernels.Khat ℓ d τ ζ)
      ((x₀ : ℝ) +ᵥ zcb 1) :=
    Work.Residues.mdifferentiableAt_Khat_snd ℓ d hd τ ((x₀ : ℝ) +ᵥ zcb 1)
      (segment_not_orbit hre hy hx₁)
  have hcomp : ContinuousAt (fun x : ℝ => Work.Kernels.Khat ℓ d τ ((x : ℝ) +ᵥ zcb 1)) x₀ :=
    ContinuousAt.comp (f := fun x : ℝ => (x : ℝ) +ᵥ zcb 1) (x := x₀)
      hmd.continuousAt hvadd.continuousAt
  exact hcomp.continuousWithinAt

/-- **Continuity of `t ↦ K̂(τ, x + i t)` on `[1,∞)` for `x = ±1`.**

For `x = 1` (resp. `x = -1`) the points `x + i t` with `t ≥ 1` are never poles of `K̂(τ,·)`:
a pole would be a translate `τ + n`, whose real part is `±1/2, ±3/2`, never `±1`. -/
theorem khat_shift_continuous (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 12 ≤ τ.im) {x : ℝ}
    (hx : x = 1 ∨ x = -1) :
    ContinuousOn (fun t : ℝ => Work.Kernels.Khat ℓ d τ (x +ᵥ zcb t)) (Set.Ici 1) := by
  intro t₀ ht₀
  have ht1 : (0 : ℝ) < t₀ := lt_of_lt_of_le one_pos ht₀
  have hζim : ((x +ᵥ zcb t₀ : ℍ)).im = t₀ := by
    rw [UpperHalfPlane.vadd_im, zcb_im ht1]
  have hζre : ((x +ᵥ zcb t₀ : ℍ)).re = x := by
    rw [UpperHalfPlane.vadd_re, zcb_re ht1, add_zero]
  have hzp : Work.Kernels.jInvariantFun (x +ᵥ zcb t₀) ≠ Work.Kernels.jInvariantFun τ := by
    intro h
    have hζre1 : (-1 : ℝ) ≤ ((x +ᵥ zcb t₀ : ℍ)).re := by
      rw [hζre]; rcases hx with rfl | rfl <;> norm_num
    have hζre2 : ((x +ᵥ zcb t₀ : ℍ)).re ≤ 1 := by
      rw [hζre]; rcases hx with rfl | rfl <;> norm_num
    obtain h1 | h1 | h1 := j_eq_tau_of_lines τ (x +ᵥ zcb t₀) hre (by linarith)
      hζre1 hζre2 (by rw [hζim]; exact ht₀) h
    · have hr : x = τ.re := by
        rw [← hζre]; exact congrArg (fun w : ℍ => w.re) h1
      rcases hre with h | h <;> rw [h] at hr <;>
        rcases hx with hx' | hx' <;> rw [hx'] at hr <;> norm_num at hr
    · have hr : x = -1 + τ.re := by
        rw [← hζre, ← UpperHalfPlane.vadd_re]
        exact congrArg (fun w : ℍ => w.re) h1
      rcases hre with h | h <;> rw [h] at hr <;>
        rcases hx with hx' | hx' <;> rw [hx'] at hr <;> norm_num at hr
    · have hr : x = 1 + τ.re := by
        rw [← hζre, ← UpperHalfPlane.vadd_re]
        exact congrArg (fun w : ℍ => w.re) h1
      rcases hre with h | h <;> rw [h] at hr <;>
        rcases hx with hx' | hx' <;> rw [hx'] at hr <;> norm_num at hr
  have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => Work.Kernels.Khat ℓ d τ ζ)
      (x +ᵥ zcb t₀) :=
    Work.Residues.mdifferentiableAt_Khat_snd ℓ d hd τ (x +ᵥ zcb t₀) hzp
  have hzcb : ContinuousAt (fun t : ℝ => x +ᵥ zcb t) t₀ := by
    refine (Topology.IsInducing.continuousAt_iff (f := fun t : ℝ => x +ᵥ zcb t) (x := t₀)
      UpperHalfPlane.isEmbedding_coe.isInducing).mpr ?_
    change ContinuousAt (fun t : ℝ => UpperHalfPlane.coe (x +ᵥ zcb t)) t₀
    have hcoe : (fun t : ℝ => UpperHalfPlane.coe (x +ᵥ zcb t))
        = fun t : ℝ => (x : ℂ) + ((zcb t : ℍ) : ℂ) := by
      funext t
      rw [UpperHalfPlane.coe_vadd]
    rw [hcoe]
    exact continuousAt_const.add ((UpperHalfPlane.continuous_coe.continuousAt).comp
      (continuousOn_zcb.continuousAt (isOpen_Ioi.mem_nhds ht1)))
  have hcomp : ContinuousAt (fun t : ℝ => Work.Kernels.Khat ℓ d τ (x +ᵥ zcb t)) t₀ :=
    ContinuousAt.comp (f := fun t : ℝ => x +ᵥ zcb t) (x := t₀) hmd.continuousAt hzcb
  exact hcomp.continuousWithinAt

/-- **The hatted kernel is bounded on the segment `{Im = 1, |Re| ≤ 1}`.** -/
theorem khat_segment_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 12 ≤ τ.im) :
    ∃ M : ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖Work.Kernels.Khat ℓ d τ ((x : ℝ) +ᵥ zcb 1)‖ ≤ M := by
  obtain ⟨x₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1))
    ((khat_segment_continuous ℓ d hd hre hy).norm)
  exact ⟨‖Work.Kernels.Khat ℓ d τ ((x₀ : ℝ) +ᵥ zcb 1)‖, fun x hx => hmax hx⟩

/-- **The `S`-transported cusp model of `K̂` is `Aexp (Ĝ)`.**

`Aexp (Ĝ) τ t` (the exponential model of the hatted kernel) is the `S`-transported cusp model
`(𝒢₊^{(d)}(τ, i t) - 𝒢₋^{(d)}(τ, i t))/2` used in `khat_tail_deviation`. -/
theorem Aexp_Ghat_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    Work.Asymptotics.Aexp (Work.CKFinal.Ghat ℓ d) τ t
      = (Work.Asymptotics.Compact.Gplus d τ (zcb t)
          - Work.Asymptotics.Compact.Gminus d ℓ τ (zcb t)) / 2 := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hpowe : (τ : ℂ) ^ (-((d : ℤ) / 2)) * (τ : ℂ) ^ ((d : ℤ) / 2) = 1 := by
    rw [← zpow_add₀ hτ]; simp
  have h1 := Work.CKFinal.Aexp_S_smul ℓ d τ t
  have h2 : Work.Asymptotics.Aexp (Work.CKFinal.Ghat ℓ d) τ t
      = - (τ : ℂ) ^ (-((d : ℤ) / 2))
          * Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (ModularGroup.S • τ) t := by
    rw [h1]
    rw [show - (τ : ℂ) ^ (-((d : ℤ) / 2))
          * (-(τ : ℂ) ^ ((d : ℤ) / 2) * Work.Asymptotics.Aexp (Work.CKFinal.Ghat ℓ d) τ t)
        = ((τ : ℂ) ^ (-((d : ℤ) / 2)) * (τ : ℂ) ^ ((d : ℤ) / 2))
          * Work.Asymptotics.Aexp (Work.CKFinal.Ghat ℓ d) τ t from by ring,
      hpowe, one_mul]
  rw [h2, Work.Asymptotics.Tile.Aexp_Gcusp_eq_Gfun' ℓ d hd (ModularGroup.S • τ) t ht,
    ← zcb_eq_imagAxis ht,
    Work.Asymptotics.KhatE1.STPure.Gfun_S_smul ℓ d hd τ (zcb t)]
  rw [show - (τ : ℂ) ^ (-((d : ℤ) / 2))
        * (-(τ : ℂ) ^ ((d : ℤ) / 2)
          * (Work.Asymptotics.Compact.Gplus d τ (zcb t)
              - Work.Asymptotics.Compact.Gminus d ℓ τ (zcb t)) / 2)
      = ((τ : ℂ) ^ (-((d : ℤ) / 2)) * (τ : ℂ) ^ ((d : ℤ) / 2))
        * ((Work.Asymptotics.Compact.Gplus d τ (zcb t)
            - Work.Asymptotics.Compact.Gminus d ℓ τ (zcb t)) / 2) from by ring,
    hpowe, one_mul]

end

end Work.CKFinal.LineDecay
