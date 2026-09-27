import Mathlib
import Submission.Work.Drive.N2Lead.twistToolkit
import Submission.Work.Drive.N2Lead.arcZ_re_strictMono
import Submission.Work.Drive.N2Lead.saddleArcs

/-!
# The Möbius pin curve row

The Möbius saddle packet pins the level curve of the model window onto the two model arcs
`cE3 (arcZ ηs w)` (`Work.Drive.N2Lead.arcZ ηs w = I * sqrt (ηs - I w)`).  The *pin curve row* is the
statement that the pushed, vertically twisted image of the arc

  `w ↦ pushY Dp εp 1 (twistX ε (-1) (cE3 (arcZ ηs w)))`

is a curve whose planar projection `proj2 = (x, y) ↦ x + i y`

* never vanishes, and
* has non-zero angular rate `Im (conj (P w) * P' w)`,

on the part of the parameter set on which the arc lies in the rigid region of both twists:
`ε ≤ Re (arcZ ηs w)` (so that `twistX ε (-1)` is the half turn `(x,y,z) ↦ (x,-y,-z)`) and
`εp ≤ |Im (arcZ ηs w)|` (so that `pushY Dp εp 1` is the rigid translation `y ↦ y ∓ Dp`).

The angular rate is computed explicitly: writing `z = arcZ ηs w = re + i im` (so `z² = -ηs + i w`),
the twisted projection is `P = re + i (im + Dp)` and `P' = conj z'` with `z' = I / (2 z)`, whence

  `Im (conj P * P') = (ηs + Dp * im) / (2 * ‖z‖²) > 0`.

The only delicate point is that the hypotheses are *non-strict*: at `Re = ε` resp. `|Im| = εp` the
slab twist/push is at the boundary of its plateau, so the composite is not locally equal to the
rigid formula.  Both plateaux are nevertheless first-order flat, and the needed fact is
`deriv Real.smoothTransition 0 = 0`, proved below from `expNegInvGlue.tendsto_polynomial_inv_mul_zero`
(and its differentiability, `expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul`).
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter Polynomial

noncomputable section

/-! ## The smooth transition at its left plateau -/

/-- The `C^∞` smooth transition has vanishing derivative at `0`: it is `0` for `x ≤ 0`, and
`expNegInvGlue x = exp (-1/x)` decays faster than `x`. -/
theorem hasDerivAt_smoothTransition_zero : HasDerivAt Real.smoothTransition 0 0 := by
  have h1 : HasDerivAt expNegInvGlue 0 0 := by
    have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) 0
    simpa using h
  have hdiff : Differentiable ℝ expNegInvGlue := by
    simpa using expNegInvGlue.differentiable_polynomial_eval_inv_mul (1 : ℝ[X])
  have h2d : DifferentiableAt ℝ (fun x : ℝ => expNegInvGlue (1 - x)) 0 :=
    (hdiff (1 - 0)).comp 0 ((differentiableAt_id (x := (0:ℝ))).const_sub 1)
  have hden : HasDerivAt (fun x : ℝ => expNegInvGlue x + expNegInvGlue (1 - x))
      (deriv (fun x : ℝ => expNegInvGlue x + expNegInvGlue (1 - x)) 0) 0 :=
    ((hdiff 0).add h2d).hasDerivAt
  have hne : expNegInvGlue 0 + expNegInvGlue (1 - 0) ≠ 0 := by
    have hp : 0 < expNegInvGlue 1 := expNegInvGlue.pos_of_pos (by norm_num)
    rw [expNegInvGlue.zero, sub_zero]
    linarith
  have h := h1.div hden hne
  have hval : (0 * (expNegInvGlue 0 + expNegInvGlue (1 - 0))
      - expNegInvGlue 0 * deriv (fun x : ℝ => expNegInvGlue x + expNegInvGlue (1 - x)) 0)
      / (expNegInvGlue 0 + expNegInvGlue (1 - 0)) ^ 2 = 0 := by
    rw [expNegInvGlue.zero]; ring
  rw [hval] at h
  exact h

/-- The smooth transition has vanishing derivative everywhere on its left plateau `(-∞, 0]`. -/
theorem hasDerivAt_smoothTransition_of_nonpos {y : ℝ} (hy : y ≤ 0) :
    HasDerivAt Real.smoothTransition 0 y := by
  rcases lt_or_eq_of_le hy with h | rfl
  · refine (hasDerivAt_const y (0:ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds h] with z hz
    exact Real.smoothTransition.zero_of_nonpos hz.le
  · exact hasDerivAt_smoothTransition_zero

/-! ## The push profile -/

/-- The vertical profile of the push at `s = 1`, in the form adapted to differentiation. -/
theorem pushProf_one_eq (D ε y : ℝ) :
    Work.Drive.N2Lead.pushProf D ε 1 y
      = y + D * (2 * Real.smoothTransition ((y + ε) / (2 * ε)) - 1) := by
  simp [Work.Drive.N2Lead.pushProf]

/-- If a curve `A` stays on the rigid side `y ≤ -εp` of the push band, the push is a first-order
rigid translation: `u ↦ pushProf D εp 1 (A u)` has the same derivative as `A`.  (The hypothesis is
non-strict; at `A t = -εp` the smooth transition is used at the left end of its transition
interval, where its derivative vanishes by `hasDerivAt_smoothTransition_of_nonpos`.) -/
theorem hasDerivAt_pushProf_one_comp {D εp : ℝ} (hεp : 0 < εp) {A : ℝ → ℝ} {t A' : ℝ}
    (hA : HasDerivAt A A' t) (hy : A t ≤ -εp) :
    HasDerivAt (fun u => Work.Drive.N2Lead.pushProf D εp 1 (A u)) A' t := by
  have hfun : (fun u => Work.Drive.N2Lead.pushProf D εp 1 (A u))
      = fun u => A u + D * (2 * Real.smoothTransition ((A u + εp) / (2 * εp)) - 1) := by
    funext u
    exact pushProf_one_eq D εp (A u)
  rw [hfun]
  have hγ : HasDerivAt (fun u => (A u + εp) / (2 * εp)) (A' / (2 * εp)) t :=
    (hA.add_const εp).div_const (2 * εp)
  have hst : HasDerivAt Real.smoothTransition 0 ((A t + εp) / (2 * εp)) :=
    hasDerivAt_smoothTransition_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  have hcomp : HasDerivAt (fun u => Real.smoothTransition ((A u + εp) / (2 * εp))) 0 t := by
    have h := hst.comp t hγ
    rw [zero_mul] at h
    exact h
  have h2 : HasDerivAt (fun u => 2 * Real.smoothTransition ((A u + εp) / (2 * εp)) - 1) 0 t := by
    have h3 := hcomp.const_mul 2
    have h4 : HasDerivAt (fun u : ℝ => (1:ℝ)) 0 t := hasDerivAt_const t 1
    have h5 := h3.sub h4
    rw [mul_zero, sub_zero] at h5
    exact h5
  have h6 : HasDerivAt
      (fun u => D * (2 * Real.smoothTransition ((A u + εp) / (2 * εp)) - 1)) 0 t := by
    have h := h2.const_mul D
    rw [mul_zero] at h
    exact h
  have h7 := hA.add h6
  rw [add_zero] at h7
  exact h7

/-- On the rigid side `y ≤ -ε` the push profile is the translation `y ↦ y - D`. -/
theorem pushProf_one_eq_sub {D ε y : ℝ} (hε : 0 < ε) (hy : y ≤ -ε) :
    Work.Drive.N2Lead.pushProf D ε 1 y = y - D := by
  rw [pushProf_one_eq]
  have harg : (y + ε) / (2 * ε) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [Real.smoothTransition.zero_of_nonpos harg]
  ring

/-! ## The model arc and its twist -/

/-- The derivative of the imaginary part of the model arc. -/
theorem hasDerivAt_im_arcZ (η : ℝ) (hη : 0 < η) (w : ℝ) :
    HasDerivAt (fun u : ℝ => (Work.Drive.N2Lead.arcZ η u).im)
      (Complex.I / (2 * Work.Drive.N2Lead.arcZ η w)).im w := by
  have h := Work.Drive.N2Lead.ReStrictMono.hasDerivAt_arcZ η hη w
  have hF : HasFDerivAt (fun u : ℝ => Work.Drive.N2Lead.arcZ η u)
      (ContinuousLinearMap.toSpanSingleton ℝ (Complex.I / (2 * Work.Drive.N2Lead.arcZ η w))) w :=
    h.hasFDerivAt
  have hF2 : HasFDerivAt (fun u : ℝ => (Work.Drive.N2Lead.arcZ η u).im)
      (Complex.imCLM.comp
        (ContinuousLinearMap.toSpanSingleton ℝ (Complex.I / (2 * Work.Drive.N2Lead.arcZ η w)))) w :=
    HasFDerivAt.comp w (ContinuousLinearMap.hasFDerivAt Complex.imCLM) hF
  have h3 := hF2.hasDerivAt
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply] using h3

/-- The first coordinate of the vertically twisted model arc. -/
theorem twistX_neg_one_cE3_zero (ε : ℝ) (ζ : ℂ) :
    (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2.cE3 ζ)) 0 = ζ.re := by
  rw [Work.Drive.N2Lead.twistX_eq, Work.Drive.N2Lead.rot12_first,
    Work.Drive.N2.cE3_apply_zero]

/-- The second coordinate of the vertically twisted model arc. -/
theorem twistX_neg_one_cE3_one (ε : ℝ) (ζ : ℂ) :
    (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2.cE3 ζ)) 1
      = ζ.im * Real.cos (-(Real.pi * Real.smoothTransition ((ζ.re + ε) / (2 * ε)))) := by
  rw [Work.Drive.N2Lead.twistX_eq]
  simp only [Work.Drive.N2Lead.rot12, Work.Drive.N2.cE3_apply_one, Work.Drive.N2.cE3_apply_two,
    Work.Drive.N2Lead.twistAngleX]
  simp

/-! ## The value of the angular rate -/

/-- The algebraic core: if `z'` is the reciprocal-ish quantity `I / (2 z)` (in the weak form
`z' * (2 z) = I`) and `z = re + i im` solves `re² - im² = -ηs` with `im > 0`, then the angular rate
of the pushed projection is `(ηs + Dp * im) / (2 * ‖z‖²) ≠ 0`. -/
theorem key_algebra (z z' : ℂ) (Dp ηs : ℝ) (hz : z' * (2 * z) = Complex.I)
    (hηs : 0 < ηs) (hDp : 0 ≤ Dp) (him : 0 < z.im)
    (hsq : z.re ^ 2 - z.im ^ 2 = -ηs) :
    ((⟨z.re, z.im + Dp⟩ : ℂ) * ⟨z'.re, -z'.im⟩).im ≠ 0 := by
  have hre : z'.re * (2 * z.re) - z'.im * (2 * z.im) = 0 := by
    have h := congrArg Complex.re hz
    simpa [Complex.mul_re] using h
  have him' : z'.re * (2 * z.im) + z'.im * (2 * z.re) = 1 := by
    have h := congrArg Complex.im hz
    simpa [Complex.mul_im] using h
  have h1 : z'.re * z.re = z'.im * z.im := by linarith
  have h3 : z'.re * z.im = 1 / 2 - z'.im * z.re := by linarith
  have h4 : z'.im * z.im = z'.re * z.re := h1.symm
  have h5 : z'.im * z.re = 1 / 2 - z'.re * z.im := by linarith
  have ha : 2 * (z.re ^ 2 + z.im ^ 2) * z'.re = z.im := by
    calc 2 * (z.re ^ 2 + z.im ^ 2) * z'.re
        = 2 * (z'.re * z.re) * z.re + 2 * (z'.re * z.im) * z.im := by ring
      _ = 2 * (z'.im * z.im) * z.re + 2 * (1 / 2 - z'.im * z.re) * z.im := by rw [h1, h3]
      _ = z.im := by ring
  have hb : 2 * (z.re ^ 2 + z.im ^ 2) * z'.im = z.re := by
    calc 2 * (z.re ^ 2 + z.im ^ 2) * z'.im
        = 2 * (z'.im * z.re) * z.re + 2 * (z'.im * z.im) * z.im := by ring
      _ = 2 * (1 / 2 - z'.re * z.im) * z.re + 2 * (z'.re * z.re) * z.im := by rw [h5, h4]
      _ = z.re := by ring
  have himX : (((⟨z.re, z.im + Dp⟩ : ℂ) * ⟨z'.re, -z'.im⟩).im)
      = (z.im + Dp) * z'.re - z.re * z'.im := by
    rw [Complex.mul_im]
    ring
  have hX : ((z.im + Dp) * z'.re - z.re * z'.im) * (2 * (z.re ^ 2 + z.im ^ 2))
      = ηs + Dp * z.im := by
    linear_combination (z.im + Dp) * ha - z.re * hb - hsq
  rw [himX]
  intro hzero
  rw [hzero, zero_mul] at hX
  have h0 : 0 ≤ Dp * z.im := mul_nonneg hDp him.le
  linarith

/-! ## The pin curve row -/

theorem mobiusPinCurveRow {ηs ε εp Dp c₀ m : ℝ} (hηs : 0 < ηs) (hε : 0 < ε)
    (hεp : 0 < εp) (hDp : 0 ≤ Dp) (hc₀ : 0 < c₀) :
    ∀ w : ℝ, c₀ ≤ |w| → |w| ≤ m → ε ≤ (Work.Drive.N2Lead.arcZ ηs w).re →
      εp ≤ |(Work.Drive.N2Lead.arcZ ηs w).im| →
      Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
          (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2.cE3 (Work.Drive.N2Lead.arcZ ηs w)))) ≠ 0 ∧
      (star (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
          (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2.cE3 (Work.Drive.N2Lead.arcZ ηs w)))))
        * deriv (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
            (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2.cE3 (Work.Drive.N2Lead.arcZ ηs u))))) w).im
        ≠ 0 := by
  intro w hc0 hwm hre him
  have hwne : w ≠ 0 := by
    intro h
    rw [h, abs_zero] at hc0
    linarith
  have hz0 : Work.Drive.N2Lead.arcZ ηs w ≠ 0 :=
    Work.Drive.N2Lead.ReStrictMono.arcZ_ne_zero_of_eta_pos hηs w
  have himpos : 0 < (Work.Drive.N2Lead.arcZ ηs w).im :=
    Work.Drive.N2Lead.ReStrictMono.im_arcZ_pos hηs w
  have himge : εp ≤ (Work.Drive.N2Lead.arcZ ηs w).im := by
    rw [abs_of_pos himpos] at him
    exact him
  have hsq : (Work.Drive.N2Lead.arcZ ηs w).re ^ 2 - (Work.Drive.N2Lead.arcZ ηs w).im ^ 2 = -ηs := by
    have h := Work.Drive.N2Lead.arcZ_sq_re ηs w
    rw [pow_two, Complex.mul_re] at h
    linarith
  -- the abbreviations
  set Z : ℝ → ℂ := Work.Drive.N2Lead.arcZ ηs with hZdef
  set z' : ℂ := Complex.I / (2 * Z w) with hz'def
  set θ : ℝ → ℝ := fun u => -(Real.pi * Real.smoothTransition (((Z u).re + ε) / (2 * ε)))
    with hθdef
  set A : ℝ → ℝ := fun u => (Z u).im * Real.cos (θ u) with hAdef
  set P : ℝ → ℂ := fun u => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
    (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2.cE3 (Z u)))) with hPdef
  change P w ≠ 0 ∧ (star (P w) * deriv P w).im ≠ 0
  -- derivatives of the components of the arc
  have hcc : HasDerivAt (fun u : ℝ => (Z u).re) z'.re w := by
    rw [hZdef, hz'def]
    exact Work.Drive.N2Lead.ReStrictMono.hasDerivAt_re_arcZ ηs hηs w
  have hdd : HasDerivAt (fun u : ℝ => (Z u).im) z'.im w := by
    rw [hZdef, hz'def]
    exact hasDerivAt_im_arcZ ηs hηs w
  -- the twist angle at `w`
  have hsxw : 1 ≤ ((Z w).re + ε) / (2 * ε) := by
    rw [le_div_iff₀ (by linarith)]
    linarith [hre]
  have hθw : θ w = -Real.pi := by
    have h : θ w = -(Real.pi * Real.smoothTransition (((Z w).re + ε) / (2 * ε))) := by
      simp [hθdef]
    rw [h, Real.smoothTransition.one_of_one_le hsxw]
    ring
  have hcosθw : Real.cos (θ w) = -1 := by rw [hθw, Real.cos_neg, Real.cos_pi]
  have hsinθw : Real.sin (θ w) = 0 := by rw [hθw, Real.sin_neg, Real.sin_pi, neg_zero]
  -- the derivative of the twist angle
  set K : ℝ := -(Real.pi * (deriv Real.smoothTransition (((Z w).re + ε) / (2 * ε))
    * (z'.re / (2 * ε)))) with hKdef
  have hθK : HasDerivAt θ K w := by
    rw [hθdef, hKdef]
    have hsx : HasDerivAt (fun u : ℝ => ((Z u).re + ε) / (2 * ε)) (z'.re / (2 * ε)) w :=
      (hcc.add_const ε).div_const (2 * ε)
    have hdiff : DifferentiableAt ℝ Real.smoothTransition (((Z w).re + ε) / (2 * ε)) :=
      ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp)).differentiableAt
    have hd : HasDerivAt Real.smoothTransition
        (deriv Real.smoothTransition (((Z w).re + ε) / (2 * ε))) (((Z w).re + ε) / (2 * ε)) :=
      hdiff.hasDerivAt
    have hcomp : HasDerivAt
        (Real.smoothTransition ∘ fun u : ℝ => ((Z u).re + ε) / (2 * ε))
        (deriv Real.smoothTransition (((Z w).re + ε) / (2 * ε)) * (z'.re / (2 * ε))) w :=
      hd.comp w hsx
    exact (hcomp.const_mul Real.pi).neg
  -- the curve `A`: the second coordinate of the twisted arc
  have hA : HasDerivAt A (-z'.im) w := by
    have hcos : HasDerivAt (fun u : ℝ => Real.cos (θ u)) (-Real.sin (θ w) * K) w :=
      (Real.hasDerivAt_cos (θ w)).comp w hθK
    have hprod : HasDerivAt (fun u : ℝ => (Z u).im * Real.cos (θ u))
        (z'.im * Real.cos (θ w) + (Z w).im * (-(Real.sin (θ w)) * K)) w :=
      hdd.mul hcos
    rw [hAdef]
    convert hprod using 1
    rw [hcosθw, hsinθw]
    ring
  have hAwval : A w = -(Z w).im := by
    simp only [hAdef]
    rw [hcosθw]
    ring
  have hAwle : A w ≤ -εp := by
    rw [hAwval]
    linarith
  -- the second coordinate of the pushed, twisted arc
  have hQ : HasDerivAt (fun u => Work.Drive.N2Lead.pushProf Dp εp 1 (A u)) (-z'.im) w :=
    hasDerivAt_pushProf_one_comp hεp hA hAwle
  -- the pushed, twisted projection, in coordinates
  have hPeq : ∀ u : ℝ,
      P u = (⟨(Z u).re, Work.Drive.N2Lead.pushProf Dp εp 1 (A u)⟩ : ℂ) := by
    intro u
    simp only [hPdef, hAdef, hθdef, Work.Drive.N2Lead.proj2,
      Work.Drive.N2Lead.pushY_apply_zero, Work.Drive.N2Lead.pushY_apply_one]
    rw [twistX_neg_one_cE3_zero, twistX_neg_one_cE3_one]
  have hPw : P w = (⟨(Z w).re, -(Z w).im - Dp⟩ : ℂ) := by
    rw [hPeq w, hAwval]
    congr 1
    exact pushProf_one_eq_sub hεp (by linarith)
  -- the derivative of the projection
  have hPc : HasDerivAt P (⟨z'.re, -z'.im⟩ : ℂ) w := by
    have h1 : HasDerivAt (fun u : ℝ => (((Z u).re : ℝ) : ℂ)) (z'.re : ℂ) w :=
      HasDerivAt.ofReal_comp hcc
    have h2 : HasDerivAt
        (fun u : ℝ => (((Work.Drive.N2Lead.pushProf Dp εp 1 (A u) : ℝ)) : ℂ) * Complex.I)
        ((((-z'.im : ℝ)) : ℂ) * Complex.I) w :=
      (HasDerivAt.ofReal_comp hQ).mul_const Complex.I
    have h3 : HasDerivAt (fun u : ℝ => (((Z u).re : ℝ) : ℂ)
        + (((Work.Drive.N2Lead.pushProf Dp εp 1 (A u) : ℝ)) : ℂ) * Complex.I)
        ((z'.re : ℂ) + ((((-z'.im : ℝ)) : ℂ) * Complex.I)) w := h1.add h2
    have hv : (z'.re : ℂ) + ((((-z'.im : ℝ)) : ℂ) * Complex.I) = (⟨z'.re, -z'.im⟩ : ℂ) := by
      apply Complex.ext <;> simp
    rw [hv] at h3
    have hfun : (fun u : ℝ => (((Z u).re : ℝ) : ℂ)
        + (((Work.Drive.N2Lead.pushProf Dp εp 1 (A u) : ℝ)) : ℂ) * Complex.I) = P := by
      funext u
      rw [hPeq u]
      apply Complex.ext <;> simp
    rw [hfun] at h3
    exact h3
  have hPderiv : deriv P w = (⟨z'.re, -z'.im⟩ : ℂ) := hPc.deriv
  -- the reciprocal relation for `z'`
  have h2Zw : (2 : ℂ) * Z w ≠ 0 := mul_ne_zero two_ne_zero hz0
  have hz'mul : z' * (2 * Z w) = Complex.I := by
    rw [hz'def, div_mul_cancel₀ _ h2Zw]
  constructor
  · rw [hPw]
    intro hzero
    have him2 : (-(Z w).im - Dp) = 0 := by
      have h := congrArg Complex.im hzero
      simpa using h
    have h0 : 0 ≤ Dp := hDp
    linarith
  · rw [hPw, hPderiv]
    have hstar : star (⟨(Z w).re, -(Z w).im - Dp⟩ : ℂ)
        = (⟨(Z w).re, (Z w).im + Dp⟩ : ℂ) := by
      apply Complex.ext <;> simp <;> ring
    rw [hstar]
    exact key_algebra (Z w) z' Dp ηs hz'mul hηs hDp himpos hsq

end

end Work.Drive.N2C
