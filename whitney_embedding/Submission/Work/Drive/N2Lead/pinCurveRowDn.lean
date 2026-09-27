import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperCoreKit
import Submission.Work.Drive.N2C.mobiusPinCurveRow
import Submission.Work.Drive.N2Lead.arcZ_re_strictMono

/-!
# The pin curve row of the *lower* model arc

`Work.Drive.N2Lead.dnCurve ηs Dp εp ε` is the planar picture of the pushed, twisted **lower** model
arc point `star (arcZ ηs u)` (`mobiusUpperCoreKit`).  This file proves `pinCurveRowDn`: on the
parameter set on which the arc lies in the rigid region of the twists
(`ε ≤ |Re (arcZ ηs w)|`, `εp ≤ Im (arcZ ηs w)`), the pushed, twisted projection `P` of the lower arc
has non-zero angular rate, `Im (conj (P w) * P' w) ≠ 0`.

The computation is the mirror of `Work.Drive.N2C.mobiusPinCurveRow` (the upper arc).  Writing
`Z = arcZ ηs w = re + i·im` with `im > 0` and `z' = I / (2Z)` (the derivative of `Z`, so
`z'.re = im / (2‖Z‖²)`, `z'.im = re / (2‖Z‖²)`), the twisted point is
`cE3 (star Z) = (re, -im, 0)`; the vertical twist is the half turn `(x,y,z) ↦ (x,-y,-z)` when
`re ≥ ε` and the *identity* when `re ≤ -ε` (both cases are allowed by `ε ≤ |re|`), and the push is
rigid on both plateaus (`y ↦ y + Dp` for `y ≥ εp`, `y ↦ y - Dp` for `y ≤ -εp`).  Hence

* `re ≥ ε`: the picture is `P = re + i (im + Dp)`, `P' = z'`, and
  `Im (conj P · P') = -(ηs + Dp·im) / (2‖Z‖²) ≠ 0`;
* `re ≤ -ε`: the picture is `P = re + i (-im - Dp)`, `P' = conj z'`, and
  `Im (conj P · P') = (ηs + Dp·im) / (2‖Z‖²) ≠ 0`.

The only delicate point (shared with the upper arc) is that the hypotheses on the rigid regions are
*non-strict*, so at the boundary of a plateau the twists are not locally rigid; both plateaus are
first order flat there, which is what the two plateau derivative lemmas below provide.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-! ## The smooth transition on its right plateau -/

/-- The `C^∞` smooth transition is symmetric about `1/2`:
`τ (1 - x) = 1 - τ x`. -/
theorem pinDn_smoothTransition_one_sub (x : ℝ) :
    Real.smoothTransition (1 - x) = 1 - Real.smoothTransition x := by
  have h1 : (1 : ℝ) - (1 - x) = x := by ring
  have hne : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  rw [Real.smoothTransition, Real.smoothTransition, h1, eq_sub_iff_add_eq']
  simp only [add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x)]
  rw [← add_div, div_self hne]

/-- The smooth transition has vanishing derivative everywhere on its right plateau `[1, ∞)`
(mirror of `Work.Drive.N2C.hasDerivAt_smoothTransition_of_nonpos`). -/
theorem pinDn_hasDerivAt_smoothTransition_one_le {y : ℝ} (hy : 1 ≤ y) :
    HasDerivAt Real.smoothTransition 0 y := by
  rcases lt_or_eq_of_le hy with h | rfl
  · refine (hasDerivAt_const y (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds h] with z hz
    exact Real.smoothTransition.one_of_one_le hz.le
  · have hfun : Real.smoothTransition = fun x : ℝ => 1 - Real.smoothTransition (1 - x) := by
      funext x
      rw [pinDn_smoothTransition_one_sub]
      ring
    rw [hfun]
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).const_sub 1
    have h2 : HasDerivAt Real.smoothTransition 0 (1 - 1) := by
      simpa using Work.Drive.N2C.hasDerivAt_smoothTransition_zero
    have h3 : HasDerivAt (Real.smoothTransition ∘ fun x : ℝ => 1 - x) 0 1 := by
      simpa using h2.comp 1 h1
    have h4 : HasDerivAt (fun x : ℝ => Real.smoothTransition (1 - x)) 0 1 := by
      simpa [Function.comp_def] using h3
    have h5 := h4.const_sub 1
    simpa using h5

/-! ## Rigidity of the push on its right plateau -/

/-- On the right plateau `y ≥ ε` the push profile at `s = 1` is the translation `y ↦ y + D`. -/
theorem pinDn_pushProf_one_eq_add {D ε y : ℝ} (hε : 0 < ε) (hy : ε ≤ y) :
    pushProf D ε 1 y = y + D := by
  rw [Work.Drive.N2C.pushProf_one_eq]
  have harg : 1 ≤ (y + ε) / (2 * ε) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  rw [Real.smoothTransition.one_of_one_le harg]
  ring

/-- If a curve `A` stays on the rigid side `εp ≤ A t` of the push band, the push is a first-order
rigid translation: `u ↦ pushProf D εp 1 (A u)` has the same derivative as `A`.  (The hypothesis is
non-strict; at `A t = εp` the smooth transition is used at the right end of its transition interval,
where its derivative vanishes.) -/
theorem pinDn_hasDerivAt_pushProf_one_comp_right {D εp : ℝ} (hεp : 0 < εp) {A : ℝ → ℝ}
    {t A' : ℝ} (hA : HasDerivAt A A' t) (hy : εp ≤ A t) :
    HasDerivAt (fun u => pushProf D εp 1 (A u)) A' t := by
  have hfun : (fun u => pushProf D εp 1 (A u))
      = fun u => A u + D * (2 * Real.smoothTransition ((A u + εp) / (2 * εp)) - 1) := by
    funext u
    exact Work.Drive.N2C.pushProf_one_eq D εp (A u)
  rw [hfun]
  have hγ : HasDerivAt (fun u => (A u + εp) / (2 * εp)) (A' / (2 * εp)) t :=
    (hA.add_const εp).div_const (2 * εp)
  have harg : 1 ≤ (A t + εp) / (2 * εp) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hst : HasDerivAt Real.smoothTransition 0 ((A t + εp) / (2 * εp)) :=
    pinDn_hasDerivAt_smoothTransition_one_le harg
  have hcomp : HasDerivAt (fun u => Real.smoothTransition ((A u + εp) / (2 * εp))) 0 t := by
    have h := hst.comp t hγ
    rw [zero_mul] at h
    exact h
  have h2 : HasDerivAt (fun u => 2 * Real.smoothTransition ((A u + εp) / (2 * εp)) - 1) 0 t := by
    have h3 := hcomp.const_mul 2
    have h4 : HasDerivAt (fun u : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
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

/-- The derivative of a negated (real valued) curve, in lambda form. -/
theorem pinDn_hasDerivAt_neg {f : ℝ → ℝ} {t c : ℝ} (h : HasDerivAt f c t) :
    HasDerivAt (fun u => -(f u)) (-c) t := by
  have h2 : HasDerivAt (fun u : ℝ => (0 : ℝ) - f u) (-c) t := h.const_sub 0
  simpa using h2

/-! ## The algebra of the lower-arc angular rate -/

/-- The algebraic core in the shape of the lower arc when the twist is the half turn:
with `z = re + i·im` the lower arc's picture is `re + i (im + Dp)` and its derivative is `z'`, so the
angular rate is the *negative* of the upper arc's. -/
theorem pinDn_key_algebra (z z' : ℂ) (Dp ηs : ℝ) (hz : z' * (2 * z) = Complex.I)
    (hηs : 0 < ηs) (hDp : 0 ≤ Dp) (him : 0 < z.im) (hsq : z.re ^ 2 - z.im ^ 2 = -ηs) :
    ((⟨z.re, -(z.im + Dp)⟩ : ℂ) * ⟨z'.re, z'.im⟩).im ≠ 0 := by
  have h := Work.Drive.N2C.key_algebra z z' Dp ηs hz hηs hDp him hsq
  have hre : ((⟨z.re, -(z.im + Dp)⟩ : ℂ) * ⟨z'.re, z'.im⟩).im
      = -(((⟨z.re, z.im + Dp⟩ : ℂ) * ⟨z'.re, -z'.im⟩)).im := by
    simp [Complex.mul_im]
    ring
  rw [hre]
  intro hc
  exact h (by linarith)

/-! ## The pin curve row of the lower arc -/

theorem pinCurveRowDn {ηs ε εp Dp : ℝ} (hηs : 0 < ηs) (hε : 0 < ε) (hεp : 0 < εp)
    (hDp : 0 ≤ Dp) :
    ∀ w : ℝ, ε ≤ |(Work.Drive.N2Lead.arcZ ηs w).re| → εp ≤ (Work.Drive.N2Lead.arcZ ηs w).im →
      (star (Work.Drive.N2Lead.dnCurve ηs Dp εp ε w)
        * deriv (Work.Drive.N2Lead.dnCurve ηs Dp εp ε) w).im ≠ 0 := by
  intro w hre him
  have hz0 : Work.Drive.N2Lead.arcZ ηs w ≠ 0 :=
    Work.Drive.N2Lead.ReStrictMono.arcZ_ne_zero_of_eta_pos hηs w
  have himpos : 0 < (Work.Drive.N2Lead.arcZ ηs w).im :=
    Work.Drive.N2Lead.ReStrictMono.im_arcZ_pos hηs w
  have hsq : (Work.Drive.N2Lead.arcZ ηs w).re ^ 2 - (Work.Drive.N2Lead.arcZ ηs w).im ^ 2 = -ηs := by
    have h := Work.Drive.N2Lead.arcZ_sq_re ηs w
    rw [pow_two, Complex.mul_re] at h
    linarith
  set Z : ℝ → ℂ := Work.Drive.N2Lead.arcZ ηs with hZdef
  set z' : ℂ := Complex.I / (2 * Z w) with hz'def
  set θ : ℝ → ℝ := fun u => -(Real.pi * Real.smoothTransition (((Z u).re + ε) / (2 * ε)))
    with hθdef
  set A : ℝ → ℝ := fun u => -((Z u).im * Real.cos (θ u)) with hAdef
  set P : ℝ → ℂ := Work.Drive.N2Lead.dnCurve ηs Dp εp ε with hPdef
  change (star (P w) * deriv P w).im ≠ 0
  have hcc : HasDerivAt (fun u : ℝ => (Z u).re) z'.re w := by
    rw [hZdef, hz'def]
    exact Work.Drive.N2Lead.ReStrictMono.hasDerivAt_re_arcZ ηs hηs w
  have hdd : HasDerivAt (fun u : ℝ => (Z u).im) z'.im w := by
    rw [hZdef, hz'def]
    exact Work.Drive.N2C.hasDerivAt_im_arcZ ηs hηs w
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
  -- the derivative of the height `A` of the twisted arc
  have hcosθ : HasDerivAt (fun u : ℝ => Real.cos (θ u)) (-Real.sin (θ w) * K) w :=
    (Real.hasDerivAt_cos (θ w)).comp w hθK
  have hB : HasDerivAt (fun u : ℝ => (Z u).im * Real.cos (θ u))
      (z'.im * Real.cos (θ w) + (Z w).im * (-(Real.sin (θ w)) * K)) w := hdd.mul hcosθ
  -- the curve in coordinates
  have hPeq : ∀ u : ℝ, P u = (⟨(Z u).re, pushProf Dp εp 1 (A u)⟩ : ℂ) := by
    intro u
    simp only [hPdef, hAdef, hθdef, Work.Drive.N2Lead.dnCurve, Work.Drive.N2Lead.proj2,
      Work.Drive.N2Lead.pushY_apply_zero, Work.Drive.N2Lead.pushY_apply_one, hZdef]
    rw [Work.Drive.N2C.twistX_neg_one_cE3_zero, Work.Drive.N2C.twistX_neg_one_cE3_one]
    simp
  have h2Zw : (2 : ℂ) * Z w ≠ 0 := mul_ne_zero two_ne_zero (by rw [hZdef]; exact hz0)
  have hz'mul : z' * (2 * Z w) = Complex.I := by
    rw [hz'def, div_mul_cancel₀ _ h2Zw]
  rcases le_abs.1 hre with hrecase | hrecase
  · -- Case 1: `ε ≤ Re Z`: the twist is the half turn, the push is at its right plateau.
    have hθw : θ w = -Real.pi := by
      have hsxw : 1 ≤ ((Z w).re + ε) / (2 * ε) := by
        rw [le_div_iff₀ (by linarith)]
        linarith
      have h : θ w = -(Real.pi * Real.smoothTransition (((Z w).re + ε) / (2 * ε))) := by
        simp [hθdef]
      rw [h, Real.smoothTransition.one_of_one_le hsxw]
      ring
    have hcosθw : Real.cos (θ w) = -1 := by rw [hθw, Real.cos_neg, Real.cos_pi]
    have hsinθw : Real.sin (θ w) = 0 := by rw [hθw, Real.sin_neg, Real.sin_pi, neg_zero]
    have hB' : HasDerivAt (fun u : ℝ => (Z u).im * Real.cos (θ u)) (-z'.im) w := by
      convert hB using 1
      rw [hcosθw, hsinθw]
      ring
    have hA : HasDerivAt A z'.im w := by
      rw [hAdef]
      have h := pinDn_hasDerivAt_neg hB'
      simpa using h
    have hAwval : A w = (Z w).im := by
      simp only [hAdef]
      rw [hcosθw]
      ring
    have hAwge : εp ≤ A w := by rw [hAwval]; exact him
    have hQ : HasDerivAt (fun u => pushProf Dp εp 1 (A u)) z'.im w :=
      pinDn_hasDerivAt_pushProf_one_comp_right hεp hA hAwge
    have hPc : HasDerivAt P (⟨z'.re, z'.im⟩ : ℂ) w := by
      have h1 : HasDerivAt (fun u : ℝ => (((Z u).re : ℝ) : ℂ)) (z'.re : ℂ) w :=
        HasDerivAt.ofReal_comp hcc
      have h2 : HasDerivAt
          (fun u : ℝ => (((pushProf Dp εp 1 (A u) : ℝ)) : ℂ) * Complex.I)
          (((z'.im : ℝ) : ℂ) * Complex.I) w :=
        (HasDerivAt.ofReal_comp hQ).mul_const Complex.I
      have h3 : HasDerivAt (fun u : ℝ => (((Z u).re : ℝ) : ℂ)
          + (((pushProf Dp εp 1 (A u) : ℝ)) : ℂ) * Complex.I)
          ((z'.re : ℂ) + (((z'.im : ℝ) : ℂ) * Complex.I)) w := h1.add h2
      have hv : (z'.re : ℂ) + (((z'.im : ℝ) : ℂ) * Complex.I) = (⟨z'.re, z'.im⟩ : ℂ) := by
        apply Complex.ext <;> simp
      rw [hv] at h3
      have hfun : (fun u : ℝ => (((Z u).re : ℝ) : ℂ)
          + (((pushProf Dp εp 1 (A u) : ℝ)) : ℂ) * Complex.I) = P := by
        funext u
        rw [hPeq u]
        apply Complex.ext <;> simp
      rw [hfun] at h3
      exact h3
    have hPderiv : deriv P w = (⟨z'.re, z'.im⟩ : ℂ) := hPc.deriv
    have hPw : P w = (⟨(Z w).re, (Z w).im + Dp⟩ : ℂ) := by
      have h1 : pushProf Dp εp 1 (A w) = A w + Dp := pinDn_pushProf_one_eq_add hεp hAwge
      rw [hPeq w, h1, hAwval]
    rw [hPw, hPderiv]
    have hstar : star (⟨(Z w).re, (Z w).im + Dp⟩ : ℂ)
        = (⟨(Z w).re, -((Z w).im + Dp)⟩ : ℂ) := by
      apply Complex.ext <;> simp
    rw [hstar]
    exact pinDn_key_algebra (Z w) z' Dp ηs hz'mul hηs hDp himpos hsq
  · -- Case 2: `ε ≤ -Re Z`, i.e. `Re Z ≤ -ε`: the twist is the identity and the push is at its
    -- left plateau.
    have hθw : θ w = 0 := by
      have hszw : ((Z w).re + ε) / (2 * ε) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have h : θ w = -(Real.pi * Real.smoothTransition (((Z w).re + ε) / (2 * ε))) := by
        simp [hθdef]
      rw [h, Real.smoothTransition.zero_of_nonpos hszw]
      ring
    have hcosθw : Real.cos (θ w) = 1 := by rw [hθw, Real.cos_zero]
    have hsinθw : Real.sin (θ w) = 0 := by rw [hθw, Real.sin_zero]
    have hB' : HasDerivAt (fun u : ℝ => (Z u).im * Real.cos (θ u)) z'.im w := by
      convert hB using 1
      rw [hcosθw, hsinθw]
      ring
    have hA : HasDerivAt A (-z'.im) w := by
      rw [hAdef]
      exact pinDn_hasDerivAt_neg hB'
    have hAwval : A w = -(Z w).im := by
      simp only [hAdef]
      rw [hcosθw]
      ring
    have hAwle : A w ≤ -εp := by rw [hAwval]; linarith
    have hQ : HasDerivAt (fun u => pushProf Dp εp 1 (A u)) (-z'.im) w :=
      Work.Drive.N2C.hasDerivAt_pushProf_one_comp hεp hA hAwle
    have hPc : HasDerivAt P (⟨z'.re, -z'.im⟩ : ℂ) w := by
      have h1 : HasDerivAt (fun u : ℝ => (((Z u).re : ℝ) : ℂ)) (z'.re : ℂ) w :=
        HasDerivAt.ofReal_comp hcc
      have h2 : HasDerivAt
          (fun u : ℝ => (((pushProf Dp εp 1 (A u) : ℝ)) : ℂ) * Complex.I)
          ((((-z'.im : ℝ)) : ℂ) * Complex.I) w :=
        (HasDerivAt.ofReal_comp hQ).mul_const Complex.I
      have h3 : HasDerivAt (fun u : ℝ => (((Z u).re : ℝ) : ℂ)
          + (((pushProf Dp εp 1 (A u) : ℝ)) : ℂ) * Complex.I)
          ((z'.re : ℂ) + ((((-z'.im) : ℝ) : ℂ) * Complex.I)) w := h1.add h2
      have hv : (z'.re : ℂ) + ((((-z'.im) : ℝ) : ℂ) * Complex.I) = (⟨z'.re, -z'.im⟩ : ℂ) := by
        apply Complex.ext <;> simp
      rw [hv] at h3
      have hfun : (fun u : ℝ => (((Z u).re : ℝ) : ℂ)
          + (((pushProf Dp εp 1 (A u) : ℝ)) : ℂ) * Complex.I) = P := by
        funext u
        rw [hPeq u]
        apply Complex.ext <;> simp
      rw [hfun] at h3
      exact h3
    have hPderiv : deriv P w = (⟨z'.re, -z'.im⟩ : ℂ) := hPc.deriv
    have hPw : P w = (⟨(Z w).re, -((Z w).im) - Dp⟩ : ℂ) := by
      have h1 : pushProf Dp εp 1 (A w) = A w - Dp :=
        Work.Drive.N2C.pushProf_one_eq_sub hεp hAwle
      rw [hPeq w, h1, hAwval]
    rw [hPw, hPderiv]
    have hstar : star (⟨(Z w).re, -((Z w).im) - Dp⟩ : ℂ)
        = (⟨(Z w).re, (Z w).im + Dp⟩ : ℂ) := by
      apply Complex.ext
      · simp
      · simp
        ring
    rw [hstar]
    exact Work.Drive.N2C.key_algebra (Z w) z' Dp ηs hz'mul hηs hDp himpos hsq

end

end Work.Drive.N2Lead
