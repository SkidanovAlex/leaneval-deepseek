import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperCoreKit
import Submission.Work.Drive.N2C.mobiusPinCurveRow
import Submission.Work.Drive.N2Lead.arcZ_re_strictMono

/-!
# The pin curve row of the Möbius saddle, outside the twist band

`Work.Drive.N2Lead.pinCurveRowUp` is the row of the Möbius saddle packet that says: on the part of the
pin parameter set where the model arc `arcZ ηs w` is *outside* the vertical twist band
(`ε ≤ |Re (arcZ ηs w)|`) and *outside* the push band in direction `y`
(`εp ≤ Im (arcZ ηs w)`), the planar projection

  `P = proj2 ∘ pushY Dp εp 1 ∘ twistX ε (-1) ∘ cE3 ∘ arcZ ηs`  (i.e. `upCurve ηs Dp εp ε`)

has non-zero angular rate `Im (conj P · P')`.

The proof splits on the sign of `Re (arcZ ηs w)`, which is also the sign of `w` (`2 Re Im = w` with
`Im > 0`):

* on the right, `ε ≤ Re`, the composite `proj2 ∘ pushY ∘ twistX ∘ cE3` is the *rigid* formula
  `w ↦ Re - i (Im + Dp)` (the twist is the half turn `(x,y,z) ↦ (x,-y,-z)` and the push is the
  translation `y ↦ y - Dp`), and the rate is `(ηs + Dp · Im) / (2 ‖arcZ‖²) > 0`.  This is exactly
  the proved row `Work.Drive.N2C.mobiusPinCurveRow`, which we reuse (the extra bounds `c₀ ≤ |w| ≤ m`
  it asks for are satisfied with `c₀ = m = |w|` because `Re > 0` forces `w > 0`);
* on the left, `Re ≤ -ε`, the twist is the *identity* and the push is the translation `y ↦ y + Dp`,
  so the projection is the rigid formula `w ↦ Re + i (Im + Dp)` and the rate is
  `-(ηs + Dp · Im) / (2 ‖arcZ‖²) < 0`.  This is `upCurve_rate_left` below.

Both sign cases are at the *boundary* of the plateau of the two twists (`|Re| = ε`, `Im = εp`), so
the two transitions `smoothTransition` are used at first-order flat points: at the left end of the
twist argument (`≤ 0`) the angle simply vanishes (so only the *value* of the transition matters, and
the derivative of the angle is multiplied by `sin 0 = 0`), and at the right end of the push argument
(`≥ 1`) we need `deriv smoothTransition 1 = 0`, proved here as
`hasDerivAt_smoothTransition_one`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-! ## The scalar algebra of the two signs

`Work.Drive.N2C.key_algebra` is the right-hand case; the left-hand case is the same computation with
the sign of the `Dp`-shift reversed, and is `key_algebra_left` below. -/

/-- **The algebra of the left-hand case**: with `z' = I / (2 z)` (`z' * (2 z) = I`), `z = re + i im`
solving `im > 0`, `re² - im² = -ηs` (`ηs > 0`) and `Dp ≥ 0`, the angular rate of the rigid left
formula `re + i (im + Dp)` is `-(ηs + Dp · im) / (2 ‖z‖²) < 0`, in particular non-zero. -/
theorem key_algebra_left (z z' : ℂ) (Dp ηs : ℝ) (hz : z' * (2 * z) = Complex.I)
    (hηs : 0 < ηs) (hDp : 0 ≤ Dp) (him : 0 < z.im)
    (hsq : z.re ^ 2 - z.im ^ 2 = -ηs) :
    ((⟨z.re, -(z.im + Dp)⟩ : ℂ) * z').im ≠ 0 := by
  have hre : z'.re * (2 * z.re) - z'.im * (2 * z.im) = 0 := by
    have h := congrArg Complex.re hz
    simpa [Complex.mul_re] using h
  have him' : z'.re * (2 * z.im) + z'.im * (2 * z.re) = 1 := by
    have h := congrArg Complex.im hz
    simpa [Complex.mul_im] using h
  have h1 : z'.re * z.re = z'.im * z.im := by linarith
  have h3 : z'.re * z.im = 1 / 2 - z'.im * z.re := by linarith
  have h5 : z'.im * z.re = 1 / 2 - z'.re * z.im := by linarith
  have h4 : z'.im * z.im = z'.re * z.re := h1.symm
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
  have himX : (((⟨z.re, -(z.im + Dp)⟩ : ℂ) * z').im)
      = z.re * z'.im - (z.im + Dp) * z'.re := by
    rw [Complex.mul_im]
    ring
  have hX : (z.re * z'.im - (z.im + Dp) * z'.re) * (2 * (z.re ^ 2 + z.im ^ 2))
      = -(ηs + Dp * z.im) := by
    linear_combination z.re * hb - (z.im + Dp) * ha + hsq
  rw [himX]
  intro hzero
  rw [hzero, zero_mul] at hX
  have h0 : 0 ≤ Dp * z.im := mul_nonneg hDp him.le
  linarith

/-! ## The flatness of `smoothTransition` at its right end -/

private lemma smoothTransition_add_one_sub (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  have hx : (1:ℝ) - (1 - x) = x := by ring
  simp only [Real.smoothTransition, hx]
  rw [add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x), ← add_div,
    div_self (Real.smoothTransition.pos_denom x).ne']

private lemma differentiableAt_smoothTransition (x : ℝ) :
    DifferentiableAt ℝ Real.smoothTransition x :=
  ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp)).differentiableAt

/-- The `C^∞` smooth transition has vanishing derivative at `1` (its right plateau point), by the
symmetry `smoothTransition x + smoothTransition (1 - x) = 1` together with the flatness at `0`
(`Work.Drive.N2C.hasDerivAt_smoothTransition_zero`). -/
theorem hasDerivAt_smoothTransition_one : HasDerivAt Real.smoothTransition 0 1 := by
  have hlin_diff : DifferentiableAt ℝ (fun x : ℝ => (1:ℝ) - x) 1 := by fun_prop
  have hA : deriv (fun x : ℝ => Real.smoothTransition (1 - x)) 1 = 0 := by
    have h := deriv_comp (x := (1:ℝ)) (h := fun x : ℝ => 1 - x) (h₂ := Real.smoothTransition)
      (differentiableAt_smoothTransition ((fun x : ℝ => 1 - x) 1)) hlin_diff
    rw [show deriv (fun x : ℝ => Real.smoothTransition (1 - x)) 1
        = deriv (Real.smoothTransition ∘ fun x : ℝ => 1 - x) 1 from rfl, h]
    simp [Work.Drive.N2C.hasDerivAt_smoothTransition_zero.deriv]
  have hG : (fun x : ℝ => Real.smoothTransition (1 - x))
      = fun x => 1 - Real.smoothTransition x := by
    funext x; linarith [smoothTransition_add_one_sub x]
  have hB : deriv (fun x : ℝ => Real.smoothTransition (1 - x)) 1
      = - deriv Real.smoothTransition 1 := by
    rw [hG, deriv_const_sub]
  have hd : deriv Real.smoothTransition 1 = 0 := by linarith [hA, hB]
  have hres := (differentiableAt_smoothTransition 1).hasDerivAt
  rwa [hd] at hres

/-- The smooth transition has vanishing derivative everywhere on its right plateau `[1, ∞)`. -/
theorem hasDerivAt_smoothTransition_of_one_le {y : ℝ} (hy : 1 ≤ y) :
    HasDerivAt Real.smoothTransition 0 y := by
  rcases lt_or_eq_of_le hy with h | rfl
  · refine (hasDerivAt_const y (1:ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds h] with z hz
    exact Real.smoothTransition.one_of_one_le hz.le
  · exact hasDerivAt_smoothTransition_one

/-! ## The push on its rigid upper side -/

/-- If a curve `A` stays on the rigid side `εp ≤ A` of the push band, the push is a first-order
rigid translation: `u ↦ pushProf D εp 1 (A u)` has the same derivative as `A`.  (The hypothesis is
non-strict; at `A t = εp` the smooth transition is used at the right end of its transition interval,
where its derivative vanishes by `hasDerivAt_smoothTransition_of_one_le`.)  This is the mirror of
`Work.Drive.N2C.hasDerivAt_pushProf_one_comp`. -/
theorem hasDerivAt_pushProf_one_comp_of_le {D εp : ℝ} (hεp : 0 < εp) {A : ℝ → ℝ} {t A' : ℝ}
    (hA : HasDerivAt A A' t) (hy : εp ≤ A t) :
    HasDerivAt (fun u => pushProf D εp 1 (A u)) A' t := by
  have hfun : (fun u => pushProf D εp 1 (A u))
      = fun u => A u + D * (2 * Real.smoothTransition ((A u + εp) / (2 * εp)) - 1) := by
    funext u
    exact Work.Drive.N2C.pushProf_one_eq D εp (A u)
  rw [hfun]
  have hγ : HasDerivAt (fun u => (A u + εp) / (2 * εp)) (A' / (2 * εp)) t :=
    (hA.add_const εp).div_const (2 * εp)
  have hst : HasDerivAt Real.smoothTransition 0 ((A t + εp) / (2 * εp)) :=
    hasDerivAt_smoothTransition_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)
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

/-! ## The angular rate on the left of the twist band -/

/-- **The angular rate of the pin curve on the left of the twist band.**  If `Re (arcZ ηs w) ≤ -ε`
and `εp ≤ Im (arcZ ηs w)` then the projection `proj2 (pushY Dp εp 1 (twistX ε (-1) (cE3 (arcZ ηs w))))`
is the rigid formula `Re + i (Im + Dp)` and its angular rate is
`-(ηs + Dp · Im) / (2 ‖arcZ ηs w‖²) ≠ 0`. -/
theorem upCurve_rate_left {ηs ε εp Dp : ℝ} (hηs : 0 < ηs) (hε : 0 < ε) (hεp : 0 < εp)
    (hDp : 0 ≤ Dp) {w : ℝ} (hre : (arcZ ηs w).re ≤ -ε) (him : εp ≤ (arcZ ηs w).im) :
    (star (upCurve ηs Dp εp ε w) * deriv (upCurve ηs Dp εp ε) w).im ≠ 0 := by
  have himpos : 0 < (arcZ ηs w).im := ReStrictMono.im_arcZ_pos hηs w
  have hsq : (arcZ ηs w).re ^ 2 - (arcZ ηs w).im ^ 2 = -ηs := by
    have h := arcZ_sq_re ηs w
    rw [pow_two, Complex.mul_re] at h
    linarith
  set Z : ℝ → ℂ := arcZ ηs with hZdef
  set z' : ℂ := Complex.I / (2 * Z w) with hz'def
  set θ : ℝ → ℝ := fun u => -(Real.pi * Real.smoothTransition (((Z u).re + ε) / (2 * ε)))
    with hθdef
  set A : ℝ → ℝ := fun u => (Z u).im * Real.cos (θ u) with hAdef
  set P : ℝ → ℂ := fun u => proj2 (pushY Dp εp 1 (twistX ε (-1) (Work.Drive.N2.cE3 (Z u))))
    with hPdef
  change (star (P w) * deriv P w).im ≠ 0
  have hcc : HasDerivAt (fun u : ℝ => (Z u).re) z'.re w := by
    rw [hZdef, hz'def]
    exact ReStrictMono.hasDerivAt_re_arcZ ηs hηs w
  have hdd : HasDerivAt (fun u : ℝ => (Z u).im) z'.im w := by
    rw [hZdef, hz'def]
    exact Work.Drive.N2C.hasDerivAt_im_arcZ ηs hηs w
  have hsxw : ((Z w).re + ε) / (2 * ε) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hθw : θ w = 0 := by
    simp only [hθdef, Real.smoothTransition.zero_of_nonpos hsxw, mul_zero, neg_zero]
  have hcosθw : Real.cos (θ w) = 1 := by rw [hθw, Real.cos_zero]
  have hsinθw : Real.sin (θ w) = 0 := by rw [hθw, Real.sin_zero]
  set K : ℝ := -(Real.pi * (deriv Real.smoothTransition (((Z w).re + ε) / (2 * ε))
    * (z'.re / (2 * ε)))) with hKdef
  have hθK : HasDerivAt θ K w := by
    rw [hθdef, hKdef]
    have hsx : HasDerivAt (fun u : ℝ => ((Z u).re + ε) / (2 * ε)) (z'.re / (2 * ε)) w :=
      (hcc.add_const ε).div_const (2 * ε)
    have hdiff : DifferentiableAt ℝ Real.smoothTransition (((Z w).re + ε) / (2 * ε)) :=
      differentiableAt_smoothTransition _
    have hd : HasDerivAt Real.smoothTransition
        (deriv Real.smoothTransition (((Z w).re + ε) / (2 * ε))) (((Z w).re + ε) / (2 * ε)) :=
      hdiff.hasDerivAt
    have hcomp : HasDerivAt
        (Real.smoothTransition ∘ fun u : ℝ => ((Z u).re + ε) / (2 * ε))
        (deriv Real.smoothTransition (((Z w).re + ε) / (2 * ε)) * (z'.re / (2 * ε))) w :=
      hd.comp w hsx
    exact (hcomp.const_mul Real.pi).neg
  have hA : HasDerivAt A z'.im w := by
    have hcos : HasDerivAt (fun u : ℝ => Real.cos (θ u)) (-Real.sin (θ w) * K) w :=
      (Real.hasDerivAt_cos (θ w)).comp w hθK
    have hprod : HasDerivAt (fun u : ℝ => (Z u).im * Real.cos (θ u))
        (z'.im * Real.cos (θ w) + (Z w).im * (-(Real.sin (θ w)) * K)) w :=
      hdd.mul hcos
    rw [hAdef]
    convert hprod using 1
    rw [hcosθw, hsinθw]
    ring
  have hAwval : A w = (Z w).im := by
    simp only [hAdef]
    rw [hcosθw]
    ring
  have hAwge : εp ≤ A w := by rw [hAwval]; exact him
  have hQ : HasDerivAt (fun u => pushProf Dp εp 1 (A u)) z'.im w :=
    hasDerivAt_pushProf_one_comp_of_le hεp hA hAwge
  have hPeq : ∀ u : ℝ, P u = (⟨(Z u).re, pushProf Dp εp 1 (A u)⟩ : ℂ) := by
    intro u
    simp only [hPdef, hAdef, hθdef, proj2, pushY_apply_zero, pushY_apply_one]
    rw [Work.Drive.N2C.twistX_neg_one_cE3_zero, Work.Drive.N2C.twistX_neg_one_cE3_one]
  have hPw : P w = (⟨(Z w).re, (Z w).im + Dp⟩ : ℂ) := by
    rw [hPeq w, hAwval, pushProf_one_eq_of_le hεp him]
  have hPc : HasDerivAt P (⟨z'.re, z'.im⟩ : ℂ) w := by
    have h1 : HasDerivAt (fun u : ℝ => (((Z u).re : ℝ) : ℂ)) (z'.re : ℂ) w :=
      HasDerivAt.ofReal_comp hcc
    have h2 : HasDerivAt
        (fun u : ℝ => (((pushProf Dp εp 1 (A u) : ℝ)) : ℂ) * Complex.I)
        ((((z'.im : ℝ)) : ℂ) * Complex.I) w :=
      (HasDerivAt.ofReal_comp hQ).mul_const Complex.I
    have h3 : HasDerivAt (fun u : ℝ => (((Z u).re : ℝ) : ℂ)
        + (((pushProf Dp εp 1 (A u) : ℝ)) : ℂ) * Complex.I)
        ((z'.re : ℂ) + ((((z'.im : ℝ)) : ℂ) * Complex.I)) w := h1.add h2
    have hv : (z'.re : ℂ) + ((((z'.im : ℝ)) : ℂ) * Complex.I) = (⟨z'.re, z'.im⟩ : ℂ) := by
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
  have hz0 : Z w ≠ 0 := by
    rw [hZdef]
    exact ReStrictMono.arcZ_ne_zero_of_eta_pos hηs w
  have h2Zw : (2 : ℂ) * Z w ≠ 0 := mul_ne_zero two_ne_zero hz0
  have hz'mul : z' * (2 * Z w) = Complex.I := by
    rw [hz'def, div_mul_cancel₀ _ h2Zw]
  rw [hPw, hPderiv]
  have hstar : star (⟨(Z w).re, (Z w).im + Dp⟩ : ℂ)
      = (⟨(Z w).re, -((Z w).im + Dp)⟩ : ℂ) := by
    apply Complex.ext <;> simp
  rw [hstar]
  exact key_algebra_left (Z w) z' Dp ηs hz'mul hηs hDp himpos hsq

/-! ## The pin curve row -/

/-- **The pin curve row of the Möbius saddle, outside the twist band.**  For `ηs, ε, εp > 0`,
`Dp ≥ 0` and every `w` with `ε ≤ |Re (arcZ ηs w)|` and `εp ≤ Im (arcZ ηs w)`, the planar projection
`upCurve ηs Dp εp ε` of the pushed, twisted upper arc point has non-zero angular rate. -/
theorem pinCurveRowUp {ηs ε εp Dp : ℝ} (hηs : 0 < ηs) (hε : 0 < ε) (hεp : 0 < εp)
    (hDp : 0 ≤ Dp) :
    ∀ w : ℝ, ε ≤ |(Work.Drive.N2Lead.arcZ ηs w).re| → εp ≤ (Work.Drive.N2Lead.arcZ ηs w).im →
      (star (Work.Drive.N2Lead.upCurve ηs Dp εp ε w)
        * deriv (Work.Drive.N2Lead.upCurve ηs Dp εp ε) w).im ≠ 0 := by
  intro w hεre him
  have himpos : 0 < (arcZ ηs w).im := ReStrictMono.im_arcZ_pos hηs w
  rcases lt_or_ge 0 (arcZ ηs w).re with hpos | hnonpos
  · -- right of the twist band: the rigid half-turn + downward push formula
    have hre : ε ≤ (arcZ ηs w).re := by
      rwa [abs_of_pos hpos] at hεre
    have himabs : εp ≤ |(arcZ ηs w).im| := by rwa [abs_of_pos himpos]
    have hw2 : w = 2 * (arcZ ηs w).re * (arcZ ηs w).im := by
      have h := arcZ_sq_im ηs w
      rw [pow_two, Complex.mul_im] at h
      linarith
    have hwpos : 0 < w := by
      rw [hw2]; positivity
    have hres := (Work.Drive.N2C.mobiusPinCurveRow (ηs := ηs) (ε := ε) (εp := εp) (Dp := Dp)
      (c₀ := |w|) (m := |w|) hηs hε hεp hDp (abs_pos.mpr (ne_of_gt hwpos)) w
      le_rfl le_rfl hre himabs).2
    exact hres
  · -- left of the twist band: the rigid identity twist + upward push formula
    have hneg : (arcZ ηs w).re < 0 := by
      refine lt_of_le_of_ne hnonpos (fun h0 => ?_)
      rw [h0, abs_zero] at hεre
      linarith
    have hre : (arcZ ηs w).re ≤ -ε := by
      have h1 : ε ≤ -(arcZ ηs w).re := by
        rw [abs_of_neg hneg] at hεre
        exact hεre
      linarith
    exact upCurve_rate_left hηs hε hεp hDp hre him

end

end Work.Drive.N2Lead
