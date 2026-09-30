import Mathlib
import Submission.Work.BMF.perron_twist_core
import Submission.Work.BMF.liouville.zeta_tw_perron
import Submission.Work.BMF.liouville.zetaTw_rect_defs
import Submission.Commons.NumberTheory.Zeta.psi_sub_id_powLog_real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

namespace Work.BMF.liouville

open Complex MeasureTheory intervalIntegral
open scoped Real Interval Topology

set_option maxHeartbeats 0

/-! ## Helper lemmas -/

/-- `zetaTwH u x` is holomorphic on any set avoiding `w = 0` and the zeros of `ζ₁(·+iu)`. -/
private lemma zetaTwH_differentiableOn_of (u x : ℝ) (hx : 0 < x) {S : Set ℂ}
    (hS : S ⊆ {p : ℂ | 0 < p.re})
    (hζ : ∀ p ∈ S, riemannZeta₁ (p + (u : ℂ) * Complex.I) ≠ 0) :
    DifferentiableOn ℂ (zetaTwH u x) S := by
  have hV : {p : ℂ | 0 < p.re} ∈ 𝓝 (zetaTwPole u) := by
    refine (Complex.isOpen_re_gt 0).mem_nhds ?_
    simp [zetaTwPole]
  have hφ : DifferentiableOn ℂ (zetaTwPhi x) {p : ℂ | 0 < p.re} := by
    refine (Commons.NumberTheory.Zeta.cpow_div_self_differentiableOn (x := x) hx).mono ?_
    intro p hp hp0
    rw [hp0] at hp
    simp at hp
  have hdslope : DifferentiableOn ℂ (dslope (zetaTwPhi x) (zetaTwPole u)) {p : ℂ | 0 < p.re} :=
    (Complex.differentiableOn_dslope (f := zetaTwPhi x) (c := zetaTwPole u)
      (s := {p : ℂ | 0 < p.re}) hV).mpr hφ
  have hL : DifferentiableOn ℂ
      (Commons.NumberTheory.Zeta.zeta1LogDeriv ∘ fun p : ℂ => p + (u : ℂ) * Complex.I) S :=
    (Commons.NumberTheory.Zeta.zeta1LogDeriv_differentiableOn_noZero).comp
      ((differentiableOn_id.add_const ((u : ℂ) * Complex.I)))
      (by intro p hp; exact hζ p hp)
  have hfin : DifferentiableOn ℂ (fun p : ℂ => dslope (zetaTwPhi x) (zetaTwPole u) p
      - zetaTwPhi x p * Commons.NumberTheory.Zeta.zeta1LogDeriv (p + (u : ℂ) * Complex.I)) S :=
    (hdslope.mono hS).sub ((hφ.mono hS).mul hL)
  exact hfin

/-- Residue of `cst/(s-u)` around a rectangle containing `u` strictly inside. -/
private lemma rectInt_const_div_sub {z w : ℂ} (cst u : ℂ) (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) :
    Commons.NumberTheory.Zeta.rectInt z w (fun s : ℂ => cst / (s - u)) =
      cst * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  have hfun : (fun s : ℂ => cst / (s - u)) = fun s : ℂ => cst * (s - u)⁻¹ := by
    funext s
    rw [div_eq_mul_inv]
  rw [hfun, Commons.NumberTheory.Zeta.rectInt_const_mul cst (fun s : ℂ => (s - u)⁻¹)]
  congr 1
  simpa [Commons.NumberTheory.Zeta.rectInt] using
    (Commons.Analysis.Complex.rectIntegral_sub_inv_inside (z := z) (w := w) (u := u) hzre hzim huin)

/-- Pointwise pole subtraction for the twisted Perron integrand. -/
private lemma zetaTwG_eq_principal_add_H (u x : ℝ) {w : ℂ}
    (hww : w ≠ zetaTwPole u) (hz : riemannZeta₁ (w + (u : ℂ) * Complex.I) ≠ 0) :
    zetaTwG u x w = zetaTwP u x w + zetaTwH u x w := by
  set s : ℂ := w + (u : ℂ) * Complex.I with hs
  have hs1 : s ≠ 1 := by
    intro h
    apply hww
    have h' : w = 1 - (u : ℂ) * Complex.I := by
      rw [hs] at h
      linear_combination h
    rw [zetaTwPole, h']
    ring
  have hderiv : deriv riemannZeta s / riemannZeta s =
      -(s - 1)⁻¹ + Commons.NumberTheory.Zeta.zeta1LogDeriv s := by
    rw [Commons.NumberTheory.Zeta.deriv_zeta_div_zeta_eq s hs1 hz]
    simp [Commons.NumberTheory.Zeta.zeta1LogDeriv]
  have hw0 : w - zetaTwPole u = s - 1 := by
    rw [hs, zetaTwPole]
    ring
  have hslope : dslope (zetaTwPhi x) (zetaTwPole u) w =
      (w - zetaTwPole u)⁻¹ * (zetaTwPhi x w - zetaTwPhi x (zetaTwPole u)) := by
    rw [dslope_of_ne (zetaTwPhi x) hww, slope_def_module, smul_eq_mul]
  have hres : zetaTwPhi x (zetaTwPole u) = zetaTwRes u x := rfl
  have harg : w + (u : ℂ) * Complex.I = s := hs.symm
  have hLHS : zetaTwG u x w = -(deriv riemannZeta s / riemannZeta s) * zetaTwPhi x w := by
    simp only [zetaTwG, zetaTwPhi]
    rw [harg]
    ring
  have hRHS : zetaTwP u x w + zetaTwH u x w =
      -(deriv riemannZeta s / riemannZeta s) * zetaTwPhi x w := by
    simp only [zetaTwP, zetaTwH, Function.comp_apply]
    rw [hslope, hres, harg, hderiv]
    rw [← hw0]
    rw [div_eq_mul_inv]
    ring
  rw [hLHS, hRHS]

/-- Expansion of `rectInt` for the twisted Perron integrand. -/
private lemma rectInt_zetaTwG_eq (u x T σ₁ : ℝ) :
    Commons.NumberTheory.Zeta.rectInt ((σ₁ : ℂ) - (T : ℂ) * Complex.I)
        (((1 + 1 / Real.log x : ℝ) : ℂ) + (T : ℂ) * Complex.I) (zetaTwG u x) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (zetaTwBot u x T σ₁ + zetaTwPerron u x T - zetaTwTop u x T σ₁
          - zetaTwLeft u x T σ₁) := by
  set z : ℂ := (σ₁ : ℂ) - (T : ℂ) * Complex.I with hz
  set w : ℂ := (((1 + 1 / Real.log x : ℝ)) : ℂ) + (T : ℂ) * Complex.I with hw
  have hzre : z.re = σ₁ := by simp [z]
  have hzim : z.im = -T := by simp [z]
  have hwre : w.re = 1 + 1 / Real.log x := by simp [w]
  have hwim : w.im = T := by simp [w]
  have hperp : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    refine mul_ne_zero two_ne_zero ?_
    exact_mod_cast Real.pi_ne_zero
  have hfun : (fun v : ℝ => zetaTwG u x ((v : ℂ) + (((-T : ℝ)) : ℂ) * Complex.I)) =
      fun v : ℝ => zetaTwG u x ((v : ℂ) - (T : ℂ) * Complex.I) := by
    funext v
    congr 1
    push_cast
    ring
  rw [zetaTwBot, zetaTwTop, zetaTwPerron, zetaTwLeft]
  unfold Commons.NumberTheory.Zeta.rectInt
  simp only [smul_eq_mul, hzre, hzim, hwre, hwim]
  rw [hfun]
  field_simp
  ring

/-- **Contour shift for the twisted principal-character Perron integral.**

Let `f(w) = zetaTwG u x w = −(ζ′/ζ)(w + iu)·x^w/w` (see
`Submission.Work.BMF.liouville.zeta_tw_perron`) and let `R` be the rectangle
`[σ₁, 1 + 1/log x] × [-T, T]` in the `w`-plane.  Since `σ₁ < 1` and `|u| < T`, the only
singularity of `f` inside `R` is the simple pole at `w = 1 - iu` (where `ζ(w + iu)` has its pole;
the point `w = 0` is not in `R` because `σ₁ > 0`), with residue `x^{1-iu}/(1-iu)`: near
`w = 1 - iu`, `−(ζ′/ζ)(w+iu) ≈ 1/(w-(1-iu))`, so `f(w) ≈ x^{1-iu}/(1-iu)·1/(w-(1-iu))`.

Traversing `∂R` counterclockwise and using `∮ f = 2πi·residue`, with the right edge
`Re w = 1 + 1/log x` parametrized upward, gives the identity below: `zetaTwPerron` is `(1/2π)`
times the right-edge integral, while `zetaTwTop`, `zetaTwBot`, `zetaTwLeft` are the normalized
top, bottom and left edge integrals (all defined in
`Submission.Work.BMF.liouville.zeta_tw_perron`).  The signs come out as
`right = residue + top − bottom + left` because the top edge is traversed right-to-left and the
left edge downward.

Templates: `Work.BMF.rect_edge_decomp` (rectangle decomposition, pole-free case) and, in
`Submission/Commons/NumberTheory/Zeta/psi_sub_id_powLog_real.lean`, the pole subtraction for the
*untwisted* problem (`psiIntF_eq_polar_add_hFunc_of_zeta1_ne_zero`,
`rectInt_hFunc_zero_noZero`, `psiIntF_rectInt_eq_noZero`) together with
`Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal`.  Route: subtract the principal part
`x^{1-iu}/(1-iu)·1/(w-(1-iu))` from `f`, apply the pole-free rectangle decomposition to the
difference (holomorphic on `R`, since `ζ(w+iu) ≠ 0` there by `hZ` and `w = 0 ∉ R`), and use
`∮ dw/(w-(1-iu)) = 2πi` for the subtracted term. -/
theorem zetaTwPerron_rect (u x T σ₁ : ℝ) (hx : 1 < x) (hT : 0 < T) (hσ₁ : 0 < σ₁)
    (hσ₁1 : σ₁ < 1) (hσ₁lt : σ₁ < 1 + 1 / Real.log x) (huT : |u| < T)
    (hZ : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 1 + 1 / Real.log x → |s.im - u| ≤ T → s ≠ 1 →
      riemannZeta s ≠ 0) :
    zetaTwPerron u x T =
      (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))
        + zetaTwTop u x T σ₁ - zetaTwBot u x T σ₁ + zetaTwLeft u x T σ₁ := by
  change zetaTwPerron u x T = zetaTwRes u x + zetaTwTop u x T σ₁ - zetaTwBot u x T σ₁
    + zetaTwLeft u x T σ₁
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hc1 : 1 < 1 + 1 / Real.log x := by
    have : 0 < 1 / Real.log x := by positivity
    linarith
  obtain ⟨hua, hub⟩ := abs_lt.mp huT
  -- ζ₁ does not vanish on the relevant rectangle of the `s = p + iu` plane
  have hZ₁ : ∀ p : ℂ, σ₁ ≤ p.re → p.re ≤ 1 + 1 / Real.log x → |p.im| ≤ T →
      riemannZeta₁ (p + (u : ℂ) * Complex.I) ≠ 0 := by
    intro p h1 h2 h3
    set s : ℂ := p + (u : ℂ) * Complex.I with hs
    by_cases hs1 : s = 1
    · rw [hs1]
      simp
    · have hsre : s.re = p.re := by simp [hs]
      have hsim : s.im - u = p.im := by rw [hs]; simp
      have hζ : riemannZeta s ≠ 0 :=
        hZ s (by rw [hsre]; exact h1) (by rw [hsre]; exact h2) (by rw [hsim]; exact h3) hs1
      have hmul : riemannZeta s = (s - 1)⁻¹ * riemannZeta₁ s := riemannZeta_eq_inv_sub_mul hs1
      rw [hmul] at hζ
      exact (mul_ne_zero_iff.mp hζ).2
  -- the rectangle in the `w`-plane
  set z : ℂ := (σ₁ : ℂ) - (T : ℂ) * Complex.I with hz
  set w : ℂ := (((1 + 1 / Real.log x : ℝ)) : ℂ) + (T : ℂ) * Complex.I with hw
  have hzre : z.re = σ₁ := by simp [z]
  have hzim : z.im = -T := by simp [z]
  have hwre : w.re = 1 + 1 / Real.log x := by simp [w]
  have hwim : w.im = T := by simp [w]
  have hzre_lt : z.re < w.re := by rw [hzre, hwre]; linarith
  have hzim_lt : z.im < w.im := by rw [hzim, hwim]; linarith
  have hpole_re : (zetaTwPole u).re = 1 := by simp [zetaTwPole]
  have hpole_im : (zetaTwPole u).im = -u := by simp [zetaTwPole]
  have hUI1 : Set.uIcc σ₁ (1 + 1 / Real.log x) = Set.Icc σ₁ (1 + 1 / Real.log x) :=
    Set.uIcc_of_le (le_of_lt hσ₁lt)
  have hUI2 : Set.uIcc (-T) T = Set.Icc (-T) T := Set.uIcc_of_le (by linarith)
  have hbre : ∀ p : ℂ, p ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im →
      σ₁ ≤ p.re ∧ p.re ≤ 1 + 1 / Real.log x ∧ |p.im| ≤ T := by
    intro p hp
    obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hp
    rw [hzre, hwre] at h1
    rw [hzim, hwim] at h2
    have h1' : p.re ∈ Set.Icc σ₁ (1 + 1 / Real.log x) := by simpa only [hUI1] using h1
    have h2' : p.im ∈ Set.Icc (-T) T := by simpa only [hUI2] using h2
    exact ⟨(Set.mem_Icc.mp h1').1, (Set.mem_Icc.mp h1').2,
      abs_le.mpr ⟨(Set.mem_Icc.mp h2').1, (Set.mem_Icc.mp h2').2⟩⟩
  -- `zetaTwH` is holomorphic on the rectangle
  have hHdiff : DifferentiableOn ℂ (zetaTwH u x) (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    refine zetaTwH_differentiableOn_of u x (by linarith) ?_ ?_
    · intro p hp
      exact lt_of_lt_of_le hσ₁ (hbre p hp).1
    · intro p hp
      exact hZ₁ p (hbre p hp).1 (hbre p hp).2.1 (hbre p hp).2.2
  -- integrability of the `zetaTwH` edges
  have iH1 : IntervalIntegrable (fun v : ℝ => zetaTwH u x ((v : ℂ) + (z.im : ℂ) * Complex.I))
      volume z.re w.re :=
    ((hHdiff.continuousOn).comp (by fun_prop) (by
      intro v hv
      exact Complex.mem_reProdIm.mpr ⟨by simpa using hv, by simp⟩)).intervalIntegrable
  have iH2 : IntervalIntegrable (fun v : ℝ => zetaTwH u x ((v : ℂ) + (w.im : ℂ) * Complex.I))
      volume z.re w.re :=
    ((hHdiff.continuousOn).comp (by fun_prop) (by
      intro v hv
      exact Complex.mem_reProdIm.mpr ⟨by simpa using hv, by simp⟩)).intervalIntegrable
  have iH3 : IntervalIntegrable (fun t : ℝ => zetaTwH u x ((w.re : ℂ) + (t : ℂ) * Complex.I))
      volume z.im w.im :=
    ((hHdiff.continuousOn).comp (by fun_prop) (by
      intro v hv
      exact Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hv⟩)).intervalIntegrable
  have iH4 : IntervalIntegrable (fun t : ℝ => zetaTwH u x ((z.re : ℂ) + (t : ℂ) * Complex.I))
      volume z.im w.im :=
    ((hHdiff.continuousOn).comp (by fun_prop) (by
      intro v hv
      exact Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hv⟩)).intervalIntegrable
  -- integrability of the principal-part edges
  have hUo : IsOpen {p : ℂ | p ≠ zetaTwPole u} := isOpen_ne
  have hcontP : ContinuousOn (zetaTwP u x) {p : ℂ | p ≠ zetaTwPole u} := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact continuousOn_id.sub continuousOn_const
    · intro p hp
      exact sub_ne_zero.mpr hp
  have iP1 : IntervalIntegrable (fun v : ℝ => zetaTwP u x ((v : ℂ) + (z.im : ℂ) * Complex.I))
      volume z.re w.re :=
    Commons.NumberTheory.Zeta.edge_integrable_horiz (f := zetaTwP u x)
      (U := {p : ℂ | p ≠ zetaTwPole u}) hUo hcontP (a := z.re) (b := w.re) (r := z.im) (by
        intro v hv h
        have h0him := congrArg (fun p : ℂ => p.im) h
        have him : z.im = (zetaTwPole u).im := by simpa using h0him
        rw [hzim, hpole_im] at him
        linarith)
  have iP2 : IntervalIntegrable (fun v : ℝ => zetaTwP u x ((v : ℂ) + (w.im : ℂ) * Complex.I))
      volume z.re w.re :=
    Commons.NumberTheory.Zeta.edge_integrable_horiz (f := zetaTwP u x)
      (U := {p : ℂ | p ≠ zetaTwPole u}) hUo hcontP (a := z.re) (b := w.re) (r := w.im) (by
        intro v hv h
        have h0him := congrArg (fun p : ℂ => p.im) h
        have him : w.im = (zetaTwPole u).im := by simpa using h0him
        rw [hwim, hpole_im] at him
        linarith)
  have iP3 : IntervalIntegrable (fun t : ℝ => zetaTwP u x ((w.re : ℂ) + (t : ℂ) * Complex.I))
      volume z.im w.im :=
    Commons.NumberTheory.Zeta.edge_integrable_vert (f := zetaTwP u x)
      (U := {p : ℂ | p ≠ zetaTwPole u}) hUo hcontP (c := z.im) (d := w.im) (a := w.re) (by
        intro v hv h
        have h0hre := congrArg (fun p : ℂ => p.re) h
        have hre : w.re = (zetaTwPole u).re := by simpa using h0hre
        rw [hwre, hpole_re] at hre
        linarith [one_div_pos.mpr hlogx])
  have iP4 : IntervalIntegrable (fun t : ℝ => zetaTwP u x ((z.re : ℂ) + (t : ℂ) * Complex.I))
      volume z.im w.im :=
    Commons.NumberTheory.Zeta.edge_integrable_vert (f := zetaTwP u x)
      (U := {p : ℂ | p ≠ zetaTwPole u}) hUo hcontP (c := z.im) (d := w.im) (a := z.re) (by
        intro v hv h
        have h0hre := congrArg (fun p : ℂ => p.re) h
        have hre : z.re = (zetaTwPole u).re := by simpa using h0hre
        rw [hzre, hpole_re] at hre
        linarith)
  -- the expansion on the rectangle
  have hper : Commons.NumberTheory.Zeta.rectInt z w (zetaTwG u x) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (zetaTwBot u x T σ₁ + zetaTwPerron u x T - zetaTwTop u x T σ₁
          - zetaTwLeft u x T σ₁) := by
    rw [hz, hw]
    exact rectInt_zetaTwG_eq u x T σ₁
  -- `zetaTwH` integrates to zero
  have hHzero : Commons.NumberTheory.Zeta.rectInt z w (zetaTwH u x) = 0 := by
    simpa [Commons.NumberTheory.Zeta.rectInt] using
      (Complex.integral_boundary_rect_eq_zero_of_differentiableOn (zetaTwH u x) z w hHdiff)
  -- the principal part integrates to the residue
  have huin : z.re < (zetaTwPole u).re ∧ (zetaTwPole u).re < w.re ∧
      z.im < (zetaTwPole u).im ∧ (zetaTwPole u).im < w.im := by
    rw [hzre, hwre, hzim, hwim, hpole_re, hpole_im]
    exact ⟨hσ₁1, hc1, by linarith, by linarith⟩
  have hPres : Commons.NumberTheory.Zeta.rectInt z w (zetaTwP u x) =
      zetaTwRes u x * (2 * (Real.pi : ℂ) * Complex.I) := by
    show Commons.NumberTheory.Zeta.rectInt z w (fun p : ℂ => zetaTwRes u x / (p - zetaTwPole u))
      = zetaTwRes u x * (2 * (Real.pi : ℂ) * Complex.I)
    exact rectInt_const_div_sub (zetaTwRes u x) (zetaTwPole u) hzre_lt hzim_lt huin
  -- splitting on the boundary
  have hsplit : Commons.NumberTheory.Zeta.rectInt z w (zetaTwG u x) =
      Commons.NumberTheory.Zeta.rectInt z w (zetaTwP u x)
        + Commons.NumberTheory.Zeta.rectInt z w (zetaTwH u x) := by
    have hcongr : Commons.NumberTheory.Zeta.rectInt z w (zetaTwG u x) =
        Commons.NumberTheory.Zeta.rectInt z w (fun p : ℂ => zetaTwP u x p + zetaTwH u x p) := by
      apply Commons.NumberTheory.Zeta.rectInt_congr_boundary
      · intro v hv
        have hmem : (v : ℂ) + z.im * Complex.I ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im :=
          Complex.mem_reProdIm.mpr ⟨by simpa using hv, by simp⟩
        have hp := hbre _ hmem
        refine zetaTwG_eq_principal_add_H u x ?_ ?_
        · intro h
          have h0him := congrArg (fun p : ℂ => p.im) h
          have him : z.im = (zetaTwPole u).im := by simpa using h0him
          rw [hzim, hpole_im] at him
          linarith
        · exact hZ₁ _ hp.1 hp.2.1 hp.2.2
      · intro v hv
        have hmem : (v : ℂ) + w.im * Complex.I ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im :=
          Complex.mem_reProdIm.mpr ⟨by simpa using hv, by simp⟩
        have hp := hbre _ hmem
        refine zetaTwG_eq_principal_add_H u x ?_ ?_
        · intro h
          have h0him := congrArg (fun p : ℂ => p.im) h
          have him : w.im = (zetaTwPole u).im := by simpa using h0him
          rw [hwim, hpole_im] at him
          linarith
        · exact hZ₁ _ hp.1 hp.2.1 hp.2.2
      · intro v hv
        have hmem : (w.re : ℂ) + v * Complex.I ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im :=
          Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hv⟩
        have hp := hbre _ hmem
        refine zetaTwG_eq_principal_add_H u x ?_ ?_
        · intro h
          have h0hre := congrArg (fun p : ℂ => p.re) h
          have hre : w.re = (zetaTwPole u).re := by simpa using h0hre
          rw [hwre, hpole_re] at hre
          linarith [one_div_pos.mpr hlogx]
        · exact hZ₁ _ hp.1 hp.2.1 hp.2.2
      · intro v hv
        have hmem : (z.re : ℂ) + v * Complex.I ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im :=
          Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hv⟩
        have hp := hbre _ hmem
        refine zetaTwG_eq_principal_add_H u x ?_ ?_
        · intro h
          have h0hre := congrArg (fun p : ℂ => p.re) h
          have hre : z.re = (zetaTwPole u).re := by simpa using h0hre
          rw [hzre, hpole_re] at hre
          linarith
        · exact hZ₁ _ hp.1 hp.2.1 hp.2.2
    rw [hcongr]
    exact Commons.NumberTheory.Zeta.rectInt_add iP1 iH1 iP2 iH2 iP3 iH3 iP4 iH4
  have hval : Commons.NumberTheory.Zeta.rectInt z w (zetaTwG u x) =
      zetaTwRes u x * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hsplit, hPres, hHzero, add_zero]
  have hperp : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hmain : zetaTwBot u x T σ₁ + zetaTwPerron u x T - zetaTwTop u x T σ₁
      - zetaTwLeft u x T σ₁ = zetaTwRes u x := by
    have hPS : (2 * (Real.pi : ℂ) * Complex.I) *
        (zetaTwBot u x T σ₁ + zetaTwPerron u x T - zetaTwTop u x T σ₁ - zetaTwLeft u x T σ₁) =
        (2 * (Real.pi : ℂ) * Complex.I) * zetaTwRes u x := by
      rw [← hper, hval, mul_comm (zetaTwRes u x)]
    exact mul_left_cancel₀ hperp hPS
  linear_combination hmain

end Work.BMF.liouville

-- The same statement, also exposed under the canonical module name
-- `Work.BMF.liouville.zetaTwPerron_rect` (the theorem above lives in the doubly nested namespace
-- `Work.BMF.liouville.Work.BMF.liouville` because the requested statement carried its own
-- `namespace`/`end` pair).
/-- **Contour shift for the twisted principal-character Perron integral.**

Let `f(w) = zetaTwG u x w = −(ζ′/ζ)(w + iu)·x^w/w` (see
`Submission.Work.BMF.liouville.zeta_tw_perron`) and let `R` be the rectangle
`[σ₁, 1 + 1/log x] × [-T, T]` in the `w`-plane.  Since `σ₁ < 1` and `|u| < T`, the only
singularity of `f` inside `R` is the simple pole at `w = 1 - iu` (where `ζ(w + iu)` has its pole;
the point `w = 0` is not in `R` because `σ₁ > 0`), with residue `x^{1-iu}/(1-iu)`: near
`w = 1 - iu`, `−(ζ′/ζ)(w+iu) ≈ 1/(w-(1-iu))`, so `f(w) ≈ x^{1-iu}/(1-iu)·1/(w-(1-iu))`.

Traversing `∂R` counterclockwise and using `∮ f = 2πi·residue`, with the right edge
`Re w = 1 + 1/log x` parametrized upward, gives the identity below: `zetaTwPerron` is `(1/2π)`
times the right-edge integral, while `zetaTwTop`, `zetaTwBot`, `zetaTwLeft` are the normalized
top, bottom and left edge integrals (all defined in
`Submission.Work.BMF.liouville.zeta_tw_perron`).  The signs come out as
`right = residue + top − bottom + left` because the top edge is traversed right-to-left and the
left edge downward.

Templates: `Work.BMF.rect_edge_decomp` (rectangle decomposition, pole-free case) and, in
`Submission/Commons/NumberTheory/Zeta/psi_sub_id_powLog_real.lean`, the pole subtraction for the
*untwisted* problem (`psiIntF_eq_polar_add_hFunc_of_zeta1_ne_zero`,
`rectInt_hFunc_zero_noZero`, `psiIntF_rectInt_eq_noZero`) together with
`Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal`.  Route: subtract the principal part
`x^{1-iu}/(1-iu)·1/(w-(1-iu))` from `f`, apply the pole-free rectangle decomposition to the
difference (holomorphic on `R`, since `ζ(w+iu) ≠ 0` there by `hZ` and `w = 0 ∉ R`), and use
`∮ dw/(w-(1-iu)) = 2πi` for the subtracted term. -/
theorem zetaTwPerron_rect (u x T σ₁ : ℝ) (hx : 1 < x) (hT : 0 < T) (hσ₁ : 0 < σ₁)
    (hσ₁1 : σ₁ < 1) (hσ₁lt : σ₁ < 1 + 1 / Real.log x) (huT : |u| < T)
    (hZ : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 1 + 1 / Real.log x → |s.im - u| ≤ T → s ≠ 1 →
      riemannZeta s ≠ 0) :
    zetaTwPerron u x T =
      (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))
        + zetaTwTop u x T σ₁ - zetaTwBot u x T σ₁ + zetaTwLeft u x T σ₁ := Work.BMF.liouville.Work.BMF.liouville.zetaTwPerron_rect u x T σ₁
  hx hT hσ₁ hσ₁1 hσ₁lt huT hZ

end Work.BMF.liouville
