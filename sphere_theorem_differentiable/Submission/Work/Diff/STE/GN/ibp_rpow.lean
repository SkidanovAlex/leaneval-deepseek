import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.integral_mul_pd_eq_neg
import Submission.Work.Diff.STE.fourierCoeff_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.GN

/-! ## Auxiliary lemmas

The facts below are the pieces of the proof of `ibp_rpow`:

* `pd_ofReal_local` and `integral_mul_pdR_eq_neg_aux`: the real-valued version of the periodic
  integration by parts, obtained from the complex-valued library lemma
  `Work.Diff.STE.integral_mul_pd_eq_neg` by complexification;
* `abs_rpow_mul_deriv`, `abs_rpow_mul_contDiff`: the derivative and the `C¹`-smoothness of
  `s ↦ |s| ^ (p - 2) * s` for `p ≥ 2`.
-/

/-- `pd` of a real-valued function, viewed as a complex-valued function. -/
private lemma pd_ofReal_local {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (F : (ι → ℝ) → ℝ) (x : ι → ℝ) (hF : DifferentiableAt ℝ F x) :
    Work.Diff.STE.pd i (fun y => (F y : ℂ)) x = ((Work.Diff.STE.pdR i F x : ℝ) : ℂ) := by
  have hfd : fderiv ℝ (fun y => (F y : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ F x) := by
    have h := (Complex.ofRealCLM.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
    have h2 : (fun y => (F y : ℂ)) = (⇑Complex.ofRealCLM ∘ F) := rfl
    rw [h2]; exact h
  simp only [Work.Diff.STE.pd, Work.Diff.STE.pdR]
  rw [hfd, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

/-- **Real-valued periodic integration by parts on the unit torus.**  For `C¹` real functions
`f g` on the unit cube `(0,1]^ι` that are `1`-periodic in the coordinate `i`,
`∫ f ∂ᵢg = - ∫ (∂ᵢf) g`.

This is the complex-valued library lemma `Work.Diff.STE.integral_mul_pd_eq_neg` applied to
`fun x => (f x : ℂ)` and `fun x => (g x : ℂ)`, with `pd_ofReal_local` identifying the two
integrands and `integral_ofReal` turning the complex set integrals into the real ones. -/
private lemma integral_mul_pdR_eq_neg_aux {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (f g : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfp : Work.Diff.STE.PeriodicIn i f) (hgp : Work.Diff.STE.PeriodicIn i g) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), f x * Work.Diff.STE.pdR i g x
      = - ∫ x in Work.Diff.STE.unitCube (ι := ι), Work.Diff.STE.pdR i f x * g x := by
  have hF : ContDiff ℝ 1 (fun x : ι → ℝ => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hG : ContDiff ℝ 1 (fun x : ι → ℝ => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hFp : Work.Diff.STE.PeriodicIn i (fun x : ι → ℝ => (f x : ℂ)) := by
    intro x; show (f (x + Pi.single i 1) : ℂ) = (f x : ℂ); rw [hfp x]
  have hGp : Work.Diff.STE.PeriodicIn i (fun x : ι → ℝ => (g x : ℂ)) := by
    intro x; show (g (x + Pi.single i 1) : ℂ) = (g x : ℂ); rw [hgp x]
  have hIBP := Work.Diff.STE.integral_mul_pd_eq_neg i (fun x : ι → ℝ => (f x : ℂ))
    (fun x : ι → ℝ => (g x : ℂ)) hF hG hFp hGp
  have h1 : (∫ x in Work.Diff.STE.unitCube,
        (f x : ℂ) * Work.Diff.STE.pd i (fun y : ι → ℝ => (g y : ℂ)) x)
      = ∫ x in Work.Diff.STE.unitCube, ((f x * Work.Diff.STE.pdR i g x : ℝ) : ℂ) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [pd_ofReal_local i g x (hg.differentiable_one.differentiableAt), ← Complex.ofReal_mul]
  have h2 : (∫ x in Work.Diff.STE.unitCube,
        Work.Diff.STE.pd i (fun y : ι → ℝ => (f y : ℂ)) x * (g x : ℂ))
      = ∫ x in Work.Diff.STE.unitCube, ((Work.Diff.STE.pdR i f x * g x : ℝ) : ℂ) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [pd_ofReal_local i f x (hf.differentiable_one.differentiableAt), ← Complex.ofReal_mul]
  rw [h1, h2] at hIBP
  have h3 : (∫ x in Work.Diff.STE.unitCube, ((f x * Work.Diff.STE.pdR i g x : ℝ) : ℂ))
      = ((∫ x in Work.Diff.STE.unitCube, f x * Work.Diff.STE.pdR i g x : ℝ) : ℂ) :=
    integral_ofReal
  have h4 : (∫ x in Work.Diff.STE.unitCube, ((Work.Diff.STE.pdR i f x * g x : ℝ) : ℂ))
      = ((∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.pdR i f x * g x : ℝ) : ℂ) :=
    integral_ofReal
  rw [h3, h4] at hIBP
  apply Complex.ofReal_injective
  rw [Complex.ofReal_neg]
  exact hIBP

/-- **The derivative of `s ↦ |s| ^ (p - 2) * s`, `p ≥ 2`.**  Its value is `(p - 1) |s| ^ (p - 2)`;
at the origin the case `p = 2` gives the identity map and the case `p > 2` gives derivative `0`. -/
private lemma abs_rpow_mul_deriv (p : ℝ) (hp : 2 ≤ p) (s : ℝ) :
    HasDerivAt (fun s : ℝ => |s| ^ (p - 2) * s) ((p - 1) * |s| ^ (p - 2)) s := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · -- `s < 0`: on a neighbourhood of `s` the function is `t ↦ -((-t) ^ (p - 1))`
    have hderiv : HasDerivAt (fun t : ℝ => -((-t) ^ (p - 1))) ((p - 1) * |s| ^ (p - 2)) s := by
      have hc : HasDerivAt (fun t : ℝ => -t) (-1) s := hasDerivAt_neg s
      have hcomp := (Real.hasDerivAt_rpow_const (x := -s) (p := p - 1)
        (Or.inl (by linarith : -s ≠ 0))).comp s hc
      refine hcomp.neg.congr_deriv ?_
      rw [abs_of_neg hs]
      ring_nf
    refine hderiv.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds hs] with t ht
    have ht' : t < 0 := ht
    rw [abs_of_neg ht']
    have hu : (0 : ℝ) < -t := by linarith
    have hkey : (-t) ^ (p - 2) * (-t) = (-t) ^ (p - 1) := by
      rw [← Real.rpow_add_one (ne_of_gt hu) (p - 2), show p - 2 + 1 = p - 1 by ring]
    calc (-t) ^ (p - 2) * t = (-t) ^ (p - 2) * (-(-t)) := by ring
      _ = -((-t) ^ (p - 2) * (-t)) := by rw [mul_neg]
      _ = -((-t) ^ (p - 1)) := by rw [hkey]
  · -- `s = 0`
    rcases eq_or_lt_of_le hp with h2 | h2
    · -- `p = 2`: the function is the identity
      subst h2
      have hfun : (fun t : ℝ => |t| ^ ((2 : ℝ) - 2) * t) = fun t => t := by
        funext t; rw [show (2 : ℝ) - 2 = 0 by norm_num, Real.rpow_zero, one_mul]
      rw [hfun]
      have hc : ((2 : ℝ) - 1) * |(0 : ℝ)| ^ ((2 : ℝ) - 2) = 1 := by norm_num
      rw [hc]
      exact hasDerivAt_id 0
    · -- `p > 2`: the difference quotient `|t| ^ (p-2)` tends to `0`
      have hzero : (p - 1) * |(0 : ℝ)| ^ (p - 2) = 0 := by
        rw [abs_zero, Real.zero_rpow (ne_of_gt (by linarith : 0 < p - 2)), mul_zero]
      rw [hzero]
      rw [hasDerivAt_iff_tendsto_slope]
      have hcont : ContinuousAt (fun t : ℝ => |t| ^ (p - 2)) 0 :=
        ((Real.continuous_rpow_const (by linarith : 0 ≤ p - 2)).comp continuous_abs).continuousAt
      have hval : |(0 : ℝ)| ^ (p - 2) = 0 := by
        rw [abs_zero, Real.zero_rpow (ne_of_gt (by linarith : 0 < p - 2))]
      have htend : Filter.Tendsto (fun t : ℝ => |t| ^ (p - 2))
          (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds 0) := by
        have h := hcont.tendsto
        rw [hval] at h
        exact h.mono_left nhdsWithin_le_nhds
      refine htend.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      rw [slope_def_field]
      simp only [sub_zero]
      rw [show |(0 : ℝ)| ^ (p - 2) * 0 = 0 by ring, sub_zero, eq_div_iff ht0]
  · -- `0 < s`: on a neighbourhood of `s` the function is `t ↦ t ^ (p - 1)`
    have hderiv : HasDerivAt (fun t : ℝ => t ^ (p - 1)) ((p - 1) * |s| ^ (p - 2)) s := by
      have hr := Real.hasDerivAt_rpow_const (x := s) (p := p - 1) (Or.inl (ne_of_gt hs))
      refine hr.congr_deriv ?_
      rw [abs_of_pos hs]
      ring_nf
    refine hderiv.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    have ht' : 0 < t := ht
    rw [abs_of_pos ht']
    rw [← Real.rpow_add_one (ne_of_gt ht') (p - 2), show p - 2 + 1 = p - 1 by ring]

/-- **`s ↦ |s| ^ (p - 2) * s` is `C¹` for `p ≥ 2`.** -/
private lemma abs_rpow_mul_contDiff (p : ℝ) (hp : 2 ≤ p) :
    ContDiff ℝ 1 (fun s : ℝ => |s| ^ (p - 2) * s) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (abs_rpow_mul_deriv p hp s).differentiableAt, ?_⟩
  have hderiv : deriv (fun s : ℝ => |s| ^ (p - 2) * s)
      = fun s => (p - 1) * |s| ^ (p - 2) := by
    funext s; exact (abs_rpow_mul_deriv p hp s).deriv
  rw [hderiv]
  exact continuous_const.mul
    ((Real.continuous_rpow_const (by linarith : 0 ≤ p - 2)).comp continuous_abs)

/-- **Periodic integration by parts with a real power.**  For a real-valued `C^∞` `1`-periodic `g`
on the unit torus `ι → ℝ` and a real exponent `p ≥ 2`,

`∫_{cube} |∂ᵢ g|^p = -(p-1) ∫_{cube} g · |∂ᵢ g|^{p-2} · ∂ᵢ∂ᵢ g`,

where `∂ᵢ = Work.Diff.STE.pdR i` is the directional derivative along `eᵢ` and the integrals are
over the half-open unit cube `Work.Diff.STE.unitCube` (a fundamental domain for the periodicity).

Route.  Set `w = pdR i g` and `φ s = |s| ^ (p - 2) * s`, which is `C¹` on `ℝ` for `p ≥ 2`
(its derivative is `(p-1) |s|^(p-2)`, and `φ` is `C¹` at `0` because `|s|^{p-1} = o(s)` there
when `p > 2`; for `p = 2`, `φ = id`): this is `abs_rpow_mul_contDiff`, with derivative
`abs_rpow_mul_deriv`.  Then `f := φ ∘ w` is `C¹` and periodic in the direction `i`, and the
real-valued periodic integration by parts `integral_mul_pdR_eq_neg_aux`
(`∫ f ∂ᵢ g = -∫ (∂ᵢ f) g`) gives the claim, since `f · ∂ᵢg = |w|^p` and
`∂ᵢ f = (p-1)|w|^(p-2) · ∂ᵢ∂ᵢg`. -/
theorem ibp_rpow {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (p : ℝ) (hp : 2 ≤ p)
    (g : (ι → ℝ) → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : Work.Diff.STE.Periodic1 g) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), |Work.Diff.STE.pdR i g x| ^ p
      = -((p - 1) * ∫ x in Work.Diff.STE.unitCube (ι := ι),
          g x * |Work.Diff.STE.pdR i g x| ^ (p - 2) * Work.Diff.STE.pdR i (Work.Diff.STE.pdR i g) x) := by
  -- `w = ∂ᵢ g` and `φ s = |s| ^ (p-2) * s`; the claim follows from the periodic integration by
  -- parts `∫ f ∂ᵢg = -∫ (∂ᵢf) g` applied to `f = φ ∘ w`.
  set w : (ι → ℝ) → ℝ := Work.Diff.STE.pdR i g with hw
  set φ : ℝ → ℝ := fun s => |s| ^ (p - 2) * s with hφ
  -- finite smoothness of `g`
  have hg2 : ContDiff ℝ (((2 : ℕ)) : WithTop ℕ∞) g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg1 : ContDiff ℝ (((1 : ℕ)) : WithTop ℕ∞) g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  -- `w` is `C¹`
  have hw1 : ContDiff ℝ (((1 : ℕ)) : WithTop ℕ∞) w := by
    rw [hw]
    have h : ContDiff ℝ (((1 : ℕ)) : WithTop ℕ∞) (fderiv ℝ g) :=
      hg2.fderiv_right (m := 1) (le_refl _)
    have h3 : ContDiff ℝ (((1 : ℕ)) : WithTop ℕ∞)
        (fun x => (fderiv ℝ g x) (Pi.single i (1 : ℝ))) := by
      have h4 := (ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).contDiff.comp h
      simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using h4
    exact h3
  -- `φ` is `C¹`
  have hφC1 : ContDiff ℝ (((1 : ℕ)) : WithTop ℕ∞) φ :=
    show ContDiff ℝ (((1 : ℕ)) : WithTop ℕ∞) (fun s : ℝ => |s| ^ (p - 2) * s)
      from abs_rpow_mul_contDiff p hp
  -- hence `f = φ ∘ w` is `C¹`
  have hF1 : ContDiff ℝ (((1 : ℕ)) : WithTop ℕ∞) (fun x => φ (w x)) := by
    change ContDiff ℝ (((1 : ℕ)) : WithTop ℕ∞) (φ ∘ w)
    exact hφC1.comp hw1
  -- `w` is periodic in the direction `i` (derivative of a periodic function)
  have hgd : Differentiable ℝ g := hg2.differentiable (by norm_num)
  have hwper : Work.Diff.STE.PeriodicIn i w := by
    rw [hw]
    intro x
    have hshift : fderiv ℝ (fun y : ι → ℝ => y + Pi.single i 1) x
        = ContinuousLinearMap.id ℝ (ι → ℝ) := by simp
    have hcomp : fderiv ℝ (fun y : ι → ℝ => g (y + Pi.single i 1)) x = fderiv ℝ g x := by
      rw [show (fun y : ι → ℝ => g (y + Pi.single i 1)) = g from funext (hper i)]
    have h2 : fderiv ℝ (fun y : ι → ℝ => g (y + Pi.single i 1)) x
        = (fderiv ℝ g (x + Pi.single i 1)).comp
            (fderiv ℝ (fun y : ι → ℝ => y + Pi.single i 1) x) :=
      fderiv_comp x hgd.differentiableAt (by fun_prop)
    rw [hcomp, hshift, ContinuousLinearMap.comp_id] at h2
    simp only [pdR]
    rw [← h2]
  have hFper : Work.Diff.STE.PeriodicIn i (fun x => φ (w x)) := by
    intro x
    change φ (w (x + Pi.single i 1)) = φ (w x)
    rw [hwper x]
  -- periodic integration by parts
  have hibp := integral_mul_pdR_eq_neg_aux i (fun x => φ (w x)) g hF1 hg1 hFper (hper i)
  -- `φ (w x) * w x = |w x| ^ p`
  have hs : ∀ x : ι → ℝ, w x * w x = |w x| ^ (((2 : ℕ)) : ℝ) := by
    intro x
    rw [← sq, ← sq_abs, Real.rpow_natCast]
  have hpt1 : ∀ x : ι → ℝ, φ (w x) * w x = |w x| ^ p := by
    intro x
    change (|w x| ^ (p - 2) * w x) * w x = |w x| ^ p
    rw [mul_assoc, hs x]
    rw [← Real.rpow_add' (x := |w x|) (y := p - 2) (z := (((2 : ℕ)) : ℝ)) (abs_nonneg (w x))
      (by push_cast; linarith)]
    rw [show p - 2 + (((2 : ℕ)) : ℝ) = p by push_cast; ring]
  -- `pdR i (φ ∘ w) x = (p-1) |w x|^(p-2) ∂ᵢ w x`
  have hpt2 : ∀ x : ι → ℝ,
      Work.Diff.STE.pdR i (fun y => φ (w y)) x
        = (p - 1) * |w x| ^ (p - 2) * Work.Diff.STE.pdR i w x := by
    intro x
    have hφf : fderiv ℝ φ (w x)
        = ContinuousLinearMap.toSpanSingleton ℝ ((p - 1) * |w x| ^ (p - 2)) :=
      show fderiv ℝ (fun s : ℝ => |s| ^ (p - 2) * s) (w x) = _
        from (abs_rpow_mul_deriv p hp (w x)).hasFDerivAt.fderiv
    have hd1 : DifferentiableAt ℝ φ (w x) := (abs_rpow_mul_deriv p hp (w x)).differentiableAt
    have hd2 : DifferentiableAt ℝ w x := hw1.differentiable_one.differentiableAt
    change (fderiv ℝ (φ ∘ w) x) (Pi.single i 1)
      = (p - 1) * |w x| ^ (p - 2) * (fderiv ℝ w x) (Pi.single i 1)
    rw [fderiv_comp x hd1 hd2, ContinuousLinearMap.comp_apply, hφf,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  -- rewrite the two integrands
  have hL : (∫ x in Work.Diff.STE.unitCube, φ (w x) * w x)
      = ∫ x in Work.Diff.STE.unitCube, |w x| ^ p := by
    rw [show (fun x : ι → ℝ => φ (w x) * w x) = (fun x => |w x| ^ p) from funext hpt1]
  have hR : (∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.pdR i (fun x => φ (w x)) x * g x)
      = (p - 1) * ∫ x in Work.Diff.STE.unitCube,
          g x * |w x| ^ (p - 2) * Work.Diff.STE.pdR i w x := by
    rw [show (fun x : ι → ℝ => Work.Diff.STE.pdR i (fun x => φ (w x)) x * g x)
        = (fun x => (p - 1) * (g x * |w x| ^ (p - 2) * Work.Diff.STE.pdR i w x))
        from funext (fun x => by rw [hpt2 x]; ring)]
    exact MeasureTheory.integral_const_mul _ _
  rw [← hw] at hibp
  rw [hL] at hibp
  rw [hR] at hibp
  exact hibp

end Work.Diff.STE.GN
