/-
# The Koebe derivative bound for the inverse Böttcher coordinate

For a parameter `c` whose dynamical Böttcher coordinate `φ` exists (`IsDynBottcher c φ`, the
dynamical data being `hN : Work.EL.DynB c φ`), let `Ψ = Work.ELRig.invBottcher hN` be the
inverse Böttcher coordinate: the homeomorphism inverse of `φ`, viewed as a total function.  It is
holomorphic and injective on the exterior disc `{w | 1 < ‖w‖}` and maps that disc into the
escaping set (`Work.ELRig.invBottcher_spec`).

This file proves the **Koebe derivative (one-quarter) bound** for `Ψ`:

`‖Ψ'(w)‖ (‖w‖ - 1) / 4 ≤ ‖y - Ψ w‖` for every `w` with `1 < ‖w‖` and every `y` outside the
escaping set.

Since the Euclidean disc `B(w, ‖w‖-1)` is contained in the exterior disc, the elementary
"local" form of Koebe's quarter theorem — the image of `B(w, r)` under a univalent map contains
the disc of radius `|f'(w)| r / 4` around the image of the centre — applies, and every point of
`Ψ '' B(w, ‖w‖ - 1)` is escaping, whereas `y` is not.  The local form is derived here from the
second-coefficient bound `‖f''(0)‖ ≤ 4`
(`Work.LandLeaves.koebeDerivAux.bieberbachSecondCoeff`) by the classical
Koebe-transform argument.

## Main results

* `Work.LandLeaves.kdB_koebeQuarter` : Koebe's quarter theorem for a univalent map on the unit
  ball (the `‖deriv f 0‖/4` form);
* `Work.LandLeaves.koebeDerivBound` : the derivative bound for the inverse Böttcher coordinate.
-/
import Mathlib
import Submission.Work.LandLeaves.bottcherInverse
import Submission.Work.LandLeaves.koebeDerivAux.bieberbachSecondCoeff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Metric Set

noncomputable section

/-! ## Koebe's quarter theorem from Bieberbach's second-coefficient bound

The route is the classical one.  After an affine reduction to the normalisation
`f 0 = 0`, `deriv f 0 = 1`, an omitted value `w` produces the Koebe transform
`z ↦ w f z / (w - f z)`, again normalised and univalent, with second derivative `f''(0) + 2/w`;
applying `‖f''(0)‖ ≤ 4` (`Work.LandLeaves.koebeDerivAux.bieberbachSecondCoeff`) to both `f` and its transform gives
`‖w‖ ≥ 1/4`.  The helpers below are named with the `kdB_` prefix so as not to collide with the
similarly named copies of this argument living in the sibling stubs
`Work.LandLeaves.koebeQuarter` and `Work.LandLeaves.rayAccum_subset_fixp`. -/

/-- `iteratedDeriv 2 g 0 = deriv (deriv g) 0`. -/
theorem kdB_iteratedDeriv_two_eq (g : ℂ → ℂ) : iteratedDeriv 2 g 0 = deriv (deriv g) 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]

/-- First derivative at `0` of the Koebe transform of a normalised univalent `f`. -/
theorem kdB_deriv_koebeTransform (f : ℂ → ℂ) (w : ℂ) (hw : w ≠ 0) (h0 : f 0 = 0)
    (h1 : deriv f 0 = 1) (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∀ z ∈ Metric.ball 0 1, f z ≠ w) :
    deriv (fun z => w * f z / (w - f z)) 0 = 1 := by
  have hball : Metric.ball (0 : ℂ) 1 ∈ nhds 0 := Metric.ball_mem_nhds 0 one_pos
  have hf0' : DifferentiableAt ℂ f 0 := hd.differentiableAt hball
  rw [show (fun z => w * f z / (w - f z)) = ((fun z => w * f z)/(fun z => (w - f z))) from rfl]
  rw [deriv_div (x := 0) (c := fun z => w * f z) (d := fun z => (w - f z))
      (by fun_prop) (by fun_prop) (by simpa [h0] using hw)]
  have h1' : deriv (fun z : ℂ => w * f z) 0 = w := by
    rw [deriv_const_mul w hf0', h1, mul_one]
  have h2' : deriv (fun z : ℂ => w - f z) 0 = -1 := by
    rw [deriv_const_sub w, h1]
  rw [h1', h2', h0]
  field_simp
  ring

/-- Second derivative at `0` of the Koebe transform of a normalised univalent `f`. -/
theorem kdB_iteratedDeriv_two_koebeTransform (f : ℂ → ℂ) (w : ℂ) (hw : w ≠ 0) (h0 : f 0 = 0)
    (h1 : deriv f 0 = 1) (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∀ z ∈ Metric.ball 0 1, f z ≠ w) :
    iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0 = iteratedDeriv 2 f 0 + 2 / w := by
  have hball : Metric.ball (0 : ℂ) 1 ∈ nhds 0 := Metric.ball_mem_nhds 0 one_pos
  have hfd0 : DifferentiableAt ℂ f 0 := hd.differentiableAt hball
  set h : ℂ → ℂ := fun z => w * f z / (w - f z) with hh
  have hderiv : deriv h =ᶠ[nhds 0] (fun z => w^2 * deriv f z / (w - f z)^2) := by
    filter_upwards [hball] with z hz
    have hfz : DifferentiableAt ℂ f z := hd.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have hne' : w - f z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hne z hz))
    rw [hh]
    rw [show (fun z => w * f z / (w - f z)) = ((fun z => w * f z)/(fun z => (w - f z))) from rfl]
    rw [deriv_div (x := z) (c := fun z => w * f z) (d := fun z => (w - f z))
      (by fun_prop) (by fun_prop) hne']
    have ha : deriv (fun z => w * f z) z = w * deriv f z := deriv_const_mul w hfz
    have hb : deriv (fun z => w - f z) z = -deriv f z := deriv_const_sub w
    rw [ha, hb]; field_simp; ring
  rw [kdB_iteratedDeriv_two_eq h, hderiv.deriv_eq]
  have hDerivf : DifferentiableAt ℂ (deriv f) 0 :=
    (hd.deriv Metric.isOpen_ball).differentiableAt hball
  have hA : DifferentiableAt ℂ (fun z => w^2 * deriv f z) 0 := by fun_prop
  have hB : DifferentiableAt ℂ (fun z => (w - f z)^2) 0 :=
    ((differentiableAt_const w).sub hfd0).pow 2
  have hnz : (w - f 0)^2 ≠ 0 := by rw [h0, sub_zero]; exact pow_ne_zero 2 hw
  rw [show (fun z => w^2 * deriv f z / (w - f z)^2)
        = ((fun z => w^2 * deriv f z)/(fun z => (w - f z)^2)) from rfl]
  rw [deriv_div (x := 0) (c := fun z => w^2 * deriv f z) (d := fun z => (w - f z)^2) hA hB hnz]
  have hdA : deriv (fun z => w^2 * deriv f z) 0 = w^2 * iteratedDeriv 2 f 0 := by
    rw [deriv_const_mul (w^2) hDerivf]
    exact congrArg (fun t => w^2 * t) (kdB_iteratedDeriv_two_eq f).symm
  have hdB : deriv (fun z => (w - f z)^2) 0 = -2 * w := by
    have h1' : DifferentiableAt ℂ (fun y : ℂ => (w - y)^2) (f 0) := by fun_prop
    rw [show (fun z : ℂ => (w - f z)^2) = (fun y : ℂ => (w - y)^2) ∘ f from rfl]
    rw [deriv_comp _ h1' hfd0]
    have h2 : deriv (fun y : ℂ => (w - y)^2) (f 0) = -2 * w := by
      have h3 : DifferentiableAt ℂ (fun y : ℂ => y^2) (w - f 0) := by fun_prop
      have h4 : DifferentiableAt ℂ (fun y : ℂ => w - y) (f 0) := by fun_prop
      rw [show (fun y : ℂ => (w - y)^2) = (fun y : ℂ => y^2) ∘ (fun y : ℂ => w - y) from rfl]
      rw [deriv_comp _ h3 h4]
      have h5 : deriv (fun y : ℂ => y^2) (w - f 0) = 2 * (w - f 0) := by
        rw [deriv_fun_pow differentiableAt_id 2, deriv_id'']; norm_num
      have h6 : deriv (fun y : ℂ => w - y) (f 0) = -1 := by
        simpa using deriv_const_sub (x := f 0) (f := fun y : ℂ => y) w
      rw [h5, h6, h0]; ring
    rw [h2, h1]; ring
  rw [hdA, hdB, h0, h1]
  field_simp
  ring

theorem kdB_differentiableOn_koebeTransform (f : ℂ → ℂ) (w : ℂ)
    (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∀ z ∈ Metric.ball 0 1, f z ≠ w) :
    DifferentiableOn ℂ (fun z => w * f z / (w - f z)) (Metric.ball 0 1) := by
  rw [show (fun z => w * f z / (w - f z)) = ((fun z => w * f z)/(fun z => (w - f z))) from rfl]
  exact (hd.const_mul w).div ((differentiableOn_const w).sub hd)
    (fun z hz => sub_ne_zero.mpr (Ne.symm (hne z hz)))

theorem kdB_injOn_koebeTransform (f : ℂ → ℂ) (w : ℂ) (hw : w ≠ 0)
    (hf : Set.InjOn f (Metric.ball 0 1)) (hne : ∀ z ∈ Metric.ball 0 1, f z ≠ w) :
    Set.InjOn (fun z => w * f z / (w - f z)) (Metric.ball 0 1) := by
  intro z1 hz1 z2 hz2 heq
  have hne1 : w - f z1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (hne z1 hz1))
  have hne2 : w - f z2 ≠ 0 := sub_ne_zero.mpr (Ne.symm (hne z2 hz2))
  have hdiv : f z1 / (w - f z1) = f z2 / (w - f z2) := by
    have := congrArg (fun t => w⁻¹ * t) heq
    simpa only [← mul_div_assoc, inv_mul_cancel_left₀ hw] using this
  have hcross : f z1 * (w - f z2) = f z2 * (w - f z1) := by
    rw [div_eq_div_iff hne1 hne2] at hdiv; exact hdiv
  have : w * f z1 = w * f z2 := by linear_combination hcross
  exact hf hz1 hz2 (mul_left_cancel₀ hw this)

theorem kdB_koebeTransform_zero (f : ℂ → ℂ) (w : ℂ) (h0 : f 0 = 0) :
    (fun z => w * f z / (w - f z)) 0 = 0 := by simp [h0]

/-- **Koebe's quarter theorem, normalised form.** -/
theorem kdB_koebeQuarter_normalized (f : ℂ → ℂ) (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf : Set.InjOn f (Metric.ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    Metric.ball 0 (1/4 : ℝ) ⊆ f '' Metric.ball 0 1 := by
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  by_contra hmem
  have hne : ∀ z ∈ Metric.ball 0 1, f z ≠ w := by
    intro z hz hzw; exact hmem ⟨z, hz, hzw⟩
  have hw0 : w ≠ 0 := by
    intro hw0; exact hmem ⟨0, by simp [zero_lt_one], by rw [h0, hw0]⟩
  have hd' := kdB_differentiableOn_koebeTransform f w hd hne
  have hf' := kdB_injOn_koebeTransform f w hw0 hf hne
  have h0' := kdB_koebeTransform_zero f w h0
  have h1' := kdB_deriv_koebeTransform f w hw0 h0 h1 hd hne
  have h2' := kdB_iteratedDeriv_two_koebeTransform f w hw0 h0 h1 hd hne
  have hb1 := Work.LandLeaves.koebeDerivAux.bieberbachSecondCoeff f hd hf h0 h1
  have hb2 := Work.LandLeaves.koebeDerivAux.bieberbachSecondCoeff (fun z => w * f z / (w - f z)) hd' hf' h0' h1'
  have hnorm : ‖(2 : ℂ)/w‖ ≤ 8 := by
    have : (2 : ℂ)/w = iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0 - iteratedDeriv 2 f 0 := by
      rw [h2']; ring
    rw [this]
    calc ‖_ - _‖ ≤ ‖iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0‖ + ‖iteratedDeriv 2 f 0‖ :=
          norm_sub_le _ _
      _ ≤ 4 + 4 := add_le_add hb2 hb1
      _ = 8 := by norm_num
  rw [norm_div, Complex.norm_ofNat] at hnorm
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have : (1:ℝ)/4 ≤ ‖w‖ := by
    rw [div_le_iff₀ hwpos] at hnorm
    linarith
  linarith

/-- **Koebe's quarter theorem** (un-normalised form): for a univalent holomorphic `f` on the
unit ball with `f 0 = 0`, the ball of radius `‖deriv f 0‖/4` about `0` is contained in the
image. -/
theorem kdB_koebeQuarter (f : ℂ → ℂ) (hf : Set.InjOn f (Metric.ball 0 1))
    (hd : DifferentiableOn ℂ f (Metric.ball 0 1)) (h0 : f 0 = 0) :
    Metric.ball 0 (‖deriv f 0‖ / 4) ⊆ f '' Metric.ball 0 1 := by
  rcases eq_or_ne (deriv f 0) 0 with hc | hc
  · rw [hc, norm_zero, zero_div]
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact absurd hz (not_lt.mpr (norm_nonneg z))
  · set c : ℂ := deriv f 0 with hcdef
    set g : ℂ → ℂ := fun z => c⁻¹ * f z with hgdef
    have hball : Metric.ball (0 : ℂ) 1 ∈ nhds 0 := Metric.ball_mem_nhds 0 one_pos
    have hgd : DifferentiableOn ℂ g (Metric.ball 0 1) := hd.const_mul c⁻¹
    have hgj : Set.InjOn g (Metric.ball 0 1) := by
      intro z1 hz1 z2 hz2 heq
      exact hf hz1 hz2 (mul_left_cancel₀ (inv_ne_zero hc) heq)
    have hg0 : g 0 = 0 := by simp [hgdef, h0]
    have hg1 : deriv g 0 = 1 := by
      rw [hgdef, deriv_const_mul c⁻¹ (hd.differentiableAt hball)]
      rw [← hcdef]; field_simp
    have hnorm := kdB_koebeQuarter_normalized g hgd hgj hg0 hg1
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hwc : w / c ∈ Metric.ball (0 : ℂ) (1/4 : ℝ) := by
      rw [Metric.mem_ball, dist_zero_right, norm_div]
      rw [div_lt_iff₀ hcpos]; linarith
    obtain ⟨z, hz, hze⟩ := hnorm hwc
    refine ⟨z, hz, ?_⟩
    have hze' : f z = w := by
      rw [hgdef] at hze
      rw [div_eq_mul_inv] at hze
      have hzz : c⁻¹ * f z = w * c⁻¹ := hze
      have h2 : c⁻¹ * f z = c⁻¹ * w := by rw [hzz, mul_comm w c⁻¹]
      exact mul_left_cancel₀ (inv_ne_zero hc) h2
    exact hze'

/-! ## The derivative bound for the inverse Böttcher coordinate -/

theorem koebeDerivBound {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hφ : Work.ParamRays.IsDynBottcher c φ) :
    ∀ w : ℂ, 1 < ‖w‖ → ∀ y : ℂ, y ∉ Work.ParamRays.escapingSet c →
      ‖deriv (Work.ELRig.invBottcher hN) w‖ * (‖w‖ - 1) / 4 ≤ ‖y - Work.ELRig.invBottcher hN w‖ := by
  intro w hw y hy
  have han : AnalyticOnNhd ℂ φ (Work.Bottcher.EscapeSet c) := Work.ELRig.analyticOnNhd_dynBottcher hφ
  have hΨinj : ∀ a b : ℂ, 1 < ‖a‖ → 1 < ‖b‖ →
      Work.ELRig.invBottcher hN a = Work.ELRig.invBottcher hN b → a = b := by
    intro a b ha hb hab
    rw [← (Work.ELRig.invBottcher_spec hN ha).2, ← (Work.ELRig.invBottcher_spec hN hb).2, hab]
  set r : ℝ := ‖w‖ - 1 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  set G : ℂ → ℂ := fun ζ => Work.ELRig.invBottcher hN (w + (r : ℂ) * ζ) - Work.ELRig.invBottcher hN w with hGdef
  have hmem : ∀ ζ ∈ ball 0 1, 1 < ‖w + (r : ℂ) * ζ‖ := by
    intro ζ hζ
    rw [mem_ball, dist_zero_right] at hζ
    have h1 : ‖(r : ℂ) * ζ‖ = r * ‖ζ‖ := by
      rw [norm_mul, show ‖(r : ℂ)‖ = r by simp [abs_of_pos hrpos]]
    have h2 : ‖w + (r : ℂ) * ζ‖ ≥ ‖w‖ - ‖(r : ℂ) * ζ‖ := by
      have h3 := norm_sub_le (w + (r:ℂ)*ζ) ((r:ℂ)*ζ)
      have h4 : w + (r:ℂ)*ζ - (r:ℂ)*ζ = w := by ring
      rw [h4] at h3
      linarith
    have h5 : r * ‖ζ‖ < r := mul_lt_of_lt_one_right hrpos hζ
    rw [h1] at h2
    rw [hrdef] at h2 h5 ⊢
    linarith
  have hG0 : G 0 = 0 := by simp [hGdef]
  have hGd : DifferentiableOn ℂ G (ball 0 1) := by
    intro ζ hζ
    have hΨat : DifferentiableAt ℂ (Work.ELRig.invBottcher hN) (w + (r : ℂ) * ζ) :=
      (Work.ELRig.analyticAt_invBottcher hN han (hmem ζ hζ)).differentiableAt
    have hlin : DifferentiableAt ℂ (fun ζ : ℂ => w + (r : ℂ) * ζ) ζ := by fun_prop
    have hh := (hΨat.comp ζ hlin).sub (differentiableAt_const (Work.ELRig.invBottcher hN w))
    exact hh.differentiableWithinAt
  have hGinj : InjOn G (ball 0 1) := by
    intro ζ hζ ζ' hζ' heq
    have hΨeq : Work.ELRig.invBottcher hN (w + (r:ℂ)*ζ) = Work.ELRig.invBottcher hN (w + (r:ℂ)*ζ') := by
      have h2 : Work.ELRig.invBottcher hN (w + (r:ℂ)*ζ) - Work.ELRig.invBottcher hN w
          = Work.ELRig.invBottcher hN (w + (r:ℂ)*ζ') - Work.ELRig.invBottcher hN w := heq
      exact sub_left_inj.mp h2
    have hweq : w + (r:ℂ)*ζ = w + (r:ℂ)*ζ' := hΨinj _ _ (hmem ζ hζ) (hmem ζ' hζ') hΨeq
    have h3 : (r:ℂ)*ζ = (r:ℂ)*ζ' := add_left_cancel hweq
    exact mul_left_cancel₀ (by exact_mod_cast hrpos.ne' : (r:ℂ) ≠ 0) h3
  have hGderiv : deriv G 0 = (r : ℂ) * deriv (Work.ELRig.invBottcher hN) w := by
    have hlin : HasDerivAt (fun ζ : ℂ => w + (r:ℂ)*ζ) (r:ℂ) 0 := by
      have h2 : HasDerivAt (fun ζ : ℂ => (r:ℂ)*ζ) (r:ℂ) 0 := by
        simpa using (hasDerivAt_id (0:ℂ)).const_mul (r:ℂ)
      simpa using h2.const_add w
    have hout : HasDerivAt (Work.ELRig.invBottcher hN) (deriv (Work.ELRig.invBottcher hN) w)
        (w + (r:ℂ)*0) := by
      simpa using (Work.ELRig.analyticAt_invBottcher hN han (hmem 0 (by simp))).differentiableAt.hasDerivAt
    have hcomp : HasDerivAt (fun ζ : ℂ => Work.ELRig.invBottcher hN (w + (r:ℂ)*ζ))
        (deriv (Work.ELRig.invBottcher hN) w * (r:ℂ)) 0 := by
      have hh := hout.comp 0 hlin
      simpa [Function.comp_def] using hh
    have hG : HasDerivAt G (deriv (Work.ELRig.invBottcher hN) w * (r:ℂ)) 0 := by
      have hh := hcomp.sub_const (Work.ELRig.invBottcher hN w)
      simpa [hGdef] using hh
    rw [hG.deriv, mul_comm]
  have hnorm : ‖deriv G 0‖ = r * ‖deriv (Work.ELRig.invBottcher hN) w‖ := by
    rw [hGderiv, norm_mul, show ‖(r:ℂ)‖ = r by simp [abs_of_pos hrpos]]
  have hnotmem : y - Work.ELRig.invBottcher hN w ∉ G '' ball 0 1 := by
    rintro ⟨ζ, hζ, hζeq⟩
    have h1 : 1 < ‖w + (r:ℂ)*ζ‖ := hmem ζ hζ
    have h2 : Work.ELRig.invBottcher hN (w + (r:ℂ)*ζ) ∈ Work.ParamRays.escapingSet c := by
      rw [← Work.Bottcher.Contraction.escapeSet_eq_escapingSet c]
      exact (Work.ELRig.invBottcher_spec hN h1).1
    have h3 : Work.ELRig.invBottcher hN (w + (r:ℂ)*ζ) = y := by
      have h4 : Work.ELRig.invBottcher hN (w + (r:ℂ)*ζ) - Work.ELRig.invBottcher hN w
          = y - Work.ELRig.invBottcher hN w := hζeq
      exact sub_left_inj.mp h4
    exact hy (h3 ▸ h2)
  have hkq := kdB_koebeQuarter G hGinj hGd hG0
  have hkey : ‖deriv G 0‖ / 4 ≤ ‖y - Work.ELRig.invBottcher hN w‖ := by
    by_contra hcon
    push Not at hcon
    exact hnotmem (hkq (by rw [mem_ball, dist_zero_right]; exact hcon))
  rw [hnorm] at hkey
  calc ‖deriv (Work.ELRig.invBottcher hN) w‖ * r / 4
      = r * ‖deriv (Work.ELRig.invBottcher hN) w‖ / 4 := by ring
    _ ≤ ‖y - Work.ELRig.invBottcher hN w‖ := hkey

end

end Work.LandLeaves
