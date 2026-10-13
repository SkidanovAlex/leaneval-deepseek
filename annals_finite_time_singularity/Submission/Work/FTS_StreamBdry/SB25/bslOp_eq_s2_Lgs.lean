/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS_StreamBdry.SB25.bslOp_eq_s2_Lgs` (leaf E3 of the SB2/SB5 plan)

The ground-state identity of the singular stream-boundary problem: for `(z,θ)` in the open
quadrant `Qd` and `Q` of class `C²` at `(z,θ)`,

`bslOp α Q z θ = sin(2θ) · Lgs α (Q / sin 2θ) z θ`,

where `Lgs` is the operator on the ground-state transform `u = Q/sin 2θ` (the version of
`bslOp` with no zero-order and no mixed term), `Work.FTS_StreamBdry.SB25.Lgs`.

The verification is a pointwise computation.  Write `g := (sin 2θ)⁻¹`.  Since the factor
`sin 2θ'` depends only on the angular variable, the `D_z`-part of `Lgs` is just `1/g² = sin²2θ`
times the `pz`-part of `bslOp`, while the angular part

`-g·∂_θθu - (4 cos 2θ / sin 2θ - tan θ)·g·∂_θu`

expands, using `g' = -2cos 2θ / sin²2θ`, `g'' = 4/sin 2θ + 8 cos²2θ / sin³2θ`, into
`-∂_θθQ + tan θ·∂_θQ + (tan²θ - 5)Q = Lzero Q`, the last step being the elementary identity
`2·cot(2θ)·tan θ = 1 - tan²θ`.

The three facts that make the computation go through cleanly are
* `g·∂_θu = g'·Q + g·∂_θQ` (product rule on the angular slice),
* `sin 2θ · g = 1`, `sin 2θ · g' = -2cos 2θ / sin 2θ`,
  `sin 2θ · g'' = 4 + 8cos²2θ / sin²2θ` (clearing the denominators),
* `sin(2θ) ≠ 0` on the quadrant, so the angular slices of `Q` are differentiable there.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ### Auxiliary calculus -/

/-- Slice derivatives of a `C²` function. -/
private lemma p_slice_derivs {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry F) (z, θ)) :
    HasDerivAt (fun z' => F z' θ) (Work.Spaces.pz F z θ) z ∧
      HasDerivAt (fun θ' => F z θ') (Work.Spaces.pth F z θ) θ ∧
      HasDerivAt (fun z' => Work.Spaces.pz F z' θ) (Work.Spaces.pzIter 2 F z θ) z ∧
      HasDerivAt (fun θ' => Work.Spaces.pth F z θ') (Work.Spaces.pthIter 2 F z θ) θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry F) (z, θ) := h.differentiableAt (by norm_num)
  have hsl2 : ContDiffAt ℝ 2 (fun z' => F z' θ) z := by
    have h2 := h.comp z (ContDiffAt.prodMk contDiffAt_id contDiffAt_const)
    convert h2 using 1
    funext x; rfl
  have hsl2' : ContDiffAt ℝ 2 (fun θ' => F z θ') θ := by
    have h2 := h.comp θ (ContDiffAt.prodMk contDiffAt_const contDiffAt_id)
    convert h2 using 1
    funext x; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : HasDerivAt (fun z' : ℝ => Function.uncurry F (z', θ))
        ((fderiv ℝ (Function.uncurry F) (z, θ)) (1, 0)) z :=
      Work.Spaces.hasDerivAt_slice_fst hd.hasFDerivAt
    rw [Work.Spaces.pz_eq_fderiv hd]
    simpa only [Function.uncurry] using h1
  · have h1 : HasDerivAt (fun θ' : ℝ => Function.uncurry F (z, θ'))
        ((fderiv ℝ (Function.uncurry F) (z, θ)) (0, 1)) θ :=
      Work.Spaces.hasDerivAt_slice_snd hd.hasFDerivAt
    rw [Work.Spaces.pth_eq_fderiv hd]
    simpa only [Function.uncurry] using h1
  · have hder : ContDiffAt ℝ 1 (deriv (fun z' => F z' θ)) z :=
      hsl2.derivWithin (m := 1) (by norm_num)
    have h3 := (hder.differentiableAt (by norm_num)).hasDerivAt
    simpa only [Work.Spaces.pz, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h3
  · have hder : ContDiffAt ℝ 1 (deriv (fun θ' => F z θ')) θ :=
      hsl2'.derivWithin (m := 1) (by norm_num)
    have h3 := (hder.differentiableAt (by norm_num)).hasDerivAt
    simpa only [Work.Spaces.pth, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h3

/-- `pth` of `tan θ · F`. -/
private lemma p_pth_tan_mul {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry F) (z, θ)) (hc : Real.cos θ ≠ 0) :
    Work.Spaces.pth (fun z' θ' => Real.tan θ' * F z' θ') z θ
      = (1 / Real.cos θ ^ 2) * F z θ + Real.tan θ * Work.Spaces.pth F z θ := by
  have hslice : HasDerivAt (fun θ' => F z θ') (Work.Spaces.pth F z θ) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Function.uncurry F (z, θ'))
        ((fderiv ℝ (Function.uncurry F) (z, θ)) (0, 1)) θ :=
      Work.Spaces.hasDerivAt_slice_snd h.hasFDerivAt
    rw [Work.Spaces.pth_eq_fderiv h]
    simpa only [Function.uncurry] using h1
  have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := by
    have h1 : HasDerivAt Real.tan (deriv Real.tan θ) θ :=
      ((Real.differentiableAt_tan (x := θ)).mpr hc).hasDerivAt
    rwa [Real.deriv_tan] at h1
  have hmul : HasDerivAt (fun θ' => Real.tan θ' * F z θ')
      ((1 / Real.cos θ ^ 2) * F z θ + Real.tan θ * Work.Spaces.pth F z θ) θ :=
    htan.mul hslice
  rw [show Work.Spaces.pth (fun z' θ' => Real.tan θ' * F z' θ') z θ
      = deriv (fun θ' => Real.tan θ' * F z θ') θ from rfl, hmul.deriv]

/-! ### The factor `sin(2θ)⁻¹` and its derivatives -/

private def gs (θ : ℝ) : ℝ := (Real.sin (2 * θ))⁻¹
private def gs1 (θ : ℝ) : ℝ := -(2 * Real.cos (2 * θ)) / (Real.sin (2 * θ)) ^ 2
private def gs2 (θ : ℝ) : ℝ :=
  4 / Real.sin (2 * θ) + 8 * Real.cos (2 * θ) ^ 2 / (Real.sin (2 * θ)) ^ 3

private lemma sinSin {θ : ℝ} : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ'))
    (2 * Real.cos (2 * θ)) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h3 : HasDerivAt (Real.sin ∘ fun θ' : ℝ => 2 * θ') (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h2
  have h4 : Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) := by ring
  rw [h4] at h3
  convert h3 using 1
  funext x; rfl

private lemma cosCos {θ : ℝ} : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ'))
    (-2 * Real.sin (2 * θ)) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h3 : HasDerivAt (Real.cos ∘ fun θ' : ℝ => 2 * θ') (-Real.sin (2 * θ) * 2) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ h2
  have h4 : -Real.sin (2 * θ) * 2 = -2 * Real.sin (2 * θ) := by ring
  rw [h4] at h3
  convert h3 using 1
  funext x; rfl

private lemma hasDerivAt_gs {θ : ℝ} (h : Real.sin (2 * θ) ≠ 0) : HasDerivAt gs (gs1 θ) θ := by
  have hinv : HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ'))⁻¹)
      (-(2 * Real.cos (2 * θ)) / (Real.sin (2 * θ)) ^ 2) θ := sinSin.inv h
  show HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ'))⁻¹)
      (-(2 * Real.cos (2 * θ)) / (Real.sin (2 * θ)) ^ 2) θ
  exact hinv

private lemma hasDerivAt_gs1 {θ : ℝ} (h : Real.sin (2 * θ) ≠ 0) : HasDerivAt gs1 (gs2 θ) θ := by
  have hnum : HasDerivAt (fun θ' : ℝ => -(2 * Real.cos (2 * θ'))) (4 * Real.sin (2 * θ)) θ := by
    have h3 : HasDerivAt (fun y : ℝ => -2 * Real.cos (2 * y))
        (-2 * (-2 * Real.sin (2 * θ))) θ := cosCos.const_mul (-2 : ℝ)
    have h4 : -2 * (-2 * Real.sin (2 * θ)) = 4 * Real.sin (2 * θ) := by ring
    rw [h4] at h3
    convert h3 using 1
    funext y; ring
  have hden : HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ')) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (2 * Real.cos (2 * θ))) θ := sinSin.pow 2
  have hdenne : (Real.sin (2 * θ)) ^ 2 ≠ 0 := pow_ne_zero 2 h
  have hdiv := hnum.div hden hdenne
  have key : (4 * Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ 2
        - (-(2 * Real.cos (2 * θ))) * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (2 * Real.cos (2 * θ))))
        / ((Real.sin (2 * θ)) ^ 2) ^ 2 = gs2 θ := by
    rw [gs2]
    field_simp
    ring
  rw [key] at hdiv
  show HasDerivAt (fun θ' : ℝ => -(2 * Real.cos (2 * θ')) / (Real.sin (2 * θ')) ^ 2) (gs2 θ) θ
  exact hdiv

private lemma sin2_mul_gs (θ : ℝ) (h : Real.sin (2 * θ) ≠ 0) : Real.sin (2 * θ) * gs θ = 1 := by
  rw [gs]
  exact mul_inv_cancel₀ h

private lemma sin2_mul_gs1 (θ : ℝ) (h : Real.sin (2 * θ) ≠ 0) :
    Real.sin (2 * θ) * gs1 θ = -(2 * Real.cos (2 * θ)) / Real.sin (2 * θ) := by
  rw [gs1, div_eq_mul_inv]
  field_simp

private lemma sin2_mul_gs2 (θ : ℝ) (h : Real.sin (2 * θ) ≠ 0) :
    Real.sin (2 * θ) * gs2 θ
      = 4 + 8 * Real.cos (2 * θ) ^ 2 / Real.sin (2 * θ) ^ 2 := by
  rw [gs2, div_eq_mul_inv, div_eq_mul_inv]
  field_simp

/-! ### The main identity -/

theorem bslOp_eq_s2_Lgs (α : ℝ) (Q : ℝ → ℝ → ℝ) :
    Work.FTS_StreamBdry.SB25.BslOpEqS2Lgs α Q := by
  intro z θ hQd hQ
  rw [Work.Construction.Qd, Set.mem_prod] at hQd
  obtain ⟨hz, hθ⟩ := hQd
  simp only [Work.Construction.s2]
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_)
    linarith [hθ.2, Real.pi_pos]
  have hcos : Real.cos θ ≠ 0 := by
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2]⟩)
  have hsinθ : Real.sin θ ≠ 0 := by
    intro h0
    apply hsin
    rw [Real.sin_two_mul, h0]; ring
  have hcosθ : Real.cos θ ≠ 0 := by
    intro h0
    apply hsin
    rw [Real.sin_two_mul, h0]; ring
  obtain ⟨hQz, hQθ, hQzz, hQθθ⟩ := p_slice_derivs hQ
  have hQdiff : DifferentiableAt ℝ (Function.uncurry Q) (z, θ) := hQ.differentiableAt (by norm_num)
  have htan : Work.Spaces.pth (fun z' θ' => Real.tan θ' * Q z' θ') z θ
      = (1 / Real.cos θ ^ 2) * Q z θ + Real.tan θ * Work.Spaces.pth Q z θ :=
    p_pth_tan_mul hQdiff hcos
  set u : ℝ → ℝ → ℝ := fun z' θ' => Q z' θ' / Real.sin (2 * θ') with hu
  have hgs := hasDerivAt_gs hsin
  have hgs1 := hasDerivAt_gs1 hsin
  have hpzu : ∀ z' θ',
      Work.Spaces.pz u z' θ' = Work.Spaces.pz Q z' θ' / Real.sin (2 * θ') := by
    intro z' θ'
    rw [hu]
    simp only [Work.Spaces.pz]
    rw [deriv_div_const]
  have hpz2u : ∀ z' θ',
      Work.Spaces.pzIter 2 u z' θ' = Work.Spaces.pzIter 2 Q z' θ' / Real.sin (2 * θ') := by
    intro z' θ'
    show deriv (fun z'' => Work.Spaces.pz u z'' θ') z'
        = deriv (fun z'' => Work.Spaces.pz Q z'' θ') z' / Real.sin (2 * θ')
    rw [show (fun z'' => Work.Spaces.pz u z'' θ')
        = (fun z'' => Work.Spaces.pz Q z'' θ' / Real.sin (2 * θ')) from
      funext (fun z'' => hpzu z'' θ'), deriv_div_const]
  have hpthu_gen : ∀ θ', Real.sin (2 * θ') ≠ 0 → ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ') →
      Work.Spaces.pth u z θ' = gs θ' * Work.Spaces.pth Q z θ' + Q z θ' * gs1 θ' := by
    intro θ' h' hQ'
    have hd' : DifferentiableAt ℝ (fun θ'' => Q z θ'') θ' :=
      ((p_slice_derivs hQ').2.1).differentiableAt
    rw [hu]
    show deriv (fun θ'' => Q z θ'' / Real.sin (2 * θ'')) θ'
        = gs θ' * Work.Spaces.pth Q z θ' + Q z θ' * gs1 θ'
    rw [show (fun θ'' => Q z θ'' / Real.sin (2 * θ'')) = (fun θ'' => gs θ'' * Q z θ'') from by
      funext θ''
      rw [gs, div_eq_mul_inv, mul_comm]]
    rw [show Work.Spaces.pth Q z θ' = deriv (fun θ'' => Q z θ'') θ' from rfl]
    rw [show (fun θ'' => gs θ'' * Q z θ'') = gs * (fun θ'' => Q z θ'') from rfl]
    rw [deriv_mul (hasDerivAt_gs h').differentiableAt hd', (hasDerivAt_gs h').deriv]
    ring
  have hpthu : Work.Spaces.pth u z θ
      = gs θ * Work.Spaces.pth Q z θ + Q z θ * gs1 θ := hpthu_gen θ hsin hQ
  have hpth2u : Work.Spaces.pthIter 2 u z θ
      = gs1 θ * Work.Spaces.pth Q z θ + gs θ * Work.Spaces.pthIter 2 Q z θ
        + (Work.Spaces.pth Q z θ * gs1 θ + Q z θ * gs2 θ) := by
    have hev : (fun θ' => Work.Spaces.pth u z θ') =ᶠ[𝓝 θ]
        (fun θ' => gs θ' * Work.Spaces.pth Q z θ' + Q z θ' * gs1 θ') := by
      have hQev : ∀ᶠ θ' in 𝓝 θ, ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ') :=
        (ContinuousAt.prodMk continuousAt_const continuousAt_id).tendsto.eventually
          (hQ.eventually (by norm_num))
      have hnev : ∀ᶠ θ' in 𝓝 θ, Real.sin (2 * θ') ≠ 0 :=
        (Real.continuous_sin.continuousAt.comp
          (continuousAt_const.mul continuousAt_id)).eventually_ne hsin
      filter_upwards [hQev, hnev] with θ' h1 h2
      exact hpthu_gen θ' h2 h1
    have hd : HasDerivAt (fun θ' => gs θ' * Work.Spaces.pth Q z θ' + Q z θ' * gs1 θ')
        (gs1 θ * Work.Spaces.pth Q z θ + gs θ * Work.Spaces.pthIter 2 Q z θ
          + (Work.Spaces.pth Q z θ * gs1 θ + Q z θ * gs2 θ)) θ :=
      (hgs.mul hQθθ).add (hQθ.mul hgs1)
    show deriv (fun θ' => Work.Spaces.pth u z θ') θ = _
    rw [hev.deriv_eq, hd.deriv]
  have hC1 : Real.sin (2 * θ) * Work.Spaces.pz u z θ = Work.Spaces.pz Q z θ := by
    rw [hpzu z θ]
    exact mul_div_cancel₀ _ hsin
  have hC2 : Real.sin (2 * θ) * Work.Spaces.pzIter 2 u z θ = Work.Spaces.pzIter 2 Q z θ := by
    rw [hpz2u z θ]
    exact mul_div_cancel₀ _ hsin
  have hC3 : Real.sin (2 * θ) * Work.Spaces.pth u z θ
      = Work.Spaces.pth Q z θ - Q z θ * (2 * Real.cos (2 * θ)) / Real.sin (2 * θ) := by
    rw [hpthu, mul_add]
    rw [show Real.sin (2 * θ) * (gs θ * Work.Spaces.pth Q z θ)
        = (Real.sin (2 * θ) * gs θ) * Work.Spaces.pth Q z θ from by ring,
      sin2_mul_gs θ hsin, one_mul]
    rw [show Real.sin (2 * θ) * (Q z θ * gs1 θ)
        = Q z θ * (Real.sin (2 * θ) * gs1 θ) from by ring, sin2_mul_gs1 θ hsin]
    ring
  have hC4 : Real.sin (2 * θ) * Work.Spaces.pthIter 2 u z θ
      = Work.Spaces.pthIter 2 Q z θ
        - (2 * Real.cos (2 * θ) / Real.sin (2 * θ)) * Work.Spaces.pth Q z θ
        - (2 * Real.cos (2 * θ) / Real.sin (2 * θ)) * Work.Spaces.pth Q z θ
        + (4 + 8 * Real.cos (2 * θ) ^ 2 / Real.sin (2 * θ) ^ 2) * Q z θ := by
    rw [hpth2u]
    rw [show Real.sin (2 * θ) * (gs1 θ * Work.Spaces.pth Q z θ
          + gs θ * Work.Spaces.pthIter 2 Q z θ
          + (Work.Spaces.pth Q z θ * gs1 θ + Q z θ * gs2 θ))
        = (Real.sin (2 * θ) * gs1 θ) * Work.Spaces.pth Q z θ
          + (Real.sin (2 * θ) * gs θ) * Work.Spaces.pthIter 2 Q z θ
          + (Work.Spaces.pth Q z θ * (Real.sin (2 * θ) * gs1 θ)
            + Q z θ * (Real.sin (2 * θ) * gs2 θ)) from by ring]
    rw [sin2_mul_gs θ hsin, sin2_mul_gs1 θ hsin, sin2_mul_gs2 θ hsin]
    ring
  have key_z : Real.sin (2 * θ) * (-(α ^ 2) * Work.Spaces.DzIter 2 u z θ
        - 5 * α * Work.Spaces.Dz u z θ)
      = -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Q z θ
        - α * (5 + α) * z * Work.Spaces.pz Q z θ := by
    have hDzu : Work.Spaces.Dz u z θ = z * Work.Spaces.pz u z θ := rfl
    have hDzI : Work.Spaces.DzIter 2 u z θ
        = z * (Work.Spaces.pz u z θ + z * Work.Spaces.pzIter 2 u z θ) := by
      have hslice : HasDerivAt (fun z' => Work.Spaces.pz u z' θ)
          (Work.Spaces.pzIter 2 u z θ) z := by
        have h1 : (fun z' => Work.Spaces.pz u z' θ)
            = (fun z' => Work.Spaces.pz Q z' θ / Real.sin (2 * θ)) :=
          funext (fun z' => hpzu z' θ)
        rw [h1, hpz2u z θ]
        exact hQzz.div_const (Real.sin (2 * θ))
      have hprod : HasDerivAt (fun z' => z' * Work.Spaces.pz u z' θ)
          (1 * Work.Spaces.pz u z θ + z * Work.Spaces.pzIter 2 u z θ) z :=
        (hasDerivAt_id z).mul hslice
      show z * deriv (fun z' => z' * Work.Spaces.pz u z' θ) z
          = z * (Work.Spaces.pz u z θ + z * Work.Spaces.pzIter 2 u z θ)
      rw [hprod.deriv]
      ring
    rw [hDzI, hDzu]
    rw [show Real.sin (2 * θ) * (-(α ^ 2) * (z * (Work.Spaces.pz u z θ
            + z * Work.Spaces.pzIter 2 u z θ)) - 5 * α * (z * Work.Spaces.pz u z θ))
        = -(α ^ 2) * (z * (Real.sin (2 * θ) * Work.Spaces.pz u z θ)
            + z ^ 2 * (Real.sin (2 * θ) * Work.Spaces.pzIter 2 u z θ))
          - 5 * α * (z * (Real.sin (2 * θ) * Work.Spaces.pz u z θ)) from by ring]
    rw [hC1, hC2]
    ring
  have key_t : Real.sin (2 * θ) * (-(Work.Spaces.pthIter 2 u z θ)
        - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * Work.Spaces.pth u z θ)
      = -(Work.Spaces.pthIter 2 Q z θ)
        + Work.Spaces.pth (fun z' θ' => Real.tan θ' * Q z' θ') z θ - 6 * Q z θ := by
    rw [htan]
    rw [show Real.sin (2 * θ) * (-(Work.Spaces.pthIter 2 u z θ)
          - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * Work.Spaces.pth u z θ)
        = -(Real.sin (2 * θ) * Work.Spaces.pthIter 2 u z θ)
          - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ)
            * (Real.sin (2 * θ) * Work.Spaces.pth u z θ) from by ring]
    rw [hC3, hC4]
    have ht2 : 1 / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      rw [← Real.sin_sq_add_cos_sq θ]
      ring
    rw [ht2]
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul]
    field_simp
    ring_nf
    have hpyth : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ
      linarith
    rw [hpyth]
    ring
  rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, Lgs]
  rw [show Real.sin (2 * θ) * (-(α ^ 2) * Work.Spaces.DzIter 2 u z θ
        - 5 * α * Work.Spaces.Dz u z θ - Work.Spaces.pthIter 2 u z θ
        - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * Work.Spaces.pth u z θ)
      = Real.sin (2 * θ) * (-(α ^ 2) * Work.Spaces.DzIter 2 u z θ
          - 5 * α * Work.Spaces.Dz u z θ)
        + Real.sin (2 * θ) * (-(Work.Spaces.pthIter 2 u z θ)
          - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ)
            * Work.Spaces.pth u z θ) from by ring]
  rw [key_z, key_t]

end Work.FTS_StreamBdry.SB25
