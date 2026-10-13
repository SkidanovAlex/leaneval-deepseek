import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.ConstructionInstance.GCompDefs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Taylor bounds for the modulation `g` at `z = 0`

This file proves `Work.ConstructionInstance.g_taylor_bounds`: a function `g` which is `C²` on an
open neighbourhood of the quadrant `[0,∞) × [0,π/2]` and whose `z`-slice at `z = 0` vanishes
together with its `z`-derivative is dominated on the box `[0,2] × [0,π/2]` by a constant,
uniformly in the angle, according to

  `|g z θ| ≤ K z²`,  `|∂_z g z θ| ≤ K z`,  `|∂_θ g z θ| ≤ K z`.

The proof is the mean-value theorem applied to the radial slices of the (finitely many)
second-order partial derivatives of `g`.  The only analytic input is that `g` is `C²` on a
neighbourhood of the closed box: this makes the second Fréchet derivative of `uncurry g`
continuous on the (open) neighbourhood, hence its restriction to the compact box is bounded,
and that bound is exactly the constant in the mean-value estimate.  The values of `g` and
`∂_z g` at `z = 0` are supplied by the hypotheses `hquad0`, `hquad1`, and `∂_θ g z θ` is
controlled starting from its (vanishing) value at `z = 0`.
-/

open Set Filter
open scoped Topology

namespace Work.ConstructionInstance

set_option autoImplicit false

theorem g_taylor_bounds {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hquad1 : ∀ θ : ℝ, Work.Spaces.pz g 0 θ = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ K * z ^ 2 ∧ |Work.Spaces.pz g z θ| ≤ K * z
        ∧ |Work.Spaces.pth g z θ| ≤ K * z := by
  let G : ℝ × ℝ → ℝ := Function.uncurry g
  let U : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)
  have hopen : IsOpen U := isOpen_Ioi.prod isOpen_Ioo
  -- the closed box `[0,2] × [0,π/2]` sits inside the open neighbourhood `U`
  have hboxU : (Set.Icc (0:ℝ) 2 ×ˢ Work.Spaces.Iθ) ⊆ U := by
    rintro p ⟨hz, hθ⟩
    rw [Work.Spaces.Iθ] at hθ
    exact ⟨by rw [Set.mem_Ioi]; linarith [hz.1],
           by constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]⟩
  have hboxC : IsCompact (Set.Icc (0:ℝ) 2 ×ˢ Work.Spaces.Iθ) :=
    isCompact_Icc.prod (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)
  -- `fderiv G` is `C¹` and `fderiv (fderiv G)` is continuous on `U`
  have hG1 : ContDiffOn ℝ 1 (fderiv ℝ G) U :=
    hsm.fderiv_of_isOpen hopen (by norm_num)
  have hG2 : ContinuousOn (fderiv ℝ (fderiv ℝ G)) U :=
    hG1.continuousOn_fderiv_of_isOpen hopen (by norm_num)
  -- the two second-order partial derivatives `∂_z∂_z g` and `∂_z∂_θ g`, read off the
  -- second Fréchet derivative, are continuous on `U`, hence bounded on the box
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ => ((fderiv ℝ (fderiv ℝ G) p) (1,0)) (1,0)) U := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (fderiv ℝ (fderiv ℝ G) p) (1,0)) U :=
      hG2.clm_apply continuousOn_const
    exact h1.clm_apply continuousOn_const
  have hcont3 : ContinuousOn (fun p : ℝ × ℝ => ((fderiv ℝ (fderiv ℝ G) p) (1,0)) (0,1)) U := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (fderiv ℝ (fderiv ℝ G) p) (1,0)) U :=
      hG2.clm_apply continuousOn_const
    exact h1.clm_apply continuousOn_const
  obtain ⟨B1, hB1⟩ := hboxC.exists_bound_of_continuousOn (hcont2.mono hboxU)
  obtain ⟨B2, hB2⟩ := hboxC.exists_bound_of_continuousOn (hcont3.mono hboxU)
  set M1 : ℝ := max B1 0 with hM1
  set M2 : ℝ := max B2 0 with hM2
  set K : ℝ := max 1 (max M1 M2) with hK
  have hK0 : 0 ≤ K := by rw [hK]; exact le_trans zero_le_one (le_max_left _ _)
  have hK1 : B1 ≤ K := by
    rw [hK, hM1]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hK2 : B2 ≤ K := by
    rw [hK, hM2]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨K, hK0, ?_⟩
  intro z θ hz0 hz2 hθ
  have hdiff : ∀ x : ℝ, 0 ≤ x → x ≤ 2 → DifferentiableAt ℝ G (x, θ) := fun x hx0 hx2 =>
    (hsm.differentiableOn (by norm_num)).differentiableAt
      (hopen.mem_nhds (hboxU ⟨⟨hx0, hx2⟩, hθ⟩))
  -- the curried partial derivatives are the Fréchet derivatives in the two coordinate directions
  have hpz_fd : ∀ x : ℝ, 0 ≤ x → x ≤ 2 →
      (fderiv ℝ G (x, θ)) (1,0) = Work.Spaces.pz g x θ :=
    fun x hx0 hx2 => (Work.Spaces.pz_eq_fderiv (hdiff x hx0 hx2)).symm
  have hpth_fd : ∀ x : ℝ, 0 ≤ x → x ≤ 2 →
      (fderiv ℝ G (x, θ)) (0,1) = Work.Spaces.pth g x θ :=
    fun x hx0 hx2 => (Work.Spaces.pth_eq_fderiv (hdiff x hx0 hx2)).symm
  -- ## derivatives of the radial slices
  have hdg : ∀ x ∈ Set.Icc (0:ℝ) z,
      HasDerivWithinAt (fun y => g y θ) ((fderiv ℝ G (x, θ)) (1,0)) (Set.Icc 0 z) x := by
    intro x hx
    have hx2 : x ≤ 2 := le_trans hx.2 hz2
    have hd := hdiff x hx.1 hx2
    have hcomp : HasFDerivAt (G ∘ (fun y : ℝ => (y, θ)))
        ((fderiv ℝ G (x, θ)) ∘SL ContinuousLinearMap.inl ℝ ℝ ℝ) x :=
      hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x θ)
    have h1 : HasDerivAt (G ∘ (fun y : ℝ => (y, θ))) ((fderiv ℝ G (x, θ)) (1,0)) x := by
      simpa [ContinuousLinearMap.inl_apply] using hcomp.hasDerivAt
    exact h1.hasDerivWithinAt
  have hdu : ∀ x ∈ Set.Icc (0:ℝ) z,
      HasDerivWithinAt (fun y => (fderiv ℝ G (y, θ)) (1,0))
        (((fderiv ℝ (fderiv ℝ G) (x, θ)) (1,0)) (1,0)) (Set.Icc 0 z) x := by
    intro x hx
    have hx2 : x ≤ 2 := le_trans hx.2 hz2
    have hxU : (x, θ) ∈ U := hboxU ⟨⟨hx.1, hx2⟩, hθ⟩
    have hDdiff : DifferentiableAt ℝ (fderiv ℝ G) (x, θ) :=
      (hG1.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hxU)
    have hE1 : HasFDerivAt (ContinuousLinearMap.apply ℝ ℝ ((1:ℝ),(0:ℝ)))
        (ContinuousLinearMap.apply ℝ ℝ ((1:ℝ),(0:ℝ))) (fderiv ℝ G (x, θ)) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1:ℝ),(0:ℝ))).hasFDerivAt
    have hcomp1 := hE1.comp (x, θ) hDdiff.hasFDerivAt
    have hcurve : HasDerivAt (fun y : ℝ => (y, θ)) ((1:ℝ),(0:ℝ)) x := by
      simpa using (hasDerivAt_id x).prodMk (hasDerivAt_const x θ)
    have hcomp2 := hcomp1.comp_hasDerivAt x hcurve
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply] using hcomp2.hasDerivWithinAt
  have hdw : ∀ x ∈ Set.Icc (0:ℝ) z,
      HasDerivWithinAt (fun y => (fderiv ℝ G (y, θ)) (0,1))
        (((fderiv ℝ (fderiv ℝ G) (x, θ)) (1,0)) (0,1)) (Set.Icc 0 z) x := by
    intro x hx
    have hx2 : x ≤ 2 := le_trans hx.2 hz2
    have hxU : (x, θ) ∈ U := hboxU ⟨⟨hx.1, hx2⟩, hθ⟩
    have hDdiff : DifferentiableAt ℝ (fderiv ℝ G) (x, θ) :=
      (hG1.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hxU)
    have hE1 : HasFDerivAt (ContinuousLinearMap.apply ℝ ℝ ((0:ℝ),(1:ℝ)))
        (ContinuousLinearMap.apply ℝ ℝ ((0:ℝ),(1:ℝ))) (fderiv ℝ G (x, θ)) :=
      (ContinuousLinearMap.apply ℝ ℝ ((0:ℝ),(1:ℝ))).hasFDerivAt
    have hcomp1 := hE1.comp (x, θ) hDdiff.hasFDerivAt
    have hcurve : HasDerivAt (fun y : ℝ => (y, θ)) ((1:ℝ),(0:ℝ)) x := by
      simpa using (hasDerivAt_id x).prodMk (hasDerivAt_const x θ)
    have hcomp2 := hcomp1.comp_hasDerivAt x hcurve
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply] using hcomp2.hasDerivWithinAt
  -- ## the uniform bounds on the second-order partials
  have hbnd_u : ∀ x ∈ Set.Ico (0:ℝ) z,
      ‖((fderiv ℝ (fderiv ℝ G) (x, θ)) (1,0)) (1,0)‖ ≤ K := by
    intro x hx
    have hx2 : x ≤ 2 := le_trans (le_of_lt hx.2) hz2
    have h := hB1 (x, θ) ⟨⟨hx.1, hx2⟩, hθ⟩
    rw [Real.norm_eq_abs] at h
    exact le_trans h hK1
  have hbnd_w : ∀ x ∈ Set.Ico (0:ℝ) z,
      ‖((fderiv ℝ (fderiv ℝ G) (x, θ)) (1,0)) (0,1)‖ ≤ K := by
    intro x hx
    have hx2 : x ≤ 2 := le_trans (le_of_lt hx.2) hz2
    have h := hB2 (x, θ) ⟨⟨hx.1, hx2⟩, hθ⟩
    rw [Real.norm_eq_abs] at h
    exact le_trans h hK2
  -- ## `|∂_z g z θ| ≤ K z`
  have hMVT_u := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun y => (fderiv ℝ G (y, θ)) (1,0))
      (f' := fun y => ((fderiv ℝ (fderiv ℝ G) (y, θ)) (1,0)) (1,0))
      (a := 0) (b := z) (C := K) hdu hbnd_u
  have hpzu : ∀ y ∈ Set.Icc (0:ℝ) z, |Work.Spaces.pz g y θ| ≤ K * y := by
    intro y hy
    have hy2 : y ≤ 2 := le_trans hy.2 hz2
    have h := hMVT_u y hy
    rw [Real.norm_eq_abs] at h
    have h0 : (fderiv ℝ G (0, θ)) (1,0) = 0 := by
      rw [hpz_fd 0 (le_refl (0:ℝ)) (by norm_num), hquad1 θ]
    rw [hpz_fd y hy.1 hy2, h0, sub_zero, sub_zero] at h
    exact h
  -- ## `|g z θ| ≤ K z²`
  have hbnd_g : ∀ x ∈ Set.Ico (0:ℝ) z, ‖(fderiv ℝ G (x, θ)) (1,0)‖ ≤ K * z := by
    intro x hx
    have hx2 : x ≤ 2 := le_trans (le_of_lt hx.2) hz2
    rw [Real.norm_eq_abs, hpz_fd x hx.1 hx2]
    calc |Work.Spaces.pz g x θ| ≤ K * x := hpzu x ⟨hx.1, le_of_lt hx.2⟩
      _ ≤ K * z := mul_le_mul_of_nonneg_left (le_of_lt hx.2) hK0
  have hMVT_g := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun y => g y θ)
      (f' := fun y => (fderiv ℝ G (y, θ)) (1,0))
      (a := 0) (b := z) (C := K * z) hdg hbnd_g
  have hgz : |g z θ| ≤ K * z ^ 2 := by
    have h := hMVT_g z ⟨hz0, le_refl z⟩
    rw [Real.norm_eq_abs, hquad0 θ, sub_zero, sub_zero] at h
    calc |g z θ| ≤ K * z * z := h
      _ = K * z ^ 2 := by ring
  -- ## `|∂_θ g z θ| ≤ K z`
  have hpth0 : Work.Spaces.pth g 0 θ = 0 := by
    rw [Work.Spaces.pth]
    have : (fun θ' => g 0 θ') = fun _ => (0:ℝ) := by funext θ'; exact hquad0 θ'
    rw [this, deriv_const]
  have hMVT_w := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun y => (fderiv ℝ G (y, θ)) (0,1))
      (f' := fun y => ((fderiv ℝ (fderiv ℝ G) (y, θ)) (1,0)) (0,1))
      (a := 0) (b := z) (C := K) hdw hbnd_w
  have hpthz : |Work.Spaces.pth g z θ| ≤ K * z := by
    have h := hMVT_w z ⟨hz0, le_refl z⟩
    rw [Real.norm_eq_abs] at h
    have h0 : (fderiv ℝ G (0, θ)) (0,1) = 0 := by
      rw [hpth_fd 0 (le_refl (0:ℝ)) (by norm_num), hpth0]
    rw [hpth_fd z hz0 hz2, h0, sub_zero, sub_zero] at h
    exact h
  exact ⟨hgz, hpzu z ⟨hz0, le_refl z⟩, hpthz⟩

end Work.ConstructionInstance
