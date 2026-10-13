import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_package_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slice data of `E g` at a fixed radius

`slice_data` collects the three facts about the angular slice `θ ↦ (E g) z θ` of the produced
stream function which the boundary Schauder analysis of the box-`C²` chapter uses:

* the slice is `C²` on `(0,π/2)` (from the open-quadrant `C^∞`-smoothness of `E g`, which the
  package `EllPkgK.smooth` supplies);
* the slice of the elliptic source `θ ↦ Lzero (E g) z θ` is continuous there — `Lzero` is a
  combination of `θ`-derivatives of `C^∞` functions, so this is again a slice-continuity
  statement, applied to `pthIter 2 (E g)` and to `pth (fun z θ => tan θ * (E g) z θ)`;
* the slice solves the *slice ODE* `S'' = tan θ · S' + cos⁻²θ · S − 6 S − Lzero S`, which is
  just the definition of `Lzero Ψ = −∂_θ²Ψ + ∂_θ(tan θ · Ψ) − 6Ψ` rearranged, the product rule
  giving `∂_θ(tan θ · S) = cos⁻²θ · S + tan θ · S'`.

No hypothesis on `α` other than `0 < α` is used; the constants `hα`, `hα4` are part of the
requested interface (they are the standing hypotheses of the chapter) and are kept verbatim.
-/

namespace Work.FTS_EllLimOK.ProducerH.H2.Dev

theorem slice_data {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {g : Work.FTS.Galerkin.Fn}
    (hg : Work.FTS.ClassC.ClassC α g) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 2 (fun θ' => (E g) z θ') (Set.Ioo (0:ℝ) (Real.pi / 2)) ∧
    ContinuousOn (fun θ => Work.Elliptic.Lzero (E g) z θ) (Set.Ioo (0:ℝ) (Real.pi / 2)) ∧
    (∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      deriv (deriv (fun θ' => (E g) z θ')) θ
        = Real.tan θ * deriv (fun θ' => (E g) z θ') θ
          + ((Real.cos θ)^2)⁻¹ * (E g) z θ - 6 * (E g) z θ - Work.Elliptic.Lzero (E g) z θ) := by
  -- the open-quadrant `C^∞`-smoothness of the produced stream function
  have hΨ : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).2.2.smooth
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => (E g) z θ')
      (Set.Ioo (0:ℝ) (Real.pi / 2)) := hΨ.curry_θ hz
  have h2 : ContDiffOn ℝ 2 (fun θ' => (E g) z θ') (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
    hslice.of_le (by norm_num)
  -- `pthIter n (E g)` stays `C^∞` on the open quadrant
  have hpthIter_smooth : ∀ n : ℕ,
      Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter n (E g)) := by
    intro n
    induction n with
    | zero => rw [Work.Spaces.pthIter_zero]; exact hΨ
    | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth
  refine ⟨h2, ?_, ?_⟩
  · -- the source `Lzero (E g) z` is a combination of `θ`-slices of `C^∞` functions
    have htan : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.tan p.2)
        Work.FTS.EllipticEst.Q0 := by
      have h : (fun p : ℝ × ℝ => Real.tan p.2)
          = fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2 := by
        funext p; exact Real.tan_eq_sin_div_cos p.2
      rw [h]
      refine ContDiffOn.div ?_ ?_ ?_
      · exact Real.contDiff_sin.contDiffOn.comp contDiffOn_snd (fun x hx => Set.mem_univ _)
      · exact Real.contDiff_cos.contDiffOn.comp contDiffOn_snd (fun x hx => Set.mem_univ _)
      · intro p hp
        exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hp.2.1], hp.2.2⟩)
    have hG : ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (fun z θ => Real.tan θ * (E g) z θ)) Work.FTS.EllipticEst.Q0 := by
      have hfun : Function.uncurry (fun z θ => Real.tan θ * (E g) z θ)
          = fun p : ℝ × ℝ => Real.tan p.2 * Function.uncurry (E g) p := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [hfun]
      exact htan.mul hΨ
    have hpthG : ContinuousOn
        (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * (E g) z θ) z θ)
        (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
      (Work.FTS.LocData.contDiffOn_slice_θ
        (Work.FTS.LocData.contDiffOn_pth Work.FTS.EllipticEst.isOpen_Q0 hG) hz).continuousOn
    have hpthI2 : ContinuousOn (fun θ => Work.Spaces.pthIter 2 (E g) z θ)
        (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
      ((hpthIter_smooth 2).curry_θ hz).continuousOn
    have hLfun : (fun θ => Work.Elliptic.Lzero (E g) z θ)
        = fun θ => -(Work.Spaces.pthIter 2 (E g) z θ)
            + Work.Spaces.pth (fun z θ => Real.tan θ * (E g) z θ) z θ - 6 * (E g) z θ := by
      funext θ; rfl
    rw [hLfun]
    exact ((hpthI2.neg).add hpthG).sub (hslice.continuousOn.const_mul 6)
  · -- the slice ODE, which is `Lzero` rearranged
    intro θ hθ
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hSd : HasDerivAt (fun θ'' => (E g) z θ'')
        (deriv (fun θ'' => (E g) z θ'') θ) θ :=
      ((h2.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt
    have htan : HasDerivAt Real.tan (((Real.cos θ) ^ 2)⁻¹) θ := by
      simpa only [one_div] using Real.hasDerivAt_tan (ne_of_gt hcos)
    have hprod : deriv (fun θ'' => Real.tan θ'' * (E g) z θ'') θ
        = ((Real.cos θ) ^ 2)⁻¹ * (E g) z θ
          + Real.tan θ * deriv (fun θ'' => (E g) z θ'') θ :=
      (htan.mul hSd).deriv
    have hLfun : Work.Elliptic.Lzero (E g) z
        = fun θ => -deriv (deriv (fun θ' => (E g) z θ')) θ
            + deriv (fun θ' => Real.tan θ' * (E g) z θ') θ - 6 * (E g) z θ := by
      funext θ'
      simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
        Work.Spaces.pth]
    have hL := congrFun hLfun θ
    rw [hL, hprod]
    ring

end Work.FTS_EllLimOK.ProducerH.H2.Dev
