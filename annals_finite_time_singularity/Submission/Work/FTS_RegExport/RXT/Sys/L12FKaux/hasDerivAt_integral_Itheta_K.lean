/-
Copyright: work module for the Elgindi finite-time singularity project.

# Differentiation under the angular integral with the weight `K`

This module proves

  `Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K`,

the `x`-derivative of the parametric angular integral

  `x ↦ ∫_{Iθ} K(θ) · f(x,θ) dθ`,   `K(θ) = 3 sinθ cos²θ`,

for a datum `f` which is only `C²` on the *open* quadrant `Q0 = (0,∞) × (0,π/2)` and
bounded (together with `∂_z f`) on the open strip `(z/2, 2z) × (0,π/2)` around the base
point `z > 0`.  The conclusion is the natural one,

  `∂_z (∫_{Iθ} K(θ) f(·,θ)) = ∫_{Iθ} K(θ) ∂_z f(z,θ)`,

which is the input used by the `L₁₂`/`FK` development of `FTS_RegExport`.

The differentiation itself is the open-quadrant rule
`Work.FTS_RegExport.RXT.Slots.hasDerivAt_integral_Itheta_Q0` (the analogue of
`Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt` for data that are smooth only on
the open quadrant).  All that has to be supplied here is:

* joint continuity of the integrand and of its candidate `x`-derivative on `Q0`
  (`f` is continuous there and `∂_z f` is continuous there because `∂_z` costs one order
  of differentiability — `continuousOn_pz_of_two` below);
* integrability of the base integrand `θ ↦ K(θ) f(z,θ)` on `Iθ` (a.e. strong measurability
  from the open-quadrant continuity, plus the a.e. bound coming from `hb0` and `|K| ≤ 3`);
* the uniform a.e. bound on the candidate derivative on the strip (from `hb`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.RXT.Slots.v2_Prelim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary facts about the weight `K` and about `∂_z` -/

/-- `|K(θ)| = |3 sinθ cos²θ| ≤ 3` on all of `ℝ` (in particular on `Iθ`). -/
private theorem abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    have h := Real.abs_cos_le_one θ
    nlinarith [abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  have hcs : |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 :=
    calc |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 * 1 :=
          mul_le_mul hs hc (sq_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hK : |Work.Spaces.K θ| = 3 * (|Real.sin θ| * Real.cos θ ^ 2) := by
    rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      abs_of_nonneg (sq_nonneg (Real.cos θ))]
    ring
  rw [hK]
  linarith [hcs]

/-- `K` is continuous. -/
private theorem continuous_K : Continuous Work.Spaces.K := by
  unfold Work.Spaces.K
  exact ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2))

/-- `∂_z` costs one order of differentiability: the uncurried `∂_z f` of a datum that is
jointly `C²` on the open quadrant is jointly continuous there. -/
private theorem continuousOn_pz_of_two {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz f)) Work.FTS.EllipticEst.Q0 := by
  have hchain : ∀ p ∈ Work.FTS.EllipticEst.Q0, Function.uncurry (Work.Spaces.pz f) p
      = (fderiv ℝ (Function.uncurry f) p) (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp))
  have hfd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry f) p)
      Work.FTS.EllipticEst.Q0 := by
    have h' := h.fderivWithin (m := 1) Work.FTS.EllipticEst.isOpen_Q0.uniqueDiffOn
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    refine h'.congr (fun p hp => ?_)
    rw [fderivWithin_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hp]
  have hcomp : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) p) (1, 0))
      Work.FTS.EllipticEst.Q0 :=
    hfd.clm_apply contDiffOn_const
  exact (hcomp.congr hchain).continuousOn

/-! ## The main statement -/

theorem hasDerivAt_integral_Itheta_K {f : ℝ → ℝ → ℝ} {z C : ℝ}
    (h2 : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hz : 0 < z) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.pz f x θ| ≤ C)
    (hb0 : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f x θ| ≤ C) :
    HasDerivAt (fun x => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f x θ)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f z θ) z := by
  -- `C ≥ 0` is what makes `3 * C` an admissible dominating constant in the two a.e. bounds
  -- below; it is recorded here (the bounds themselves come from `hb`/`hb0` and `|K| ≤ 3`).
  have _hC : (0 : ℝ) ≤ C := hC
  have hV : IsOpen (Set.Ioo (z / 2) (2 * z)) := isOpen_Ioo
  have hzV : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  have hVpos : ∀ x ∈ Set.Ioo (z / 2) (2 * z), 0 < x := fun x hx => by linarith [hx.1, hz]
  -- joint continuity of the angular factor `θ ↦ K θ` on the open quadrant
  have hKc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      Work.FTS.EllipticEst.Q0 := continuous_K.comp_continuousOn continuousOn_snd
  -- joint continuity of the integrand `(x,θ) ↦ K θ · f x θ` on the open quadrant
  have hg : ContinuousOn (Function.uncurry (fun x θ => Work.Spaces.K θ * f x θ))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun x θ => Work.Spaces.K θ * f x θ)
        = fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry f p := by
      funext p; rcases p with ⟨x, θ⟩; rfl
    rw [hfun]
    exact hKc.mul h2.continuousOn
  -- joint continuity of the candidate derivative `(x,θ) ↦ K θ · ∂_z f x θ`
  have hpc : ContinuousOn (Function.uncurry (Work.Spaces.pz f)) Work.FTS.EllipticEst.Q0 :=
    continuousOn_pz_of_two h2
  have hg' : ContinuousOn
      (Function.uncurry (fun x θ => Work.Spaces.K θ * Work.Spaces.pz f x θ))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun x θ => Work.Spaces.K θ * Work.Spaces.pz f x θ)
        = fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry (Work.Spaces.pz f) p := by
      funext p; rcases p with ⟨x, θ⟩; rfl
    rw [hfun]
    exact hKc.mul hpc
  -- the a.e. bound on the base integrand `θ ↦ K θ · f z θ`
  have hbnd0 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * f z θ‖ ≤ 3 * C := by
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_K_le_three θ) (hb0 z hzV θ hθ) (abs_nonneg _) (by norm_num)
  -- integrability of the base integrand on the finite measure space `Iθ`
  have hint : Integrable (fun θ => Work.Spaces.K θ * f z θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Integrable.of_bound (Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0 hg hz) (3 * C) hbnd0
  -- the uniform a.e. bound on the candidate derivative on the strip
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      ‖Work.Spaces.K θ * Work.Spaces.pz f x θ‖ ≤ 3 * C := by
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_K_le_three θ) (hb x hx θ hθ) (abs_nonneg _) (by norm_num)
  -- the pointwise `x`-derivative, at every interior angle and every `x` in the strip
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (fun y => Work.Spaces.K θ * f y θ)
        (Work.Spaces.K θ * Work.Spaces.pz f x θ) x := by
    intro θ hθ x hx
    have hx0 : 0 < x := hVpos x hx
    have hd : DifferentiableAt ℝ (Function.uncurry f) (x, θ) :=
      (h2.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hx0, hθ.1, hθ.2⟩))
    have h1 : HasDerivAt (fun y : ℝ => f y θ) (deriv (fun y : ℝ => f y θ) x) x :=
      (Work.Spaces.differentiableAt_curry_left hd).hasDerivAt
    simpa only [Work.Spaces.pz] using h1.const_mul (Work.Spaces.K θ)
  exact Work.FTS_RegExport.RXT.Slots.hasDerivAt_integral_Itheta_Q0
    (g := fun x θ => Work.Spaces.K θ * f x θ)
    (g' := fun x θ => Work.Spaces.K θ * Work.Spaces.pz f x θ)
    hV hzV hVpos hg hg' hint hbound hdiff

end Work.FTS_RegExport.RXT.Sys.L12FKaux
