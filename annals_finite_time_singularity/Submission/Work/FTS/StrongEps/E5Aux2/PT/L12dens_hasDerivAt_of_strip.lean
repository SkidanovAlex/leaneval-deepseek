/-
Work module for the Elgindi finite-time singularity project.

# `∂_x (L₁₂dens f) = ∫_θ (K θ ∂_z f(x,θ)/x − K θ f(x,θ)/x²)`

This module proves

  `Work.FTS.StrongEps.E5Aux2.PT.L12dens_hasDerivAt_of_strip`,

the `x`-derivative of the `L₁₂`-density

  `L₁₂dens f x = ∫_{Iθ} K(θ) · f(x,θ) / x dθ`,   `K(θ) = 3 sinθ cos²θ`,

for a datum `f` which is only `C²` on the *open* quadrant `Q0 = (0,∞) × (0,π/2)` and whose
first two `z`-derivatives are bounded by the *same* constant `C` on the open strip
`(x/2, 2x) × (0,π/2)` around the base point `x > 0`.

Since the integrand already contains the factor `1/x`, the claim is the plain differentiation
under the integral sign, i.e. the `Q0`-version
`Work.FTS_RegExport.RXT.Slots.hasDerivAt_integral_Itheta_Q0` applied to
`g y θ = K θ · f y θ / y` and `g' y θ = K θ ∂_z f(y,θ)/y − K θ f(y,θ)/y²`.  Everything that has
to be supplied is

* joint continuity of `g` and `g'` on the open quadrant (from `C²`-ness of `f`, hence of
  `∂_z f`, and from `y ≠ 0` there);
* integrability of the base slice `θ ↦ K θ f(x,θ)/x` on the finite interval `Iθ`;
* the uniform a.e. bound on the candidate derivative over the strip, with constant
  `3C/(x/2) + 3C/(x/2)²` (from `|K| ≤ 3` and `|f|, |∂_z f| ≤ C` on the strip);
* the pointwise derivative at every interior angle, which is the quotient rule.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2.PT

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary facts about the weight `K` and about `∂_z` -/

/-- `|K(θ)| = |3 sinθ cos²θ| ≤ 3` on all of `ℝ`. -/
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
private theorem continuousOn_uncurry_pz_of_two {f : ℝ → ℝ → ℝ}
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

theorem L12dens_hasDerivAt_of_strip {f : ℝ → ℝ → ℝ} {x C : ℝ} (hx : 0 < x) (hC : 0 ≤ C)
    (h2 : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hb₀ : ∀ y ∈ Set.Ioo (x / 2) (2 * x), ∀ θ ∈ Set.Ioo 0 (π / 2), |f y θ| ≤ C)
    (hb₁ : ∀ y ∈ Set.Ioo (x / 2) (2 * x), ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pz f y θ| ≤ C) :
    HasDerivAt (fun x => Work.Construction.L12dens f x)
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Work.Spaces.pz f x θ / x
        - Work.Spaces.K θ * f x θ / x ^ 2)) x := by
  have hxV : x ∈ Set.Ioo (x / 2) (2 * x) := ⟨by linarith, by linarith⟩
  have hV : IsOpen (Set.Ioo (x / 2) (2 * x)) := isOpen_Ioo
  have hVpos : ∀ y ∈ Set.Ioo (x / 2) (2 * x), 0 < y := fun y hy => by linarith [hy.1, hx]
  -- joint continuity on the open quadrant
  have hKc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2) Work.FTS.EllipticEst.Q0 :=
    continuous_K.comp_continuousOn continuousOn_snd
  have hfc : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0 := h2.continuousOn
  have hpc : ContinuousOn (Function.uncurry (Work.Spaces.pz f)) Work.FTS.EllipticEst.Q0 :=
    continuousOn_uncurry_pz_of_two h2
  have hg : ContinuousOn (Function.uncurry (fun y θ => Work.Spaces.K θ * f y θ / y))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun y θ => Work.Spaces.K θ * f y θ / y)
        = fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry f p / p.1 := by
      funext p; rcases p with ⟨y, θ⟩; rfl
    rw [hfun]
    exact (hKc.mul hfc).div continuousOn_fst (fun p hp => ne_of_gt hp.1)
  have hg' : ContinuousOn
      (Function.uncurry (fun y θ => Work.Spaces.K θ * Work.Spaces.pz f y θ / y
        - Work.Spaces.K θ * f y θ / y ^ 2)) Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun y θ => Work.Spaces.K θ * Work.Spaces.pz f y θ / y
        - Work.Spaces.K θ * f y θ / y ^ 2)
        = fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry (Work.Spaces.pz f) p / p.1
            - Work.Spaces.K p.2 * Function.uncurry f p / p.1 ^ 2 := by
      funext p; rcases p with ⟨y, θ⟩; rfl
    rw [hfun]
    exact ((hKc.mul hpc).div continuousOn_fst (fun p hp => ne_of_gt hp.1)).sub
      ((hKc.mul hfc).div (continuousOn_fst.pow 2)
        (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1)))
  -- integrability of the base slice
  have hint : Integrable (fun θ => Work.Spaces.K θ * f x θ / x)
      (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.of_bound (Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0 hg hx)
      (3 * C / x) ?_
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hx]
    exact div_le_div_of_nonneg_right
      (mul_le_mul (abs_K_le_three θ) (hb₀ x hxV θ hθ) (abs_nonneg _) (by norm_num)) hx.le
  -- the uniform a.e. bound on the candidate derivative over the strip
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ∀ y ∈ Set.Ioo (x / 2) (2 * x),
      ‖Work.Spaces.K θ * Work.Spaces.pz f y θ / y - Work.Spaces.K θ * f y θ / y ^ 2‖
        ≤ 3 * C / (x / 2) + 3 * C / (x / 2) ^ 2 := by
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ y hy => ?_)
    have hy0 : 0 < y := hVpos y hy
    have h1 : |Work.Spaces.K θ * Work.Spaces.pz f y θ / y| ≤ 3 * C / y := by
      rw [abs_div, abs_mul, abs_of_pos hy0]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (abs_K_le_three θ) (hb₁ y hy θ hθ) (abs_nonneg _) (by norm_num)) hy0.le
    have h2' : |Work.Spaces.K θ * f y θ / y ^ 2| ≤ 3 * C / y ^ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg y)]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (abs_K_le_three θ) (hb₀ y hy θ hθ) (abs_nonneg _) (by norm_num))
        (sq_nonneg y)
    have h3C : (0 : ℝ) ≤ 3 * C := by linarith
    have hhalf : 0 < x / 2 := by linarith
    have hsq : (x / 2) ^ 2 ≤ y ^ 2 := by nlinarith [hhalf, hy.1]
    have hb₁' : 3 * C / y ≤ 3 * C / (x / 2) :=
      div_le_div_of_nonneg_left h3C hhalf hy.1.le
    have hb₂' : 3 * C / y ^ 2 ≤ 3 * C / (x / 2) ^ 2 :=
      div_le_div_of_nonneg_left h3C (pow_pos hhalf 2) hsq
    rw [Real.norm_eq_abs]
    calc |Work.Spaces.K θ * Work.Spaces.pz f y θ / y - Work.Spaces.K θ * f y θ / y ^ 2|
        ≤ |Work.Spaces.K θ * Work.Spaces.pz f y θ / y| + |Work.Spaces.K θ * f y θ / y ^ 2| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (Work.Spaces.K θ * Work.Spaces.pz f y θ / y)
              (-(Work.Spaces.K θ * f y θ / y ^ 2))
      _ ≤ 3 * C / (x / 2) + 3 * C / (x / 2) ^ 2 := by linarith
  -- the pointwise derivative at every interior angle
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ y ∈ Set.Ioo (x / 2) (2 * x),
      HasDerivAt (fun z => Work.Spaces.K θ * f z θ / z)
        (Work.Spaces.K θ * Work.Spaces.pz f y θ / y - Work.Spaces.K θ * f y θ / y ^ 2) y := by
    intro θ hθ y hy
    have hy0 : 0 < y := hVpos y hy
    have hd : DifferentiableAt ℝ (Function.uncurry f) (y, θ) :=
      (h2.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hy0, hθ.1, hθ.2⟩))
    have h1 : HasDerivAt (fun z : ℝ => f z θ) (Work.Spaces.pz f y θ) y := by
      simpa only [Work.Spaces.pz] using
        (Work.Spaces.differentiableAt_curry_left hd).hasDerivAt
    have h2' := (h1.const_mul (Work.Spaces.K θ)).div (hasDerivAt_id y) (ne_of_gt hy0)
    convert h2' using 1
    · funext z
      simp only [Pi.div_apply, id_eq]
    · simp only [id_eq]
      field_simp
  -- differentiation under the angular integral
  have key := Work.FTS_RegExport.RXT.Slots.hasDerivAt_integral_Itheta_Q0
    (g := fun y θ => Work.Spaces.K θ * f y θ / y)
    (g' := fun y θ => Work.Spaces.K θ * Work.Spaces.pz f y θ / y
      - Work.Spaces.K θ * f y θ / y ^ 2)
    (V := Set.Ioo (x / 2) (2 * x)) hV hxV hVpos hg hg' hint hbound hdiff
  have hfun : (fun y => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f y θ / y)
      = fun y => Work.Construction.L12dens f y := by
    funext y
    simp only [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ]
  rw [hfun] at key
  exact key

end Work.FTS.StrongEps.E5Aux2.PT
