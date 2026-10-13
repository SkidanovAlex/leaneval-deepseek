/-
Copyright: work module for the Elgindi finite-time singularity project.

# The *honest* class of data of the level-`0` `η`-weighted elliptic estimate

This module fixes the hypothesis class of
`Work.FTS.EllipticEst.l2etaHonestCore` (Elgindi, Annals **194** (2021), Steps 1--2 of
Proposition `prop:H2`, tex 840--890): solutions of `(PolarBSL)` that are smooth on the *open*
quadrant only, with the Dirichlet data, the pointwise decay at `z → ∞`, the two solvability
conditions `OrthCond F`, `OrthCond Ψ`, and the *honesty* `HkMem α 0` of the three quantities
`F`, `z²∂_zzΨ`, `∂_θθΨ`.

The class deliberately omits `Work.Spaces.SmoothNbhd` (smoothness on a *neighbourhood of the
closed* quadrant) and `Work.FTS.EllipticEst.ZDecay`; both are consequences of the honesty for
the estimates below, but neither is a hypothesis here.  In particular the class contains
functions of the shape `Ψ(z,θ) = z ^ s · φ(θ)` (`s > 3/2`, `s` possibly non-integral) and
functions whose `θ`-slices are discontinuous at `θ = 0` with `Ψ z 0 = 0` as a *value*; the
estimates must be insensitive to both.

## Vocabulary

* `σ θ = sin(2θ)^{-η}`, `ρ z θ = w z² σ θ`, `AngSecond.IP g h = ∫_z ∫_θ g h ρ` (imported);
* `HkSq α 0 g = IP g g` for *honest* `g` (`HkSq_zero_eq`, `IP_self_eq_HkSq`);
* `A = z²∂_zzΨ`, `B = ∂_θθΨ`, `G = z∂_zΨ`, `u = ∂_θ(tan θ · Ψ)`, `f = ‖F‖_ρ`, and
  `‖g‖_ρ² = HkSq α 0 g`.

## Contents

* `Hon`: the class described above;
* `HkSq_zero_eq`: the level-`0` `HkSq`-integrand, pointwise;
* `IP_self_eq_HkSq`: `IP g g = HkSq α 0 g`, i.e. `‖g‖_ρ²` is the honest `IP`-pairing;
* `Hon.eq_solve`, `Hon.eq_solve'`: the rearrangements of `(PolarBSL)`
  `α²A = -F - α(5+α)G - B + u - 6Ψ` on the open quadrant;
* `HkSq_zero_nonneg`, `HkSq_zero_const_mul`, `hksq_sqrt_sq`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.HkSq_eq_lintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The hypothesis class -/

/-- **The honest class of the level-`0` `η`-weighted elliptic estimate.**  `(F,Ψ)` solves
`(PolarBSL)` on the *open* quadrant, has the Dirichlet data and the pointwise decay at `z → ∞`,
satisfies the two solvability conditions `OrthCond F`, `OrthCond Ψ`, is smooth on the open
quadrant, the three `ℋ⁰`-integrands of `F`, `z²∂_zzΨ`, `∂_θθΨ` are honest, and the two *mixed*
level-`1/2` slots of `Ψ` — the `ℋ⁰`-integrands of `z ∂_z∂_θΨ` and of `z ∂_z∂_θ²Ψ` — are honest
(the fields `memMix1`, `memMix2` below; they are the level-`1/2` honesty that the transcription
of Proposition `H2` had been carrying silently). -/
structure Hon (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : Prop where
  /-- `0 < α`. -/
  hα : 0 < α
  /-- `α ≤ 1/4`. -/
  hα4 : α ≤ 1 / 4
  /-- `(PolarBSL)` holds on the open quadrant. -/
  eq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ
  /-- The Dirichlet datum at `θ = 0`. -/
  d0 : ∀ z, Ψ z 0 = 0
  /-- The Dirichlet datum at `θ = π/2`. -/
  dπ : ∀ z, Ψ z (π / 2) = 0
  /-- Pointwise decay at `z → ∞`. -/
  dec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (nhds 0)
  /-- The solvability condition on the source. -/
  orthF : Work.Elliptic.OrthCond F
  /-- The solvability condition on the solution (Step 1 of `prop:L2`). -/
  orthΨ : Work.Elliptic.OrthCond Ψ
  /-- Smoothness on the open quadrant. -/
  sm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
  /-- Honesty of the source. -/
  memF : Work.Spaces.HkMem α 0 F
  /-- Honesty of `z²∂_zzΨ`. -/
  memA : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  /-- Honesty of `∂_θθΨ`. -/
  memB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)
  /-- **The mixed `(1,1)`-slot honesty: the level-`0` honesty of `z ∂_z∂_θΨ`.**

  This is *not* a consequence of the fields above; it is the level-`1/2` honesty that the
  transcription of Proposition `H2` had been carrying silently, and that the workspace records as
  one of the two exact obstructions to the `I₁` coercivity of Step 2
  (`Final/NOTES_honI1Lower_session_revival.md` §2, "Wall A").  Its role is to make the a.e.-`z`
  angular traces of `G = z∂_zΨ` vanish: `HkMem α 0 (z∂_z∂_θ²Ψ)`-type slice data plus this field
  gives `Final/honGSliceTraceAe`, hence `Final/honGHNonpos`.  Data constructed by *converting*
  from a class that has the regularity (`EllHyp`, `SmoothNbhd`, `SmN`, or the paper's data, which
  is smooth on a closed neighbourhood of the quadrant and compactly supported in `z`) satisfies
  it. -/
  memMix1 : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pth Ψ) z θ)
  /-- **The mixed `(1,2)`-slot honesty: the level-`0` honesty of `z ∂_z∂_θ²Ψ`.**

  This is the second of the two level-`1/2` slots, and the hypothesis of the `z`-integration by
  parts engine `H2W.WeakAux.I1_ibp_identity_open` that drives the `I₁` coercivity
  (`Final/honI1Lower_of_mixedHon`, whose conclusion is verbatim the `I₁` slot consumed by
  `Honest.step3BAngularClean`, hence by `Honest.step2Angular` and by the Step-3 angular estimate
  `Final.step3Angle_fts`). -/
  memMix2 : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)

/-! ## The angular weight and its elementary algebra -/

/-- `sin(2θ) ≥ 0` on `Iθ = [0,π/2]`. -/
theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- **The elementary algebra of the angular weight**: for `0 ≤ s`,
`(w / s^{η/2})² = w² · s^{-η}`. -/
theorem sq_weight_eq {w s : ℝ} (hs : 0 ≤ s) :
    (w / s ^ (Work.Spaces.eta / 2)) ^ 2 = w ^ 2 * s ^ (-(Work.Spaces.eta)) := by
  have heta : Work.Spaces.eta ≠ 0 := by norm_num [Work.Spaces.eta]
  have hhalf : Work.Spaces.eta / 2 ≠ 0 := by positivity
  rcases eq_or_lt_of_le hs with h0 | hpos
  · subst h0
    rw [Real.zero_rpow hhalf, div_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), Real.zero_rpow (neg_ne_zero.mpr heta)]
    ring
  · have hsq : (s ^ (Work.Spaces.eta / 2)) ^ 2 = s ^ Work.Spaces.eta := by
      rw [sq, ← Real.rpow_add hpos]
      congr 1
      norm_num [Work.Spaces.eta]
    rw [div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hpos)]

/-! ## The level-`0` integrand, and the identification of `HkSq α 0` with the `IP`-pairing -/

/-- **The level-`0` `HkSq`-integrand.**  At level `0` the mixed-derivative sum of
`Work.Spaces.HkIntegrand` is empty, so the integrand is the single square
`(g z θ · w z / sin(2θ)^{η/2})²`. -/
theorem HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.pzIter_zero, Finset.range_one,
    Finset.sum_singleton]
  norm_num

/-- **`HkSq α 0` as the iterated integral of the square of the weighted profile.** -/
theorem HkSq_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ =>
    HkIntegrand_zero_eq α g z θ

/-- The pointwise identity behind `IP_self_eq_HkSq`, on the angular interval. -/
theorem sq_profile_eq (g : ℝ → ℝ → ℝ) (z θ : ℝ) (hsin : 0 ≤ Real.sin (2 * θ)) :
    (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [mul_pow, sq_weight_eq hsin]
  ring

/-- **`HkSq α 0 g` is the `IP`-pairing of `g` with itself**:
`IP g g = ∫_z ∫_θ g² w² σ = HkSq α 0 g`. -/
theorem IP_self_eq_HkSq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    AngSecond.IP g g = Work.Spaces.HkSq α 0 g := by
  rw [HkSq_zero_eq]
  unfold AngSecond.IP
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  unfold AngSecond.w2 AngSecond.sig
  simp only [sq_profile_eq g z θ (sin_two_nonneg_of_mem_Iθ hθ)]
  ring

/-! ## Nonnegativity and homogeneity -/

theorem HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand]
  refine add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity

/-- The level-`0` `HkSq` of any function is nonnegative. -/
theorem HkSq_zero_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.HkSq α 0 g := by
  rw [Work.Spaces.HkSq]
  exact integral_nonneg fun z => integral_nonneg fun θ => HkIntegrand_nonneg α 0 g z θ

/-- `(√ (HkSq α 0 g))² = HkSq α 0 g`. -/
theorem hksq_sqrt_sq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    (Real.sqrt (Work.Spaces.HkSq α 0 g)) ^ 2 = Work.Spaces.HkSq α 0 g :=
  Real.sq_sqrt (HkSq_zero_nonneg α g)

/-- **Homogeneity of `HkSq α 0` under multiplication by a constant.** -/
theorem HkSq_zero_const_mul (α c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 (fun z θ => c * g z θ) = c ^ 2 * Work.Spaces.HkSq α 0 g := by
  rw [HkSq_zero_eq, HkSq_zero_eq]
  rw [show (fun z => ∫ θ in Work.Spaces.Iθ, (c * g z θ *
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 from by
    funext z
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [← MeasureTheory.integral_const_mul]

/-- **Negation invariance**, at the level of the iterated integral. -/
theorem HkSq_zero_neg (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 (fun z θ => -g z θ) = Work.Spaces.HkSq α 0 g := by
  rw [HkSq_zero_eq, HkSq_zero_eq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring

/-! ## Monotonicity of `HkSq α 0` -/

/-- **Monotonicity of `HkSq α 0` under a pointwise domination of the weighted profiles**, given
the honesty of both integrands.  This is the tool that turns the pointwise rearrangement
`α²A = -F - α(5+α)G - B + u - 6Ψ` into an estimate of `‖A‖_ρ`. -/
theorem HkSq_zero_le_of_le {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) (hg : Work.Spaces.HkMem α 0 g)
    (h : ∀ z θ, Work.Spaces.HkIntegrand α 0 f z θ ≤ Work.Spaces.HkIntegrand α 0 g z θ) :
    Work.Spaces.HkSq α 0 f ≤ Work.Spaces.HkSq α 0 g := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_mono_on hf.2 hg.2 measurableSet_Ici ?_
  intro z hz
  exact MeasureTheory.setIntegral_mono_on (hf.1 z hz) (hg.1 z hz) measurableSet_Icc
    fun θ _ => h z θ

/-! ## The equation, rearranged -/

/-- **`(PolarBSL)` solved for the second derivatives.**  On the open quadrant,
`α² z²∂_zzΨ = -F - α(5+α) z∂_zΨ - ∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`, which is the equation in the
form used by Step 3 of the estimate. -/
theorem Hon.eq_solve {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      = -F z θ - α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)
        - Work.Spaces.pthIter 2 Ψ z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ := by
  have hb := h.eq z hz θ h0 h1
  rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at hb
  linarith [hb]

/-- The same identity in the notation of the estimate: with `A = z²∂_zzΨ`, `B = ∂_θθΨ`,
`G = z∂_zΨ` and `u = ∂_θ(tan θ · Ψ)`, `α²A = -F - α(5+α)G - B + u - 6Ψ` on the open quadrant. -/
theorem Hon.eq_solve' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    α ^ 2 * ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
      = -F z θ - α * (5 + α) * ((fun z θ => z * Work.Spaces.pz Ψ z θ) z θ)
        - (Work.Spaces.pthIter 2 Ψ) z θ
        + (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)) z θ - 6 * Ψ z θ :=
  h.eq_solve hz h0 h1

end Work.FTS.EllipticEst.Honest
