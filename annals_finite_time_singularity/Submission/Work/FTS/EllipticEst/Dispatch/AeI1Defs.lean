/-
Copyright: work module for the Elgindi finite-time singularity project.

# Shared vocabulary for `aeI1ChainCompact`

This file owns the abbreviations of the `I₁` chain of Step 2 of `prop:H2`
(Elgindi, Annals 194 (3) 2021) in the *compact* case (support in a rectangle
`[a,b] × [c,d]` with `0 < a` and `d < π/2`), so that the pieces of the chain can
be stated and proved in modules that import this one.

The chain identity is

  `i1D Φ = i1Pp Φ - 2η(1+η) i1N Φ - 2η i1Aa Φ + i1X Φ`,

proved from the two integrations by parts of `I₁` (`SlotA.I1_z_ibp_open` and
`H2W.I1_cross_bookkeeping`) together with the angular integration by parts of
the cross term (`SlotA.cross_theta_ibp`); with the sharp angular Hardy bound
(`i1N ≤ (1+η)^{-2} i1Pp + C i1Aa`) and the Cauchy–Schwarz bound
(`i1X ≥ -2√(i1Aa · i1Bb)`) this gives the lower bound on `i1D` behind the
statement `Work.FTS.EllipticEst.Dispatch.aeI1ChainCompact`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.I1_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false

/-! ## The objects of the chain -/

/-- `U = z ∂_z Φ`. -/
def i1U (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Φ z θ

/-- `B = ∂_θ² Φ`. -/
def i1B (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Φ

/-- `A = z² ∂_z² Φ`. -/
def i1A (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Φ z θ

/-- `Pp = ⟨∂_θ U, ∂_θ U⟩ = ∫∫ (z ∂_z ∂_θ Φ)² w² σ`: the `θ`-derivative of `U`, squared. -/
def i1Pp (Φ : ℝ → ℝ → ℝ) : ℝ :=
  Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pth (i1U Φ)) (Work.Spaces.pth (i1U Φ))

/-- `Aa = ⟨U, U⟩ = ∫∫ (z ∂_z Φ)² w² σ`. -/
def i1Aa (Φ : ℝ → ℝ → ℝ) : ℝ :=
  Work.FTS.EllipticEst.AngSecond.IP (i1U Φ) (i1U Φ)

/-- `Bb = ⟨B, B⟩ = ∫∫ (∂_θ² Φ)² w² σ`. -/
def i1Bb (Φ : ℝ → ℝ → ℝ) : ℝ :=
  Work.FTS.EllipticEst.AngSecond.IP (i1B Φ) (i1B Φ)

/-- `D = ⟨A, B⟩ = ∫∫ (z² ∂_z² Φ)(∂_θ² Φ) w² σ`: the mixed pairing bounded below. -/
def i1D (Φ : ℝ → ℝ → ℝ) : ℝ :=
  Work.FTS.EllipticEst.AngSecond.IP (i1A Φ) (i1B Φ)

/-- `N = ∫_z w² ∫_θ (z ∂_z Φ)² cos²(2θ) sin(2θ)^{-(2+η)}`, the `cos²`-weighted term
produced by the angular integration by parts.  Note that no `σ`-factor is present: the
weight here is `sin(2θ)^{-(2+η)}`. -/
def i1N (Φ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
    * ∫ θ in Work.Spaces.Iθ, (i1U Φ z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))

/-- `X = -⟨cw · U, B⟩` with `cw z = 2(z-1)/(1+z) = 2 - 4/(1+z)`: the transfer term of the
`z`-integration by parts (the `(w²)'` term). -/
def i1X (Φ : ℝ → ℝ → ℝ) : ℝ :=
  - Work.FTS.EllipticEst.AngSecond.IP
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * i1U Φ z θ) (i1B Φ)

/-! ## Identification of `HkSq α 0` with the weighted pairing -/

/-- `HkSq α 0 g` is the `w² σ`-weighted `L²`-mass of `g`, i.e. `⟨g, g⟩`. -/
theorem HkSq_zero_eq_IP (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g = Work.FTS.EllipticEst.AngSecond.IP g g := by
  have hI : Work.Spaces.HkIntegrand α 0 g
      = fun z θ => (g z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    funext z θ
    simp only [Work.Spaces.HkIntegrand]
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Work.Spaces.DzIter_zero]
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
  rw [Work.Spaces.HkSq, hI, ← Work.Spaces.L2Sq,
    Work.FTS.EllipticEst.AngSecond.L2Sq_mul_W]

/-! ## Elementary nonnegativity -/

theorem i1Aa_nonneg (Φ : ℝ → ℝ → ℝ) : 0 ≤ i1Aa Φ :=
  Work.FTS.EllipticEst.AngSecond.IP_self_nonneg _

theorem i1Bb_nonneg (Φ : ℝ → ℝ → ℝ) : 0 ≤ i1Bb Φ :=
  Work.FTS.EllipticEst.AngSecond.IP_self_nonneg _

theorem i1Pp_nonneg (Φ : ℝ → ℝ → ℝ) : 0 ≤ i1Pp Φ :=
  Work.FTS.EllipticEst.AngSecond.IP_self_nonneg _

end Work.FTS.EllipticEst.Dispatch
