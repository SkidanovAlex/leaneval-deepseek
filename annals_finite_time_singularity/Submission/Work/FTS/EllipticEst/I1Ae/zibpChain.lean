import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.pointwise_ident
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_zouter
import Submission.Work.FTS.EllipticEst.AeI1Fts.iter_swap_compact
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `I1Ae/zibpChain` — the radial integration by parts in the `z`-outer iterated form

`AeI1Fts.zibp_cut` is the pointwise-in-`θ` identity

  `∫_z χ_n w² Fp u(·,θ) = -∫_z χ_n' (z∂_zu)(∂_θθu) w²`,

and `AeI1Fts.zibp_zouter` integrates it against the angular weight `σ·χ_ε` after pulling the
`z`-dependent factors out of the *inner* (`θ`-)integral.  The present target is the same
identity in the *opposite* grouping: both sides are `z`-outer iterated integrals whose inner
(`θ`-)integrands still carry the `z`-factors `χ_n z`, `w²z` and `χ_n'`.  The proof is therefore
two `integral_const_mul` pull-outs (`zibpChain_inner_lhs`, `zibpChain_inner_rhs`) turning the
two iterated integrals into the shape of `zibp_zouter`, followed by `zibp_zouter` itself.

The degenerate case `π/2 < ε` is handled separately: then `χ_ε` vanishes identically, because
its two plateaus `θ > ε/2` and `θ < π/2 - ε/2` are disjoint.
-/

namespace Work.FTS.EllipticEst.I1Ae

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- **Pull the `z`-factors out of the inner `θ`-integral (left hand side).** -/
private theorem zibpChain_inner_lhs {u : ℝ → ℝ → ℝ} (n : ℕ) (ε : ℝ) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
          * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
          * Work.FTS.EllipticEst.AeI1Fts.Fp u z θ)
      = ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
          * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
              * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
              * Work.FTS.EllipticEst.AeI1Fts.Fp u z θ := by
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
          * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
          * Work.FTS.EllipticEst.AeI1Fts.Fp u z θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
            * (Work.FTS.EllipticEst.AeI1Fts.sigE θ * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
                * Work.FTS.EllipticEst.AeI1Fts.Fp u z θ) from
    setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]

/-- **Pull the `z`-factors out of the inner `θ`-integral (right hand side), rewriting `Fd` as
`z w² · (U u · BB u)`.** -/
private theorem zibpChain_inner_rhs {u : ℝ → ℝ → ℝ} (n : ℕ) (ε : ℝ) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.AeI1Fts.sigE θ * deriv (Work.FTS.EllipticEst.cut n) z
          * (Work.FTS.EllipticEst.SliceMixedAux.cut ε θ * Work.FTS.EllipticEst.AeI1Fts.Fd u z θ))
      = ∫ z in Set.Ioi 0, (z * deriv (Work.FTS.EllipticEst.cut n) z)
          * (Work.Spaces.w z) ^ 2
          * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
              * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
              * (Work.FTS.EllipticEst.AeI1Fts.U u z θ
                  * Work.FTS.EllipticEst.AeI1Fts.BB u z θ) := by
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.AeI1Fts.sigE θ * deriv (Work.FTS.EllipticEst.cut n) z
          * (Work.FTS.EllipticEst.SliceMixedAux.cut ε θ * Work.FTS.EllipticEst.AeI1Fts.Fd u z θ))
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
          ((z * deriv (Work.FTS.EllipticEst.cut n) z) * (Work.Spaces.w z) ^ 2)
            * (Work.FTS.EllipticEst.AeI1Fts.sigE θ
                * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
                * (Work.FTS.EllipticEst.AeI1Fts.U u z θ
                    * Work.FTS.EllipticEst.AeI1Fts.BB u z θ)) from
    setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by
      simp only [Work.FTS.EllipticEst.AeI1Fts.Fd, Work.FTS.EllipticEst.AeI1Fts.U,
        Work.FTS.EllipticEst.AeI1Fts.BB]
      ring)]
  rw [MeasureTheory.integral_const_mul]

/-- The angular cut-off vanishes identically as soon as `π/2 < ε`: the two plateau conditions
`θ > ε/2` and `θ < π/2 - ε/2` are then incompatible. -/
private theorem cut_eq_zero_of_pi_half_lt {ε θ : ℝ} (hε : 0 < ε) (hπε : Real.pi / 2 < ε) :
    Work.FTS.EllipticEst.SliceMixedAux.cut ε θ = 0 := by
  rcases le_or_gt θ (ε / 2) with h1 | h1
  · exact Work.FTS.EllipticEst.SliceMixedAux.cut_eq_zero_low hε h1
  · exact Work.FTS.EllipticEst.SliceMixedAux.cut_eq_zero_high hε (by linarith)

theorem zibpChain {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
          * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
          * Work.FTS.EllipticEst.AeI1Fts.Fp u z θ)
      = - (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.AeI1Fts.sigE θ * deriv (Work.FTS.EllipticEst.cut n) z
          * (Work.FTS.EllipticEst.SliceMixedAux.cut ε θ * Work.FTS.EllipticEst.AeI1Fts.Fd u z θ)) := by
  by_cases hπ : ε ≤ Real.pi / 2
  · -- the non-degenerate case: `zibp_cut`, integrated against `σ · χ_ε` with the two swaps
    have hS : Work.FTS.EllipticEst.SmoothOpen u :=
      Work.FTS.EllipticEst.smoothOpen_of_forall (fun m => h.smooth m)
    calc (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * Work.FTS.EllipticEst.AeI1Fts.Fp u z θ)
        = ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
                * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
                * Work.FTS.EllipticEst.AeI1Fts.Fp u z θ := zibpChain_inner_lhs n ε
      _ = - (∫ z in Set.Ioi 0, (z * deriv (Work.FTS.EllipticEst.cut n) z)
              * (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
                * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
                * (Work.FTS.EllipticEst.AeI1Fts.U u z θ
                    * Work.FTS.EllipticEst.AeI1Fts.BB u z θ)) :=
          Work.FTS.EllipticEst.AeI1Fts.zibp_zouter hS n hε hπ
      _ = - (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
            Work.FTS.EllipticEst.AeI1Fts.sigE θ * deriv (Work.FTS.EllipticEst.cut n) z
              * (Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
                  * Work.FTS.EllipticEst.AeI1Fts.Fd u z θ)) := by
          rw [zibpChain_inner_rhs]
  · -- the degenerate case: `χ_ε` vanishes everywhere, so both integrals are `0`
    have hπε : Real.pi / 2 < ε := not_le.mp hπ
    have hzero : ∀ θ : ℝ, Work.FTS.EllipticEst.SliceMixedAux.cut ε θ = 0 :=
      fun θ => cut_eq_zero_of_pi_half_lt hε hπε
    simp only [hzero, mul_zero, zero_mul, integral_zero, neg_zero]

end

end Work.FTS.EllipticEst.I1Ae
