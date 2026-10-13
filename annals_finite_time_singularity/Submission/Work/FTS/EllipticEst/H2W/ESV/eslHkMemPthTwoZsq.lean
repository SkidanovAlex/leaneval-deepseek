import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.H2W.AeDataAof
import Submission.Work.FTS.EllipticEst.H2W.ESV.aSliceHonest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∂_θ²(z²∂_z²Ψ) ∈ ℋ⁰` for a datum of the weak class `EllWeakPos α 2 F Ψ`

This module proves `Work.FTS.EllipticEst.H2W.eslHkMemPthTwoZsq`: for every datum
`(F, Ψ)` of the weak hypothesis class `TT.EllWeakPos α 2 F Ψ` (no hypothesis on `α` is
needed), the angular second derivative of the radial datum `z²∂_z²Ψ` is honest at level `0`:

  `HkMem α 0 (∂_θ²(z²∂_z²Ψ))`.

Equivalently — by Clairaut on the open quadrant, where `Ψ` is `C^∞` — the function is
`z² ∂_z²(∂_θ²Ψ) = D_z² H - D_z H` with `H = ∂_θ²Ψ`, and `z²∂_z² = D_z² - D_z`.  The
honesty is therefore read off from the two radial summands

  `(D_z H · w/sin(2θ)^{η/2})²`, `(D_z² H · w/sin(2θ)^{η/2})²`

of the *level-`2`* `ℋ`-integrand of `H`, which is honest by the hypothesis
`TT.EllWeakPos.memB : HkMem α 2 (∂_θ²Ψ)` (`RPFresh.excess_zsummand_mem`), and the pointwise
identity `deriv_deriv_zsq_pzIter2_eq` of `H2W.aSliceHonest`.  The passage from the pointwise
domination to `HkMem α 0` is `RPFresh.HkMem_zero_of_majorant`; the boundary points `z = 0`
and `θ ∈ {0, π/2}`, where the identity is not available, are the junk points of the integrand
(`HkIntegrand_zero_zero`, `HkIntegrand_zero_theta_zero`, `HkIntegrand_zero_theta_pi`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Honesty of `∂_θ²(z²∂_z²Ψ)` at level `0`.**  From smoothness of `Ψ` on the open
quadrant and the honesty of `H = ∂_θ²Ψ` at level `2`, the angular second derivative of the
radial datum `z²∂_z²Ψ` belongs to `ℋ⁰`. -/
theorem HkMem_pthIter2_zsq_pzIter2 {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hmemB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) :
    Work.Spaces.HkMem α 0
      (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
  have hSH : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    smoothOpen_pthIter_H2W hSΨ 2
  -- the two radial summands of the level-`2` integrand of `H = ∂_θ²Ψ`
  have hb1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 1 (Work.Spaces.pthIter 2 Ψ)
      ((hSH.DzIter 1).continuousOn) hmemB (by norm_num)
  have hb2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 2 (Work.Spaces.pthIter 2 Ψ)
      ((hSH.DzIter 2).continuousOn) hmemB (by norm_num)
  -- continuity of the slice function on the open quadrant (via the Clairaut identity)
  have hcontG : ContinuousOn
      (Function.uncurry (fun z θ =>
        deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hbase : ContinuousOn
        (fun p : ℝ × ℝ =>
          p.1 ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (continuousOn_fst.pow 2).mul ((hSH.pzIter 2).continuousOn)
    refine hbase.congr ?_
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact deriv_deriv_zsq_pzIter2_Qop hSΨ hz ⟨hθ0, hθ1⟩
  -- the target function unfolds definitionally to the explicit `deriv` form
  change Work.Spaces.HkMem α 0
    (fun z θ => deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ)
  refine Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_of_majorant (α := α)
    (f := fun z θ =>
      deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ)
    (M := fun z θ =>
      2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
        + 2 * Work.Spaces.HkIntegrand α 0
            (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ)
    hcontG ?_ ?_ ?_
  · -- the `θ`-slices of the majorant are integrable
    intro z hz
    exact ((hb2.1 z hz).const_mul 2).add ((hb1.1 z hz).const_mul 2)
  · -- the `z`-integral of the majorant is integrable
    have h' := (hb2.2.const_mul 2).add (hb1.2.const_mul 2)
    refine h'.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Pi.add_apply, MeasureTheory.integral_add ((hb2.1 z hz).const_mul 2)
      ((hb1.1 z hz).const_mul 2), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  · -- the pointwise domination on the closed quadrant
    intro z hz θ hθ
    have hMnn : 0 ≤ 2 * Work.Spaces.HkIntegrand α 0
          (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
        + 2 * Work.Spaces.HkIntegrand α 0
          (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ := by
      have h₁ := Work.Spaces.HkIntegrand_nonneg α 0
        (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
      have h₂ := Work.Spaces.HkIntegrand_nonneg α 0
        (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ
      linarith
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz_eq | hz_pos
    · -- `z = 0`
      subst hz_eq
      rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_z]
      exact hMnn
    · rcases eq_or_lt_of_le hθ.1 with hθ_eq | hθ_pos
      · -- `θ = 0`
        subst hθ_eq
        rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_theta_zero]
        exact hMnn
      · rcases eq_or_lt_of_le hθ.2 with hθ_eq | hθ_lt
        · -- `θ = π/2`
          subst hθ_eq
          rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_theta_pi]
          exact hMnn
        · -- interior: use the pointwise identity and AM–GM
          rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_eq,
            deriv_deriv_zsq_pzIter2_eq hSΨ hz_pos ⟨hθ_pos, hθ_lt⟩,
            Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_eq,
            Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_eq]
          set A := Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ with hA
          set B := Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ with hB
          set c := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hc
          nlinarith [sq_nonneg (A * c + B * c), sq_nonneg (A * c), sq_nonneg (B * c)]

/-- The requested lemma: for every datum of the weak class `TT.EllWeakPos α 2 F Ψ`, the
function `∂_θ²(z²∂_z²Ψ)` is honest at level `0`. -/
theorem eslHkMemPthTwoZsq (α : ℝ) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    Work.Spaces.HkMem α 0
      (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
  HkMem_pthIter2_zsq_pzIter2 ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mpr h.smooth)
    h.memB

end Work.FTS.EllipticEst.H2W
