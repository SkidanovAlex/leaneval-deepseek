import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.trunc_identity
import Submission.Work.FTS.EllipticEst.AeI1Fts.IP_add_repr
import Submission.Work.FTS.EllipticEst.AeI1Fts.tendsto_terms_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.tendsto_term_psi_cut
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/radial_alt` — the radial `z`-integration by parts of the chain, assembled

This is the assembly of the identity

  `IP (AA u)(BB u) + IP (cw·U)(BB u) = ∫_z w²∫_θ V²σ - 2η·∫_z w²∫_θ U·V·cos(2θ)·σ₁`

out of

* the *truncated* identity `trunc_identity` (both integrations by parts against the two
  cut-offs `χ_k = cut k` and `ψ_k = SliceMixedAux.cut (1/(k+1))`, proved), and
* the four `k → ∞` limits collected in `tendsto_terms_cut` together with the vanishing of the
  boundary term `tendsto_term_psi_cut`, and
* the representation `IP_add_repr` of the two pairings on the left.

Route of the limit passage (the cut-offs are sent to `1` simultaneously): the `z`-cut-off term
vanishes because `|∫_θ σ ψ (U·BB)| ≤ √(∫_θ σU²)·√(∫_θ σB²)·w²` and the extra factor `z·χ_k'`
is uniformly bounded with support escaping to `0` and `∞` (`cut_deriv_tendsto_zero`); the
`ψ`-cut-off term vanishes by the endpoint rate of `U` (`slice_rate`); the three remaining terms
pass to their limits by dominated convergence (`HkMem` of `AA`, `BB`, `V` and the `N`-bound of
`N_bound`, which controls `w²U²cos²(2θ)σ₂`).
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

theorem radial_identity_alt {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.U u))
    (hV : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.V u))
    (hA : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.AA u))
    (hB : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.BB u)) :
    Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeI1Fts.AA u)
        (Work.FTS.EllipticEst.AeI1Fts.BB u)
      + Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AeI1Fts.U u z θ)
          (Work.FTS.EllipticEst.AeI1Fts.BB u)
      = (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2
                  * Work.FTS.EllipticEst.AeI1Fts.sigE θ)
        - 2 * Work.Spaces.eta
            * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
                * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                    Work.FTS.EllipticEst.AeI1Fts.U u z θ
                      * Work.FTS.EllipticEst.AeI1Fts.V u z θ * Real.cos (2 * θ)
                      * Work.FTS.EllipticEst.AeI1Fts.sig1 θ) := by
  obtain ⟨h1, h2, h3, h4⟩ := tendsto_terms_cut h hU hV hA hB
  have h5 := tendsto_term_psi_cut h hU hV
  -- the limit of the truncated right-hand side
  have hRHS : Filter.Tendsto (fun k : ℕ =>
        - (∫ z in Set.Ioi 0, (z * deriv (Work.FTS.EllipticEst.cut k) z)
              * (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, sigE θ
              * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
              * (U u z θ * BB u z θ))
        + (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
            * ∫ θ in Iθo, sigE θ
              * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
              * (V u z θ) ^ 2)
        - 2 * Work.Spaces.eta * (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z
            * (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, sig1 θ
              * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
              * (U u z θ * V u z θ * Real.cos (2 * θ)))
        + (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
            * ∫ θ in Iθo, sigE θ
              * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
              * (U u z θ * V u z θ)))
      Filter.atTop
      (nhds (-(0 : ℝ)
        + (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, sigE θ * (V u z θ) ^ 2)
        - 2 * Work.Spaces.eta * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo,
            sig1 θ * (U u z θ * V u z θ * Real.cos (2 * θ)))
        + 0)) := by
    have hcomb := ((h2.neg.add h3).sub (h4.const_mul (2 * Work.Spaces.eta))).add h5
    simpa only [Pi.zero_apply] using hcomb
  -- the truncated identity, in the limit
  have hlimA : Filter.Tendsto (fun k : ℕ => ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z
        * (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, sigE θ
          * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
          * (AA u z θ * BB u z θ
              + Work.FTS.EllipticEst.AngSecond.cw z * U u z θ * BB u z θ))
      Filter.atTop
      (nhds (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, sigE θ
          * (AA u z θ * BB u z θ
              + Work.FTS.EllipticEst.AngSecond.cw z * U u z θ * BB u z θ))) := h1
  have huniq : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, sigE θ
        * (AA u z θ * BB u z θ
            + Work.FTS.EllipticEst.AngSecond.cw z * U u z θ * BB u z θ))
      = (-(0 : ℝ)
        + (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, sigE θ * (V u z θ) ^ 2)
        - 2 * Work.Spaces.eta * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo,
            sig1 θ * (U u z θ * V u z θ * Real.cos (2 * θ)))
        + 0) := by
    refine tendsto_nhds_unique (Filter.Tendsto.congr' ?_ hlimA) hRHS
    exact Filter.Eventually.of_forall (fun k => trunc_identity h k)
  -- identification of the three values
  have hC : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo,
        sigE θ * (V u z θ) ^ 2)
      = (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo,
          (V u z θ) ^ 2 * sigE θ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    congr 1
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)
  have hD : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo,
        sig1 θ * (U u z θ * V u z θ * Real.cos (2 * θ)))
      = (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo,
          U u z θ * V u z θ * Real.cos (2 * θ) * sig1 θ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    congr 1
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)
  rw [hC, hD] at huniq
  rw [IP_add_repr h hU hA hB, huniq]
  ring

end

end Work.FTS.EllipticEst.AeI1Fts
