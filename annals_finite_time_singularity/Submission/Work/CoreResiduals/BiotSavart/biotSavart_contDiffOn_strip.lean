import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one
import Submission.Work.CoreResiduals.BiotSavart.DerivDefs
import Submission.Work.CoreResiduals.BiotSavart.TimeDerivContinuous
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_dtContinuous
import Submission.Work.CoreResiduals.BiotSavart.timeDeriv_xHolderOn_of_stripBundle
import Submission.Work.CoreResiduals.BiotSavart.exists_windowExtension_of_stripBundle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Metric Filter Topology Set
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

/-- **The `C¹` clause of the space-time statement, for a bundled strip vorticity.**

For `0 < α < 1` and `ω` satisfying the full strip bundle `BSAdmissibleStripFull α ω R S`, the reconstructed velocity `q ↦ BS (ω(·,q.2)) q.1` is `C¹` on the strip `ℝ³ × [0,S]`.

This is one of the three conjuncts of `IsContDiffHolderOn` in the space-time statement (`BiotSavartSpaceTime α`), and it is the qualitative part: the workspace already proves the same `C¹` statement for the bundle `BSAdmissibleOnWindow ω R T` together with `TimeDerivLocallyLipschitz ω T` (`BiotSavart.biotSavartSpacetimeC1_holds`).

**Suggested route.**  `ContDiffOn` on the strip is local, so it suffices to prove `ContDiffWithinAt ℝ 1 f (univ ×ˢ Icc 0 S) (x,t)` for each `t ∈ Icc 0 S`.  Both the `x`-derivative (Calderón–Zygmund, needs support/boundedness/`x`-Hölder of the slice `ω(·,t)`) and the `t`-derivative (differentiation under the integral sign, `Work.StabilityFar.Decay.hasDerivAt_biotSavart`, needs the slices `t`-differentiable with bounded `∂ₜω`) are local in `t` inside the strip, so the endpoints are not a problem: one can re-run the argument of `biotSavartSpacetimeC1_holds` with the strip bundle's clauses restricted to `Icc 0 S` (they all hold there), or extend `ω` in `t` and instantiate the existing window result (the reviewer's note: the extension must make `∂ₜω̃` *locally Lipschitz* in `t` for `TimeDerivLocallyLipschitz`, which is available from `TimeDerivStripHolder` only for `α ≥ 1`, so `β < α` should be used if taking the extension route).  Note that `∂ₜω(·,t)` is supported in `closedBall 0 R` on `Icc 0 S` (`TimeDerivStrip` plus the support clause). -/
theorem biotSavart_contDiffOn_strip {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ}
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ContDiffOn ℝ 1 (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1)
      (Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
  by_cases hSneg : S < 0
  · -- The strip is empty: nothing to prove.
    have hIcc : Set.Icc (0:ℝ) S = ∅ := Set.Icc_eq_empty_iff.mpr (not_le.mpr hSneg)
    rw [hIcc, Set.prod_empty]
    exact contDiffOn_empty
  · rcases lt_or_eq_of_le (not_lt.mp hSneg) with hSpos | hSzero
    · -- `0 < S`: extend `ω` to a two-sided window and apply the window theorem.
      obtain ⟨c, hcpos, Cx, hCxnn, hxH⟩ := timeDeriv_xHolderOn_of_stripBundle hα hα1 hSpos hbun
      obtain ⟨ω_ext, hagree, hadmw, hdtcw⟩ :=
        exists_windowExtension_of_stripBundle hα hα1 hSpos hbun ⟨c, hcpos, Cx, hCxnn, hxH⟩
      have hOn : ContDiffOn ℝ 1 (fun q : Work.LWP.R3 × ℝ =>
          Work.LWP.biotSavart (fun y => ω_ext y q.2) q.1) (Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
        intro q hq
        have hqIcc : q.2 ∈ Set.Icc (0:ℝ) S := hq.2
        have ht : q.2 ∈ Work.ConstructionInstance.preWindow (S + 1) := by
          change q.2 ∈ Set.Ioo (-2) (S + 1)
          exact ⟨by linarith [hqIcc.1], by linarith [hqIcc.2]⟩
        exact (biotSavartSpacetimeC1_of_dtContinuous hadmw hdtcw q.1 q.2 ht).contDiffWithinAt
      refine ContDiffOn.congr hOn ?_
      intro q hq
      have hfun : (fun y : Work.LWP.R3 => ω y q.2) = (fun y => ω_ext y q.2) :=
        funext fun y => (hagree q.2 hq.2 y).symm
      rw [hfun]
    · -- `S = 0`: the strip is the hyperplane `{t = 0}` and the field is a single slice.
      obtain rfl : S = 0 := hSzero.symm
      obtain ⟨⟨hRpos, hsupp, hbdd, hhold, htime, hmeas⟩, ⟨hdc, hbddD, hmeasD⟩, hholdD⟩ := hbun
      obtain ⟨M, hM⟩ := hbdd
      obtain ⟨H, hH⟩ := hhold
      have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 0 := Set.left_mem_Icc.mpr le_rfl
      have hbdd0 : ∀ a : Work.LWP.R3, ‖ω a 0‖ ≤ max M 0 :=
        fun a => le_trans (hM 0 h0 a) (le_max_left _ _)
      have hsupp0 : ∀ a : Work.LWP.R3, ω a 0 ≠ 0 → a ∈ Metric.closedBall 0 R :=
        fun a ha => hsupp 0 h0 a ha
      have hmeas0 : MeasureTheory.AEStronglyMeasurable (fun a : Work.LWP.R3 => ω a 0)
          MeasureTheory.volume := hmeas 0 h0
      have hhold0 : ∀ a b : Work.LWP.R3,
          ‖ω a 0 - ω b 0‖ ≤ (H : ℝ) * ‖a - b‖ ^ (α : ℝ) := by
        intro a b
        have hH0 : HolderWith H α (fun x : Work.LWP.R3 => ω x 0) := hH 0 h0
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hH0.dist_le a b
      have hF : ContDiff ℝ 1 (Work.LWP.biotSavart (fun y => ω y 0)) :=
        biotSavart_contDiff_one hRpos (le_max_right _ _) hα hbdd0 hsupp0 hmeas0 hhold0
      refine ContDiffOn.congr
        (((hF.comp contDiff_fst).contDiffOn).mono (Set.subset_univ _)) ?_
      intro q hq
      have hq0 : q.2 = 0 := by
        obtain ⟨hq1, hq2⟩ := Set.mem_Icc.mp hq.2
        exact le_antisymm hq2 hq1
      rw [hq0]
      rfl

end Work.CoreResiduals.BiotSavart
