/-
# `GalFields/Norm/radA_slotSum4_le` — the order-`4` weighted `L²`-bound for the radial
transfer profile `radA α f`

For every `0 < α ≤ 1` and every `f ∈ CoerAdm α` with `HkMem α 4 f`, the whole slot sum

  `∑_{j<5} (D_z^j (radA α f)(z))² w(z)²`

is integrable on `Iz = [0,∞)` and its integral is bounded by
`C·(|f|²_{ℋ⁴} + |D_θ f|²_{ℋ⁴})` with a constant `C` independent of `α` and `f`.

This is `E1Norm.radA_sum_le` (`n ≤ 3`) at the top slot `n = 4`, which is the sharp reachable
order: `CoerAdm α f` supplies `ℋ⁵`-membership (`RegQ α 5`), hence `L₁₂ f ∈ C⁴((0,∞))` and the
order-`4` slot `D_z^4 (L₁₂ f) = -Qang f 3` (weighted integrability of `Qang f 3` is the
boundary `i ≤ 4` of the angular-moment estimates).  The order-`4` assembly is in
`Submission/Work/FTS/GalFields/Norm/RadA4/Own.lean`; here we only instantiate its constants:

* `RadA4.radA_sum_le_four` (the radial bound at order `4`);
* `RadA4.ampB_slotSum5_bound` and `E1Norm.ampA_uniform_bound` (the two `α`-uniform profile
  bounds);
* `E1Norm.Qang_sq_w_sq_le_HkSq` (the angular moments, constant `∫_θ K²`);
* `E1Norm.C0_sq_le_HkSq` (the projector constant, `(C₀ f)² ≤ 64|f|²_{ℋ⁴}`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Radial
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Main
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.C0_sq_le_HkSq
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Qang_sq_w_sq_le_HkSq
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadA
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadABnd
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAId
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAPieces
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadL12
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.GalFields.Norm.RadA4.Own

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.Norm

theorem radA_slotSum4_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.Nonlin.CoerAdm α f → Work.Spaces.HkMem α 4 f →
      MeasureTheory.IntegrableOn
          (fun z : ℝ => ∑ j ∈ Finset.range 5,
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range 5,
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
          ≤ C * (Work.Spaces.HkSq α 4 f + Work.Spaces.HkSq α 4 (Work.Spaces.Dth f)) := by
  obtain ⟨Kb, hKbpos, hKb⟩ := Work.FTS.GalFields.Norm.RadA4.ampB_slotSum5_bound
  obtain ⟨KA, hKApos, hKA⟩ := Work.FTS.CoercivityFix.Transfer.E1Norm.ampA_uniform_bound
  have hKth : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.GalFields.Norm.RadA4.radA_sum_le_four
    (CQ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) (CC := 64) (Kb := Kb) (K := KA)
    hKth (by norm_num) hKbpos hKApos.le
    (fun β m g hβ hβ1 hsm hmem i hi =>
      Work.FTS.CoercivityFix.Transfer.E1Norm.Qang_sq_w_sq_le_HkSq m β g hβ hβ1 hsm hmem i hi)
    (fun β m g hβ hβ1 hg hmem =>
      Work.FTS.CoercivityFix.Transfer.E1Norm.C0_sq_le_HkSq β hβ hβ1 m hg hmem)
    (fun β hβ hβ1 => hKb β hβ hβ1)
    (fun β hβ hβ1 b hb z hz => hKA β hβ hβ1 b hb z hz)
  exact ⟨C, hCpos, fun α hα hα1 f hf hmem => hC α 4 f hα hα1 le_rfl hf hmem⟩

end Work.FTS.GalFields.Norm
