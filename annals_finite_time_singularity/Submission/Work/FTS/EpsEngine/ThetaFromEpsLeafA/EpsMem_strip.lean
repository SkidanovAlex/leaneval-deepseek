import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.StripDefs
import Submission.Work.FTS.StrongEps.EpsSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ThetaFromEpsLeafA/EpsMem_strip` — the strip truncations of an `EpsMem` profile are `EpsMem`

`EpsMem α f` is the *honesty* predicate of the weighted space `X` of the `ε`-scheme: the weighted
square `(f · epsW α)²` is integrable on the quarter plane `Iz ×ˢ Iθ` (so that `EpsSq α f` is an
honest integral rather than Lean's junk value `0`).

The two angular truncations

    stripLo φ g = (z,θ) ↦ if θ ≤ φ then g z θ else 0 ,
    stripHi φ g = (z,θ) ↦ if π/2 - φ ≤ θ then g z θ else 0

of a profile are *dominated* by the profile itself, so they inherit `EpsMem`.  The point is that
their weighted squares are the indicators of the (measurable) sets `{θ ≤ φ}` resp.
`{π/2 - φ ≤ θ}` times `(g · epsW α)²`:

    (stripLo φ g · epsW α)² = 1_{θ ≤ φ} · (g · epsW α)² ,
    (stripHi φ g · epsW α)² = 1_{π/2 - φ ≤ θ} · (g · epsW α)² .

Integrability of a measurable indicator times an integrable function is
`MeasureTheory.integrable_indicator_iff`.  All of `φ` is allowed (for `φ ≤ 0` the lower strip is
a.e. empty on `Iθ`), and no continuity of `g` is needed.
-/

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafA

open MeasureTheory Set

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Multiplying an `if`-whose-`else`-branch-is-`0` by anything and squaring truncates the square. -/
private theorem ite_zero_mul_sq (c : Prop) [Decidable c] (a b : ℝ) :
    ((if c then a else (0 : ℝ)) * b) ^ 2 = if c then (a * b) ^ 2 else 0 := by
  by_cases h : c <;> simp [h]

/-- **Domination by an indicator.**  If the weighted square of `h` is the indicator (of a
measurable set `S`) of the weighted square of `g`, and `g ∈ X`, then `h ∈ X`.

This is the abstract form of both halves of `EpsMem_strip`: the truncated weighted square is the
indicator of the corresponding angular half-plane times the untruncated one, and the indicator may
be moved inside the integral. -/
private theorem epsMem_of_indicator {α : ℝ} {g h : Work.FTS.Galerkin.Fn}
    (hg : Work.FTS.StrongEps.EpsMem α g) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hfun : (fun p : ℝ × ℝ => (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      = S.indicator (fun p : ℝ × ℝ =>
          (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)) :
    Work.FTS.StrongEps.EpsMem α h := by
  have hs : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  have hInt : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hg
  rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, hfun]
  refine (MeasureTheory.integrable_indicator_iff hs).mp ?_
  have hEq : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator
        (S.indicator (fun p : ℝ × ℝ =>
          (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
      = (S ∩ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)).indicator
        (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) := by
    funext p
    by_cases hp : p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ
    · rw [Set.indicator_of_mem hp]
      by_cases hq : p ∈ S
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (Set.mem_inter hq hp)]
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (fun h => hq h.1)]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (fun h => hp h.2)]
  rw [hEq]
  exact (MeasureTheory.integrable_indicator_iff (hS.inter hs)).mpr
    (hInt.mono_set Set.inter_subset_right)

theorem EpsMem_strip {α : ℝ} {g : Work.FTS.Galerkin.Fn}
    (hg : Work.FTS.StrongEps.EpsMem α g) (φ : ℝ) :
    Work.FTS.StrongEps.EpsMem α (Work.FTS.EpsEngine.ThetaFromEps.stripLo φ g) ∧
    Work.FTS.StrongEps.EpsMem α (Work.FTS.EpsEngine.ThetaFromEps.stripHi φ g) := by
  constructor
  · refine epsMem_of_indicator hg (S := {p : ℝ × ℝ | p.2 ≤ φ})
      (measurableSet_le measurable_snd measurable_const) ?_
    funext p
    have hstrip : Work.FTS.EpsEngine.ThetaFromEps.stripLo φ g p.1 p.2
        = if p.2 ≤ φ then g p.1 p.2 else 0 := rfl
    rw [hstrip, ite_zero_mul_sq]
    by_cases hp : p.2 ≤ φ
    · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.2 ≤ φ} from hp), if_pos hp]
    · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.2 ≤ φ} from hp), if_neg hp]
  · refine epsMem_of_indicator hg (S := {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2})
      (measurableSet_le measurable_const measurable_snd) ?_
    funext p
    have hstrip : Work.FTS.EpsEngine.ThetaFromEps.stripHi φ g p.1 p.2
        = if Real.pi / 2 - φ ≤ p.2 then g p.1 p.2 else 0 := rfl
    rw [hstrip, ite_zero_mul_sq]
    by_cases hp : Real.pi / 2 - φ ≤ p.2
    · rw [Set.indicator_of_mem
        (show p ∈ {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2} from hp), if_pos hp]
    · rw [Set.indicator_of_notMem
        (show p ∉ {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2} from hp), if_neg hp]

end Work.FTS.EpsEngine.ThetaFromEpsLeafA
