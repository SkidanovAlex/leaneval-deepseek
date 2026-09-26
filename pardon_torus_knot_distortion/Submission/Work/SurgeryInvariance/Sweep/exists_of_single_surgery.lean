import Mathlib
import Submission.Work.SurgeryInvariance.Core

/-!
# A single `2`-surgery is realised by a sweep

`Work.SurgeryInvariance.Sweep` records a one-parameter family of regions cut out of the torus by a
family of spheres: away from a finite exceptional set the region moves by an ambient isotopy of
`ℝ³` preserving the surface (`RegionIsotopic`), and at an exceptional parameter it changes by a
single `2`-surgery (`SurgeryShape`), i.e. by adding or removing the **interior of an embedded disc
of the surface**.

This file provides the *converse* direction, namely that the local model of a single surgery is
realised by an honest sweep: if the region `A` is obtained from the region `A'` by adjoining the
interior of an embedded disc `D` of `F`, the two regions being disjoint and open in `F`, then there
is a sweep whose region at time `0` is `A` and whose region at time `1` is `A'`.

The sweep is the piecewise constant family `region t = A` for `t ≤ 1/2` and `region t = A'` for
`t > 1/2`, with the single exceptional parameter `1/2`.  It is regular (`RegionIsotopic.refl`)
everywhere else, and at `1/2` the region on the right of the critical parameter is obtained from
the region on the left by exactly the surgery modelled by `D`.  No regularity of the family in the
parameter is required by the structure `Sweep`, so this constant-in-between family is legitimate.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.SurgeryInvariance.Sweep

/-- **The local model of a single `2`-surgery is a sweep.**  If `A = A' ∪ D.interior` with `A'`
and `D.interior` open in the surface and disjoint, there is a sweep `S` of `F` with `S.region 0 =
A` and `S.region 1 = A'`: the family is constant equal to `A` before the critical parameter `1/2`
and constant equal to `A'` after it, the surgery at `1/2` being exactly the passage from `A` to
`A'` through the interior of the embedded disc `D`. -/
theorem exists_of_single_surgery {P : Work.CoreTopology.ParamTorus}
    (A A' : Set LeanEval.KnotTheory.PardonDistortion.R3) (D : Work.SurgeryInvariance.DiscRegion P)
    (hopen : Work.SurgeryInvariance.IsOpenInCarrier P A')
    (hdisj : Disjoint A' D.interior)
    (hA : A = A' ∪ D.interior) :
    ∃ S : Work.SurgeryInvariance.Sweep P, S.region 0 = A ∧ S.region 1 = A' := by
  classical
  -- `A` is open in the surface, being the union of the two open pieces `A'` and `D.interior`.
  have hAopen : Work.SurgeryInvariance.IsOpenInCarrier P A := by
    rw [hA]
    exact Work.SurgeryInvariance.isOpenInCarrier_union P hopen D.open_interior'
  -- the passage `A → A'` is exactly the geometric shape of a single `2`-surgery through `D`.
  have hshape : Work.SurgeryInvariance.SurgeryShape P A A' :=
    ⟨D, hAopen, hopen, Or.inl ⟨hA, hdisj⟩⟩
  refine ⟨⟨fun t => if t ≤ (1/2 : ℝ) then A else A', {1/2}, ?_, ?_⟩, ?_, ?_⟩
  · -- away from the critical parameter `1/2` the family is locally constant
    intro t ht
    have ht' : t ≠ 1/2 := by simpa using ht
    rcases lt_or_gt_of_ne ht' with hlt | hgt
    · have htle : t ≤ (1/2 : ℝ) := le_of_lt hlt
      refine ⟨1/2 - t, by linarith, ?_, ?_⟩
      · intro s hs
        simp only [Finset.mem_singleton]
        have hslt : s < 1/2 := by
          have := le_abs_self (s - t)
          linarith [abs_lt.mp hs]
        exact ne_of_lt hslt
      · intro s hs
        have hsle : s ≤ (1/2 : ℝ) := by
          have := le_abs_self (s - t)
          linarith [abs_lt.mp hs]
        rw [if_pos htle, if_pos hsle]
        exact Work.SurgeryInvariance.RegionIsotopic.refl P A
    · have htle : ¬ (t ≤ (1/2 : ℝ)) := not_le.mpr hgt
      refine ⟨t - 1/2, by linarith, ?_, ?_⟩
      · intro s hs
        simp only [Finset.mem_singleton]
        have hsgt : 1/2 < s := by
          have := neg_le_abs (s - t)
          linarith [abs_lt.mp hs]
        exact ne_of_gt hsgt
      · intro s hs
        have hsle : ¬ (s ≤ (1/2 : ℝ)) := by
          have := neg_le_abs (s - t)
          linarith [abs_lt.mp hs]
        rw [if_neg htle, if_neg hsle]
        exact Work.SurgeryInvariance.RegionIsotopic.refl P A'
  · -- at the critical parameter the family changes by the single surgery `A → A'`
    intro t ht
    have ht1 : t = 1/2 := by simpa using ht
    subst ht1
    refine ⟨1, one_pos, fun s _ => ?_⟩
    by_cases hsle : s ≤ (1/2 : ℝ)
    · right
      rw [if_pos (le_refl ((1/2 : ℝ))), if_pos hsle]
      exact Work.SurgeryInvariance.RegionIsotopic.refl P A
    · left
      rw [if_pos (le_refl ((1/2 : ℝ))), if_neg hsle]
      exact hshape
  · show (if (0 : ℝ) ≤ (1/2 : ℝ) then A else A') = A
    rw [if_pos (by norm_num)]
  · show (if (1 : ℝ) ≤ (1/2 : ℝ) then A else A') = A'
    rw [if_neg (by norm_num)]

end Work.SurgeryInvariance.Sweep
