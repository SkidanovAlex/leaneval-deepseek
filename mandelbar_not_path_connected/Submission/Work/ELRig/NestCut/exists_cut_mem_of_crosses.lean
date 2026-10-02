/-
# NestCut — the cut points of the nest at `b₂` are met by every crossing `K`-continuum

`exists_cut_mem_of_crosses` is the arm-free form of the cut point crossing lemma
`Work.EL.B2Data.cut_mem_of` of `Submission/Work/ELRig/Arm.lean`: a preconnected subset `T` of
the filled Julia set `K c` which meets the level-`n` nest region `tr.Δ n` and contains a point
outside its closure must contain one of the three cut points `tr.cut Z n`.

The arm is not an input here, it is produced: `T` meets `frontier (Δ n) ∩ K c` (the frontier
crossing lemma `Work.EL.meets_frontier_of`), and the tripod curve meets `K c` only in its branch
point `b₂`, which lies in the *interior* of the open region `Δ n` and hence not on its frontier.
So the crossing point lies in one of the three arms of the tripod, and
`B2Data.cut_unique` identifies it with the cut point of that arm.
-/
import Mathlib
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELRig.NestCut

/-- The tripod curve meets the filled Julia set only in its branch point: the three rays of the
tripod miss `K c` (`paramRay_subset_compl`). -/
theorem tripodCurve_inter_K_subset {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (y : ℂ) :
    Work.EL.tripodCurve hN y ∩ Work.EL.K c ⊆ {y} := by
  rintro z ⟨hz1, hz2⟩
  simp only [Work.EL.tripodCurve, Set.mem_union, Set.mem_singleton_iff] at hz1
  rcases hz1 with ((h | h) | h) | h
  · exact absurd hz2 ((Work.EL.paramRay_subset_compl hN Work.EL.b2a) h)
  · exact absurd hz2 ((Work.EL.paramRay_subset_compl hN Work.EL.b2b) h)
  · exact absurd hz2 ((Work.EL.paramRay_subset_compl hN Work.EL.b2c) h)
  · exact h

theorem exists_cut_mem_of_crosses {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {z₁ : ℂ}
    (tr : Work.EL.B2Data hN z₁) (n : ℕ) {T : Set ℂ}
    (hconn : IsPreconnected T) (hT : T ⊆ Work.EL.K c) (hmeet : (T ∩ tr.Δ n).Nonempty)
    {x' : ℂ} (hx' : x' ∈ T) (hx'c : x' ∉ closure (tr.Δ n)) :
    ∃ Z : Work.EL.ArmIdx, tr.cut Z n ∈ T := by
  obtain ⟨xin, hxinT, hxinΔ⟩ := hmeet
  obtain ⟨z, hzT, hzfr⟩ := Work.EL.meets_frontier_of (tr.isOpen_Δ n) hconn hxinT hxinΔ hx' hx'c
  have hzK : z ∈ Work.EL.K c := hT hzT
  -- the crossing point is off the tripod curve
  have hzNotTripod : z ∉ Work.EL.tripodCurve hN tr.b₂ := by
    intro hzc
    have hzb : z = tr.b₂ := by
      have h := tripodCurve_inter_K_subset hN tr.b₂ ⟨hzc, hzK⟩
      simpa using h
    -- but `b₂` lies in the open region `Δ n`, so it is not on its frontier
    have hznotΔ : z ∉ tr.Δ n := by
      have hzcl : z ∈ closure ((tr.Δ n)ᶜ) := by
        have h2 : z ∈ closure (tr.Δ n) ∩ closure ((tr.Δ n)ᶜ) :=
          (frontier_eq_closure_inter_closure (s := tr.Δ n)) ▸ hzfr
        exact h2.2
      rw [IsClosed.closure_eq ((tr.isOpen_Δ n).isClosed_compl)] at hzcl
      exact fun hzΔ => hzcl hzΔ
    exact hznotΔ (hzb ▸ tr.b2_mem_Δ n)
  -- hence it lies in one of the three arms, and there `cut_unique` identifies it
  rcases tr.tripod.mem_arm_of hzNotTripod with hA | hB | hC
  · refine ⟨Work.EL.ArmIdx.A, ?_⟩
    have hm : z ∈ frontier (tr.Δ n) ∩ Work.EL.K c ∩ Work.EL.armOf tr.tripod Work.EL.ArmIdx.A :=
      ⟨⟨hzfr, hzK⟩, hA⟩
    rw [tr.cut_unique Work.EL.ArmIdx.A n] at hm
    exact (Set.mem_singleton_iff.mp hm) ▸ hzT
  · refine ⟨Work.EL.ArmIdx.B, ?_⟩
    have hm : z ∈ frontier (tr.Δ n) ∩ Work.EL.K c ∩ Work.EL.armOf tr.tripod Work.EL.ArmIdx.B :=
      ⟨⟨hzfr, hzK⟩, hB⟩
    rw [tr.cut_unique Work.EL.ArmIdx.B n] at hm
    exact (Set.mem_singleton_iff.mp hm) ▸ hzT
  · refine ⟨Work.EL.ArmIdx.C, ?_⟩
    have hm : z ∈ frontier (tr.Δ n) ∩ Work.EL.K c ∩ Work.EL.armOf tr.tripod Work.EL.ArmIdx.C :=
      ⟨⟨hzfr, hzK⟩, hC⟩
    rw [tr.cut_unique Work.EL.ArmIdx.C n] at hm
    exact (Set.mem_singleton_iff.mp hm) ▸ hzT

end Work.ELRig.NestCut
