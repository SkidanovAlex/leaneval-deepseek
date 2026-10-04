import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- **Gluing two one-sided Taylor series across a closed interface.**  Let `w : E → F` and let
`sL, sR` be two *closed* subsets whose union is a neighbourhood of `x₀`, each carrying a Taylor
series for `w` up to order `n` (`HasFTaylorSeriesUpToOn n w pL sL`,
`HasFTaylorSeriesUpToOn n w pR sR`).  If the two series agree on the overlap `sL ∩ sR`, then `w`
is `C^n` at `x₀`.

The two series are glued into a single `p` on `sL ∪ sR` (well defined by the agreement), which is a
`HasFTaylorSeriesUpToOn` because the three fields of that structure are pointwise in the set: the
derivative field is glued by `HasFDerivWithinAt.union` (no side condition) and the continuity field
by `ContinuousOn.union_of_isClosed` (both closedness hypotheses are used). -/
theorem contDiffAt_of_hasFTaylorSeries_glue
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {w : E → F} {x₀ : E} {n : ℕ}
    {sL sR : Set E} {pL pR : E → FormalMultilinearSeries ℝ E F}
    (hL : HasFTaylorSeriesUpToOn (n : WithTop ℕ∞) w pL sL)
    (hR : HasFTaylorSeriesUpToOn (n : WithTop ℕ∞) w pR sR)
    (hcL : IsClosed sL) (hcR : IsClosed sR) (hu : sL ∪ sR ∈ nhds x₀)
    (hagree : ∀ z ∈ sL ∩ sR, pL z = pR z) :
    ContDiffAt ℝ (n : WithTop ℕ∞) w x₀ := by
  classical
  -- The glued series: `pL` where available, `pR` otherwise.
  let p : E → FormalMultilinearSeries ℝ E F := fun z => if z ∈ sL then pL z else pR z
  have hpL : ∀ z ∈ sL, p z = pL z := by
    intro z hz; show (if z ∈ sL then pL z else pR z) = pL z; exact ite_eq_left hz
  have hpR : ∀ z ∈ sR, p z = pR z := by
    intro z hz
    by_cases hzL : z ∈ sL
    · rw [hpL z hzL, hagree z ⟨hzL, hz⟩]
    · show (if z ∈ sL then pL z else pR z) = pR z; exact ite_eq_right hzL
  -- One-sided derivative statements for the glued series.
  have keyL : ∀ m : ℕ, m < (n : WithTop ℕ∞) → ∀ x ∈ sL,
      HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft sL x := by
    intro m hm x hxL
    have heq : Set.EqOn (fun y => p y m) (fun y => pL y m) sL :=
      fun y hy => by simp only [hpL y hy]
    simpa [hpL x hxL] using (hL.fderivWithin m hm x hxL).congr' heq hxL
  have keyR : ∀ m : ℕ, m < (n : WithTop ℕ∞) → ∀ x ∈ sR,
      HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft sR x := by
    intro m hm x hxR
    have heq : Set.EqOn (fun y => p y m) (fun y => pR y m) sR :=
      fun y hy => by simp only [hpR y hy]
    simpa [hpR x hxR] using (hR.fderivWithin m hm x hxR).congr' heq hxR
  -- The glued series is a Taylor series on the union.
  have hglue : HasFTaylorSeriesUpToOn (n : WithTop ℕ∞) w p (sL ∪ sR) :=
    { zero_eq := by
        intro x hx
        rcases hx with hxL | hxR
        · rw [hpL x hxL]; exact hL.zero_eq x hxL
        · rw [hpR x hxR]; exact hR.zero_eq x hxR
      fderivWithin := by
        intro m hm x hx
        have h1 : HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft sL x := by
          by_cases hxL : x ∈ sL
          · exact keyL m hm x hxL
          · exact HasFDerivWithinAt.of_notMem_closure (by rwa [hcL.closure_eq])
        have h2 : HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft sR x := by
          by_cases hxR : x ∈ sR
          · exact keyR m hm x hxR
          · exact HasFDerivWithinAt.of_notMem_closure (by rwa [hcR.closure_eq])
        exact h1.union h2
      cont := by
        intro m hm
        exact ContinuousOn.union_of_isClosed
          ((hL.cont m hm).congr fun y hy => by rw [hpL y hy])
          ((hR.cont m hm).congr fun y hy => by rw [hpR y hy]) hcL hcR }
  exact hglue.contDiffOn.contDiffAt hu

end Work.Diff.EXT
