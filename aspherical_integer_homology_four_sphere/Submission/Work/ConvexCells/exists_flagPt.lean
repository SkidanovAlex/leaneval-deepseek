import Mathlib
import Submission.Work.ConvexCells.Basic
import Submission.Work.ConvexCells.exists_exit
import Submission.Work.ConvexCells.tightAt_flagPt
import Submission.Work.ConvexCells.flagPt_extend

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ConvexCells

open scoped BigOperators

open PolytopeData

/-- Every point of the polytope lies in the open simplex of some flag (the covering half of the
barycentric subdivision theorem).

Suggested route, by strong induction on the cardinality of `P.tightAt x`: `hc` gives a face `f` with
`tight f = tightAt x`, so `posR f` is a point of `Pset` with `tightAt (posR f) = tight f`; if
`x = posR f` the one-element flag works.  Otherwise `exists_exit P h f hx hxt hne` (with
`hx : x ∈ P.Fset f` and `hxt : P.tightAt x = P.tight f`) gives `r = P.posR f + t • (x - P.posR f)`
with `tight f ⊊ tightAt r` and `r ∈ P.Fset f`, hence `(P.tightAt r).card > (P.tightAt x).card`; by
induction `r` is the realization of a flag point `s`, and then `x = (1 - t⁻¹) • P.posR f + t⁻¹ • r`
makes `x` the realization of the flag `s.flag ++ [f]` with weights `t⁻¹ * s.wt i` on the old faces
and `1 - t⁻¹` on `f` (`tight (topFace s) = tightAt r ⊋ tight f` ensures `s.flag ++ [f]` is still a
flag, i.e. `P.SubFace (topFace s) f`). -/
theorem exists_flagPt {d : ℕ} (P : PolytopeData d) (h : P.Ok) (hc : P.Carriers) (x : E d)
    (hx : x ∈ P.Pset) : ∃ s : P.FlagPt, s.toE' = x := by
  classical
  -- Strong induction on `P.m - (P.tightAt y).card`: `exists_exit` strictly increases the
  -- cardinality of the tight set, so the recursion terminates, and the disjointness of the
  -- `tightAt` sets of the successive exit points is not needed.
  suffices key : ∀ k, ∀ y : E d, y ∈ P.Pset → P.m - (P.tightAt y).card = k →
      ∃ s : P.FlagPt, s.toE' = y by
    exact key _ x hx rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x hx hk
    -- the carrier face of `x`, given by face completeness
    obtain ⟨f, hf⟩ := hc x hx
    -- `x` lies in the closed face of its carrier
    have hxf : x ∈ P.Fset f := by
      refine ⟨hx, fun i hi => ?_⟩
      exact (tightAt_of_mem P hx i).mp (by rw [← hf]; exact hi)
    by_cases hxe : x = P.posR f
    · -- `x` is the relative interior point of a face: the one-element flag works
      refine ⟨⟨[f], ?_, fun _ => 1, fun i => one_pos, ?_⟩, ?_⟩
      · simp [PolytopeData.IsFlag]
      · simp
      · rw [PolytopeData.FlagPt.toE']
        simp [hxe]
    · -- otherwise push `x` radially out of the face until a new constraint becomes tight
      obtain ⟨t, r, ht, _hr, hrF, hssub, hxr, _hmem, _hout⟩ :=
        exists_exit P h f hxf hf.symm hxe
      have hcard : (P.tightAt x).card < (P.tightAt r).card := by
        rw [← hf]
        exact Finset.card_lt_card hssub
      have hlt : P.m - (P.tightAt r).card < k := by
        have h1 : (P.tightAt x).card ≤ P.m := by
          simpa using Finset.card_le_univ (P.tightAt x)
        have h2 : (P.tightAt r).card ≤ P.m := by
          simpa using Finset.card_le_univ (P.tightAt r)
        omega
      obtain ⟨s, hs⟩ := ih _ hlt r hrF.1 rfl
      -- the flag of `s` can be extended by the carrier face `f` of `x`
      have hsub' : P.SubFace s.topFace f := by
        have h1 := tightAt_flagPt P h s
        rw [hs] at h1
        rw [PolytopeData.SubFace, ← h1]
        exact hssub
      obtain ⟨s', hs'⟩ := flagPt_extend P s f hsub' (μ := t⁻¹) (by positivity)
        (inv_lt_one_of_one_lt₀ ht)
      exact ⟨s', by rw [hs', hs, hxr]⟩

end Work.ConvexCells
