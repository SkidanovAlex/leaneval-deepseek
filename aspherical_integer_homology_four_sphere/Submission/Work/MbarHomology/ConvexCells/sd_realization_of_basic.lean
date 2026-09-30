import Mathlib
import Submission.Work.ConvexCells.Basic
import Submission.Work.ConvexCells.FlagPt_mem
import Submission.Work.ConvexCells.tightAt_flagPt
import Submission.Work.ConvexCells.exists_exit
import Submission.Work.ConvexCells.exists_flagPt
import Submission.Work.ConvexCells.flagPt_unique
import Submission.Work.MbarHomology.ConvexCells.sd_carrier_of_basic
import Submission.Work.MbarHomology.ConvexCells.exists_exit_basic
import Submission.Work.MbarHomology.ConvexCells.flagPt_unique_basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The barycentric subdivision realizes the polytope, from the basic checks only

`PolytopeData.checksBasic = true` gives `PolytopeData.OkBasic`, the first conjunct of `P.Ok`.  The
geometric content of `sd_realization` -- that a flag point lies in the polytope, that distinct flag
points have distinct realizations, and that every point of the polytope is the realization of a
flag point -- only ever uses `OkBasic`: the `OkEmp`/`OkAdd` groups of certificates are spent solely
on deriving the face-completeness hypothesis `Carriers` (`ConvexCells.Carriers_of_Ok`).

This file proves `sd_realization_of_basic`, the version of `sd_realization` in which `Carriers` is
taken as a hypothesis and the decidable input is only `checksBasic`.
-/

namespace Work.MbarHomology.ConvexCells

open scoped BigOperators
open Work.ConvexCells
open Work.ConvexCells.PolytopeData

/-- The affine realization of the open simplex of a flag lies in the polytope, using only the
basic checks. -/
theorem flagPt_mem_basic {d : ℕ} (P : PolytopeData d) (h : P.OkBasic) (s : P.FlagPt) :
    s.toE' ∈ P.Pset := by
  refine P.Pset_convex.sum_mem (t := Finset.univ)
    (fun i _ => le_of_lt (s.wt_pos i)) s.wt_sum (fun i _ => ?_)
  exact posR_mem_Pset_basic h (s.flag.get i)

/-- Every point of the polytope lies in the open simplex of some flag (the covering half of the
barycentric subdivision theorem), using only the basic checks.

The proof is the strong induction on `P.m - (P.tightAt x).card` of
`Work.ConvexCells.exists_flagPt`, with `exists_exit_basic` in place of `exists_exit` and
`tightAt_flagPt_basic` in place of `tightAt_flagPt`. -/
theorem exists_flagPt_basic {d : ℕ} (P : PolytopeData d) (h : P.OkBasic) (hc : P.Carriers)
    (x : E d) (hx : x ∈ P.Pset) : ∃ s : P.FlagPt, s.toE' = x := by
  classical
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
        exists_exit_basic P h f hxf hf.symm hxe
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
        have h1 := tightAt_flagPt_basic P h s
        rw [hs] at h1
        rw [PolytopeData.SubFace, ← h1]
        exact hssub
      obtain ⟨s', hs'⟩ := flagPt_extend P s f hsub' (μ := t⁻¹) (by positivity)
        (inv_lt_one_of_one_lt₀ ht)
      exact ⟨s', by rw [hs', hs, hxr]⟩

/-- **The barycentric subdivision realizes the polytope**, from the basic checks and the explicit
face-completeness hypothesis `Carriers`.  The `OkEmp`/`OkAdd` certificate groups of `P.Ok` are not
needed here: `sd_realization_of_carriers` obtains them only to *derive* `Carriers`. -/
theorem sd_realization_of_basic {d : ℕ} (P : Work.ConvexCells.PolytopeData d)
    (hb : P.checksBasic = true) (hc : P.Carriers) :
    Set.BijOn (fun s : P.FlagPt => s.toE') Set.univ P.Pset := by
  have hB : P.OkBasic := of_decide_eq_true hb
  refine ⟨fun s _ => flagPt_mem_basic P hB s,
    fun s _ t _ hst => flagPt_unique_basic P hB s t hst,
    fun y hy => ?_⟩
  obtain ⟨s, hs⟩ := exists_flagPt_basic P hB hc y hy
  exact ⟨s, trivial, hs⟩

end Work.MbarHomology.ConvexCells
