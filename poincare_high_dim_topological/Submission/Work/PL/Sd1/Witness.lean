import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.ascIdx_mem
import Submission.Work.PL.Shell.face_trace

/-!
# The index set of the attaching set `splitOf`

For a flag `l` (a `Nodup` list of vertices of the simplex `Δ`), the attaching set
`Work.PL.Shell.splitOf Δ T rk l` of the shelling step belonging to `l` is the set of
centroids `bary (prefAt l j)` of the prefixes at the *ascent* positions of `l`, together
with the *top* centroid `bary Δ` when the last vertex of `l` lies in `T`.

`Work.PL.Sd1.wit T rk l` is the index set of these positions: `ascIdx rk l`, plus the last
position `l.length - 1` when the last vertex of `l` lies in `T`.  The rest of the argument
is phrased in terms of this index set, because the map `j ↦ bary (prefAt l j)` is injective
on it (`Work.PL.Shell.bary_inj`), so the attaching set is a union of facets of the
subdivision simplex indexed by `wit`.
-/

namespace Work.PL.Sd1

open Set Metric Finset
open scoped BigOperators

noncomputable section

variable {N : ℕ}

/-- The index set of the attaching set: the ascent positions of the flag `l`, together
with its last position when the last vertex of `l` lies in `T`. -/
def wit (T : Finset (PL.E N)) (rk : PL.E N → ℕ) (l : List (PL.E N)) : Finset ℕ :=
  if ∃ v, l.getLast? = some v ∧ v ∈ T then insert (l.length - 1) (Work.PL.Shell.ascIdx rk l)
  else Work.PL.Shell.ascIdx rk l

/-- Membership in `wit`. -/
theorem mem_wit {T : Finset (PL.E N)} {rk : PL.E N → ℕ} {l : List (PL.E N)} {j : ℕ} :
    j ∈ wit T rk l ↔
      j ∈ Work.PL.Shell.ascIdx rk l ∨
        ((∃ v, l.getLast? = some v ∧ v ∈ T) ∧ j = l.length - 1) := by
  rw [wit]
  by_cases h : ∃ v, l.getLast? = some v ∧ v ∈ T
  · rw [if_pos h, Finset.mem_insert]
    exact ⟨fun hj => hj.elim (fun hj => Or.inr ⟨h, hj⟩) Or.inl,
      fun hj => hj.elim Or.inr (fun hj => Or.inl hj.2)⟩
  · rw [if_neg h]
    exact ⟨fun hj => Or.inl hj, fun hj => hj.elim id (fun hj => absurd hj.1 h)⟩

/-- `wit` is contained in the index set `{0, …, l.length - 1}` of the flag `l`. -/
theorem wit_subset_range (T : Finset (PL.E N)) (rk : PL.E N → ℕ) (l : List (PL.E N)) :
    wit T rk l ⊆ Finset.range l.length := by
  intro s hs
  rw [mem_wit] at hs
  rcases hs with hs | ⟨hlast, rfl⟩
  · exact Finset.mem_range.mpr (Nat.lt_of_succ_lt (Work.PL.Shell.ascIdx_mem.mp hs).choose)
  · obtain ⟨v, hv, -⟩ := hlast
    have hne : l ≠ [] := by rintro rfl; simp at hv
    rw [Finset.mem_range]
    have hpos : 0 < l.length := List.length_pos_iff.mpr hne
    exact Nat.sub_lt hpos Nat.one_pos

/-- The last position of a non-empty flag is not an ascent. -/
theorem last_notMem_ascIdx (rk : PL.E N → ℕ) (l : List (PL.E N)) :
    l.length - 1 ∉ Work.PL.Shell.ascIdx rk l := by
  intro h
  have hlt : (l.length - 1) + 1 < l.length := (Work.PL.Shell.ascIdx_mem.mp h).choose
  omega

end

end Work.PL.Sd1
