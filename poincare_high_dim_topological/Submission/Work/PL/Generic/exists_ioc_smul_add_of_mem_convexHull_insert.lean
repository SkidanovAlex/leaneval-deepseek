import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic

namespace Work.PL.Generic

open Set Metric

/-- Join decomposition: a point of `convexHull (s ∪ {y})` which is not in `convexHull s` lies on a
segment from a point of `convexHull s` to `y`, with the `y`-weight in `(0,1]`.
Use `Finset.convexHull_eq` (a `centerMass` representation): the `y`-weight is positive, and the
remaining weights, normalised, give `p`. -/
theorem exists_ioc_smul_add_of_mem_convexHull_insert {m : ℕ} {s : Finset (PL.E m)} {y x : PL.E m}
    (hs : s.Nonempty) (hx : x ∈ PL.simp (s ∪ {y})) (hx' : x ∉ PL.simp s) :
    ∃ μ ∈ Set.Ioc (0 : ℝ) 1, ∃ p ∈ PL.simp s, x = (1 - μ) • p + μ • y := by
  -- `s` is a nonempty set of points.
  have hne : ((s : Set (PL.E m))).Nonempty := by
    obtain ⟨v, hv⟩ := hs
    exact ⟨v, by simpa using hv⟩
  -- `↑(s ∪ {y}) = insert y ↑s`.
  have hsU : ((s ∪ {y} : Finset (PL.E m)) : Set (PL.E m)) = insert y (s : Set (PL.E m)) := by
    ext z
    simp [Set.mem_insert_iff]
  -- Hence `x` lies in the join of `convexHull ↑s` with `{y}`.
  have hxjoin : x ∈ convexJoin ℝ (convexHull ℝ (s : Set (PL.E m))) {y} := by
    have h := hx
    rw [PL.simp, hsU, convexHull_insert hne, convexJoin_comm] at h
    exact h
  -- Unfold the join: `x ∈ segment p y` for some `p ∈ convexHull ↑s`.
  rw [convexJoin_singleton_right, mem_iUnion₂] at hxjoin
  obtain ⟨p, hp, hxp⟩ := hxjoin
  rw [segment_eq_image] at hxp
  obtain ⟨t, ht, hxt⟩ := hxp
  -- The weight of `y` must be positive, else `x = p ∈ convexHull ↑s`.
  have htpos : 0 < t := by
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · exfalso
      apply hx'
      have hxp' : x = p := by rw [← hxt, ← h0]; simp
      rwa [hxp']
    · exact hpos
  exact ⟨t, ⟨htpos, ht.2⟩, p, hp, hxt.symm⟩

end Work.PL.Generic
