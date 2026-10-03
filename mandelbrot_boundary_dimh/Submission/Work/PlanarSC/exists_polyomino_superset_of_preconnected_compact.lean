import Mathlib
import Submission.Work.PlanarSC.HullDefs

/-!
# A preconnected compact set is contained in a preconnected dyadic polyomino

`K ⊆ U` with `K` nonempty, compact and preconnected, `U` open, is enclosed in a *connected*
finite union of closed dyadic squares of a single level which is still contained in `U`.

The idea is the canonical exhaustion `Work.Spine.Plane.polyK U hU n = ⋃ p ∈ cells U hU n, dSq n p`
of `U`: for `n` large it contains `K`.  Keep only those cells of level `n` which meet `K`; every
such cell then contains a point of the preconnected `K`, so the cells all "hang together" through
`K`, and the resulting polyomino is preconnected while still being a sub-polyomino of the
exhaustion, hence contained in `U`.
-/

open Set

namespace Work.PlanarSC

open Commons.Topology.Plane (dSq)

/-- The closed level-`n` dyadic square `dSq n p` is convex — it is the intersection of the two
half-plane strips cut out by the intervals of its real and imaginary parts. -/
lemma convex_dSq (n : ℕ) (p : ℤ × ℤ) : Convex ℝ (dSq n p) := by
  have h : dSq n p =
      {z : ℂ | z.re ∈ Set.Icc ((p.1 : ℝ) / 2 ^ n) (((p.1 : ℝ) + 1) / 2 ^ n)} ∩
        {z : ℂ | z.im ∈ Set.Icc ((p.2 : ℝ) / 2 ^ n) (((p.2 : ℝ) + 1) / 2 ^ n)} := by
    ext z
    simp only [dSq, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc]
    tauto
  rw [h]
  exact ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

/-- **A union of dyadic cells glued through a preconnected set is preconnected.**  If every cell
`dSq n p`, `p ∈ s`, meets the preconnected set `K`, and `K` is itself covered by those cells, then
`⋃ p ∈ s, dSq n p` is preconnected: it is `K` together with the cells of `s`, each of which hangs
off `K` in a single point. -/
lemma isPreconnected_biUnion_dSq_of_meets {n : ℕ} {K : Set ℂ} (hK : IsPreconnected K)
    {s : Finset (ℤ × ℤ)} (hsub : K ⊆ ⋃ p ∈ s, dSq n p)
    (hmeets : ∀ p ∈ s, (dSq n p ∩ K).Nonempty) :
    IsPreconnected (⋃ p ∈ s, dSq n p) := by
  -- Adding the cells of `s` one at a time to `K` keeps the union preconnected.
  have key : ∀ t : Finset (ℤ × ℤ), (∀ p ∈ t, (dSq n p ∩ K).Nonempty) →
      IsPreconnected (K ∪ ⋃ p ∈ t, dSq n p) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _
      simpa using hK
    · intro a t _ ih ht
      have ht' : ∀ p ∈ t, (dSq n p ∩ K).Nonempty :=
        fun p hp => ht p (Finset.mem_insert_of_mem hp)
      have hpre_t := ih ht'
      obtain ⟨x, hxa, hxK⟩ := ht a (Finset.mem_insert_self a t)
      have hcell : IsPreconnected (dSq n a) := (convex_dSq n a).isPreconnected
      have hres := IsPreconnected.union x (Or.inl hxK) hxa hpre_t hcell
      have hset : (K ∪ ⋃ p ∈ t, dSq n p) ∪ dSq n a
          = K ∪ ⋃ p ∈ insert a t, dSq n p := by
        rw [Finset.set_biUnion_insert, Set.union_assoc,
          Set.union_comm (⋃ p ∈ t, dSq n p) (dSq n a)]
      rwa [hset] at hres
  -- `K` is contained in the union, so adjoining `K` changes nothing.
  have hkey := key s hmeets
  rwa [Set.union_eq_right.mpr hsub] at hkey

/-- A nonempty compact preconnected `K ⊆ U` (with `U` open in `ℂ`) lies in a dyadic polyomino
`dyadicPolyomino n S ⊆ U` which is itself preconnected.

Hint: `Submission.Work.PlanarSC.HullDefs` imports `PolyDefs` → `PolyTools` →
`Submission.Lib.Unif2.Work.Spine.Plane.Dyadic`, so `Work.Spine.Plane.exists_polyK_superset_of_compact`
(with `polyK U hU n = dyadicPolyomino n (cells U hU n)`, definitionally) is available; filter the
canonical exhaustion cells `cells U hU n` by "meets `K`" and use that every such cell contains a
common point of the preconnected `K`. -/
theorem exists_polyomino_superset_of_preconnected_compact {U : Set ℂ} (hU : IsOpen U) {K : Set ℂ}
    (hKc : IsCompact K) (hKne : K.Nonempty) (hKp : IsPreconnected K) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (S : Finset (ℤ × ℤ)),
      K ⊆ dyadicPolyomino n S ∧ dyadicPolyomino n S ⊆ U ∧
        IsPreconnected (dyadicPolyomino n S) := by
  classical
  -- A level at which the canonical exhaustion of `U` already contains `K`.
  obtain ⟨n, hn⟩ := Work.Spine.Plane.exists_polyK_superset_of_compact U hU hKc hKU
  -- The cells of that level which meet `K`.
  set S : Finset (ℤ × ℤ) :=
    (Work.Spine.Plane.cells U hU n).filter (fun p => (dSq n p ∩ K).Nonempty) with hSdef
  have hS_mem : ∀ p : ℤ × ℤ, p ∈ S ↔
      p ∈ Work.Spine.Plane.cells U hU n ∧ (dSq n p ∩ K).Nonempty := by
    intro p; rw [hSdef, Finset.mem_filter]
  -- Every point of `K` lies in one of the retained cells.
  have hKsub : K ⊆ ⋃ p ∈ S, dSq n p := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ :=
      mem_iUnion₂.mp (hn hz : z ∈ ⋃ p ∈ Work.Spine.Plane.cells U hU n, dSq n p)
    exact mem_iUnion₂.mpr ⟨p, (hS_mem p).mpr ⟨hp, ⟨z, hzp, hz⟩⟩, hzp⟩
  refine ⟨n, S, ?_, ?_, ?_⟩
  · rw [dyadicPolyomino]; exact hKsub
  · -- `S` is a sub-collection of the exhaustion cells, which all lie in `U`.
    intro z hz
    rw [dyadicPolyomino] at hz
    obtain ⟨p, hpS, hzp⟩ := mem_iUnion₂.mp hz
    refine Work.Spine.Plane.polyK_subset U hU n ?_
    rw [Work.Spine.Plane.polyK]
    exact mem_iUnion₂.mpr ⟨p, ((hS_mem p).mp hpS).1, hzp⟩
  · rw [dyadicPolyomino]
    exact isPreconnected_biUnion_dSq_of_meets hKp hKsub fun p hp => ((hS_mem p).mp hp).2

end Work.PlanarSC
