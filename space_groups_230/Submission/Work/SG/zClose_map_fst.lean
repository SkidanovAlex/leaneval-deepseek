import Mathlib
import Submission.Work.SG.SGprelude

/-!
# `zClose_map_fst`: the matrix projection of the integer affine closure

`zClose gens d k acc` is the (`k`-fold) integer affine closure of `gens` started from `acc`; it is
the list of affine pairs `(A, u)`, where `A` is a flat `3 × 3` matrix (row major, `List ℤ`) and
`u` an integer translation (`List ℤ`), multiplied with

`zMul d (A, u) (B, v) = (A * B, (u + A v) mod d)`.

`mClose gensM k accM` is the matrix closure of `SGprelude`, using `m9mul` for the flat matrix
product and starting from `accM`.

The point is that projecting an affine element onto its matrix commutes with the closure, at the
level of *membership*:

* `zClose_map_fst`: `l ∈ (zClose gens d k acc).map (·.1) ↔ l ∈ mClose (gens.map (·.1)) k
  (acc.map (·.1))`.

The two closures do **not** commute as `List`-equalities: the deduplication step of `zClose`
removes duplicate *pairs*, while the one of `mClose` removes duplicate *matrices*, so the lists
may differ (e.g. two generators with the same matrix and different translations).  Membership,
however, is all that one step can change, and that is what is proved here.

This mirrors the `ℚ`-side statement `sgClose_map_fst` verbatim, with `sgMulPair` replaced by
`zMul d`; the accumulator is generalised in the induction so that `sameMem_mClose` can be
applied to the two (possibly different, but member-equal) accumulators.
-/

namespace Work.SG

/-- `L` and `M` have the same members. -/
private def SameMem {α : Type*} (L M : List α) : Prop := ∀ x, x ∈ L ↔ x ∈ M

/-- One round of `zClose`, projected to the matrices, has the same members as one round of
`mClose` started from the projected accumulator. -/
private theorem sameMem_zF (gens acc : List (List ℤ × List ℤ)) (d : ℕ) :
    SameMem ((zF gens d acc).map (·.1)) (mF (gens.map (·.1)) (acc.map (·.1))) := by
  intro x
  simp only [zF, mF, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map, zMul]
  constructor
  · rintro ⟨a, (ha | ⟨a1, ha1, g, hg, rfl⟩), hfst⟩
    · exact Or.inl ⟨a, ha, hfst⟩
    · exact Or.inr ⟨a1.1, ⟨a1, ha1, rfl⟩, g.1, ⟨g, hg, rfl⟩, hfst⟩
  · rintro (⟨a, ha, hfst⟩ | ⟨b, ⟨a1, ha1, he1⟩, g1, ⟨g, hg, he2⟩, hmul⟩)
    · exact ⟨a, Or.inl ha, hfst⟩
    · refine ⟨zMul d a1 g, Or.inr ⟨a1, ha1, g, hg, rfl⟩, ?_⟩
      show m9mul a1.1 g.1 = x
      rw [he1, he2]; exact hmul

/-- One closure round on the matrix side preserves the members. -/
private theorem sameMem_mF {gM L M : List (List ℤ)} (h : SameMem L M) :
    SameMem (mF gM L) (mF gM M) := by
  intro x
  simp only [mF, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map]
  constructor
  · rintro (hx | ⟨a, ha, g, hg, rfl⟩)
    · exact Or.inl ((h x).mp hx)
    · exact Or.inr ⟨a, (h a).mp ha, g, hg, rfl⟩
  · rintro (hx | ⟨a, ha, g, hg, rfl⟩)
    · exact Or.inl ((h x).mpr hx)
    · exact Or.inr ⟨a, (h a).mpr ha, g, hg, rfl⟩

/-- Every closure round on the matrix side preserves the members. -/
private theorem sameMem_mClose {gM : List (List ℤ)} (k : ℕ) {L M : List (List ℤ)}
    (h : SameMem L M) : SameMem (mClose gM k L) (mClose gM k M) := by
  induction k generalizing L M with
  | zero => exact h
  | succ k ih => exact ih (sameMem_mF h)

/-- Membership version of the statement, with `gens` and `acc` explicit so that the induction
can generalise the accumulator. -/
private theorem zClose_map_fst_aux (gens acc : List (List ℤ × List ℤ)) (d k : ℕ) (l : List ℤ) :
    l ∈ (zClose gens d k acc).map (·.1) ↔
      l ∈ mClose (gens.map (·.1)) k (acc.map (·.1)) := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
    have hstep : zClose gens d (k+1) acc =
        zClose gens d k (zF gens d acc) := rfl
    have hstep2 : mClose (gens.map (·.1)) (k+1) (acc.map (·.1)) =
        mClose (gens.map (·.1)) k (mF (gens.map (·.1)) (acc.map (·.1))) := rfl
    rw [hstep, ih, hstep2]
    exact sameMem_mClose k (sameMem_zF gens acc d) l

/-- The matrix image of the integer closure is the matrix closure. -/
theorem zClose_map_fst (gens : List (List ℤ × List ℤ)) (d k : ℕ) (acc : List (List ℤ × List ℤ))
    (l : List ℤ) :
    l ∈ (zClose gens d k acc).map (·.1) ↔ l ∈ mClose (gens.map (·.1)) k (acc.map (·.1)) :=
  zClose_map_fst_aux gens acc d k l

end Work.SG
