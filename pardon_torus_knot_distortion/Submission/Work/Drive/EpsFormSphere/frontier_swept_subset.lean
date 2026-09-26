import Mathlib
import Submission.Work.Drive.EpsFormSphere.Sideways

/-!
# The frontier of the swept ball

The sideways sweep of Pardon's Lemma 3 removes from the box `PBox s c σ` the part of the thin slab
`Work.Drive.EpsSphere.slabZ c σ u h` that lies *behind* the moving wall `{y | ℓ y < lam}`:

`PBox s c σ \ (Work.Drive.EpsSphere.slabZ c σ u h ∩ {y | ℓ y < lam})`.

Its frontier is therefore constrained: away from the frontier of the box it is exactly the frontier of
the removed region, and the frontier of the removed region is the union of the two slab faces
`|y (σ 2) - (c (σ 2) + u)| = h` and the wall `{ℓ = lam}` inside the slab.

The two steps are proved separately below.

* `frontier_sdiff_subset` — purely topological: `frontier (A \ B) ⊆ frontier A ∪ frontier B` for any
  two sets (no openness needed: the point is that a frontier point of `A \ B` is in `closure A`, so
  if it is not in `frontier A` it is in `interior A`, and there the frontier of `A \ B` is the
  frontier of `B`).
* `frontier_slabZ_wall_subset` — the frontier of `Work.Drive.EpsSphere.slabZ ∩ {ℓ < lam}`: the closure of the removed
  region lies in the closed slab and in the closed half-space, while the region itself is open, so a
  frontier point either sits on a slab face or on the wall.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Drive.EpsFormSphere

/-- **The frontier of a difference of sets**: `∂(A \ B) ⊆ ∂A ∪ ∂B`.

Only incidentally topological — no hypothesis on `A` or `B` is needed.  If `x ∈ ∂(A \ B)` then
`x ∈ closure A`; if moreover `x ∉ ∂A` then `x ∈ interior A`, and an interior point of `A` which is in
`interior B`, or outside `closure B`, is an interior point of `A \ B` — contradiction.  Hence
`x ∈ ∂B`. -/
theorem frontier_sdiff_subset {X : Type*} [TopologicalSpace X] (A B : Set X) :
    frontier (A \ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  rw [frontier, Set.mem_sdiff] at hx
  obtain ⟨hxcl, hxint⟩ := hx
  rw [Set.mem_union]
  by_cases hxA : x ∈ interior A
  · right
    rw [frontier, Set.mem_sdiff]
    refine ⟨?_, ?_⟩
    · by_contra hxB
      have hxcB : x ∈ (closure B)ᶜ := hxB
      have hopen : IsOpen (interior A ∩ (closure B)ᶜ) :=
        isOpen_interior.inter isClosed_closure.isOpen_compl
      have hsub : interior A ∩ (closure B)ᶜ ⊆ A \ B := by
        rintro y ⟨hyA, hyB⟩
        exact ⟨interior_subset hyA, fun hyB' => hyB (subset_closure hyB')⟩
      exact hxint (interior_maximal hsub hopen ⟨hxA, hxcB⟩)
    · intro hxB
      have hsub : A \ B ⊆ (interior A ∩ interior B)ᶜ := by
        rintro y ⟨hyA, hyB⟩
        intro hyi
        exact hyB (interior_subset hyi.2)
      have hclosed : IsClosed (interior A ∩ interior B)ᶜ :=
        (isOpen_interior.inter isOpen_interior).isClosed_compl
      exact (closure_minimal hsub hclosed hxcl) ⟨hxA, hxB⟩
  · left
    rw [frontier, Set.mem_sdiff]
    exact ⟨closure_mono Set.sdiff_subset hxcl, hxA⟩

/-- **The frontier of the removed region** `Work.Drive.EpsSphere.slabZ c σ u h ∩ {y | ℓ y < lam}` lies on the two slab
faces `|y (σ 2) - (c (σ 2) + u)| = h` or on the wall `{ℓ = lam}` inside the slab. -/
theorem frontier_slabZ_wall_subset {c : R3} {σ : Equiv.Perm (Fin 3)} {u h lam : ℝ}
    {ℓ : R3 →L[ℝ] ℝ} :
    frontier (Work.Drive.EpsSphere.slabZ c σ u h ∩ {y : R3 | ℓ y < lam}) ⊆
      {y : R3 | |y (σ 2) - (c (σ 2) + u)| = h} ∪
        {y : R3 | |y (σ 2) - (c (σ 2) + u)| < h ∧ ℓ y = lam} := by
  intro x hx
  rw [frontier, Set.mem_sdiff] at hx
  obtain ⟨hxcl, hxint⟩ := hx
  have hf : Continuous fun y : R3 => |y (σ 2) - (c (σ 2) + u)| := by fun_prop
  have hopen : IsOpen (Work.Drive.EpsSphere.slabZ c σ u h ∩ {y : R3 | ℓ y < lam}) := by
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt hf continuous_const
    · exact isOpen_lt ℓ.continuous continuous_const
  -- the removed region is open, so a frontier point is not in it
  have hxD : ¬ ((|x (σ 2) - (c (σ 2) + u)| < h) ∧ ℓ x < lam) := by
    rw [hopen.interior_eq] at hxint
    simpa [Work.Drive.EpsSphere.slabZ] using hxint
  -- ... but it is in both closed sets
  have hle1 : |x (σ 2) - (c (σ 2) + u)| ≤ h :=
    closure_minimal (fun y hy => le_of_lt hy.1) (isClosed_le hf continuous_const) hxcl
  have hle2 : ℓ x ≤ lam :=
    closure_minimal (fun y hy => le_of_lt hy.2) (isClosed_le ℓ.continuous continuous_const) hxcl
  rcases lt_or_ge (|x (σ 2) - (c (σ 2) + u)|) h with hlt | hge
  · -- strictly inside the slab: the wall contains it
    right
    exact ⟨hlt, le_antisymm hle2 (not_lt.mp (fun hc => hxD ⟨hlt, hc⟩))⟩
  · -- on the boundary of the slab
    left
    exact le_antisymm hle1 hge

/-- **The frontier of the swept ball `PBox \ (slabZ ∩ {ℓ < lam})` lies on the box sphere, on the slab faces, or on the wall `{ℓ = lam}`.** -/
theorem frontier_swept_subset {s u h lam : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} (hpos : 0 < h) :
    frontier {y : LeanEval.KnotTheory.PardonDistortion.R3 | y ∈ Submission.PBox s c σ ∧
        ¬ (y ∈ Work.Drive.EpsSphere.slabZ c σ u h ∧ ℓ y < lam)} ⊆
      frontier (Submission.PBox s c σ) ∪
        ({y : LeanEval.KnotTheory.PardonDistortion.R3 | |y (σ 2) - (c (σ 2) + u)| = h} ∪
          {y : LeanEval.KnotTheory.PardonDistortion.R3 | |y (σ 2) - (c (σ 2) + u)| < h ∧ ℓ y = lam}) := by
  set B : Set R3 := Work.Drive.EpsSphere.slabZ c σ u h ∩ {y : R3 | ℓ y < lam} with hB
  have hset : {y : R3 | y ∈ Submission.PBox s c σ ∧
      ¬ (y ∈ Work.Drive.EpsSphere.slabZ c σ u h ∧ ℓ y < lam)} = Submission.PBox s c σ \ B := by
    ext y
    simp [hB, Work.Drive.EpsSphere.slabZ]
  rw [hset]
  refine subset_trans (frontier_sdiff_subset (Submission.PBox s c σ) B) ?_
  rw [hB]
  intro y hy
  rcases hy with hy | hy
  · exact Or.inl hy
  · exact Or.inr (frontier_slabZ_wall_subset hy)

end Work.Drive.EpsFormSphere
