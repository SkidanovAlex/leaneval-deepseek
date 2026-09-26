import Mathlib

/-!
# A polygonal path through a finite sequence of points

Given `n ≥ 1` and points `v 0, …, v n` in the plane, there is a continuous path `q` from `v 0`
to `v n` whose image is contained in the union of the segments joining consecutive vertices.

The path is obtained abstractly, without ever writing the interpolating formula: the union

  `S = ⋃ i : Fin n, segment ℝ (v i.castSucc) (v i.succ)`

of consecutive segments is *path connected* (a chain of segments, each meeting the next), and every
vertex `v i` lies in `S`; `IsPathConnected.exists_path_through_family` then produces a path through
all the vertices whose range lies in `S`.

The path connectedness of the union is proved by induction, splitting off the last segment with
`iUnion_fin_succ_eq` and gluing with `IsPathConnected.union`.  Note that `n = 0` is excluded: with
no vertex there is no segment, so no path.
-/

open Set

namespace Work.BoxShrink.Bubble.Plane

/-- A `Fin (n+1)`-indexed union splits into the part indexed by `castSucc` and the last index. -/
lemma iUnion_fin_succ_eq {α : Type*} (n : ℕ) (f : Fin (n + 1) → Set α) :
    (⋃ i : Fin (n + 1), f i) = (⋃ j : Fin n, f j.castSucc) ∪ f (Fin.last n) := by
  ext x
  simp only [mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inl ⟨j, hi⟩
    · exact Or.inr hi
  · rintro (⟨j, hj⟩ | h)
    · exact ⟨j.castSucc, hj⟩
    · exact ⟨Fin.last n, h⟩

/-- The union of the consecutive segments of a chain of `m + 1` segments is path connected. -/
lemma isPathConnected_segment_union_aux (m : ℕ) (v : Fin (m + 2) → ℝ × ℝ) :
    IsPathConnected (⋃ i : Fin (m + 1), segment ℝ (v i.castSucc) (v i.succ)) := by
  induction m with
  | zero =>
      rw [iUnion_fin_succ_eq (n := 0)
        (f := fun i : Fin 1 => segment ℝ (v i.castSucc) (v i.succ))]
      simp
      exact (convex_segment _ _).isPathConnected ⟨_, left_mem_segment ℝ _ _⟩
  | succ k ih =>
      rw [iUnion_fin_succ_eq (n := k + 1)
        (f := fun i : Fin (k + 2) => segment ℝ (v i.castSucc) (v i.succ))]
      refine IsPathConnected.union ?_ ?_ ?_
      · exact ih (v ∘ Fin.castSucc)
      · exact (convex_segment _ _).isPathConnected ⟨_, left_mem_segment ℝ _ _⟩
      · exact ⟨v ((Fin.last k).castSucc.succ),
          mem_iUnion.mpr ⟨Fin.last k, right_mem_segment ℝ _ _⟩,
          left_mem_segment ℝ _ _⟩

/-- **Existence of a polygonal path through a finite sequence of points.**

For `n ≥ 1` and points `v : Fin (n+1) → ℝ × ℝ` there is a continuous path `q` on the unit interval
with `q 0 = v 0`, `q 1 = v (Fin.last n)` and whose image lies in the union of the segments joining
consecutive vertices. -/
theorem exists_polyPath (n : ℕ) (hn : 0 < n) (v : Fin (n + 1) → ℝ × ℝ) :
    ∃ q : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
      q ⟨0, by norm_num⟩ = v 0 ∧
      q ⟨1, by norm_num⟩ = v (Fin.last n) ∧
      (∀ t : Set.Icc (0 : ℝ) 1,
        q t ∈ ⋃ i : Fin n, segment ℝ (v i.castSucc) (v i.succ)) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpc : IsPathConnected (⋃ i : Fin (m + 1), segment ℝ (v i.castSucc) (v i.succ)) :=
    isPathConnected_segment_union_aux m v
  have hmem : ∀ i : Fin (m + 1 + 1),
      v i ∈ ⋃ j : Fin (m + 1), segment ℝ (v j.castSucc) (v j.succ) := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hj
    · rw [hj]
      exact mem_iUnion.mpr ⟨j, left_mem_segment ℝ _ _⟩
    · rw [hj]
      exact mem_iUnion.mpr ⟨⟨m, Nat.lt_succ_self m⟩, right_mem_segment ℝ _ _⟩
  obtain ⟨γ, hγ, -⟩ := hpc.exists_path_through_family v hmem
  refine ⟨γ.toContinuousMap, ?_, ?_, ?_⟩
  · exact Path.source γ
  · exact Path.target γ
  · intro t
    exact hγ (mem_range_self t)

end Work.BoxShrink.Bubble.Plane
