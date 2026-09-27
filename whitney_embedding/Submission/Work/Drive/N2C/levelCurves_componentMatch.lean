import Mathlib
import Submission.Work.Drive.N2C.defs

/-!
# `N2C`: two parametrisations of a level enumerate the same components

`Work.Drive.N2C.LevelCurves f b n` records the parametrisation rows of the level `f = b` by `n`
periodic curves.  Its rows say exactly that the level is the *disjoint* union of the `n` compact
connected sets `range (γ i)`:

* `val`   : `range (γ i)` is contained in the level;
* `cover` : the level is contained in `⋃ i, range (γ i)`;
* `disj`  : the `range (γ i)` are pairwise disjoint;

and the curves are non-trivial periodic curves (`sm` + `per` make each `range (γ i)` the image of
the compact circle `[0,1]`, hence a nonempty compact — in a Hausdorff manifold, closed — set, and
`sm` makes it preconnected, as the continuous image of `ℝ`).

Consequently the *number* `n` of curves is an invariant of the level, and moreover the
`n`-element family of ranges is determined up to a permutation of the indices.  That is the
statement proved here: a bijection `σ : Fin n' → Fin n` with
`Set.range (L'.γ i) = Set.range (L.γ (σ i))`.

The proof is a "preconnected set in a finite disjoint union of closed sets" argument: a
preconnected set meeting two of the closed sets would be split by them.  We only use the two-set
form `isPreconnected_iff_subset_of_disjoint_closed`.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- **The range of a level curve is closed.**  By `per`, the range of the `1`-periodic curve `γ i`
is the image of the compact interval `[0,1]` (using `Int.fract` to reduce a parameter modulo `1`)
and `sm` makes `γ i` continuous; a compact set of a Hausdorff space is closed. -/
lemma isClosed_range_γ {f : M → ℝ} {b : ℝ} {n : ℕ} (L : LevelCurves f b n) (i : Fin n) :
    IsClosed (Set.range (L.γ i)) := by
  have hcont : Continuous (L.γ i) := (L.sm i).continuous
  have hrange : Set.range (L.γ i) = L.γ i '' Set.Icc (0:ℝ) 1 := by
    ext x; constructor
    · rintro ⟨t, rfl⟩
      have hp : Function.Periodic (L.γ i) (1:ℝ) := L.per i
      have h : L.γ i (Int.fract t + (⌊t⌋ : ℤ)) = L.γ i (Int.fract t) := by
        simpa using (hp.int_mul ⌊t⌋) (Int.fract t)
      rw [Int.fract_add_floor] at h
      exact ⟨Int.fract t, ⟨Int.fract_nonneg t, le_of_lt (Int.fract_lt_one t)⟩, h.symm⟩
    · rintro ⟨t, _, rfl⟩; exact ⟨t, rfl⟩
  rw [hrange]
  exact (isCompact_Icc.image hcont).isClosed

/-- **Every curve of a second parametrisation lies on a single curve of the first.**  The range of
`L'.γ j` is preconnected (continuous image of `ℝ`) and contained in the level, which is the union
of the pairwise disjoint closed sets `range (L.γ i)`.  Fixing `i₀` with `L'.γ j 0 ∈ range (L.γ i₀)`,
the two closed sets `range (L.γ i₀)` and the union of the remaining ranges split the range of
`L'.γ j`; the second alternative is impossible because `L'.γ j 0` lies in both pieces. -/
lemma exists_range_subset_of_levelCurves {f : M → ℝ} {b : ℝ} {n m : ℕ}
    (L : LevelCurves f b n) (L' : LevelCurves f b m) (j : Fin m) :
    ∃ i : Fin n, Set.range (L'.γ j) ⊆ Set.range (L.γ i) := by
  obtain ⟨i₀, t₀, ht₀⟩ := L.cover (L'.γ j 0) (L'.val j 0)
  refine ⟨i₀, ?_⟩
  have hS : IsPreconnected (Set.range (L'.γ j)) := isPreconnected_range ((L'.sm j).continuous)
  set v : Set M := ⋃ (i : {i : Fin n // i ≠ i₀}), Set.range (L.γ i.1) with hv
  have hclosed_v : IsClosed v := by
    rw [hv]; exact isClosed_iUnion_of_finite (fun i => isClosed_range_γ L i.1)
  have hsub : Set.range (L'.γ j) ⊆ Set.range (L.γ i₀) ∪ v := by
    rintro x ⟨s, rfl⟩
    obtain ⟨i, t, ht⟩ := L.cover (L'.γ j s) (L'.val j s)
    by_cases hi : i = i₀
    · rw [hi] at ht
      exact Or.inl ⟨t, ht.symm⟩
    · exact Or.inr (Set.mem_iUnion.2 ⟨⟨i, hi⟩, ⟨t, ht.symm⟩⟩)
  have hdisj : Set.range (L'.γ j) ∩ (Set.range (L.γ i₀) ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨-, hx1, hx2⟩
    obtain ⟨⟨i, hi⟩, hxi⟩ := Set.mem_iUnion.1 hx2
    exact (Set.disjoint_left.1 (L.disj i₀ i (Ne.symm hi)) hx1) hxi
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hS) (Set.range (L.γ i₀)) v
    (isClosed_range_γ L i₀) hclosed_v hsub hdisj with h | h
  · exact h
  · exfalso
    have hp1 : L'.γ j 0 ∈ Set.range (L.γ i₀) := ⟨t₀, ht₀.symm⟩
    have hp2 : L'.γ j 0 ∈ v := h ⟨0, rfl⟩
    obtain ⟨⟨i, hi⟩, hxi⟩ := Set.mem_iUnion.1 hp2
    exact (Set.disjoint_left.1 (L.disj i₀ i (Ne.symm hi)) hp1) hxi

/-- **Two parametrisations of the same level induce the same family of component curves.**  There
is a bijection `σ : Fin n' → Fin n` carrying each range of `L'` onto the corresponding range of
`L`. -/
theorem levelCurves_componentMatch {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {b : ℝ} {n n' : ℕ} (L : Work.Drive.N2C.LevelCurves f b n)
    (L' : Work.Drive.N2C.LevelCurves f b n') :
    ∃ σ : Fin n' → Fin n, Function.Bijective σ ∧
      (∀ i : Fin n', Set.range (L'.γ i) = Set.range (L.γ (σ i))) := by
  classical
  -- `σ j` is the (unique) curve of `L` carrying the range of `L'.γ j`; `τ` is the same map
  -- with the roles of `L` and `L'` exchanged.
  choose σ hσ using fun j => exists_range_subset_of_levelCurves L L' j
  choose τ hτ using fun i => exists_range_subset_of_levelCurves L' L i
  -- `τ ∘ σ = id` and `σ ∘ τ = id`, because the ranges are pairwise disjoint and nontrivial.
  have hτσ : ∀ j : Fin n', τ (σ j) = j := by
    intro j
    by_contra hne
    have h1 : Set.range (L'.γ j) ⊆ Set.range (L'.γ (τ (σ j))) := (hσ j).trans (hτ (σ j))
    exact (Set.disjoint_left.1 (L'.disj (τ (σ j)) j hne) (h1 ⟨0, rfl⟩)) ⟨0, rfl⟩
  have hστ : ∀ i : Fin n, σ (τ i) = i := by
    intro i
    by_contra hne
    have h1 : Set.range (L.γ i) ⊆ Set.range (L.γ (σ (τ i))) := (hτ i).trans (hσ (τ i))
    exact (Set.disjoint_left.1 (L.disj (σ (τ i)) i hne) (h1 ⟨0, rfl⟩)) ⟨0, rfl⟩
  refine ⟨σ, ⟨?_, ?_⟩, ?_⟩
  · intro j j' h
    rw [← hτσ j, h, hτσ j']
  · intro i
    exact ⟨τ i, hστ i⟩
  · intro j
    refine Set.Subset.antisymm (hσ j) ?_
    have h := hτ (σ j)
    rwa [hτσ j] at h

end Work.Drive.N2C
