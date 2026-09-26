import Mathlib

/-!
# `Work.BoxShrink.Pinch.good_of_small_cell_decomposition`

A compact subset `K ⊆ ℂ` admitting, for every `δ > 0`, a finite decomposition by pairwise
disjoint compact *convex* cells of diameter `< δ` covering `K`, can be partitioned into
nonempty compact pieces with pairwise disjoint convex hulls, all of them avoiding a prescribed
point `t ∉ K` (`Work.BoxShrink.Pinch.GoodPart K t`).

The construction is the obvious one: since `K` is compact and `t ∉ K`, the distance
`d = infDist t K` is positive; take the decomposition with `δ = d` and intersect the cells with
`K`, discarding the cells that miss `K`.  Each surviving piece lies in its convex cell, which has
diameter `< d`; the cells are pairwise disjoint, so the pieces have pairwise disjoint hulls, and a
cell meeting `K` cannot contain `t` (a point of `K ∩ cell` would be at distance `≤ diam cell < d`
from `t`).  The empty case `K = ∅` is handled by the empty family.
-/

namespace Work.BoxShrink.Pinch

open Set Metric

theorem good_of_small_cell_decomposition {K : Set ℂ} (hK : IsCompact K) {t : ℂ} (ht : t ∉ K)
    (hcell : ∀ δ : ℝ, 0 < δ → ∃ (m : ℕ) (C : Fin m → Set ℂ),
      (∀ i, IsCompact (C i)) ∧ (∀ i, Convex ℝ (C i)) ∧ (∀ i, Metric.diam (C i) < δ) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧ K ⊆ ⋃ i, C i) :
    ∃ (m : ℕ) (P : Fin m → Set ℂ),
      (∀ i, (P i).Nonempty) ∧ (∀ i, IsCompact (P i)) ∧ (∀ i, P i ⊆ K) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧ K ⊆ ⋃ i, P i ∧
      (∀ i j, i ≠ j → Disjoint (convexHull ℝ (P i)) (convexHull ℝ (P j))) ∧
      (∀ i, Disjoint (convexHull ℝ (P i)) ({t} : Set ℂ)) := by
  classical
  by_cases hKne : K.Nonempty
  · -- `K` is nonempty: take the decomposition at the scale `infDist t K`.
    have hd : 0 < Metric.infDist t K := (hK.isClosed.notMem_iff_infDist_pos hKne).mp ht
    obtain ⟨m, C, hCc, hCconv, hCdiam, hCdisj, hCcov⟩ := hcell (Metric.infDist t K) hd
    -- the cells that meet `K`, enumerated by `Fin`
    let S : Finset (Fin m) := Finset.univ.filter (fun i => (C i ∩ K).Nonempty)
    let σ : Fin S.card → Fin m := fun j => ((Finset.equivFin S).symm j).val
    have hσmem : ∀ j, σ j ∈ S := fun j => ((Finset.equivFin S).symm j).property
    have hσinj : Function.Injective σ := by
      intro a b hab
      have h1 : (Finset.equivFin S).symm a = (Finset.equivFin S).symm b := Subtype.ext hab
      exact (Finset.equivFin S).symm.injective h1
    have hσsurj : ∀ i ∈ S, ∃ j, σ j = i := by
      intro i hi
      refine ⟨(Finset.equivFin S) ⟨i, hi⟩, ?_⟩
      simp [σ]
    refine ⟨S.card, fun j => C (σ j) ∩ K, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j; exact (Finset.mem_filter.mp (hσmem j)).2
    · intro j; exact (hCc (σ j)).inter_right hK.isClosed
    · intro j; exact inter_subset_right
    · intro i j hij
      exact (hCdisj (σ i) (σ j) (fun h => hij (hσinj h))).mono inter_subset_left inter_subset_left
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hCcov hx)
      have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, ⟨x, hi, hx⟩⟩
      obtain ⟨j, hj⟩ := hσsurj i hiS
      refine mem_iUnion.mpr ⟨j, ?_, hx⟩
      rw [hj]; exact hi
    · intro i j hij
      refine (hCdisj (σ i) (σ j) (fun h => hij (hσinj h))).mono ?_ ?_
      · exact convexHull_min inter_subset_left (hCconv (σ i))
      · exact convexHull_min inter_subset_left (hCconv (σ j))
    · intro j
      rw [Set.disjoint_singleton_right]
      intro hmem
      have hsub : convexHull ℝ (C (σ j) ∩ K) ⊆ C (σ j) :=
        convexHull_min inter_subset_left (hCconv (σ j))
      -- a cell meeting `K` cannot contain `t`
      have htC : t ∉ C (σ j) := by
        intro htC
        obtain ⟨x, hxC, hxK⟩ := (Finset.mem_filter.mp (hσmem j)).2
        have hb : Bornology.IsBounded (C (σ j)) := (hCc (σ j)).isBounded
        have h1 : dist t x ≤ Metric.diam (C (σ j)) := dist_le_diam_of_mem hb htC hxC
        have h2 : Metric.diam (C (σ j)) < Metric.infDist t K := hCdiam (σ j)
        have h3 : Metric.infDist t K ≤ dist t x := (Metric.le_infDist hKne).mp le_rfl hxK
        linarith
      exact htC (hsub hmem)
  · -- `K = ∅`: the empty family works.
    refine ⟨0, fun i => i.elim0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro x hx; exact absurd ⟨x, hx⟩ hKne
    · intro i; exact i.elim0
    · intro i; exact i.elim0

end Work.BoxShrink.Pinch
