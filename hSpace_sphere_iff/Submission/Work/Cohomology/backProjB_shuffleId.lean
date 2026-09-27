import Mathlib
import Submission.Work.Cohomology.EZShuffle

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

/-- The number of `i : Fin (p + q)` lying in the interval `[p, p + k)`: there are exactly `k` of
them.  This is the cardinality computation underlying the `b`-side of the identity shuffle. -/
lemma card_filter_shift {p q : ℕ} (k : Fin (q + 1)) :
    (Finset.univ.filter (fun i : Fin (p + q) => p ≤ i.val ∧ i.val < k.val + p)).card = k.val := by
  let e : Fin k.val ↪ Fin (p + q) :=
    ⟨fun m => ⟨p + m.val, by have := m.isLt; have := k.isLt; omega⟩,
     fun a b h => by simp only [Fin.mk.injEq] at h; omega⟩
  have hset : (Finset.univ.filter (fun i : Fin (p + q) => p ≤ i.val ∧ i.val < k.val + p))
      = (Finset.univ : Finset (Fin k.val)).map e := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨i.val - p, by omega⟩, ?_⟩
      apply Fin.ext
      show p + (i.val - p) = i.val
      omega
    · rintro ⟨a, ha⟩
      have hval : i.val = p + a.val := by rw [← ha]; rfl
      exact ⟨by omega, by omega⟩
  rw [hset, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- The `b`-side shuffle map of the identity shuffle `{0, … , p-1}` reindexes the interval
`[p, p + k)` to `k`: `bCnt (shuffleId p q) ⟨k + p, _⟩ = k`. -/
lemma bCnt_shuffleId {p q : ℕ} (k : Fin (q + 1)) :
    bCnt (shuffleId p q) (⟨k.val + p, by omega⟩ : Fin (p + q + 1)) = k.val := by
  unfold bCnt
  have hset : (Finset.univ \ shuffleId p q : Finset (Fin (p + q)))
      = Finset.univ.filter (fun i : Fin (p + q) => p ≤ i.val) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter]
    simp [shuffleId]
  rw [hset, Finset.filter_filter]
  exact card_filter_shift k

theorem backProjB_shuffleId {p q : ℕ} (hA : (Work.Cohomology.shuffleId p q).card = p) :
    CategoryTheory.CategoryStruct.comp (SimplexCategory.subinterval p q (by omega))
      (Work.Cohomology.shuffleMapB (Work.Cohomology.shuffleId p q) hA)
      = CategoryTheory.CategoryStruct.id (SimplexCategory.mk q) := by
  apply SimplexCategory.Hom.ext
  ext k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.id_toOrderHom,
    shuffleMapB, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    SimplexCategory.subinterval, OrderHom.comp_coe, Function.comp_apply]
  show bCnt (shuffleId p q) (⟨k.val + p, _⟩ : Fin (p + q + 1)) = k.val
  exact bCnt_shuffleId k

end Work.Cohomology
