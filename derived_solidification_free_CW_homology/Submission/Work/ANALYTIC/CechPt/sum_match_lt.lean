import Mathlib
import Submission.Work.ANALYTIC.CechPt.LevelAux

/-!
# The "strictly below the diagonal" part of the prism identity

The prism identity for the level-`n` dyadic nerve splits the double sum
`∑_{i,j} (-1)^{i+j} G (face_j (W_i y))` into the parts `j < i`, `j = i` or `j = i+1`, and
`i + 1 < j`.  This file treats the first part: the summands with `j < i` reindex (writing
`i = k + 1`, so `k` runs over `Fin (q+1)`) into the summands with `i ≤ j`, using the facing
relation

`face_j (W_{k+1} y) = W_k (face_j y)`   (`face_W_lt`)

and the sign flip `(-1)^{k+1+j} = -(-1)^{k+j}`.
-/

namespace Work.ANALYTIC.CechPt

open Work.ANALYTIC.CechPt.Level

theorem sum_match_lt {M q : ℕ} (y : Work.ANALYTIC.CechPt.Level.lev M (q+1)) (G : Work.ANALYTIC.CechPt.Level.lev M (q+1) → ℤ) :
    (∑ p ∈ (Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter (fun p => (p.2:ℕ) < (p.1:ℕ)),
        (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (Work.ANALYTIC.CechPt.Level.face p.2 (Work.ANALYTIC.CechPt.Level.W p.1 y)))
      = - (∑ p ∈ (Finset.univ : Finset (Fin (q+2) × Fin (q+1))).filter (fun p => (p.1:ℕ) ≤ (p.2:ℕ)),
        (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (Work.ANALYTIC.CechPt.Level.W p.2 (Work.ANALYTIC.CechPt.Level.face p.1 y))) := by
  rw [← Finset.sum_neg_distrib]
  -- Reindex the pairs `(i, j)` with `j < i` by `(j, i-1)`; then `j ≤ i-1` and the two summands
  -- are the negatives of each other.
  refine Finset.sum_bij (fun p _ => (⟨min (p.2:ℕ) (q+1), by omega⟩, ⟨(p.1:ℕ)-1, by omega⟩))
    ?_ ?_ ?_ ?_
  · -- the reindexed pair lies in the "below the diagonal" region
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    omega
  · -- the reindexing is injective
    intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    simp only [Prod.mk.injEq, Fin.mk.injEq] at hab
    have h1 : (a.2:ℕ) = (b.2:ℕ) := by have := hab.1; omega
    have h2 : (a.1:ℕ) = (b.1:ℕ) := by have h := hab.2; omega
    exact Prod.ext (Fin.ext h2) (Fin.ext h1)
  · -- and surjective onto it
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨(⟨(b.2:ℕ)+1, by omega⟩, ⟨(b.1:ℕ), by omega⟩), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
  · -- the value matching: `face_W_lt` on the simplex, and `(-1)^{k+1+j} = -(-1)^{k+j}`
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have hle : (a.2:ℕ) ≤ (a.1:ℕ) - 1 := by omega
    have hF := face_W_lt (M := M) (p := q) (j := (⟨(a.1:ℕ)-1, by omega⟩ : Fin (q+1))) (y := y)
      (i := (⟨(a.2:ℕ), by omega⟩ : Fin (q+2))) (by simpa using hle)
    have hmin : min (a.2:ℕ) (q+1) = (a.2:ℕ) := by omega
    have hpow : (-1:ℤ)^((a.1:ℕ)+(a.2:ℕ)) = -(-1:ℤ)^((a.2:ℕ)+((a.1:ℕ)-1)) := by
      have hn : (a.1:ℕ)+(a.2:ℕ) = ((a.2:ℕ)+((a.1:ℕ)-1))+1 := by omega
      rw [hn, pow_succ, mul_neg_one]
    simp only [hmin]
    rw [show ((⟨(a.2:ℕ), by omega⟩ : Fin (q+3))) = a.2 from Fin.ext rfl,
      show (Fin.succ (⟨(a.1:ℕ)-1, by omega⟩ : Fin (q+1))) = a.1 from
        Fin.ext (by simp only [Fin.val_succ]; omega)] at hF
    rw [hpow, hF]
    dsimp only
    ring

end Work.ANALYTIC.CechPt
