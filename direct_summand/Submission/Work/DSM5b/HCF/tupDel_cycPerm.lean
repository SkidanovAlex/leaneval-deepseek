import Mathlib
import Submission.Work.DSM5b.HCF.CycPermDefs
import Submission.Work.DSM5b.PerfComplexDefs

/-!
# `tupDel` commutes with the deleted-interval cycle

If `v : Fin (n+2) → Fin (n+1)` takes the same value at `a < b`, then the tuples with the `b`-th and
the `a`-th entry deleted are related by the cyclic permutation `cycPerm a b hab`:

`tupDel b v k = tupDel a v (cycPerm a b hab k)`.

The two "index maps" `Fin.succAbove b` and `Fin.succAbove a ∘ cycPerm a b hab` agree everywhere on
`Fin (n+1)` except at the single index `k` with `(k:ℕ) = (a:ℕ)`, where they take the values `a`
and `b` respectively; there the hypothesis `v a = v b` closes the gap.
-/

namespace Work.DSM5b.HCF

/-- `Fin.succAbove b k` when `(k:ℕ) = (a:ℕ)` and `a < b`: the result is `a`. -/
lemma succAbove_b_of_eq {n : ℕ} (a b : Fin (n + 2)) (hab : a < b) {k : Fin (n + 1)}
    (h : (k : ℕ) = (a : ℕ)) : Fin.succAbove b k = a := by
  have hb : (a : ℕ) < (b : ℕ) := hab
  have hkb : (k : ℕ) < (b : ℕ) := by omega
  rw [Fin.succAbove_of_castSucc_lt b k (show k.castSucc < b from hkb)]
  apply Fin.ext
  rw [Fin.val_castSucc]
  exact h

/-- `Fin.succAbove a (cycPerm a b hab k)` when `(k:ℕ) = (a:ℕ)` and `a < b`: the result is `b`. -/
lemma succAbove_a_cycPerm_of_eq {n : ℕ} (a b : Fin (n + 2)) (hab : a < b) {k : Fin (n + 1)}
    (h : (k : ℕ) = (a : ℕ)) : Fin.succAbove a (cycPerm a b hab k) = b := by
  have hb : (a : ℕ) < (b : ℕ) := hab
  have hk : ((cycPerm a b hab k : Fin (n + 1)) : ℕ) = (b : ℕ) - 1 := cycPerm_val_of_eq a b hab h
  have hge : (a : ℕ) ≤ ((cycPerm a b hab k : Fin (n + 1)) : ℕ) := by rw [hk]; omega
  rw [Fin.succAbove_of_le_castSucc a _ (show a ≤ (cycPerm a b hab k).castSucc from hge)]
  apply Fin.ext
  rw [Fin.val_succ, hk]
  omega

/-- The index maps agree away from the exceptional index `(k:ℕ) = (a:ℕ)`. -/
lemma succAbove_cycPerm_eq {n : ℕ} (a b : Fin (n + 2)) (hab : a < b) {k : Fin (n + 1)}
    (hne : (k : ℕ) ≠ (a : ℕ)) :
    Fin.succAbove a (cycPerm a b hab k) = Fin.succAbove b k := by
  have hb : (a : ℕ) < (b : ℕ) := hab
  rcases lt_trichotomy (k : ℕ) (a : ℕ) with h1 | h1 | h1
  · -- `k < a`: both maps send `k` to itself
    have hj : ((cycPerm a b hab k : Fin (n + 1)) : ℕ) = (k : ℕ) := cycPerm_val_of_lt a b hab h1
    have hja : ((cycPerm a b hab k : Fin (n + 1)) : ℕ) < (a : ℕ) := by rw [hj]; exact h1
    have hkb : (k : ℕ) < (b : ℕ) := by omega
    rw [Fin.succAbove_of_castSucc_lt a _ (show (cycPerm a b hab k).castSucc < a from hja),
      Fin.succAbove_of_castSucc_lt b k (show k.castSucc < b from hkb)]
    apply Fin.ext
    rw [Fin.val_castSucc, Fin.val_castSucc, hj]
  · exact absurd h1 hne
  · by_cases h2 : (k : ℕ) < (b : ℕ)
    · -- `a < k < b`: both maps send `k` to `k - 1 + 1 = k`
      have hj : ((cycPerm a b hab k : Fin (n + 1)) : ℕ) = (k : ℕ) - 1 :=
        cycPerm_val_of_mem a b hab (le_of_lt h1) h2 (by omega)
      have hja : (a : ℕ) ≤ ((cycPerm a b hab k : Fin (n + 1)) : ℕ) := by rw [hj]; omega
      rw [Fin.succAbove_of_le_castSucc a _ (show a ≤ (cycPerm a b hab k).castSucc from hja),
        Fin.succAbove_of_castSucc_lt b k (show k.castSucc < b from h2)]
      apply Fin.ext
      rw [Fin.val_succ, Fin.val_castSucc, hj]
      omega
    · -- `b ≤ k`: both maps send `k` to `k + 1`
      have hkb : (b : ℕ) ≤ (k : ℕ) := not_lt.mp h2
      have hj : ((cycPerm a b hab k : Fin (n + 1)) : ℕ) = (k : ℕ) :=
        cycPerm_val_of_ge a b hab hkb
      have hja : (a : ℕ) ≤ ((cycPerm a b hab k : Fin (n + 1)) : ℕ) := by rw [hj]; omega
      rw [Fin.succAbove_of_le_castSucc a _ (show a ≤ (cycPerm a b hab k).castSucc from hja),
        Fin.succAbove_of_le_castSucc b k (show b ≤ k.castSucc from hkb)]
      apply Fin.ext
      rw [Fin.val_succ, Fin.val_succ, hj]

theorem tupDel_cycPerm {n : ℕ} {v : Fin (n + 2) → Fin (n + 1)} {a b : Fin (n + 2)}
    (hab : a < b) (heq : v a = v b) (k : Fin (n + 1)) :
    Work.DSM5b.tupDel b v k = Work.DSM5b.tupDel a v (Work.DSM5b.HCF.cycPerm a b hab k) := by
  rw [Work.DSM5b.tupDel_apply, Work.DSM5b.tupDel_apply]
  by_cases h : (k : ℕ) = (a : ℕ)
  · rw [succAbove_b_of_eq a b hab h, succAbove_a_cycPerm_of_eq a b hab h, heq]
  · rw [succAbove_cycPerm_eq a b hab h]

end Work.DSM5b.HCF
