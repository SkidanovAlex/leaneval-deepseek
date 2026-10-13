import Mathlib
import Submission.Work.DSEQ0.CupBasic

open CategoryTheory AlgebraicGeometry Limits
open scoped Simplicial

namespace Work.DSEQ0Cup

set_option backward.isDefEq.respectTransparency false

/-- The value of the coface `δ_k` at `j` is `j` if `j < k` and `j + 1` otherwise. -/
lemma deltaMap_apply_val (n : ℕ) (k : Fin (n+2)) (j : Fin (n+1)) :
    (Work.DSEQ0.Cup.deltaMap n k j).val = if j.val < k.val then j.val else j.val + 1 := by
  rw [show Work.DSEQ0.Cup.deltaMap n k j = Fin.succAbove k j from rfl]
  by_cases h : j.val < k.val
  · rw [ite_eq_left h, Fin.succAbove_of_castSucc_lt]
    · rfl
    · simp only [Fin.lt_def, Fin.val_castSucc]; exact h
  · rw [ite_eq_right h, Fin.succAbove_of_le_castSucc]
    · rfl
    · simp only [Fin.le_def, Fin.val_castSucc]; omega

lemma frontIdx_val (p q : ℕ) (i : Fin (p+1)) :
    (Work.DSEQ0.Cup.frontIdx p q i).val = i.val := rfl

lemma backIdx_val (p q : ℕ) (j : Fin (q+1)) :
    (Work.DSEQ0.Cup.backIdx p q j).val = p + j.val := rfl

lemma castIdx_val (p q : ℕ) (x : Fin (((p+1)+q)+1)) :
    (Work.DSEQ0.Cup.castIdx p q x).val = x.val := rfl

theorem aw_indices (p q : ℕ) :
    (∀ (k : Fin (p+q+2)) (hk : (k : ℕ) ≤ p) (i : Fin (p+1)),
        Work.DSEQ0.Cup.deltaMap (p+q) k (Work.DSEQ0.Cup.frontIdx p q i) =
          Work.DSEQ0.Cup.castIdx p q (Work.DSEQ0.Cup.frontIdx (p+1) q
            (Work.DSEQ0.Cup.deltaMap p ⟨k.val, by omega⟩ i)))
    ∧ (∀ (k : Fin (p+q+2)) (hk : (k : ℕ) ≤ p) (j : Fin (q+1)),
        Work.DSEQ0.Cup.deltaMap (p+q) k (Work.DSEQ0.Cup.backIdx p q j) =
          Work.DSEQ0.Cup.castIdx p q (Work.DSEQ0.Cup.backIdx (p+1) q j))
    ∧ (∀ (j : Fin (q+1)) (i : Fin (p+1)),
        Work.DSEQ0.Cup.deltaMap (p+q) ⟨p+1+j.val, by omega⟩ (Work.DSEQ0.Cup.frontIdx p q i) =
          Work.DSEQ0.Cup.frontIdx p (q+1) i)
    ∧ (∀ (j j' : Fin (q+1)),
        Work.DSEQ0.Cup.deltaMap (p+q) ⟨p+1+j.val, by omega⟩ (Work.DSEQ0.Cup.backIdx p q j') =
          Work.DSEQ0.Cup.backIdx p (q+1) (Work.DSEQ0.Cup.deltaMap q (Fin.succ j) j'))
    ∧ (∀ i : Fin (p+1),
        Work.DSEQ0.Cup.castIdx p q (Work.DSEQ0.Cup.frontIdx (p+1) q
            (Work.DSEQ0.Cup.deltaMap p (Fin.last (p+1)) i)) =
          Work.DSEQ0.Cup.frontIdx p (q+1) i)
    ∧ (∀ j' : Fin (q+1),
        Work.DSEQ0.Cup.castIdx p q (Work.DSEQ0.Cup.backIdx (p+1) q j') =
          Work.DSEQ0.Cup.backIdx p (q+1) (Work.DSEQ0.Cup.deltaMap q 0 j')) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk i
    apply Fin.ext
    simp only [deltaMap_apply_val, frontIdx_val, castIdx_val]
  · intro k hk j
    apply Fin.ext
    simp only [deltaMap_apply_val, backIdx_val, castIdx_val]
    split_ifs <;> omega
  · intro j i
    apply Fin.ext
    simp only [deltaMap_apply_val, frontIdx_val]
    split_ifs <;> omega
  · intro j j'
    apply Fin.ext
    simp only [deltaMap_apply_val, backIdx_val, Fin.val_succ]
    split_ifs <;> omega
  · intro i
    apply Fin.ext
    simp only [deltaMap_apply_val, frontIdx_val, castIdx_val, Fin.val_last]
    split_ifs <;> omega
  · intro j'
    apply Fin.ext
    simp only [deltaMap_apply_val, backIdx_val, castIdx_val, Fin.val_zero]
    split_ifs <;> omega

end Work.DSEQ0Cup
