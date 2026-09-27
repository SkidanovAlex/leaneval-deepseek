import Mathlib
import Submission.Work.Cohomology.EZG.dAux
import Submission.Work.Cohomology.EZG.cntB_swapA_of_ne

namespace Work.Cohomology.EZG

open CategoryTheory Simplicial Opposite
open Work.Cohomology

/-- The value of the coface map `δ k` at `j`, written with `Fin.succAbove`. -/
lemma delta_apply_val {N : ℕ} (k : Fin (N+2)) (j : Fin (N+1)) :
    ((SimplexCategory.δ k).toOrderHom j) = Fin.succAbove k j := by
  have h : ⇑(ConcreteCategory.hom (SimplexCategory.δ k)) = Fin.succAbove k :=
    SimplexCategory.coe_δ k
  exact congrFun h j

theorem delta_shB_swapA {N Q : ℕ} (A : Finset (Fin (N+1))) (q : Fin N) (k : Fin (N+2)) (hk : k.val = q.val + 1) (h : q.castSucc ∈ A ↔ q.succ ∉ A) (hB : N+1 ≤ A.card + (Q+1)) (hB' : N+1 ≤ (Work.Cohomology.EZG.swapA N A q).card + (Q+1)) : CategoryTheory.CategoryStruct.comp (SimplexCategory.δ k) (Work.Cohomology.shB A hB) = CategoryTheory.CategoryStruct.comp (SimplexCategory.δ k) (Work.Cohomology.shB (Work.Cohomology.EZG.swapA N A q) hB') := by
  have hqk : (q.succ : ℕ) = k.val := by rw [Fin.val_succ, hk]
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
  rw [shB_apply_val, shB_apply_val, delta_apply_val]
  exact cntB_swapA_of_ne A q h (Nat.le_of_lt_succ (Fin.succAbove k j).isLt)
    (fun hh => Fin.succAbove_ne k j (Fin.ext (by rw [hh, hqk])))

end Work.Cohomology.EZG
