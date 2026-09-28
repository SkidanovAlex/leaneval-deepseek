import Mathlib
import Submission.Work.HP.badclass.BadDefs

set_option autoImplicit false
noncomputable section

open MvPolynomial Finset

namespace Work.HP.badclass

/-- The torus `(ZMod p ^×)^{n+1}` has `(p-1)^{n+1}` points. -/
theorem torus_card (n p : ℕ) [NeZero p] :
    (Work.HP.torFinset n p).card = (p - 1) ^ (n + 1) := by
  classical
  have hset : Work.HP.torFinset n p
      = Fintype.piFinset (fun _ : Fin (n + 1) =>
          (Finset.univ.filter (fun z : ZMod p => z ≠ 0))) := by
    ext x
    simp only [Work.HP.torFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset]
  have h1 : ∀ _i : Fin (n + 1),
      ((Finset.univ : Finset (ZMod p)).filter (fun z => z ≠ 0)).card = p - 1 := by
    intro i
    rw [Finset.filter_ne' (Finset.univ : Finset (ZMod p)) 0,
      Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
  rw [hset, Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  exact h1 0

end Work.HP.badclass
