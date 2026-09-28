import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP.Lat

open Finset

/-- A degree-`d` monomial in `n+1` variables, described by its exponent vector, is exactly a
function `Fin (n+1) → ℕ` whose values sum to `d`: the sum condition forces each value to be `≤ d`,
so the `Fin (d+1)`-valued description is equivalent to the `ℕ`-valued one. -/
noncomputable def monEquivFun (d n : ℕ) :
    Mon d n ≃ {P : Fin (n + 1) → ℕ // ∑ i, P i = d} where
  toFun m := ⟨fun i => (m.1 i : ℕ), m.2⟩
  invFun P :=
    ⟨fun i => ⟨P.1 i, Nat.lt_succ_of_le
        ((Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq P.2)⟩,
      by simpa using P.2⟩
  left_inv m := by
    apply Subtype.ext
    funext i
    exact Fin.ext rfl
  right_inv P := by
    apply Subtype.ext
    funext i
    rfl

/-- Exponent vectors of degree-`d` monomials in `n+1` variables correspond to multisets of size
`d` on `Fin (n+1)` (a monomial determines the multiset of its variables) — "stars and bars". -/
noncomputable def monEquivSym (d n : ℕ) : Mon d n ≃ Sym (Fin (n + 1)) d :=
  (monEquivFun d n).trans (Sym.equivNatSumOfFintype (Fin (n + 1)) d).symm

/-- The number of degree-`d` monomials in `n+1` variables is the binomial coefficient
`(n + d).choose d`.

Suggested route: exhibit a bijection between `Mon d n` and the symmetric power
`Sym (Fin (n+1)) d` (a monomial determines the multiset of its variables, with multiplicities given
by the exponent vector `Mon.toFinsupp`), then use
`Sym.card_sym_eq_choose : card (Sym α k) = (card α + k - 1).choose k` from
`Mathlib/Data/Sym/Card.lean`.  Alternative: induction on `d` with the stars-and-bars recursion
`card (Mon (d+1) n) = card (Mon d n) + ...`, or an explicit bijection onto
`Finset (Fin (n+1))`-valued data. -/
theorem card_Mon (d n : ℕ) : Fintype.card (Mon d n) = (n + d).choose d := by
  rw [Fintype.card_congr (monEquivSym d n), Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  congr 1
  omega

end Work.HP.Lat
