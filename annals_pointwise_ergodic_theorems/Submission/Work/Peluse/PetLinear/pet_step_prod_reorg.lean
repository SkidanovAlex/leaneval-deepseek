import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.PetLinear

/-- Reorganise the double product over `Fin (m+1) × Bool` (with the `(0, false)` entry
contributing `1`) into the leading factor `star (F 1 (x + c 1 * a))` together with a
product over `Fin m` of the two factors `star (F j (...)) * F j (...)`, `j = i.succ.succ`.
The two `ℤ`-arguments are matched by `ring` identities. -/
theorem pet_step_prod_reorg {m : ℕ} (F : Fin (m + 2) → ℤ → ℂ) (c : Fin (m + 2) → ℤ) (x y a : ℤ) :
    (∏ i : Fin (m + 1), ∏ ε : Bool,
        (if ((i, ε) = ((0 : Fin (m + 1)), false)) then (1 : ℂ)
          else (if ε then star (F i.succ (x + (c i.succ * (y + a) - c 1 * y)))
                else F i.succ (x + (c i.succ * y - c 1 * y)))))
      = star (F 1 (x + c 1 * a)) *
        ∏ i : Fin m,
          (star (F (i.succ.succ) (x + (c (i.succ.succ) - c 1) * y + c (i.succ.succ) * a))
            * F (i.succ.succ) (x + (c (i.succ.succ) - c 1) * y)) := by
  -- peel off the `i = 0` factor of the outer product
  rw [Fin.prod_univ_succ]
  -- expand the inner product over `Bool`
  simp only [Fintype.prod_bool]
  -- evaluate the `if` conditions: `(0, ε) = (0, false)`, and `(i.succ, ε) = (0, false)` is false
  simp only [Fin.succ_ne_zero, Prod.mk.injEq, true_and, false_and, if_false, if_true,
    Fin.succ_zero_eq_one, Bool.true_eq_false, Bool.false_eq_true]
  rw [mul_one]
  congr 1
  · -- the `i = 0` factor: `x + c 1 * (y + a) - c 1 * y = x + c 1 * a`
    rw [show x + (c 1 * (y + a) - c 1 * y) = x + c 1 * a by ring]
  · -- the remaining factors, matched by reindexing `Fin m` and two ring identities
    apply Finset.prod_congr rfl
    intro i _
    rw [show x + (c i.succ.succ * (y + a) - c 1 * y)
          = x + (c i.succ.succ - c 1) * y + c i.succ.succ * a by ring,
        show x + (c i.succ.succ * y - c 1 * y) = x + (c i.succ.succ - c 1) * y by ring]

end Work.Peluse.PetLinear
