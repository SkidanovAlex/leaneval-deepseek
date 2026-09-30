import Mathlib
import Submission.Work.BW.extract_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped BigOperators

variable {R : Type*} [CommRing R] {ℓ : ℕ}

/-- Peel the first factor of a falling factorial. -/
lemma descFactorial_succ_eq (n k : ℕ) :
    n.descFactorial (k + 1) = n * (n - 1).descFactorial k := by
  have h := Nat.descFactorial_mul_descFactorial (k := 1) (m := k + 1) (n := n)
    (by omega : 1 ≤ k + 1)
  simp only [Nat.add_sub_cancel, Nat.descFactorial_one] at h
  exact (Nat.mul_comm _ _ ▸ h).symm

/-- The number of occurrences of `i` increases by one when `i` is prepended. -/
lemma cnt_cons_same (w : List (Fin ℓ)) (i : Fin ℓ) :
    cnt (i :: w) i = cnt w i + 1 := by
  simp only [cnt, List.countP_cons]
  by_cases h : i = i
  · simp
  · exact absurd rfl h

/-- Prepending `i` does not change the count of any other letter. -/
lemma cnt_cons_ne (w : List (Fin ℓ)) {i j : Fin ℓ} (h : j ≠ i) :
    cnt (i :: w) j = cnt w j := by
  simp only [cnt, List.countP_cons]
  have h' : decide (i = j) = false := by simp [Ne.symm h]
  simp [h']

/-- The `i`-th coordinate of `decr β i` is `β i - 1`. -/
lemma decr_self (β : Fin ℓ → ℕ) (i : Fin ℓ) : decr β i i = β i - 1 := by
  simp [decr]

/-- `decr` does not move any other coordinate. -/
lemma decr_ne (β : Fin ℓ → ℕ) {i j : Fin ℓ} (h : j ≠ i) : decr β i j = β j := by
  rw [decr]
  exact Function.update_of_ne h (β i - 1) β

/-- The per-coordinate factor of `mainTerm`. -/
def mFac (u D : Fin ℓ → R) (w : List (Fin ℓ)) (β : Fin ℓ → ℕ) (j : Fin ℓ) : R :=
  ((β j).descFactorial (cnt w j) : R) * D j ^ (cnt w j) * u j ^ (β j - cnt w j)

/-- `mainTerm` as a product of one factor per coordinate. -/
lemma mainTerm_eq_prod (u D : Fin ℓ → R) (w : List (Fin ℓ)) (β : Fin ℓ → ℕ) :
    mainTerm u D w β = ∏ j, mFac u D w β j := by
  unfold mainTerm mFac
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-- Off the special coordinate, prepending `i` just corresponds to `decr`. -/
lemma mFac_cons_ne (u D : Fin ℓ → R) (w : List (Fin ℓ)) (β : Fin ℓ → ℕ)
    {i j : Fin ℓ} (h : j ≠ i) :
    mFac u D (i :: w) β j = mFac u D w (decr β i) j := by
  simp only [mFac, cnt_cons_ne w h, decr_ne β h]

/-- At the special coordinate, prepending `i` multiplies by `β i · D i`. -/
lemma mFac_cons_self (u D : Fin ℓ → R) (w : List (Fin ℓ)) (β : Fin ℓ → ℕ) (i : Fin ℓ) :
    mFac u D (i :: w) β i = (β i : R) * D i * mFac u D w (decr β i) i := by
  have hexp : β i - (cnt w i + 1) = (β i - 1) - cnt w i := by omega
  simp only [mFac, cnt_cons_same w i, decr_self β i, hexp]
  rw [descFactorial_succ_eq, Nat.cast_mul, pow_succ]
  ring

/-- The recursion of the expected main term: prepending an operator to the word lowers the `i`-th exponent by one and multiplies by `β i · D i`. -/
theorem mainterm_cons {R : Type*} [CommRing R] {ℓ : ℕ} (u D : Fin ℓ → R)
    (i : Fin ℓ) (w : List (Fin ℓ)) (β : Fin ℓ → ℕ) :
    mainTerm u D (i :: w) β = (β i : R) * D i * mainTerm u D w (decr β i) := by
  rw [mainTerm_eq_prod, mainTerm_eq_prod]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton i (mFac u D (i :: w) β)
        (fun h => absurd (Finset.mem_univ i) h)]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton i (mFac u D w (decr β i))
        (fun h => absurd (Finset.mem_univ i) h)]
  rw [mFac_cons_self u D w β i]
  have hoff : (∏ j ∈ (Finset.univ : Finset (Fin ℓ)) \ {i}, mFac u D (i :: w) β j)
      = ∏ j ∈ (Finset.univ : Finset (Fin ℓ)) \ {i}, mFac u D w (decr β i) j := by
    refine Finset.prod_congr rfl (fun j hj => ?_)
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
    exact mFac_cons_ne u D w β hj.2
  rw [hoff]
  ring

end Work.BW
