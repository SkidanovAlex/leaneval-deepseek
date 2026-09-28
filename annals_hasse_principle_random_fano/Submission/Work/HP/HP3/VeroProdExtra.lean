import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HP3.VeroProdDefs

/-!
# Auxiliary API for `prodVec` (`X^m · ⟨c,X⟩`)

`addE d n hd m j` is the exponent vector `m + e_j` of the degree-`d` monomial `X^m · X_j`, for
`m : Mon (d-1) n`.  The main user is `Work.HP.HP3.veronese_prod_api`.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.HP

/-- The exponent vector of `X^m · X_j` as a natural-valued function of the coordinates. -/
def addEexp (d n : ℕ) (m : Mon (d - 1) n) (j : Fin (n + 1)) : Fin (n + 1) → ℕ :=
  fun i => (m.1 i : ℕ) + (if i = j then 1 else 0)

lemma sum_addEexp {d n : ℕ} (hd : 1 ≤ d) (m : Mon (d - 1) n) (j : Fin (n + 1)) :
    ∑ i, addEexp d n m j i = d := by
  have h1 : (∑ i : Fin (n + 1), (if i = j then (1 : ℕ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq']
    simp
  simp only [addEexp]
  rw [Finset.sum_add_distrib, h1, m.2]
  omega

lemma addEexp_lt {d n : ℕ} (hd : 1 ≤ d) (m : Mon (d - 1) n) (j : Fin (n + 1))
    (i : Fin (n + 1)) : addEexp d n m j i < d + 1 := by
  have h := (m.1 i).isLt
  simp only [addEexp]
  by_cases hij : i = j
  · rw [if_pos hij]; omega
  · rw [if_neg hij]; omega

/-- `m + e_j ∈ Mon d n` for `m : Mon (d-1) n`. -/
def addE (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) (j : Fin (n + 1)) : Mon d n :=
  ⟨fun i => ⟨addEexp d n m j i, addEexp_lt hd m j i⟩, sum_addEexp hd m j⟩

lemma addE_val (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) (j : Fin (n + 1))
    (i : Fin (n + 1)) :
    ((addE d n hd m j).1 i : ℕ) = (m.1 i : ℕ) + (if i = j then 1 else 0) := rfl

lemma addE_injective (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) :
    Function.Injective (addE d n hd m) := by
  intro j j' h
  have h2 : ((addE d n hd m j).1 j : ℕ) = ((addE d n hd m j').1 j : ℕ) :=
    congrArg (fun z : Mon d n => ((z.1 j : ℕ))) h
  rw [addE_val d n hd m j j, addE_val d n hd m j' j] at h2
  by_cases hjj : j = j'
  · exact hjj
  · exfalso
    have h3 := h2
    rw [if_pos rfl, if_neg hjj, add_zero] at h3
    omega

end Work.HP
