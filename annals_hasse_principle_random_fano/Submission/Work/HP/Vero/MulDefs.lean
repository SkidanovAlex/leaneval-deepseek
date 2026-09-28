import Mathlib
import Submission.Work.HP.Defs

/-!
# Multiplication of coefficient vectors (product of forms) and the `Ψ`-shift

A degree-`d` form in `n+1` variables is a coefficient vector `A : Mon d n → R` in the monomial
basis (`Mon d n` = exponent vectors of degree-`d` monomials).  This file introduces

* `addMon p q`, the exponent vector of the product of the monomials `p` and `q`;
* `mulVec a b d A B`, the coefficient vector of the product of a degree-`a` form `A` and a
  degree-`b` form `B`, a degree-`d` form (zero when `d ≠ a + b`);
* `unitMon P`, the indicator of a single monomial `P` (so `mulVec _ _ _ (unitMon P) c` is the
  "shift" `X^P · c` of `c`, with the property `eNorm (mulVec _ _ _ (unitMon P) c) = eNorm c`);
* `eMon n i`, the exponent vector of `X_i`, and `linVec c`, the coefficient vector of the linear
  form `∑ i, c i * X_i`.

The product is used by `Work.HP.Vero.lam_Gam_veronese_le` to lift the two-vector `Γ₂`-data to
degree `d`.
-/

set_option autoImplicit false
noncomputable section
open Finset

namespace Work.HP.Vero

/-- `p + q` as exponent vectors of monomials: the degrees add. -/
def addMon {a b n : ℕ} (p : Mon a n) (q : Mon b n) : Mon (a + b) n :=
  ⟨fun i => ⟨(p.1 i : ℕ) + (q.1 i : ℕ), by
      have hp : ((p.1 i : ℕ)) ≤ a := Nat.lt_succ_iff.mp (p.1 i).isLt
      have hq : ((q.1 i : ℕ)) ≤ b := Nat.lt_succ_iff.mp (q.1 i).isLt
      omega⟩,
   by rw [Finset.sum_add_distrib, p.2, q.2]⟩

@[simp] lemma addMon_val {a b n : ℕ} (p : Mon a n) (q : Mon b n) (i : Fin (n + 1)) :
    ((addMon p q).1 i : ℕ) = (p.1 i : ℕ) + (q.1 i : ℕ) := rfl

lemma toFinsupp_addMon {a b n : ℕ} (p : Mon a n) (q : Mon b n) :
    Mon.toFinsupp (addMon p q) = p.toFinsupp + q.toFinsupp := by
  ext i
  simp only [Mon.toFinsupp, Finsupp.equivFunOnFinite, Finsupp.coe_add, Pi.add_apply,
    Equiv.coe_fn_symm_mk]
  rfl

lemma addMon_injective_right {a b n : ℕ} (p : Mon a n) :
    Function.Injective (fun q : Mon b n => addMon p q) := by
  intro q q' h
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hv := congrArg (fun M : Mon (a + b) n => ((M.1 i : ℕ))) h
  simp only [addMon_val] at hv
  omega

lemma addMon_injective_left {a b n : ℕ} (q : Mon b n) :
    Function.Injective (fun p : Mon a n => addMon p q) := by
  intro p p' h
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hv := congrArg (fun M : Mon (a + b) n => ((M.1 i : ℕ))) h
  simp only [addMon_val] at hv
  omega

/-- The coefficient vector of the product of a degree-`a` form and a degree-`b` form, as a
degree-`d` form (zero unless `d = a + b`). -/
def mulVec {n : ℕ} (a b d : ℕ) {R : Type*} [CommSemiring R]
    (A : Mon a n → R) (B : Mon b n → R) : Mon d n → R :=
  fun M => ∑ p : Mon a n, ∑ q : Mon b n,
    if (∀ i, (p.1 i : ℕ) + (q.1 i : ℕ) = (M.1 i : ℕ)) then A p * B q else 0

/-- The indicator of a single monomial (the coefficient vector of the monomial `X^P`). -/
def unitMon {d n : ℕ} {R : Type*} [Zero R] [One R] [DecidableEq (Mon d n)]
    (P : Mon d n) : Mon d n → R := fun m => if m = P then 1 else 0

@[simp] lemma unitMon_same {d n : ℕ} {R : Type*} [Zero R] [One R] [DecidableEq (Mon d n)]
    (P : Mon d n) : unitMon (R := R) P P = 1 := by simp [unitMon]

lemma unitMon_of_ne {d n : ℕ} {R : Type*} [Zero R] [One R] [DecidableEq (Mon d n)]
    {P m : Mon d n} (h : m ≠ P) : unitMon (R := R) P m = 0 := by simp [unitMon, h]

/-- The exponent vector of `X_i` as a degree-`1` monomial. -/
def eMon (n : ℕ) (i : Fin (n + 1)) : Mon 1 n :=
  ⟨fun j => ⟨if j = i then 1 else 0, by split <;> omega⟩,
   by rw [Finset.sum_ite_eq']; simp⟩

@[simp] lemma eMon_val (n : ℕ) (i j : Fin (n + 1)) :
    ((eMon n i).1 j : ℕ) = if j = i then 1 else 0 := rfl

/-- The coefficient vector of the linear form `∑ i, c i * X_i`. -/
def linVec {n : ℕ} (c : Fin (n + 1) → ℝ) : Mon 1 n → ℝ :=
  fun m => ∑ i, if m = eMon n i then c i else 0

end Work.HP.Vero
