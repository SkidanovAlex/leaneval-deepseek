import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.density_aux

/-!
# Definitions for `Work.HP.badclass.card_badCls_le`

The set `BadCls d n p a` (`density_aux`) consists of the coefficient classes `a mod p` all of whose
nonzero `F_p`-zeros are singular.  This file collects the objects used by the second-moment
(Chebyshev) argument bounding the number of such classes:

* `gradZ d n p a i x` — the `i`-th formal partial derivative of `f_a` at `x`, over `ZMod p`
  (identically the expression appearing in `BadCls`);
* `monE d n i` — the exponent vector `d · e_i`, an element of `Mon d n` (the monomial `x_i ^ d`);
* `TorS n p` / `torFinset n p` — the torus `(ZMod p ^×) ^ {n+1}`;
* `Dset d n p x` — the coefficient classes having `x` as a *nonsingular* zero;
* `Mval d n p a` — the number of torus points at which `a` has a nonsingular zero.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP

/-- The `i`-th formal partial derivative of `f_a` at `x`, evaluated over `ZMod p`.  This is
exactly the gradient expression appearing in the definition of `BadCls`. -/
def gradZ (d n p : ℕ) (a : Mon d n → ZMod p) (i : Fin (n + 1))
    (x : Fin (n + 1) → ZMod p) : ZMod p :=
  ∑ m : Mon d n, a m * (m.1 i : ZMod p) *
    ∏ j : Fin (n + 1), x j ^ ((m.1 j : ℕ) - if j = i then 1 else 0)

/-- The exponent vector `d · e_i` of the monomial `x_i ^ d`, as an element of `Mon d n`. -/
def monE (d n : ℕ) (i : Fin (n + 1)) : Mon d n :=
  ⟨fun j => if j = i then (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)) else 0, by
    have h : ∀ j, ((if j = i then (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)) else 0 : Fin (d + 1)) : ℕ)
        = if j = i then d else 0 := by
      intro j; by_cases h : j = i <;> simp [h]
    simp only [h]
    rw [Finset.sum_ite_eq' Finset.univ i (fun _ => (d : ℕ))]
    simp⟩

/-- The `i`-th coordinate of `monE d n i` is `d`. -/
lemma monE_self (d n : ℕ) (i : Fin (n + 1)) : ((monE d n i).1 i : ℕ) = d := by
  simp only [monE]; simp

/-- The `j`-th coordinate of `monE d n i` vanishes for `j ≠ i`. -/
lemma monE_ne (d n : ℕ) (i j : Fin (n + 1)) (h : j ≠ i) : ((monE d n i).1 j : ℕ) = 0 := by
  simp only [monE]; simp [h]

/-- `Mon d n` has at least `n+1` elements (the `d`-th powers of the coordinates). -/
lemma le_NN (d n : ℕ) (hd : 1 ≤ d) : n + 1 ≤ NN d n := by
  have hinj : Function.Injective (monE d n) := by
    intro i j hij
    by_contra h
    have h1 : ((monE d n i).1 i : ℕ) = ((monE d n j).1 i : ℕ) := by rw [hij]
    rw [monE_self d n i, monE_ne d n j i h] at h1
    omega
  have h := Fintype.card_le_of_injective (monE d n) hinj
  simpa [NN] using h

/-- The torus `(ZMod p ^×) ^ {n+1}` as a set of points of `F_p^{n+1}`. -/
def TorS (n p : ℕ) : Set (Fin (n + 1) → ZMod p) := {x | ∀ i, x i ≠ 0}

/-- The torus as a finset. -/
def torFinset (n p : ℕ) [NeZero p] : Finset (Fin (n + 1) → ZMod p) :=
  Finset.univ.filter (fun x => ∀ i, x i ≠ 0)

/-- The set of coefficient classes `a` for which `x` is a *nonsingular* zero of `f_a`. -/
def Dset (d n p : ℕ) (x : Fin (n + 1) → ZMod p) : Set (Mon d n → ZMod p) :=
  {a | formEvalZMod d n p a x = 0 ∧ ∃ i, gradZ d n p a i x ≠ 0}

/-- The number of torus points at which `a` has a nonsingular zero. -/
def Mval (d n p : ℕ) [NeZero p] (a : Mon d n → ZMod p) : ℕ := by
  classical
  exact ∑ x ∈ torFinset n p, if a ∈ Dset d n p x then 1 else 0

/-- `Set.ncard` of a set in a finite type is the cardinality of the corresponding filter. -/
lemma ncard_eq_filter_card {α : Type*} [Fintype α] (s : Set α)
    [DecidablePred (fun a => a ∈ s)] :
    s.ncard = (Finset.univ.filter (fun a => a ∈ s)).card := by
  classical
  rw [← Set.ncard_coe_finset (Finset.univ.filter (fun a => a ∈ s))]
  congr 1
  ext a
  simp

/-- `Nat.card` of a submodule (as a type) is the `ncard` of its underlying set. -/
lemma ncard_coe_submodule {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (S : Submodule F V) : (S : Set V).ncard = Nat.card ↥S := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1, by simpa using x.2⟩
      invFun := fun x => ⟨x.1, by simpa using x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }

/-- A `BadCls` class has no nonsingular zero, hence `Mval` vanishes on it. -/
lemma Mval_eq_zero_of_badCls (d n p : ℕ) [NeZero p] (a : Mon d n → ZMod p)
    (ha : BadCls d n p a) : Mval d n p a = 0 := by
  rw [Mval, Finset.sum_eq_zero_iff]
  intro x hx
  simp only [torFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  by_cases h : a ∈ Dset d n p x
  · simp only [Dset, Set.mem_ofPred_eq] at h
    have hx0 : x ≠ 0 := fun h0 => hx 0 (by rw [h0]; rfl)
    exact absurd (ha x hx0 h.1 h.2.choose) h.2.choose_spec
  · simp [h]

end Work.HP
