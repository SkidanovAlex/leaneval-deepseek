import Mathlib
import Submission.Work.TMC14Core.Weyl

/-!
# `TMC14Core.InvSumAux`: combinatorial setup for the word-inversion sum `InvSumF`

We package the finite sums appearing in the identity

`∑_f ω ^ (invCount (2m) f) = (-1)^m ω ^ (m*(3m+1)/2)`

where `f` runs over the `2m`-long words over the alphabet
`{(true,true), (false,true)} = {U, V}` with exactly `m` letters `U`.

The proof strategy is a two-parameter recursion on the length `n` and the
number `a` of `U`-letters, together with the closed product formula
`∏_{k=1}^a (1 - ω^{b+k}) / ∏_{k=1}^a (1 - ω^k)`.
-/

noncomputable section

namespace Work.TMC14Core

/-- Number of coordinates of the word `f` equal to the letter `x`. -/
def cntL (x : Bool × Bool) (n : ℕ) (f : Fin n → Bool × Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => f i = x)).card

/-- The weighted word sum: words of length `n` over `{U, V}` (`U = (true,true)`,
`V = (false,true)`) with exactly `a` letters `U`, weighted by `ω ^ (invCount n f)`. -/
def wordSum (ω : ℂ) (n a : ℕ) : ℂ :=
  ∑ f ∈ (Finset.univ : Finset (Fin n → Bool × Bool)).filter
      (fun f => (∀ i, f i = (true, true) ∨ f i = (false, true)) ∧
        (Finset.univ.filter (fun i => f i = (true, true))).card = a),
    ω ^ (invCount n f)

/-- `Dprod ω a = ∏_{k=1}^{a} (1 - ω^k)`. -/
def Dprod (ω : ℂ) (a : ℕ) : ℂ :=
  ∏ k ∈ Finset.Icc 1 a, (1 - ω ^ k)

/-- `Qprod ω a b = ∏_{k=1}^{a} (1 - ω^{b+k})`. -/
def Qprod (ω : ℂ) (a b : ℕ) : ℂ :=
  ∏ k ∈ Finset.Icc 1 a, (1 - ω ^ (b + k))

/-- The word of length `n+1` starting with the letter `U = (true,true)`. -/
def consU {n : ℕ} (g : Fin n → Bool × Bool) : Fin (n+1) → Bool × Bool :=
  Fin.cons (true, true) g

/-- The word of length `n+1` starting with the letter `V = (false,true)`. -/
def consV {n : ℕ} (g : Fin n → Bool × Bool) : Fin (n+1) → Bool × Bool :=
  Fin.cons (false, true) g

@[simp] theorem consU_zero {n : ℕ} (g : Fin n → Bool × Bool) :
    consU g 0 = (true, true) := rfl

@[simp] theorem consU_succ {n : ℕ} (g : Fin n → Bool × Bool) (i : Fin n) :
    consU g i.succ = g i := rfl

@[simp] theorem consV_zero {n : ℕ} (g : Fin n → Bool × Bool) :
    consV g 0 = (false, true) := rfl

@[simp] theorem consV_succ {n : ℕ} (g : Fin n → Bool × Bool) (i : Fin n) :
    consV g i.succ = g i := rfl

theorem cntL_cons_self (x : Bool × Bool) (n : ℕ) (g : Fin n → Bool × Bool) :
    cntL x (n+1) (Fin.cons x g) = cntL x n g + 1 := by
  simp only [cntL, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    if_true, ↓reduceIte]
  omega

theorem cntL_cons_ne {x y : Bool × Bool} (h : x ≠ y) (n : ℕ) (g : Fin n → Bool × Bool) :
    cntL y (n+1) (Fin.cons x g) = cntL y n g := by
  simp only [cntL, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [if_neg h]
  simp

theorem cntL_cons (x c : Bool × Bool) (n : ℕ) (g : Fin n → Bool × Bool) :
    cntL x (n+1) (Fin.cons c g) = cntL x n g + (if c = x then 1 else 0) := by
  by_cases h : c = x
  · rw [h, if_pos rfl]; exact cntL_cons_self x n g
  · rw [if_neg h]; exact cntL_cons_ne h n g

theorem invCount_eq_dsum (n : ℕ) (f : Fin n → Bool × Bool) :
    invCount n f = ∑ i : Fin n, ∑ j : Fin n,
      (if f i = (true, true) ∧ f j = (false, true) ∧ i.val < j.val then (1:ℕ) else 0) := by
  rw [invCount]
  simp only [Finset.sum_filter, Finset.card_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : f i = (true, true)
  · simp only [hi, true_and, ↓reduceIte]
  · simp [hi]

theorem invCount_cons_tt (n : ℕ) (g : Fin n → Bool × Bool) :
    invCount (n+1) (consU g) = cntL (false, true) n g + invCount n g := by
  rw [invCount_eq_dsum (n+1) (consU g), invCount_eq_dsum n g]
  rw [Fin.sum_univ_succ]
  have h1 : (∑ j : Fin (n+1), if (consU g 0 = (true,true) ∧ consU g j = (false,true) ∧
      (0:Fin (n+1)).val < j.val) then (1:ℕ) else 0) = cntL (false,true) n g := by
    rw [Fin.sum_univ_succ]
    rw [show (if (consU g 0 = (true,true) ∧ consU g 0 = (false,true) ∧
        (0:Fin (n+1)).val < (0:Fin (n+1)).val) then (1:ℕ) else 0) = 0 from by simp]
    rw [zero_add, cntL, Finset.card_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hc : g j = (false,true)
    · have hcond : consU g 0 = (true,true) ∧ consU g j.succ = (false,true) ∧
          (0:Fin (n+1)).val < j.succ.val := by
        refine ⟨rfl, ?_, ?_⟩
        · simpa using hc
        · simp only [Fin.val_succ, Fin.val_zero]; omega
      rw [if_pos hcond, if_pos hc]
    · have hcond : ¬ (consU g 0 = (true,true) ∧ consU g j.succ = (false,true) ∧
          (0:Fin (n+1)).val < j.succ.val) := by
        rintro ⟨-, hh, -⟩
        exact hc (by simpa using hh)
      rw [if_neg hcond, if_neg hc]
  have h2 : (∑ i : Fin n, ∑ j : Fin (n+1), if (consU g i.succ = (true,true) ∧
      consU g j = (false,true) ∧ i.succ.val < j.val) then (1:ℕ) else 0)
      = ∑ i : Fin n, ∑ j : Fin n,
        (if g i = (true,true) ∧ g j = (false,true) ∧ i.val < j.val then (1:ℕ) else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.sum_univ_succ]
    rw [show (if (consU g i.succ = (true,true) ∧ consU g 0 = (false,true) ∧
        i.succ.val < (0:Fin (n+1)).val) then (1:ℕ) else 0) = 0 from by simp]
    rw [zero_add]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hc : g i = (true,true) ∧ g j = (false,true) ∧ i.val < j.val
    · have hcond : consU g i.succ = (true,true) ∧ consU g j.succ = (false,true) ∧
          i.succ.val < j.succ.val := by
        refine ⟨?_, ?_, ?_⟩
        · simpa using hc.1
        · simpa using hc.2.1
        · simp only [Fin.val_succ]; omega
      rw [if_pos hcond, if_pos hc]
    · have hcond : ¬ (consU g i.succ = (true,true) ∧ consU g j.succ = (false,true) ∧
          i.succ.val < j.succ.val) := by
        rintro ⟨h1, h2, h3⟩
        refine hc ⟨?_, ?_, ?_⟩
        · simpa using h1
        · simpa using h2
        · simp only [Fin.val_succ] at h3; omega
      rw [if_neg hcond, if_neg hc]
  rw [h1, h2]

theorem invCount_cons_ft (n : ℕ) (g : Fin n → Bool × Bool) :
    invCount (n+1) (consV g) = invCount n g := by
  rw [invCount_eq_dsum (n+1) (consV g), invCount_eq_dsum n g]
  rw [Fin.sum_univ_succ]
  have h1 : (∑ j : Fin (n+1), if (consV g 0 = (true,true) ∧ consV g j = (false,true) ∧
      (0:Fin (n+1)).val < j.val) then (1:ℕ) else 0) = 0 := by
    simp
  have h2 : (∑ i : Fin n, ∑ j : Fin (n+1), if (consV g i.succ = (true,true) ∧
      consV g j = (false,true) ∧ i.succ.val < j.val) then (1:ℕ) else 0)
      = ∑ i : Fin n, ∑ j : Fin n,
        (if g i = (true,true) ∧ g j = (false,true) ∧ i.val < j.val then (1:ℕ) else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.sum_univ_succ]
    rw [show (if (consV g i.succ = (true,true) ∧ consV g 0 = (false,true) ∧
        i.succ.val < (0:Fin (n+1)).val) then (1:ℕ) else 0) = 0 from by simp]
    rw [zero_add]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hc : g i = (true,true) ∧ g j = (false,true) ∧ i.val < j.val
    · have hcond : consV g i.succ = (true,true) ∧ consV g j.succ = (false,true) ∧
          i.succ.val < j.succ.val := by
        refine ⟨?_, ?_, ?_⟩
        · simpa using hc.1
        · simpa using hc.2.1
        · simp only [Fin.val_succ]; omega
      rw [if_pos hcond, if_pos hc]
    · have hcond : ¬ (consV g i.succ = (true,true) ∧ consV g j.succ = (false,true) ∧
          i.succ.val < j.succ.val) := by
        rintro ⟨h1, h2, h3⟩
        refine hc ⟨?_, ?_, ?_⟩
        · simpa using h1
        · simpa using h2
        · simp only [Fin.val_succ] at h3; omega
      rw [if_neg hcond, if_neg hc]
  rw [h1, h2]; simp

end Work.TMC14Core
