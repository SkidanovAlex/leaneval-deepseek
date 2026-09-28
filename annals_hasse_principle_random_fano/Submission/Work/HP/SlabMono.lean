import Mathlib
import Submission.Work.HP.SlabDefs

/-!
# The monomial computations for the slab bound

The special monomials `smon d n hd i j` are the monomials `x_i^d` (for `j = i`) and
`x_i^{d-1}x_j` (for `j ≠ i`).  This file computes their Veronese coordinates and the entries
`gradKer d n x j (smon d n hd i k)` of the "peeling matrix", and shows that the `n+1` special
monomials are distinct.
-/

set_option autoImplicit false

noncomputable section

open Finset MvPolynomial

namespace Work.HP

/-- The index map underlying `spm`: `0 ↦ i`, `k + 1 ↦ i.succAbove k`. -/
def kappa {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) → Fin (n + 1) :=
  Fin.cases i (fun k => i.succAbove k)

theorem spm_apply (d n : ℕ) (hd : 1 ≤ d) (i k : Fin (n + 1)) :
    spm d n hd i k = smon d n hd i (kappa i k) := by
  induction k using Fin.cases with
  | zero => rfl
  | succ k => rfl

theorem kappa_injective {n : ℕ} (i : Fin (n + 1)) : Function.Injective (kappa i) := by
  intro a b hab
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => rfl
    | succ b => exact absurd (show i = i.succAbove b from hab) (Fin.succAbove_ne i b).symm
  | succ a =>
    induction b using Fin.cases with
    | zero => exact absurd (show i.succAbove a = i from hab) (Fin.succAbove_ne i a)
    | succ b => exact congrArg Fin.succ (Fin.succAbove_right_injective hab)

theorem smon_self_exp (d n : ℕ) (hd : 1 ≤ d) (i k : Fin (n + 1)) :
    ((smon d n hd i i).1 k : ℕ) = if k = i then d else 0 := by
  by_cases hk : k = i
  · subst hk; simp [smon]
  · simp [smon, hk]

theorem smon_ne_exp (d n : ℕ) (hd : 1 ≤ d) (i j k : Fin (n + 1)) (hji : j ≠ i) :
    ((smon d n hd i j).1 k : ℕ) = (if k = i then d - 1 else 0) + (if k = j then 1 else 0) := by
  by_cases hk1 : k = i
  · subst hk1; simp [smon, hji, Ne.symm hji]
  · by_cases hk2 : k = j
    · subst hk2; simp [smon, hk1]
    · simp [smon, hk1, hk2]

theorem veronese_smon_self (d n : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    veronese d n x (smon d n hd i i) = x i ^ d := by
  simp only [veronese]
  rw [Finset.prod_eq_single i]
  · rw [smon_self_exp, if_pos rfl]
  · intro b _ hb; rw [smon_self_exp, if_neg hb, pow_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem gradKer_smon_self (d n : ℕ) (hd : 1 ≤ d) (i j : Fin (n + 1)) (hji : j ≠ i)
    (x : Fin (n + 1) → ℝ) : gradKer d n x j (smon d n hd i i) = 0 := by
  simp only [gradKer, smon_self_exp, if_neg hji]
  simp

theorem gradKer_smon_eq (d n : ℕ) (hd : 1 ≤ d) (i j : Fin (n + 1)) (hji : j ≠ i)
    (x : Fin (n + 1) → ℝ) : gradKer d n x j (smon d n hd i j) = x i ^ (d - 1) := by
  have hj : ((smon d n hd i j).1 j : ℕ) = 1 := by
    rw [smon_ne_exp d n hd i j j hji, if_neg hji, if_pos rfl, Nat.zero_add]
  have hprod : (∏ l ∈ Finset.univ.erase j, x l ^ ((smon d n hd i j).1 l : ℕ))
      = x i ^ (d - 1) := by
    have h1 : ∀ l ∈ Finset.univ.erase j,
        ((smon d n hd i j).1 l : ℕ) = (if l = i then d - 1 else 0) := by
      intro l hl
      have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
      rw [smon_ne_exp d n hd i j l hji, if_neg hlj, add_zero]
    rw [Finset.prod_congr rfl (fun l hl => by rw [h1 l hl])]
    rw [Finset.prod_eq_single i]
    · rw [if_pos rfl]
    · intro b _ hbi; rw [if_neg hbi, pow_zero]
    · intro h
      exact absurd (Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩) h
  simp only [gradKer, hj, hprod]
  simp

theorem gradKer_smon_ne (d n : ℕ) (hd : 1 ≤ d) (i j k : Fin (n + 1)) (hji : j ≠ i)
    (hkj : k ≠ j) (x : Fin (n + 1) → ℝ) : gradKer d n x j (smon d n hd i k) = 0 := by
  have h : ((smon d n hd i k).1 j : ℕ) = 0 := by
    rcases eq_or_ne k i with hki | hki
    · rw [hki, smon_self_exp, if_neg hji]
    · rw [smon_ne_exp d n hd i k j hki, if_neg hji, if_neg (Ne.symm hkj), add_zero]
  simp only [gradKer, h]
  simp

theorem smon_injective (d n : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) :
    Function.Injective (smon d n hd i) := by
  intro a b hab
  by_cases hai : a = i
  · by_cases hbi : b = i
    · rw [hai, hbi]
    · exfalso
      have h1 : ((smon d n hd i i).1 b : ℕ) = 0 := by
        rw [smon_self_exp, if_neg hbi]
      have h2 : ((smon d n hd i b).1 b : ℕ) = 1 := by
        rw [smon_ne_exp d n hd i b b hbi, if_neg hbi, if_pos rfl, Nat.zero_add]
      have h := congrArg (fun m : Mon d n => ((m.1 b : ℕ))) hab
      rw [hai] at h
      rw [h1, h2] at h
      exact absurd h Nat.zero_ne_one
  · by_cases hbi : b = i
    · exfalso
      have h1 : ((smon d n hd i a).1 a : ℕ) = 1 := by
        rw [smon_ne_exp d n hd i a a hai, if_neg hai, if_pos rfl, Nat.zero_add]
      have h2 : ((smon d n hd i i).1 a : ℕ) = 0 := by
        rw [smon_self_exp, if_neg hai]
      have h := congrArg (fun m : Mon d n => ((m.1 a : ℕ))) hab
      rw [hbi] at h
      rw [h1, h2] at h
      exact absurd h Nat.one_ne_zero
    · have h1 : ((smon d n hd i a).1 a : ℕ) = 1 := by
        rw [smon_ne_exp d n hd i a a hai, if_neg hai, if_pos rfl, Nat.zero_add]
      have h2 : ((smon d n hd i b).1 a : ℕ) = if a = b then 1 else 0 := by
        rw [smon_ne_exp d n hd i b a hbi, if_neg hai, Nat.zero_add]
      have h := congrArg (fun m : Mon d n => ((m.1 a : ℕ))) hab
      rw [h1, h2] at h
      by_cases hab' : a = b
      · exact hab'
      · rw [if_neg hab'] at h
        exact absurd h Nat.one_ne_zero

theorem spm_injective (d n : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) :
    Function.Injective (spm d n hd i) := by
  intro a b hab
  have h : smon d n hd i (kappa i a) = smon d n hd i (kappa i b) := by
    rw [← spm_apply d n hd i a, ← spm_apply d n hd i b]
    exact hab
  exact kappa_injective i (smon_injective d n hd i h)

end Work.HP
