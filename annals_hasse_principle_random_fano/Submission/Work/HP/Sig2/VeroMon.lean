import Mathlib
import Submission.Work.HP.Defs

/-!
# Monomial probes for the Veronese map

`Work.HP.veronese d n x : Mon d n → R` is the vector of all degree-`d` monomials
evaluated at `x`.  This file provides the two standard monomials that read off
the coordinates of `x` from `veronese d n x`:

* `diagMon d n i`     : the exponent vector `d · e_i`, with `veronese`-value `x i ^ d`;
* `pairMon d n i j`   : the exponent vector `(d-1)·e_i + e_j` (`i ≠ j`, `d ≥ 1`),
  with `veronese`-value `x i ^ (d-1) * x j`.

They are the probes used to prove that `ν_{d,n}` is injective on rays
(`Work.HP.Sig2.veronese_proportional`), hence at the heart of
`Work.HP.Sig2.nu_indep`.
-/

set_option autoImplicit false
noncomputable section

open Finset MvPolynomial

namespace Work.HP

/-- Build an element of `Mon d n` from a natural-valued exponent vector of total degree `d`. -/
def monOfNat (d n : ℕ) (m : Fin (n + 1) → ℕ) (hm : ∑ i, m i = d) : Mon d n :=
  ⟨fun i => ⟨m i, by
      have h := Finset.single_le_sum (fun i _ => Nat.zero_le (m i)) (Finset.mem_univ i)
      omega⟩, hm⟩

@[simp] theorem monOfNat_apply (d n : ℕ) (m : Fin (n + 1) → ℕ) (hm : ∑ i, m i = d)
    (i : Fin (n + 1)) : ((monOfNat d n m hm).1 i : ℕ) = m i := rfl

@[simp] theorem veronese_monOfNat {R : Type*} [CommSemiring R] (d n : ℕ)
    (m : Fin (n + 1) → ℕ) (hm : ∑ i, m i = d) (x : Fin (n + 1) → R) :
    veronese d n x (monOfNat d n m hm) = ∏ i, x i ^ (m i) := rfl

/-- The exponent vector `d · e_i`. -/
def diagMon (d n : ℕ) (i0 : Fin (n + 1)) : Mon d n :=
  monOfNat d n (Function.update (0 : Fin (n + 1) → ℕ) i0 d) (by
    have h : (∑ i, Function.update (0 : Fin (n + 1) → ℕ) i0 d i)
              = Function.update (0 : Fin (n + 1) → ℕ) i0 d i0 :=
      Finset.sum_eq_single i0 (fun b _ hb => by simp [Function.update_of_ne hb])
        (fun h => absurd (Finset.mem_univ i0) h)
    rw [h, Function.update_self])

theorem veronese_diag {R : Type*} [CommSemiring R] (d n : ℕ) (i0 : Fin (n + 1))
    (x : Fin (n + 1) → R) :
    veronese d n x (diagMon d n i0) = x i0 ^ d := by
  unfold diagMon
  rw [veronese_monOfNat]
  have h : ∏ k, x k ^ (Function.update (0 : Fin (n + 1) → ℕ) i0 d k)
      = ∏ k, (if k = i0 then x i0 ^ d else 1) := by
    apply Finset.prod_congr rfl
    intro k _
    by_cases hk : k = i0
    · subst hk; simp
    · simp [hk]
  rw [h, Finset.prod_ite_eq']
  simp

/-- The exponent vector `(d-1)·e_i + e_j`, for `i ≠ j` and `d ≥ 1`. -/
def pairMon (d n : ℕ) (i j : Fin (n + 1)) (hij : i ≠ j) (hd : 1 ≤ d) : Mon d n :=
  monOfNat d n (Function.update (Function.update (0 : Fin (n + 1) → ℕ) i (d - 1)) j 1) (by
    have hsum : (∑ k, Function.update (Function.update (0 : Fin (n + 1) → ℕ) i (d - 1)) j 1 k)
        = Function.update (Function.update (0 : Fin (n + 1) → ℕ) i (d - 1)) j 1 i
          + ∑ k ∈ Finset.univ.erase i,
              Function.update (Function.update (0 : Fin (n + 1) → ℕ) i (d - 1)) j 1 k :=
      (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)).symm
    rw [hsum]
    have hi : Function.update (Function.update (0 : Fin (n + 1) → ℕ) i (d - 1)) j 1 i = d - 1 := by
      rw [Function.update_of_ne hij, Function.update_self]
    have hrest : (∑ k ∈ Finset.univ.erase i,
        Function.update (Function.update (0 : Fin (n + 1) → ℕ) i (d - 1)) j 1 k) = 1 := by
      have hc : ∀ k ∈ Finset.univ.erase i,
          Function.update (Function.update (0 : Fin (n + 1) → ℕ) i (d - 1)) j 1 k
            = (if k = j then 1 else 0) := by
        intro k hk
        rw [Finset.mem_erase] at hk
        by_cases hkj : k = j
        · subst hkj; simp [Function.update_self]
        · simp [Function.update_of_ne hk.1, hkj]
      rw [Finset.sum_congr rfl hc, Finset.sum_ite_eq']
      rw [if_pos (Finset.mem_erase.mpr ⟨fun h => hij h.symm, Finset.mem_univ j⟩)]
    rw [hi, hrest]
    omega)

theorem veronese_pair {R : Type*} [CommSemiring R] (d n : ℕ) (i j : Fin (n + 1)) (hij : i ≠ j)
    (hd : 1 ≤ d) (x : Fin (n + 1) → R) :
    veronese d n x (pairMon d n i j hij hd) = x i ^ (d - 1) * x j := by
  unfold pairMon
  rw [veronese_monOfNat]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun k => x k ^ (Function.update (Function.update (0 : Fin (n + 1) → ℕ) i (d - 1)) j 1 k))
    (Finset.mem_univ i)]
  have hi : Function.update (Function.update (0 : Fin (n + 1) → ℕ) i (d - 1)) j 1 i = d - 1 := by
    rw [Function.update_of_ne hij, Function.update_self]
  have hrest : ∏ k ∈ Finset.univ.erase i,
      x k ^ (Function.update (Function.update (0 : Fin (n + 1) → ℕ) i (d - 1)) j 1 k) = x j := by
    have hc : ∀ k ∈ Finset.univ.erase i,
        x k ^ (Function.update (Function.update (0 : Fin (n + 1) → ℕ) i (d - 1)) j 1 k)
          = (if k = j then x j else 1) := by
      intro k hk
      rw [Finset.mem_erase] at hk
      by_cases hkj : k = j
      · subst hkj; simp [Function.update_self]
      · simp [Function.update_of_ne hk.1, hkj]
    rw [Finset.prod_congr rfl hc, Finset.prod_ite_eq']
    rw [if_pos (Finset.mem_erase.mpr ⟨fun h => hij h.symm, Finset.mem_univ j⟩)]
  rw [hi, hrest]

/-- The Veronese map does not vanish on a nonzero vector. -/
theorem veronese_ne_zero {R : Type*} [CommSemiring R] [NoZeroDivisors R] (d n : ℕ) (hd : 1 ≤ d)
    {x : Fin (n + 1) → R} (hx : x ≠ 0) : veronese d n x ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hh := congrFun h (diagMon d n i)
  rw [veronese_diag, Pi.zero_apply] at hh
  exact pow_ne_zero d hi hh

/-- `ν_{d,n}` commutes with the coercion `ℤ → ℚ`. -/
theorem veronese_intCast (d n : ℕ) (x : Fin (n + 1) → ℤ) (m : Mon d n) :
    veronese d n (fun i => (x i : ℚ)) m = ((veronese d n x m : ℤ) : ℚ) := by
  simp only [veronese]
  rw [Int.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Int.cast_pow]

end Work.HP
