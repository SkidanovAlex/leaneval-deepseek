import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.NA.VeroAux

/-!
# The bilinear form `σ` of Browning–Le Boudec–Sawin and the row maps `rᵢ`

For `n : ℕ` and `u v : Fin (n+1) → ℤ` we define `sigma n u v : Mon 2 n → ℤ`, the coefficient
vector of the quadratic form `t ↦ ⟨t,u⟩⟨t,v⟩`, by the formula

`sigma n u v m = ∑ i, ∑ j, if m = pairMon n i j then u i * v j else 0`

where `pairMon n i j` is the exponent vector of the monomial `XᵢXⱼ` (which is `Xᵢ²` when `i = j`).
This is the paper's `σ`, and the basic identity is

`∑ m, veronese 2 n z m * sigma n u v m = (∑ i, z i * u i) * (∑ j, z j * v j)`.

The row map `rowVec n i c` of `c : Mon 2 n → ℤ` is the vector with coordinates
`(rowVec n i c) j = c (pairMon n i j)`; it satisfies `rowVec n i (veronese 2 n x) = x i • x` and the
pairing identity `∑ m, sigma n (Pi.single i 1) v m * c m = ∑ j, rowVec n i c j * v j`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Vero

open Work.HP

/-- The exponent vector of the monomial `XᵢXⱼ` (`Xᵢ²` when `i = j`), as an element of `Mon 2 n`.
It is `monDij 2 n i j` of `HP/NA/VeroAux`, which in degree two is `eᵢ + eⱼ`. -/
def pairMon (n : ℕ) (i j : Fin (n + 1)) : Mon 2 n :=
  Work.HP.NA.monDij 2 n (by norm_num) i j

/-- The Veronese coordinate of `pairMon n i j` is the product `z i * z j`. -/
lemma veronese_pairMon (n : ℕ) (z : Fin (n + 1) → ℤ) (i j : Fin (n + 1)) :
    veronese 2 n z (pairMon n i j) = z i * z j := by
  rw [pairMon, Work.HP.NA.veronese_monDij]
  norm_num

/-- The paper's `σ`: the coefficient vector of the quadratic form `t ↦ ⟨t,u⟩⟨t,v⟩`. -/
def sigma (n : ℕ) (u v : Fin (n + 1) → ℤ) : Mon 2 n → ℤ :=
  fun m => ∑ i, ∑ j, if m = pairMon n i j then u i * v j else 0

/-- The `i`-th row map `rᵢ` of the paper. -/
def rowVec (n : ℕ) (i : Fin (n + 1)) (c : Mon 2 n → ℤ) : Fin (n + 1) → ℤ :=
  fun j => c (pairMon n i j)

@[simp] lemma rowVec_apply (n : ℕ) (i : Fin (n + 1)) (c : Mon 2 n → ℤ) (j : Fin (n + 1)) :
    rowVec n i c j = c (pairMon n i j) := rfl

lemma rowVec_add (n : ℕ) (i : Fin (n + 1)) (c d : Mon 2 n → ℤ) :
    rowVec n i (c + d) = rowVec n i c + rowVec n i d := by
  ext j; simp [rowVec]

lemma rowVec_smul (n : ℕ) (i : Fin (n + 1)) (a : ℤ) (c : Mon 2 n → ℤ) :
    rowVec n i (a • c) = a • rowVec n i c := by
  ext j; simp [rowVec]

lemma rowVec_neg (n : ℕ) (i : Fin (n + 1)) (c : Mon 2 n → ℤ) :
    rowVec n i (-c) = - rowVec n i c := by
  ext j; simp [rowVec]

/-- The key identity: pairing `σ u v` against a Veronese vector. -/
theorem dot_veronese_sigma (n : ℕ) (z u v : Fin (n + 1) → ℤ) :
    (∑ m : Mon 2 n, veronese 2 n z m * sigma n u v m)
      = (∑ i, z i * u i) * (∑ j, z j * v j) := by
  classical
  have h : ∀ m : Mon 2 n, veronese 2 n z m * sigma n u v m
      = ∑ i, ∑ j, (if m = pairMon n i j then (z i * u i) * (z j * v j) else 0) := by
    intro m
    rw [sigma]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hm : m = pairMon n i j
    · subst hm
      rw [if_pos rfl, if_pos rfl, veronese_pairMon]; ring
    · rw [if_neg hm, if_neg hm, mul_zero]
  rw [Finset.sum_congr rfl (fun m _ => h m), Finset.sum_comm]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (pairMon n i j) (fun _ => (z i * u i) * (z j * v j))]
  simp

/-- Pairing `σ (single i 1) v` against an arbitrary coefficient vector `c` is the pairing of the
row vector `rᵢ(c)` with `v`. -/
theorem dot_sigma_rowVec (n : ℕ) (i : Fin (n + 1)) (v : Fin (n + 1) → ℤ) (c : Mon 2 n → ℤ) :
    (∑ m : Mon 2 n, sigma n (Pi.single i 1) v m * c m)
      = ∑ j, rowVec n i c j * v j := by
  classical
  have hsig : ∀ m : Mon 2 n, sigma n (Pi.single i 1) v m
      = ∑ q, (if m = pairMon n i q then v q else 0) := by
    intro m
    rw [sigma]
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun q _ => ?_
      by_cases h : m = pairMon n i q
      · rw [if_pos h, if_pos h, Pi.single_eq_same, one_mul]
      · rw [if_neg h, if_neg h]
    · intro b _ hb
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [Pi.single_eq_of_ne hb]; simp
    · intro h; exact absurd (Finset.mem_univ i) h
  have h : ∀ m : Mon 2 n, sigma n (Pi.single i 1) v m * c m
      = ∑ q, (if m = pairMon n i q then c m * v q else 0) := by
    intro m
    rw [hsig m, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : m = pairMon n i q
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h, zero_mul]
  rw [Finset.sum_congr rfl (fun m _ => h m), Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (pairMon n i q) (fun m => c m * v q)]
  simp [rowVec]

/-- `rᵢ` of a Veronese vector is the vector `x i • x`. -/
theorem rowVec_veronese (n : ℕ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℤ) :
    rowVec n i (veronese 2 n x) = x i • x := by
  ext j
  rw [rowVec_apply, veronese_pairMon, Pi.smul_apply, smul_eq_mul, mul_comm]

end Work.HP.Vero
