import Mathlib
import Submission.Work.HP.Defs

/-!
# Counting primitive integer vectors in a ball: the coordinate box

This file sets up the elementary counting device used to lower-bound
`#{x : Fin m → ℤ | IsPrim x ∧ eNorm x ≤ X}` by `c * X^m`.

The idea: the primitive vectors in the coordinate box `[-N,N]^m ⊆ ℝ^m` (which
is contained in the Euclidean ball of radius `N√m`) are all but those whose
coordinates share a common divisor `d ≥ 2`; a union bound over `d` gives
`#(prim in box) ≥ (2N+1)^m - ∑_{d=2}^N (2N/d + 1)^m`, and the right-hand side is
`≥ c_m N^m` for `N` large.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP

open Finset

/-- `IsPrim` is decidable, so that we may filter by it. -/
instance decidableIsPrim {ι : Type*} [Fintype ι] (v : ι → ℤ) : Decidable (IsPrim v) :=
  inferInstanceAs (Decidable (Finset.univ.gcd v = 1))

/-- The coordinate box `[-N,N]^m`, as a finset of integer vectors. -/
def boxFinset (N m : ℕ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset (fun _ : Fin m => Finset.Icc (-(N : ℤ)) N)

theorem mem_boxFinset {N m : ℕ} {x : Fin m → ℤ} :
    x ∈ boxFinset N m ↔ ∀ i, |x i| ≤ (N : ℤ) := by
  simp [boxFinset, Fintype.mem_piFinset, abs_le]

/-- Vectors of the box are `d`-divisible (coordinatewise) iff they are `d` times a
vector of the box scaled by `1/d`. -/
theorem card_boxFinset (N m : ℕ) : (boxFinset N m).card = (2 * N + 1) ^ m := by
  rw [boxFinset, Fintype.card_piFinset]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Int.card_Icc]
  omega

/-- Every coordinate of an integer vector is bounded by its Euclidean norm. -/
theorem abs_coord_le_eNorm {ι : Type*} [Fintype ι] (v : ι → ℤ) (i : ι) :
    |(v i : ℝ)| ≤ eNorm v := by
  have h1 : ((v i : ℝ)) ^ 2 ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ((v j : ℝ))) (Finset.mem_univ i)
  calc |(v i : ℝ)| = Real.sqrt (((v i : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, ((v j : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = eNorm v := rfl

/-- Vectors of the coordinate box `[-N,N]^m` have Euclidean norm at most `N √m`. -/
theorem eNorm_le_of_mem_boxFinset {m N : ℕ} {x : Fin m → ℤ} (hx : x ∈ boxFinset N m) :
    eNorm x ≤ (N : ℝ) * Real.sqrt m := by
  have hcoord : ∀ i, |(x i : ℝ)| ≤ (N : ℝ) := by
    intro i
    have h : |x i| ≤ (N : ℤ) := mem_boxFinset.mp hx i
    exact_mod_cast h
  have hsq : ∑ i, ((x i : ℝ)) ^ 2 ≤ (m : ℝ) * (N : ℝ) ^ 2 := by
    calc ∑ i, ((x i : ℝ)) ^ 2 ≤ ∑ _i : Fin m, (N : ℝ) ^ 2 :=
          Finset.sum_le_sum (fun i _ => by
            nlinarith [hcoord i, abs_nonneg ((x i : ℝ)), abs_nonneg (N : ℝ),
              sq_abs ((x i : ℝ))])
      _ = (m : ℝ) * (N : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc eNorm x = Real.sqrt (∑ i, ((x i : ℝ)) ^ 2) := rfl
    _ ≤ Real.sqrt ((m : ℝ) * (N : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (N : ℝ) * Real.sqrt m := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_comm]

end Work.HP
