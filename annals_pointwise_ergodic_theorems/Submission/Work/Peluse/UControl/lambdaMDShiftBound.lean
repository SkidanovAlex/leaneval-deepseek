import Mathlib
import Submission.Work.Peluse.UControl.PetStepChain

/-!
# The shift bound of the initial PET state

`LambdaMDPetState N M P F` is the state whose shifts are `y^j` (`1 ≤ j ≤ d-1`, `d = P.natDegree`)
and `P(y)`.  A PET step needs those shifts to be bounded by `D·N` on the range `|y| ≤ cM`
(`PetState.ShiftBound`), and the constant `D` enters the step condition
`γ' ≤ γ²/(20000(D+1))`, so its *value* matters.

The bound proved here is `D = ⌈(1 + Σ_k |coeff_k|)·c^d·A/γ⌉`: for `|z| ≤ cM`,
`|z^j| ≤ (cM)^d` and `|P(z)| ≤ (Σ_k |coeff_k|)(cM)^d`, and `(cM)^d = c^dM^d ≤ c^dAγ^{-1}N` by the
scale hypothesis `M^d ≤ Aγ^{-1}N`.  This is the origin of the constant `C ≈ A/γ` of
`NOTES_petChapter5_session12.md` §2 and hence of the window bookkeeping of the PET chain.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

open Work.Peluse.UControl.PetStep

noncomputable section

/-- The elementary bound on the evaluation of an integer polynomial: for `B ≥ 1` and `|z| ≤ B`,
`|P(z)| ≤ (Σ_k |coeff_k|)·B^{natDegree P}`. -/
lemma abs_eval_le_of_le (P : Polynomial ℤ) (z B : ℤ) (hB : 1 ≤ B) (hz : |z| ≤ B) :
    |P.eval z| ≤ ((P.support.sum (fun k => (P.coeff k).natAbs) : ℕ) : ℤ) * B ^ P.natDegree := by
  rw [Polynomial.eval_eq_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have h2 : ∀ k ∈ P.support, |P.coeff k * z ^ k|
      ≤ ((P.coeff k).natAbs : ℤ) * B ^ P.natDegree := by
    intro k hk
    have hk' : k ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp k hk
    have hzpow : |z ^ k| ≤ B ^ P.natDegree := by
      rw [abs_pow]
      calc |z| ^ k ≤ B ^ k := pow_le_pow_left₀ (abs_nonneg z) hz k
        _ ≤ B ^ P.natDegree := pow_le_pow_right₀ hB hk'
    rw [abs_mul, ← Int.natCast_natAbs]
    exact mul_le_mul_of_nonneg_left hzpow (by positivity)
  refine le_trans (Finset.sum_le_sum h2) ?_
  rw [← Finset.sum_mul]
  gcongr
  push_cast
  rfl

theorem lambdaMDShiftBound (N M : ℕ) (P : Polynomial ℤ) (F : Fin (P.natDegree + 1) → ℤ → ℂ)
    (c : ℕ) (A γ : ℝ) (hN : 0 < N) (hM : 0 < M) (hA : 1 ≤ A) (hγ : 0 < γ) (hc : 1 ≤ c)
    (hscale : (M : ℝ) ^ P.natDegree ≤ A * γ⁻¹ * (N : ℝ)) :
    (LambdaMDPetState N M P F).ShiftBound N M c
      (Nat.ceil ((1 + (P.support.sum (fun k => (P.coeff k).natAbs) : ℕ) : ℝ)
        * (c : ℝ) ^ P.natDegree * (A / γ))) := by
  intro i a z hz
  have hc1 : (1 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc
  have hM1 : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hγ0 : (0 : ℝ) < γ := hγ
  set S : ℝ := ((P.support.sum (fun k => (P.coeff k).natAbs) : ℕ) : ℝ) with hSdef
  have hS0 : (0 : ℝ) ≤ S := by rw [hSdef]; positivity
  set X : ℝ := (1 + S) * (c : ℝ) ^ P.natDegree * (A / γ) with hXdef
  have hceil : X ≤ ((Nat.ceil X : ℕ) : ℝ) := Nat.le_ceil X
  have hD : X * (N : ℝ) ≤ ((Nat.ceil X : ℕ) : ℝ) * (N : ℝ) :=
    mul_le_mul_of_nonneg_right hceil (by positivity)
  have hK : (0 : ℝ) ≤ (c : ℝ) ^ P.natDegree * A * γ⁻¹ * (N : ℝ) := by positivity
  have hkey : (c : ℝ) ^ P.natDegree * (M : ℝ) ^ P.natDegree ≤ X * (N : ℝ) := by
    have h4 : A * γ⁻¹ ≤ (1 + S) * (A / γ) := by
      rw [div_eq_mul_inv]
      exact le_mul_of_one_le_left (mul_nonneg hA0 (inv_nonneg.mpr (le_of_lt hγ0))) (by linarith)
    have h5 : (c : ℝ) ^ P.natDegree * (A * γ⁻¹ * (N : ℝ))
        ≤ (c : ℝ) ^ P.natDegree * ((1 + S) * (A / γ) * (N : ℝ)) := by
      gcongr
    calc (c : ℝ) ^ P.natDegree * (M : ℝ) ^ P.natDegree
        ≤ (c : ℝ) ^ P.natDegree * (A * γ⁻¹ * (N : ℝ)) := by gcongr
      _ ≤ (c : ℝ) ^ P.natDegree * ((1 + S) * (A / γ) * (N : ℝ)) := h5
      _ = X * (N : ℝ) := by rw [hXdef]; ring
  have hkeyS : S * ((c : ℝ) ^ P.natDegree * (M : ℝ) ^ P.natDegree) ≤ X * (N : ℝ) := by
    have h2a : S * ((c : ℝ) ^ P.natDegree * (M : ℝ) ^ P.natDegree)
        ≤ S * ((c : ℝ) ^ P.natDegree * (A * γ⁻¹ * (N : ℝ))) := by
      gcongr
    have h2b : S * ((c : ℝ) ^ P.natDegree * (A * γ⁻¹ * (N : ℝ)))
        ≤ (1 + S) * ((c : ℝ) ^ P.natDegree * (A * γ⁻¹ * (N : ℝ))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2c : (1 + S) * ((c : ℝ) ^ P.natDegree * (A * γ⁻¹ * (N : ℝ))) = X * (N : ℝ) := by
      rw [hXdef, div_eq_mul_inv]; ring
    linarith [h2a, h2b, h2c]
  rcases i with i | i
  · have hQ : (LambdaMDPetState N M P F).Q (Sum.inl i) a z = z ^ (i.val + 1) := rfl
    rw [hQ, abs_pow]
    have hB1 : (1 : ℤ) ≤ (c : ℤ) * (M : ℤ) := by nlinarith
    have hik : i.val + 1 ≤ P.natDegree := by
      have := i.isLt
      omega
    have hle : |z| ^ (i.val + 1) ≤ ((c : ℤ) * (M : ℤ)) ^ P.natDegree :=
      le_trans (pow_le_pow_left₀ (abs_nonneg z) hz _) (pow_le_pow_right₀ hB1 hik)
    have hgoal : |z| ^ (i.val + 1) ≤ ((Nat.ceil X : ℕ) : ℤ) * (N : ℤ) := by
      have hleR : (((|z| ^ (i.val + 1) : ℤ)) : ℝ)
          ≤ (((((c : ℤ) * (M : ℤ)) ^ P.natDegree : ℤ)) : ℝ) := by exact_mod_cast hle
      have hkeyR : (((((c : ℤ) * (M : ℤ)) ^ P.natDegree : ℤ)) : ℝ)
          ≤ ((((Nat.ceil X : ℕ) : ℤ) * (N : ℤ) : ℤ) : ℝ) := by
        push_cast
        rw [mul_pow]
        exact le_trans hkey hD
      exact_mod_cast (le_trans hleR hkeyR)
    exact hgoal
  · have hQ : (LambdaMDPetState N M P F).Q (Sum.inr i) a z = P.eval z := rfl
    rw [hQ]
    have hB1 : (1 : ℤ) ≤ (c : ℤ) * (M : ℤ) := by nlinarith
    have h1 := abs_eval_le_of_le P z ((c : ℤ) * (M : ℤ)) hB1 hz
    have hsum : (∑ x ∈ P.support, |((P.coeff x : ℤ) : ℝ)|) = S := by
      rw [hSdef, Nat.cast_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      norm_num
    have hgoal : |P.eval z| ≤ ((Nat.ceil X : ℕ) : ℤ) * (N : ℤ) := by
      have h1R : (((|P.eval z| : ℤ)) : ℝ)
          ≤ (((((P.support.sum (fun k => (P.coeff k).natAbs) : ℕ) : ℤ)
              * ((c : ℤ) * (M : ℤ)) ^ P.natDegree : ℤ)) : ℝ) := by exact_mod_cast h1
      have hkeyR : (((((P.support.sum (fun k => (P.coeff k).natAbs) : ℕ) : ℤ)
              * ((c : ℤ) * (M : ℤ)) ^ P.natDegree : ℤ)) : ℝ)
          ≤ ((((Nat.ceil X : ℕ) : ℤ) * (N : ℤ) : ℤ) : ℝ) := by
        push_cast
        rw [hsum, mul_pow]
        exact le_trans hkeyS hD
      exact_mod_cast (le_trans h1R hkeyR)
    exact hgoal

end

end Work.Peluse.UControl
