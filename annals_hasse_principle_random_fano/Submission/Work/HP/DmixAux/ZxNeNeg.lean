import Mathlib
import Submission.Work.HP.MMReindex

/-!
# `Zx` contains no non-zero vector equal to its own negative

`Zx d n a B` is the set of *primitive* integer vectors `x` of height `≤ B` with
`f_a(x) = 0`.  Since `IsPrim x` forces `x ≠ 0` (the zero vector has coordinate gcd `0`,
not `1`), while `x = -x` forces `x = 0`, such a vector can never equal its own negative.

This is used to make the diagonal `x = y` and the anti-diagonal `x = -y` of the pair
count `Ω_{d,n}(B)` disjoint from one another.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP.DmixAux

/-- A vector satisfying `x = -x` is the zero vector. -/
private lemma eq_zero_of_eq_neg_self {ι : Type*} {x : ι → ℤ} (h : x = -x) : x = 0 := by
  funext i
  have hi : x i = -x i := by
    have := congr_fun h i
    simpa using this
  have h2 : (2 : ℤ) * x i = 0 := by linarith
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- The zero vector is not primitive. -/
private lemma not_isPrim_zero (n : ℕ) : ¬ IsPrim (0 : Fin (n + 1) → ℤ) := by
  intro h
  simp only [IsPrim] at h
  have h0 : Finset.univ.gcd (0 : Fin (n + 1) → ℤ) = 0 :=
    Finset.gcd_eq_zero_iff.mpr (by simp)
  rw [h0] at h
  exact zero_ne_one h

/-- No primitive integer vector equals its own negative. -/
theorem ZxNeNeg (d n : ℕ) [DecidableEq (Mon d n)] (a : Mon d n → ℤ) (B : ℝ)
    {x : Fin (n + 1) → ℤ} (hx : x ∈ Zx d n a B) : x ≠ -x := by
  intro h
  have hprim : IsPrim x := by
    have h1 : x ∈ Xi d n B := hx.1
    simp only [Xi, Set.mem_ofPred_eq] at h1
    exact h1.1
  rw [eq_zero_of_eq_neg_self h] at hprim
  exact not_isPrim_zero n hprim

end Work.HP.DmixAux
