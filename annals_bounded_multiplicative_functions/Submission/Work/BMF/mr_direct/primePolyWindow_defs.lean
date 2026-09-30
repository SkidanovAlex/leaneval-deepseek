import Mathlib
import Submission.Work.BMF.mr_direct.primePoly_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the *window* version of the prime Dirichlet polynomial large-values bound

The file `Work.BMF.mr_direct.primePoly_large_values` treats the dyadic interval
`[P, 2P]`.  The version needed for the short-interval mean value theorem uses a general
window `[A, B]` with `A ≤ B ≤ 4A`; the definitions here are the exact analogues of
`primePoly.primeSet`, `primePoly.primeDirPoly` and `primePoly.powCoeff` with the dyadic
interval replaced by `[⌈A⌉₊, ⌊B⌋₊]`.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct.primePolyWindow

open Finset
open scoped BigOperators

/-- The set of primes in the window `[⌈A⌉₊, ⌊B⌋₊]`. -/
noncomputable def winSet (A B : ℝ) : Finset ℕ := (Finset.Icc ⌈A⌉₊ ⌊B⌋₊).filter Nat.Prime

/-- The prime-supported Dirichlet polynomial `Σ_{p ∈ winSet A B} c p · p^{-(1+it)}`. -/
noncomputable def winDirPoly (c : ℕ → ℂ) (A B t : ℝ) : ℂ :=
  ∑ p ∈ winSet A B, c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))

/-- `winPowCoeff c A B k n` is the coefficient of `n^{-it}` in the `k`-th power of
`winDirPoly c A B`: the sum, over all `k`-tuples `f` of primes in `winSet A B` with
`∏ j, f j = n`, of `∏ j, c (f j) / (f j)`. -/
noncomputable def winPowCoeff (c : ℕ → ℂ) (A B : ℝ) (k n : ℕ) : ℂ :=
  ∑ f ∈ (Fintype.piFinset (fun _ : Fin k => winSet A B)).filter (fun f => ∏ j, f j = n),
    ∏ j, (c (f j) * ((f j : ℂ))⁻¹)

/-- Membership in `winSet A B`, unfolded. -/
lemma mem_winSet {A B : ℝ} {m : ℕ} (hm : m ∈ winSet A B) :
    Nat.Prime m ∧ ⌈A⌉₊ ≤ m ∧ m ≤ ⌊B⌋₊ := by
  rw [winSet, Finset.mem_filter] at hm
  exact ⟨hm.2, (Finset.mem_Icc.mp hm.1).1, (Finset.mem_Icc.mp hm.1).2⟩

/-- `winDirPoly` written with the `c`-coefficient and the factor `p^{-1}` combined, ready
for `primePoly.sum_pow_expand`. -/
lemma winDirPoly_eq_powForm (c : ℕ → ℂ) (A B t : ℝ) :
    winDirPoly c A B t
      = ∑ p ∈ winSet A B, (c p * (p : ℂ)⁻¹) * (p : ℂ) ^ (-(Complex.I * (t : ℂ))) := by
  rw [winDirPoly]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  rw [show -(1 + Complex.I * (t : ℂ)) = -1 + (-(Complex.I * (t : ℂ))) by ring,
    Complex.cpow_add _ _ hp0, Complex.cpow_neg_one]
  ring

end Work.BMF.mr_direct.primePolyWindow
