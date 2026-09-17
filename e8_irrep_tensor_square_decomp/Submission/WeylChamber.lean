import Submission.WeylReflect
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posDef

/-!
# The dominant chamber of the `E₈` weight lattice

A weight `v : Fin 8 → ℤ` is written in the `ω`-basis (`v i = ⟨v, αᵢ∨⟩`); `Dominant v` means
`∀ i, 0 ≤ v i` (see `Submission.WeylReflect`).

The main result here is the *positivity* input for the uniqueness of the dominant element of a
Weyl-group orbit (and for the "leading term" arguments of the character theory):

  **if `m i ≥ 0` for all `i` and `m ≠ 0` then some `i` has `0 < ∑ k, A i k * m k`**,

i.e. a nonzero nonnegative vector is not annihilated (or made nonpositive) by the Cartan form.
This follows from the positive definiteness of the `E₈` Cartan matrix
(`Commons.LinearAlgebra.Matrix.Cartan.E8_posDef`), because
`∑ i, m i * (∑ k, A i k * m k) = m ⬝ A m > 0` and every term on the left is `≤ 0` if all the
`∑ k, A i k * m k` are.
-/

set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators

namespace Submission.WeylChamber

open Submission.WeylReflect Submission.WeylRoots

/-- A nonzero nonnegative integer vector is not in the "nonpositive half" of the Cartan form. -/
theorem exists_pos_cval {m : Fin 8 → ℤ} (hm : ∀ i, 0 ≤ m i) (hne : m ≠ 0) :
    ∃ i, 0 < cval i m := by
  by_contra hcon
  push_neg at hcon
  have hvec : (fun i => (m i : ℚ)) ≠ 0 := by
    intro h
    exact hne (funext fun i => by
      have := congrFun h i
      simpa using this)
  have hpos := Commons.LinearAlgebra.Matrix.Cartan.E8_posDef (fun i => (m i : ℚ)) hvec
  have hcast : ∀ i : Fin 8,
      (∑ j, (m i : ℚ) * (CartanMatrix.E₈ i j : ℚ) * (m j : ℚ))
        = (m i : ℚ) * ((cval i m : ℤ) : ℚ) := by
    intro i
    rw [cval, Int.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    push_cast
    ring
  rw [show (∑ i, ∑ j, (m i : ℚ) * (CartanMatrix.E₈ i j : ℚ) * (m j : ℚ))
      = ∑ i, (m i : ℚ) * ((cval i m : ℤ) : ℚ) by
    apply Finset.sum_congr rfl; intro i _
    exact hcast i] at hpos
  have hle : (∑ i, (m i : ℚ) * ((cval i m : ℤ) : ℚ)) ≤ 0 := by
    apply Finset.sum_nonpos; intro i _
    exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hm i) (by exact_mod_cast hcon i)
  linarith

/-- **The origin is the only nonpositive vector in the "dual" chamber.** -/
theorem eq_zero_of_forall_cval_nonpos {m : Fin 8 → ℤ} (hm : ∀ i, 0 ≤ m i)
    (hc : ∀ i, cval i m ≤ 0) : m = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := exists_pos_cval hm hne
  exact absurd (hc i) (not_le.mpr hi)

end Submission.WeylChamber
