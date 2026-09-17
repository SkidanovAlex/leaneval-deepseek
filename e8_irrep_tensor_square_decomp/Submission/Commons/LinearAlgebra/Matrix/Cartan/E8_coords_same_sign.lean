import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple

set_option linter.unusedVariables false

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan

/-!
# Coordinates of the `E₈` roots have constant sign

The `E₈` Cartan matrix `A = CartanMatrix.E₈` is invertible over `ℤ` (its determinant is `1`); write
`A⁻¹ = E8inv`.  For an integral vector `v : Fin 8 → ℤ` the quadratic form `v ⬝ A⁻¹ v` is the squared
length of the weight `v` written in the fundamental-weight (`ω`) coordinates, so the vectors with
`v ⬝ A⁻¹ v = 2` are precisely the roots of `E₈`.

We prove that for every such `v` the vector of coordinates `w = A⁻¹ v` — which are the coefficients
of `v` in the simple-root basis — has **all coordinates of the same sign**; equivalently, `v` is a
positive or a negative root.

The proof is a positive-definiteness argument.  Set `Q(x) = ½ (x ⬝ A x) ∈ ℤ`; explicitly
`Q(x) = ∑ xᵢ² - ∑_{edges} xᵢ xⱼ` because `A` has diagonal `2` and off-diagonal entries `0`/`-1`.
For integer `x ≠ 0` we have `Q(x) > 0` by positive definiteness (`E8_posDef`), hence `Q(x) ≥ 1`
(`Q` is integer valued).  Splitting `w = p - n` into its positive and negative parts `p, n ≥ 0`
(with disjoint supports) gives

`Q(w) = Q(p) + Q(n) + ∑_{edges} (pᵢ nⱼ + nᵢ pⱼ)`,

the last term being non-negative.  Since `w ⬝ A w = v ⬝ A⁻¹ v = 2`, we have `Q(w) = 1`, so at most
one of `p, n` can be non-zero, i.e. `w` has constant sign.
-/

/-- The "half form" `½ (x ⬝ A x)` of the `E₈` Cartan matrix, written as an explicit integer
expression in the coordinates of `x`.  By `E8sign_two_mul_T8` we have
`2 * E8sign_T8 x = ∑ i, ∑ j, x i * E₈ i j * x j`. -/
def E8sign_T8 (x : Fin 8 → ℤ) : ℤ :=
  x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2
    - (x 0 * x 2 + x 1 * x 3 + x 2 * x 3 + x 3 * x 4 + x 4 * x 5 + x 5 * x 6 + x 6 * x 7)

/-- The cross term appearing when the form `E8sign_T8` is split into positive and negative parts. -/
def E8sign_cross (p n : Fin 8 → ℤ) : ℤ :=
  p 0 * n 2 + n 0 * p 2 + p 1 * n 3 + n 1 * p 3 + p 2 * n 3 + n 2 * p 3 + p 3 * n 4 + n 3 * p 4
  + p 4 * n 5 + n 4 * p 5 + p 5 * n 6 + n 5 * p 6 + p 6 * n 7 + n 6 * p 7

lemma E8sign_two_mul_T8 (x : Fin 8 → ℤ) :
    2 * E8sign_T8 x = ∑ i, ∑ j, x i * CartanMatrix.E₈ i j * x j := by
  simp only [E8sign_T8, CartanMatrix.E₈, CartanMatrix.E_eight_eq, Fin.sum_univ_eight, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val]
  ring

/-- The same identity over `ℚ`. -/
lemma E8sign_two_mul_T8_cast (x : Fin 8 → ℤ) :
    (2 : ℚ) * (E8sign_T8 x : ℚ)
      = ∑ i, ∑ j, (x i : ℚ) * (CartanMatrix.E₈ i j : ℚ) * (x j : ℚ) := by
  simp only [E8sign_T8, CartanMatrix.E₈, CartanMatrix.E_eight_eq, Fin.sum_univ_eight, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val]
  push_cast
  ring

/-- Splitting a vector into its positive and negative parts: if `p i * n i = 0` for all `i` then
`E8sign_T8 (p - n) = E8sign_T8 p + E8sign_T8 n + E8sign_cross p n`. -/
lemma E8sign_T8_decomp (p n : Fin 8 → ℤ) (hpn : ∀ i, p i * n i = 0) :
    E8sign_T8 (fun i => p i - n i) = E8sign_T8 p + E8sign_T8 n + E8sign_cross p n := by
  simp only [E8sign_T8, E8sign_cross]
  nlinarith [hpn 0, hpn 1, hpn 2, hpn 3, hpn 4, hpn 5, hpn 6, hpn 7]

/-- Positive definiteness of the form: for a nonzero integral vector `p`, `1 ≤ E8sign_T8 p`. -/
lemma E8sign_T8_pos (p : Fin 8 → ℤ) (hp : p ≠ 0) : 1 ≤ E8sign_T8 p := by
  have hp' : (fun i => (p i : ℚ)) ≠ 0 := by
    intro hh
    apply hp
    funext i
    have := congr_fun hh i
    simp only [Pi.zero_apply] at this
    exact_mod_cast this
  have hq := E8_posDef (fun i => (p i : ℚ)) hp'
  rw [← E8sign_two_mul_T8_cast] at hq
  have h2 : (0 : ℚ) < (E8sign_T8 p : ℚ) := by linarith
  have h3 : (0 : ℤ) < E8sign_T8 p := by exact_mod_cast h2
  omega

/-- Every nonzero vector `v : Fin 8 → ℤ` of squared length `2` (for the form `v ⬝ A⁻¹ v`,
`A = CartanMatrix.E₈`) is a positive or a negative root: the coordinates of `A⁻¹ v` in the simple
root basis all have the same sign. -/
theorem E8_coords_same_sign (v : Fin 8 → ℤ) (h : v ≠ 0)
    (hq : (∑ i, ∑ j, v i * Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv i j * v j) = 2) :
    (∀ i, 0 ≤ ∑ j, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv i j * v j) ∨
      (∀ i, ∑ j, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv i j * v j ≤ 0) := by
  set w : Fin 8 → ℤ := fun i => ∑ j, E8NormTwo.E8inv i j * v j with hw_def
  change (∀ i, 0 ≤ w i) ∨ (∀ i, w i ≤ 0)
  have hmul : CartanMatrix.E₈ * E8NormTwo.E8inv = 1 := by
    rw [mul_eq_one_comm]
    exact E8NormTwo.E8inv_mul_E8
  have hAw : CartanMatrix.E₈.mulVec w = v := by
    have hwmv : w = E8NormTwo.E8inv.mulVec v := by
      rw [hw_def]
      funext i
      rw [Matrix.mulVec_apply_eq_sum]
    rw [hwmv, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  have hqw : ∑ i, ∑ j, w i * CartanMatrix.E₈ i j * w j = 2 := by
    have e1 : (∑ i, ∑ j, w i * CartanMatrix.E₈ i j * w j)
        = w ⬝ᵥ (CartanMatrix.E₈.mulVec w) := by
      simp only [dotProduct, Matrix.mulVec_apply_eq_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      ring
    have e2 : w ⬝ᵥ (CartanMatrix.E₈.mulVec w)
        = ∑ i, ∑ j, v i * E8NormTwo.E8inv i j * v j := by
      rw [hAw]
      simp only [dotProduct, hw_def]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      ring
    rw [e1, e2, hq]
  set p : Fin 8 → ℤ := fun i => max 0 (w i) with hp_def
  set n : Fin 8 → ℤ := fun i => max 0 (-(w i)) with hn_def
  have hp0 : ∀ i, 0 ≤ p i := fun i => le_max_left _ _
  have hn0 : ∀ i, 0 ≤ n i := fun i => le_max_left _ _
  have hpn : ∀ i, p i * n i = 0 := by
    intro i
    simp only [hp_def, hn_def]
    by_cases hle : w i ≤ 0
    · rw [max_eq_left hle, max_eq_right (by linarith : (0 : ℤ) ≤ -(w i))]
      ring
    · rw [max_eq_right (le_of_lt (not_le.mp hle)), max_eq_left (by linarith : -(w i) ≤ 0)]
      ring
  have hwpn : ∀ i, w i = p i - n i := by
    intro i
    simp only [hp_def, hn_def]
    by_cases hle : w i ≤ 0
    · rw [max_eq_left hle, max_eq_right (by linarith : (0 : ℤ) ≤ -(w i))]; ring
    · rw [max_eq_right (le_of_lt (not_le.mp hle)), max_eq_left (by linarith : -(w i) ≤ 0)]; ring
  have hTw : E8sign_T8 w = 1 := by
    have hh := E8sign_two_mul_T8 w
    rw [hqw] at hh
    omega
  have hdec : E8sign_T8 w = E8sign_T8 p + E8sign_T8 n + E8sign_cross p n := by
    rw [show w = (fun i => p i - n i) from funext hwpn]
    exact E8sign_T8_decomp p n hpn
  have hcross : 0 ≤ E8sign_cross p n := by
    simp only [E8sign_cross]
    nlinarith [hp0 0, hp0 1, hp0 2, hp0 3, hp0 4, hp0 5, hp0 6, hp0 7,
      hn0 0, hn0 1, hn0 2, hn0 3, hn0 4, hn0 5, hn0 6, hn0 7]
  by_cases hpz : p = 0
  · right
    intro i
    have hpi : p i = 0 := by rw [hpz]; rfl
    rw [hwpn i, hpi]
    simp only [zero_sub, neg_nonpos]
    exact hn0 i
  · left
    intro i
    have hTp : 1 ≤ E8sign_T8 p := E8sign_T8_pos p hpz
    have hTn_le : E8sign_T8 n ≤ 0 := by linarith [hdec, hcross, hTp, hTw]
    have hnz : n = 0 := by
      by_contra hnne
      have h1 := E8sign_T8_pos n hnne
      omega
    have hni : n i = 0 := by rw [hnz]; rfl
    rw [hwpn i, hni]
    simp only [sub_zero]
    exact hp0 i

end Commons.LinearAlgebra.Matrix.Cartan
