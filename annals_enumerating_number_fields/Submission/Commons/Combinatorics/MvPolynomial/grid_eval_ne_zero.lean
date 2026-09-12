import Mathlib.Combinatorics.Nullstellensatz

/-!
# A nonzero polynomial in `n` variables of total degree `≤ T` is nonzero somewhere on the grid

If `p : MvPolynomial (Fin n) F` is a nonzero polynomial over a field `F` of characteristic zero
and `p.totalDegree ≤ T`, then there is a point `u : Fin n → ℕ` with `u i ≤ T` for all `i` at
which `p` does not vanish.  Equivalently, a nonzero polynomial of total degree `≤ T` cannot
vanish on the whole grid `{0, 1, …, T}^n`.

This is the "grid" form of the combinatorial Nullstellensatz: the evaluation map from
polynomials of total degree `≤ T` to functions on `{0, 1, …, T}^n` is injective.
-/

namespace Commons.Combinatorics.MvPolynomial

/-- A nonzero multivariate polynomial over a characteristic-zero field of total degree at most `T`
does not vanish on the whole grid `{0, 1, ..., T}^n`. -/
theorem grid_eval_ne_zero {F : Type*} [Field F] [CharZero F] {n T : ℕ}
    (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) (hdeg : p.totalDegree ≤ T) :
    ∃ u : Fin n → ℕ, (∀ i, u i ≤ T) ∧ MvPolynomial.eval (fun i => (u i : F)) p ≠ 0 := by
  classical
  by_contra h
  -- `S` is the grid `{0, 1, ..., T}` viewed as a finite subset of `F`.
  let S : Finset F := (Finset.range (T + 1)).image (fun i : ℕ => (i : F))
  have hS_card : S.card = T + 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ (f := fun i : ℕ => (i : F)) Nat.cast_injective]
    simp
  -- The degree of `p` in every single variable is `< T + 1 = #S`.
  have hdegOf : ∀ i : Fin n, p.degreeOf i < S.card := by
    intro i
    rw [hS_card]
    exact lt_of_le_of_lt (MvPolynomial.degreeOf_le_totalDegree p i) (Nat.lt_succ_of_le hdeg)
  -- `p` vanishes at every grid point whose coordinates lie in `S`.
  have heval : ∀ (x : Fin n → F), (∀ i, x i ∈ S) → MvPolynomial.eval x p = 0 := by
    intro x hxmem
    by_contra hz
    have hmem (i : Fin n) : ∃ a : ℕ, a ∈ Finset.range (T + 1) ∧ (a : F) = x i := by
      exact Finset.mem_image.mp (by simpa [S] using hxmem i)
    let u : Fin n → ℕ := fun i => Classical.choose (hmem i)
    have hu_mem (i : Fin n) : u i ∈ Finset.range (T + 1) ∧ (u i : F) = x i :=
      Classical.choose_spec (hmem i)
    have hu_le : ∀ i : Fin n, u i ≤ T := by
      intro i
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (hu_mem i).1)
    have hx_eq : (fun i : Fin n => (u i : F)) = x := by
      funext i
      exact (hu_mem i).2
    have hz' : MvPolynomial.eval (fun i : Fin n => (u i : F)) p ≠ 0 := by
      rwa [hx_eq]
    exact h ⟨u, hu_le, hz'⟩
  have hp0 : p = 0 :=
    MvPolynomial.eq_zero_of_eval_zero_at_prod_finset p (fun _ : Fin n => S) hdegOf heval
  exact hp hp0

end Commons.Combinatorics.MvPolynomial
