import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.MvPolynomial

/-- A nonzero multivariate polynomial over a characteristic-zero field of total degree at most `T`
does not vanish on the whole grid `{0, 1, ..., T}^n`. -/
theorem exists_eval_ne_zero_of_totalDegree_le {F : Type*} [Field F] [CharZero F] {n T : ℕ}
    (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) (hdeg : p.totalDegree ≤ T) :
    ∃ u : Fin n → ℕ, (∀ i, u i ≤ T) ∧ MvPolynomial.eval (fun i : Fin n => (u i : F)) p ≠ 0 := by
  classical
  by_contra h
  -- `h : ¬ ∃ u, (∀ i, u i ≤ T) ∧ eval (fun i => (u i : F)) p ≠ 0`
  let S : Finset F := (Finset.range (T + 1)).image (fun i : ℕ => (i : F))
  have hS_card : S.card = T + 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ (f := fun i : ℕ => (i : F)) Nat.cast_injective]
    simp
  have hdegOf : ∀ i : Fin n, p.degreeOf i < S.card := by
    intro i
    rw [hS_card]
    exact lt_of_le_of_lt (MvPolynomial.degreeOf_le_totalDegree p i) (Nat.lt_succ_of_le hdeg)
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
      exact Nat.le_of_lt_succ ((Finset.mem_range.mp (hu_mem i).1))
    have hx_eq : (fun i : Fin n => (u i : F)) = x := by
      funext i
      exact (hu_mem i).2
    have hz' : MvPolynomial.eval (fun i : Fin n => (u i : F)) p ≠ 0 := by
      rwa [hx_eq]
    exact h ⟨u, hu_le, hz'⟩
  have hp0 : p = 0 :=
    MvPolynomial.eq_zero_of_eval_zero_at_prod_finset p (fun _ : Fin n => S) hdegOf heval
  exact hp hp0

end Commons.Algebra.MvPolynomial