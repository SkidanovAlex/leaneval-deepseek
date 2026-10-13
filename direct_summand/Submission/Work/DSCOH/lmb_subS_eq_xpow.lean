import Mathlib
import Submission.Work.DSCOH.LocBasisDefs

namespace Work.DSCOH

open MvPolynomial

/-- Every element of `Poly A n` lying in the submonoid `subS S` is a monomial `xpow e` with
`e` supported in `S`. -/
lemma exists_xpow_of_mem_subS {A : Type*} [CommRing A] {n : ℕ} {S : Finset (Fin n)}
    {p : Poly A n} (hp : p ∈ subS (A := A) S) :
    ∃ e : Fin n → ℕ, (∀ i, i ∉ S → e i = 0) ∧ p = xpow (A := A) e := by
  refine Submonoid.closure_induction (motive := fun p _ =>
      ∃ e : Fin n → ℕ, (∀ i, i ∉ S → e i = 0) ∧ p = xpow (A := A) e) ?_ ?_ ?_ hp
  · rintro x ⟨i, hi, rfl⟩
    refine ⟨fun j => if j = i then (1 : ℕ) else 0, ?_, ?_⟩
    · intro j hj
      by_cases hji : j = i
      · exact absurd (hji ▸ hi) hj
      · simp [hji]
    · exact (xpow_single (A := A) (n := n) i).symm
  · exact ⟨fun _ => 0, fun i _ => rfl, by rw [xpow_zero]⟩
  · rintro x y _ _ ⟨e₁, h₁, rfl⟩ ⟨e₂, h₂, rfl⟩
    refine ⟨e₁ + e₂, ?_, ?_⟩
    · intro i hi
      simp [h₁ i hi, h₂ i hi]
    · rw [xpow_add]

theorem lmb_subS_eq_xpow {A : Type*} [CommRing A] {n : ℕ} (S : Finset (Fin n))
    (u : subS (A := A) S) :
    ∃ e : Fin n → ℕ, (∀ i, i ∉ S → e i = 0) ∧ (u : Poly A n) = xpow (A := A) e := by
  obtain ⟨e, h₁, h₂⟩ := exists_xpow_of_mem_subS (A := A) (n := n) (S := S) u.2
  exact ⟨e, h₁, h₂⟩

end Work.DSCOH
