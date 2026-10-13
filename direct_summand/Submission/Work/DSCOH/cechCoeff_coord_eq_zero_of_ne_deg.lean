import Mathlib
import Submission.Work.DSCOH.coordToolkit
import Submission.Work.DSCOH.Cech

namespace Work.DSCOH

/-!
# Coordinates of a chart Čech cochain away from the degree `-d`

The degree-zero part `degZero (shift d) S` of the chart localization of the free shifted module
`S(-d)` is spanned, by hypothesis `hB3`, by the basis elements `B S β` whose Laurent exponent `β`
has total degree `-d` (this is the graded-module computation `Work.DSCOH.locAt_monomial_basis`).
Since `B S` is an `A`-basis, an element of that span has zero coordinate at every exponent that
does not occur among these spanning vectors — in particular at every exponent `β` with
`∑ i, β i ≠ -d`.

This is the elementary linear-algebra fact used wherever the chart coordinates of a degree-zero
element of `S(-d)` are analysed: the only coordinates that can be nonzero are the ones of total
degree `-d`.

The statement is phrased with the basis family and the spanning identity `hB3` as explicit
arguments, so that it applies to the monomial basis produced by `locAt_monomial_basis`.
-/

theorem cechCoeff_coord_eq_zero_of_ne_deg {A : Type*} [CommRing A] {n : ℕ} {d : ℕ} (q : ℕ)
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (hB3 : ∀ (S : Finset (Fin n)),
      degZero (A := A) (M := Poly A n) (shift (A := A) (n := n) d) S =
        Submodule.span A {y | ∃ β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i},
          (∑ i, β.1 i) = -(d : ℤ) ∧ y = B S β})
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    (a : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q)
    (S : Finset (Fin n)) (hS : S.card = q + 1)
    (β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i}) (hβ : (∑ i, β.1 i) ≠ -(d : ℤ)) :
    ((B S).repr (cechCoeff a S hS)) β = 0 := by
  -- The `S`-component of `a` lies in the span of the basis vectors of degree `-d`.
  have hmem : cechCoeff a S hS ∈ Submodule.span A
      {y | ∃ β' : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i},
        (∑ i, β'.1 i) = -(d : ℤ) ∧ y = B S β'} := by
    rw [← hB3 S]
    exact (a ⟨S, hS⟩).2
  -- The coordinate functional at an exponent of degree `≠ -d` kills that span, because it is a
  -- linear combination of coordinates of basis vectors, all of which are distinct from `β`.
  have key : Submodule.span A
      {y | ∃ β' : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i},
        (∑ i, β'.1 i) = -(d : ℤ) ∧ y = B S β'} ≤ LinearMap.ker (coordFun B S β) := by
    rw [Submodule.span_le]
    rintro y ⟨β', hβ', rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, coordFun_apply, Module.Basis.repr_self]
    have hne : β' ≠ β := by
      intro h
      exact hβ (by rw [← h]; exact hβ')
    simp [hne]
  have hz := LinearMap.mem_ker.mp (key hmem)
  simpa [coordFun] using hz

end Work.DSCOH
