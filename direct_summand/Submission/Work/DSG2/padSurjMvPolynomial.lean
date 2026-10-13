import Mathlib

universe u

namespace Work.DSG2

/-- The `A`-algebra section of `MvPolynomial.rename (Fin.castLE h)`: it sends the variables
`X j` with `j` in the range of `Fin.castLE h` back to `X j`, and all the extra variables to `0`.
It is a left inverse of `rename (Fin.castLE h)`. -/
noncomputable def padSection {A : Type u} [CommRing A] {n N : ℕ} (h : n ≤ N) :
    MvPolynomial (Fin N) A →+* MvPolynomial (Fin n) A :=
  (MvPolynomial.killCompl (R := A) (Fin.castLE_injective h)).toRingHom

lemma padSection_rename_apply {A : Type u} [CommRing A] {n N : ℕ} (h : n ≤ N)
    (p : MvPolynomial (Fin n) A) :
    padSection h (MvPolynomial.rename (Fin.castLE h) p) = p :=
  MvPolynomial.killCompl_rename_app (Fin.castLE_injective h) p

lemma padSection_C {A : Type u} [CommRing A] {n N : ℕ} (h : n ≤ N) :
    (padSection (A := A) h).comp (MvPolynomial.C : A →+* MvPolynomial (Fin N) A)
      = (MvPolynomial.C : A →+* MvPolynomial (Fin n) A) :=
  RingHom.ext fun a => MvPolynomial.killCompl_C (Fin.castLE_injective h) a

theorem padSurjMvPolynomial {A : Type u} [CommRing A] {R : Type u} [CommRing R]
    (φ : A →+* R) {n N : ℕ} (h : n ≤ N) (ψ : MvPolynomial (Fin n) A →+* R)
    (hψ : Function.Surjective ψ) (hC : ψ.comp MvPolynomial.C = φ) :
    ∃ ψ' : MvPolynomial (Fin N) A →+* R,
      Function.Surjective ψ' ∧ ψ'.comp MvPolynomial.C = φ := by
  refine ⟨ψ.comp (padSection h), ?_, ?_⟩
  · intro r
    obtain ⟨p, hp⟩ := hψ r
    exact ⟨MvPolynomial.rename (Fin.castLE h) p, by
      rw [RingHom.comp_apply, padSection_rename_apply, hp]⟩
  · rw [RingHom.comp_assoc, padSection_C, hC]

end Work.DSG2
