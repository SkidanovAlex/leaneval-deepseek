import Mathlib
import Submission.Work.MotA.Defs
import Submission.Work.MotA.residueField_fracEquiv

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option autoImplicit false

noncomputable section

namespace Work.MotA

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **The residue field of a point of `𝔸ⁿ` is the fraction field of the coordinate quotient.**
For `x : polySpec 𝕜 n` there is a ring isomorphism
`κ(x) ≃+* Frac (𝕜[x₁,…,xₙ] ⧸ x.asIdeal)` under which the structure map
`resMap 𝕜 (polySpec 𝕜 n) x` corresponds to `(algebraMap 𝕜[x₁,…,xₙ] _).comp (algebraMap 𝕜 _)`.

This is `Work.MotA.residueField_fracEquiv` specialised to the polynomial ring
`R = MvPolynomial (Fin n) 𝕜`, with the algebra structure spelled out. -/
theorem exists_ringEquiv_residueField_fractionRing (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (x : polySpec 𝕜 n) :
    ∃ e : (polySpec 𝕜 n).residueField x ≃+*
        FractionRing (MvPolynomial (Fin n) 𝕜 ⧸ x.asIdeal),
      e.toRingHom.comp (resMap 𝕜 (polySpec 𝕜 n) x) =
        (algebraMap (MvPolynomial (Fin n) 𝕜)
          (FractionRing (MvPolynomial (Fin n) 𝕜 ⧸ x.asIdeal))).comp
            (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜)) :=
  Work.MotA.residueField_fracEquiv 𝕜 (MvPolynomial (Fin n) 𝕜) x.asIdeal x.isPrime

/-- **Ring isomorphisms versus algebra isomorphisms.**  Two `𝕜`-algebras are isomorphic as
`𝕜`-algebras exactly when there is a ring isomorphism between them that is compatible with the two
structure maps. -/
theorem nonempty_algEquiv_iff_exists_ringEquiv (𝕜 : Type) [Field 𝕜] (A B : Type) [CommRing A]
    [CommRing B] [Algebra 𝕜 A] [Algebra 𝕜 B] :
    Nonempty (A ≃ₐ[𝕜] B) ↔
      ∃ e : A ≃+* B, e.toRingHom.comp (algebraMap 𝕜 A) = algebraMap 𝕜 B := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toRingEquiv, RingHom.ext fun a => e.commutes' a⟩
  · rintro ⟨e, he⟩
    exact ⟨AlgEquiv.ofRingEquiv (f := e) fun a => DFunLike.congr_fun he a⟩

/-- Audit node **A2b**: the residue field of a point of `𝔸ⁿ` is the fraction field of the quotient
by the corresponding prime ideal, and `ResEquiv` is exactly `𝕜`-algebra isomorphism of those
fraction fields.

Key existing ingredient: `Work.MotA.residueField_fracEquiv` (file
`Submission/Work/CKLink6/residueField_fracEquiv.lean`) states, for `R` a `𝕜`-algebra and `p` a
prime ideal, that there is a ring isomorphism
`e : (Spec R).residueField ⟨p, hp⟩ ≃+* FractionRing (R ⧸ p)` with
`e ∘ resMap 𝕜 (Spec R) ⟨p,hp⟩ = (algebraMap R (FractionRing (R ⧸ p))) ∘ (algebraMap 𝕜 R)`.
Composing such an `e_x` for `x` and `e_y` for `y` with a ring isomorphism in `ResEquiv` gives
both directions (note `ResEquiv` is `∃ e : κ(x) ≃+* κ(y), e.comp (resMap 𝕜 _ x) = resMap 𝕜 _ y`).
`resMap` is injective, so no extra condition is needed. -/
theorem resEquiv_iff_fractionRing (𝕜 : Type) [Field 𝕜] (n m : ℕ) (x : polySpec 𝕜 n)
    (y : polySpec 𝕜 m) :
    ResEquiv 𝕜 x y ↔
      Nonempty (FractionRing (MvPolynomial (Fin n) 𝕜 ⧸ x.asIdeal) ≃ₐ[𝕜]
        FractionRing (MvPolynomial (Fin m) 𝕜 ⧸ y.asIdeal)) := by
  obtain ⟨ex, hex⟩ := exists_ringEquiv_residueField_fractionRing 𝕜 n x
  obtain ⟨ey, hey⟩ := exists_ringEquiv_residueField_fractionRing 𝕜 m y
  rw [nonempty_algEquiv_iff_exists_ringEquiv 𝕜]
  constructor
  · -- a `𝕜`-isomorphism `κ(x) ≅ κ(y)` of the residue fields gives one of the fraction fields
    rintro ⟨e, he⟩
    refine ⟨ex.symm.trans (e.trans ey), ?_⟩
    rw [RingEquiv.toRingHom_trans', RingEquiv.toRingHom_trans']
    simp only [RingHom.comp_assoc]
    -- `ex.symm` carries the structure map of `𝕜[x₁,…,xₙ] ⧸ x.asIdeal` to `resMap 𝕜 _ x`
    have h1 : ex.symm.toRingHom.comp
        ((algebraMap (MvPolynomial (Fin n) 𝕜)
          (FractionRing (MvPolynomial (Fin n) 𝕜 ⧸ x.asIdeal))).comp
            (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))) =
        resMap 𝕜 (polySpec 𝕜 n) x := by
      rw [← hex]
      ext a
      simp
    rw [IsScalarTower.algebraMap_eq 𝕜 (MvPolynomial (Fin n) 𝕜) _,
      h1, he, hey, ← IsScalarTower.algebraMap_eq 𝕜 (MvPolynomial (Fin m) 𝕜) _]
  · -- conversely a `𝕜`-algebra isomorphism of the fraction fields gives a `ResEquiv`
    rintro ⟨f, hf⟩
    refine ⟨ex.trans (f.trans ey.symm), ?_⟩
    rw [RingEquiv.toRingHom_trans', RingEquiv.toRingHom_trans']
    simp only [RingHom.comp_assoc]
    -- `ey.symm` carries the structure map of `𝕜[y₁,…,yₘ] ⧸ y.asIdeal` to `resMap 𝕜 _ y`
    have h2 : ey.symm.toRingHom.comp
        (algebraMap 𝕜 (FractionRing (MvPolynomial (Fin m) 𝕜 ⧸ y.asIdeal))) =
        resMap 𝕜 (polySpec 𝕜 m) y := by
      rw [IsScalarTower.algebraMap_eq 𝕜 (MvPolynomial (Fin m) 𝕜) _, ← hey]
      ext a
      simp
    rw [hex, ← IsScalarTower.algebraMap_eq 𝕜 (MvPolynomial (Fin n) 𝕜) _, hf, h2]

end Work.MotA
