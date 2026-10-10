import Mathlib
import Submission.Work.LLink.Count

set_option linter.unusedVariables false -- v435-speed

namespace Work.LLink

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- Transport of the function-field input along identifications of the residue fields: if the
residue field `κ(x)` of `x` is `𝕜`-isomorphic to the field `B` (the structure map `𝕜 → κ(x)`
corresponding to `ψ : 𝕜 →+* B`) and `κ(y)` to the field `A` (via `φ : 𝕜 →+* A`), and if `A` and
`B` are not isomorphic as `𝕜`-algebras, then `κ(y)` and `κ(x)` are not `𝕜`-isomorphic, i.e.
`¬ ResEquiv 𝕜 y x`.  This is how the paper's input `κ(ℙ¹ × C)(t) ≇ κ(ℙ¹ × C')(t)` is turned into
`¬ ResEquiv` for the two exceptional divisors of the Crauder–Katz link. -/
theorem not_resEquiv_of_ringEquiv {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}}
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] {x : X} {y : Y} {A B : Type} [Field A]
    [Field B] (φ : 𝕜 →+* A) (ψ : 𝕜 →+* B) (ex : ResAlgEquiv 𝕜 x B ψ)
    (ey : ResAlgEquiv 𝕜 y A φ) (h : ¬ ∃ e : A ≃+* B, e.toRingHom.comp φ = ψ) :
    ¬ ResEquiv 𝕜 y x := by
  -- Suppose `κ(y) ≅ κ(x)` as `𝕜`-algebras.  Composing with `κ(y) ≅ A` and `κ(x) ≅ B` yields a
  -- `𝕜`-algebra isomorphism `A ≅ B`, contradicting `h`.
  rintro ⟨e, he⟩
  obtain ⟨exe, hexe⟩ := ex
  obtain ⟨eye, heye⟩ := ey
  refine h ⟨eye.symm.trans (e.trans exe), ?_⟩
  rw [show (eye.symm.trans (e.trans exe)).toRingHom =
      (exe.toRingHom.comp e.toRingHom).comp eye.symm.toRingHom from rfl]
  simp only [RingHom.comp_assoc]
  -- `eye.symm ∘ φ = resMap 𝕜 Y y`, since `φ = eye ∘ resMap 𝕜 Y y`.
  have hsym : eye.symm.toRingHom.comp φ = resMap 𝕜 Y y := by
    rw [← heye, ← RingHom.comp_assoc]
    exact RingHom.ext fun a => by simp
  rw [hsym, he, hexe]

end Work.LLink
