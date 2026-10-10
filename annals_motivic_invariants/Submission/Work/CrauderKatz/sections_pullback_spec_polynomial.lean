import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped TensorProduct

namespace Work.CrauderKatz

/-- **Affine case of the sections of `X × 𝔸¹`.**  For a `𝕜`-algebra `A`, the fibre product
`Spec A ×_{Spec 𝕜} Spec 𝕜[t]` is `Spec A[t]`; equivalently its ring of global sections is `A[t]`.

Suggested route: `AlgebraicGeometry.pullbackSpecIso 𝕜 A 𝕜[t]` identifies the pullback with
`Spec (A ⊗[𝕜] 𝕜[t])`; `AlgebraicGeometry.Scheme.ΓSpecIso` computes its global sections; and
`polyEquivTensor' 𝕜 A : Polynomial A ≃ₐ[A] TensorProduct 𝕜 A (Polynomial 𝕜)` (or
`Algebra.TensorProduct` commutativity) identifies `A ⊗[𝕜] 𝕜[t]` with `A[t]`. -/
theorem sections_pullback_spec_polynomial (𝕜 : Type) [Field 𝕜] (A : Type) [CommRing A] [Algebra 𝕜 A] :
    Nonempty (((CategoryTheory.Limits.pullback
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 A)))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜))))).presheaf.obj
        (Opposite.op ⊤) : Type) ≃+* Polynomial A) := by
  let P := CategoryTheory.Limits.pullback
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 A)))
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜))))
  let h : P ≅ AlgebraicGeometry.Spec (CommRingCat.of (A ⊗[𝕜] Polynomial 𝕜)) :=
    AlgebraicGeometry.pullbackSpecIso 𝕜 A (Polynomial 𝕜)
  refine ⟨?e⟩
  exact ((AlgebraicGeometry.Scheme.Γ.mapIso h.op).symm.commRingCatIsoToRingEquiv).trans
    ((AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of (A ⊗[𝕜] Polynomial 𝕜))).commRingCatIsoToRingEquiv.trans
      (polyEquivTensor' 𝕜 A).symm.toRingEquiv)

end Work.CrauderKatz
