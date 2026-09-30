import Mathlib
import Submission.Work.Descent.QuotientSetup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry

namespace Work.Descent

universe u

/-- Every affine `k`-scheme is isomorphic, as a `k`-scheme, to the affine model `Spec A` of a
`k`-algebra `A`: take `A` to be the ring of global sections `Γ(X, ⊤)`, with the `k`-algebra
structure induced by the structure morphism `X ⟶ Spec k`, and the isomorphism given by the
canonical isomorphism `X ≅ Spec Γ(X, ⊤)`. -/
theorem exists_iso_Aff {k : Type u} [Field k] (X : Work.Descent.Sch k)
    [AlgebraicGeometry.IsAffine X.left] :
    ∃ (A : Type u) (inst₁ : CommRing A) (inst₂ : Algebra k A),
      Nonempty (X ≅ @Work.Descent.Aff k _ A inst₁ inst₂) := by
  let R : CommRingCat := Γ(X.left, ⊤)
  let φ : CommRingCat.of k ⟶ R :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop X.hom
  letI : Algebra k ↥R := RingHom.toAlgebra (CommRingCat.Hom.hom φ)
  refine ⟨↥R, inferInstance, inferInstance, ?_⟩
  refine ⟨Over.isoMk X.left.isoSpec ?_⟩
  change X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k ↥R)) = X.hom
  have hφ : CommRingCat.ofHom (algebraMap k ↥R) = φ := rfl
  rw [hφ]
  show X.left.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    Scheme.Hom.appTop X.hom) = X.hom
  rw [Spec.map_comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv (Scheme.Hom.appTop X.hom)]
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality]
  have hk : (Spec (CommRingCat.of k)).toSpecΓ ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [← Scheme.isoSpec_Spec_inv]
    exact Scheme.toSpecΓ_isoSpec_inv _
  rw [Category.assoc, hk, Category.comp_id]

end Work.Descent
