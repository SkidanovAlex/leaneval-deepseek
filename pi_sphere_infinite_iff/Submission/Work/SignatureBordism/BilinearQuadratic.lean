import Mathlib

/-!
# The quadratic form of a bilinear form

A quadratic form is often given by a bilinear form `F` as `x ↦ F x x`; the quadratic map axioms
are then automatic, with companion the *symmetrisation* `F + F.flip` (so no symmetry of `F` is
needed, and no hypothesis on `2`).  This is the bridge used to pass from the intersection
*pairing* `⟨y ⌣ z, c⟩` of a manifold to the intersection *quadratic form* `⟨y ⌣ y, c⟩` whose
signature is the signature of the manifold; see
`Submission/Work/SignatureBordism/Intersection.lean`.

## Main definitions and results

* `Work.SignatureBordism.quadOfBilin F` — the quadratic form `x ↦ F x x`;
* `Work.SignatureBordism.quadOfBilin_apply` — its computation rule;
* `Work.SignatureBordism.quadOfBilin_neg` — `quadOfBilin (-F) = -quadOfBilin F`;
* `Work.SignatureBordism.quadOfBilin_congr` — `F = G → quadOfBilin F = quadOfBilin G`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SignatureBordism

open QuadraticMap

noncomputable section

variable {𝕜 V : Type*}

/-- **The quadratic form associated with a bilinear form**: `x ↦ F x x`.

The companion (polar form) of this quadratic map is the symmetrisation `F + F.flip`, i.e.
`(x, y) ↦ F x y + F y x`; thus no symmetry of `F` is required, and nothing is assumed about `2`. -/
def quadOfBilin [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (F : V →ₗ[𝕜] V →ₗ[𝕜] 𝕜) : QuadraticForm 𝕜 V :=
  QuadraticMap.mk (fun x => F x x)
    (fun a x => by
      rw [map_smul F a x, LinearMap.smul_apply, map_smul (F x) a x, smul_smul])
    ⟨F + F.flip, fun x y => by
      simp only [LinearMap.add_apply, LinearMap.flip_apply, map_add, LinearMap.add_apply]
      abel⟩

/-- **The computation rule** for `quadOfBilin`: on a vector it is `F x x`. -/
@[simp] theorem quadOfBilin_apply [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (F : V →ₗ[𝕜] V →ₗ[𝕜] 𝕜) (x : V) : quadOfBilin F x = F x x :=
  rfl

/-- **`quadOfBilin` intertwines negation**: `quadOfBilin (-F) = -quadOfBilin F`. -/
@[simp] theorem quadOfBilin_neg [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (F : V →ₗ[𝕜] V →ₗ[𝕜] 𝕜) : quadOfBilin (-F) = -quadOfBilin F := by
  ext x
  simp only [quadOfBilin, QuadraticMap.coe_mk, LinearMap.neg_apply]
  simp

/-- `quadOfBilin` respects equality of bilinear forms. -/
theorem quadOfBilin_congr [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {F G : V →ₗ[𝕜] V →ₗ[𝕜] 𝕜} (h : F = G) : quadOfBilin F = quadOfBilin G := by
  rw [h]

end

end Work.SignatureBordism
