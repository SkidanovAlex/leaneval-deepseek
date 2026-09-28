import Mathlib
import Submission.Work.Projective.CPn

/-!
# All complements of a point in `ℂPⁿ` are homeomorphic

The group `GL(ℂ^{n+1})` acts on `ℂPⁿ = ℙ ℂ (ℂ^{n+1})` (the projectivisation of a linear automorphism
of the underlying vector space), and this action is transitive, so `ℂPⁿ` is homogeneous.  Hence for
any two points `a`, `b` of `ℂPⁿ` there is a homeomorphism of `ℂPⁿ` carrying `a` to `b`, and it
restricts to a homeomorphism of the complements.

The topological content is that `cpMk n : {v : ℂ^{n+1} // v ≠ 0} → ℂPⁿ` is a quotient map
(`Work.Projective.isQuotientMap_cpMk`), so continuity of a map *out of* `ℂPⁿ` needs only the
continuity of its composite with `cpMk n`; the composite in question is induced by a linear map of
`ℂ^{n+1}`, which is automatically continuous in finite dimension.

## Main results

* `Work.Projective.continuous_smul_cp` — the `GL`-action on `ℂPⁿ` is continuous;
* `Work.Projective.projHomeomorph` — a linear automorphism of `ℂ^{n+1}` induces a homeomorphism
  of `ℂPⁿ`;
* `Work.Projective.exists_smul_eq_cpOrigin` — transitivity: every point is the image of
  `cpOrigin n` under some `GL`-element;
* `Work.Projective.cp_compl_homeo` — **the complements of any two points of `ℂPⁿ` are
  homeomorphic**.
-/

open scoped LinearAlgebra.Projectivization Manifold ContDiff Topology

namespace Work.Projective

noncomputable section

/-! ## The continuity of the action of `GL` on `ℂPⁿ` -/

/-- **The action of a linear automorphism of `ℂ^{n+1}` on `ℂPⁿ` is continuous.**  Since
`cpMk n` is a quotient map, it suffices to check continuity after precomposing with `cpMk n`,
where the map is induced by a linear (hence continuous) map of `ℂ^{n+1}`. -/
theorem continuous_smul_cp (n : ℕ) (g : CPV n ≃ₗ[ℂ] CPV n) :
    Continuous (fun x : CP n => g • x) := by
  rw [(isQuotientMap_cpMk n).continuous_iff]
  change Continuous (fun v : {v : CPV n // v ≠ 0} => g • cpMk n v)
  have hc : Continuous (fun v : {v : CPV n // v ≠ 0} =>
      cpMk n ⟨(g : CPV n →ₗ[ℂ] CPV n) v.1,
        fun hz => v.2 (g.injective (by simpa using hz))⟩) :=
    (continuous_cpMk n).comp (Continuous.subtype_mk
      ((LinearMap.continuous_of_finiteDimensional (g : CPV n →ₗ[ℂ] CPV n)).comp
        continuous_subtype_val) _)
  refine hc.congr fun v => ?_
  simp only [cpMk_apply, Projectivization.smul_mk, LinearEquiv.smul_def]
  congr 1

/-! ## The homeomorphism induced by a linear automorphism -/

/-- **A linear automorphism of `ℂ^{n+1}` induces a homeomorphism of `ℂPⁿ`**, via the action of
`GL(ℂ^{n+1})` on the projectivisation; the inverse is induced by the inverse automorphism. -/
def projHomeomorph (n : ℕ) (g : CPV n ≃ₗ[ℂ] CPV n) : CP n ≃ₜ CP n where
  toFun x := g • x
  invFun x := g.symm • x
  left_inv x := by
    show g.symm • (g • x) = x
    have h : g.symm * g = 1 := inv_mul_cancel g
    rw [← mul_smul, h, one_smul]
  right_inv x := by
    show g • (g.symm • x) = x
    have h : g * g.symm = 1 := mul_inv_cancel g
    rw [← mul_smul, h, one_smul]
  continuous_toFun := continuous_smul_cp n g
  continuous_invFun := continuous_smul_cp n g.symm

@[simp]
theorem projHomeomorph_apply (n : ℕ) (g : CPV n ≃ₗ[ℂ] CPV n) (x : CP n) :
    projHomeomorph n g x = g • x := rfl

/-- `ℂPⁿ` is homogeneous under `GL(ℂ^{n+1})`: every point is the image of the origin `[1 : 0 : … : 0]`
under the action of some linear automorphism. -/
theorem exists_smul_eq_cpOrigin (n : ℕ) (x : CP n) :
    ∃ g : CPV n ≃ₗ[ℂ] CPV n, g • cpOrigin n = x := by
  haveI : MulAction.IsPretransitive (CPV n ≃ₗ[ℂ] CPV n) (CP n) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  exact MulAction.exists_smul_eq (CPV n ≃ₗ[ℂ] CPV n) (cpOrigin n) x

/-! ## Restricting a homeomorphism to corresponding subsets -/

/-- A homeomorphism `e : X ≃ₜ Y` restricts to a homeomorphism `{x // p x} ≃ₜ {y // q y}` as soon
as `p x ↔ q (e x)` for every `x`. -/
def subtypeHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {p : X → Prop} {q : Y → Prop} (h : ∀ x, p x ↔ q (e x)) : {x // p x} ≃ₜ {y // q y} where
  toFun x := ⟨e x.1, (h x.1).mp x.2⟩
  invFun y := ⟨e.symm y.1, (h (e.symm y.1)).mpr (by simpa using y.2)⟩
  left_inv x := Subtype.ext (e.left_inv x.1)
  right_inv y := Subtype.ext (e.right_inv y.1)
  continuous_toFun := Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) _

@[simp]
theorem subtypeHomeomorph_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {p : X → Prop} {q : Y → Prop} (h : ∀ x, p x ↔ q (e x)) (x : {x // p x}) :
    subtypeHomeomorph e h x = ⟨e x.1, (h x.1).mp x.2⟩ := rfl

/-! ## The complements of any two points are homeomorphic -/

/-- **The complement of any point of `ℂPⁿ` is homeomorphic to the complement of the origin
`[1 : 0 : … : 0]`.**  A linear automorphism of `ℂ^{n+1}` that moves the origin to `x` induces a
homeomorphism of `ℂPⁿ` carrying `cpOrigin n` to `x`, which restricts to the complements. -/
theorem cp_compl_homeo (n : ℕ) (x : Work.Projective.CPSpace n) :
    Nonempty (({y : Work.Projective.CPSpace n // y ≠ Work.Projective.cpOrigin n}) ≃ₜ
      ({y : Work.Projective.CPSpace n // y ≠ x})) := by
  obtain ⟨g, hg⟩ := exists_smul_eq_cpOrigin n x
  refine ⟨subtypeHomeomorph (projHomeomorph n g) fun y => ?_⟩
  rw [projHomeomorph_apply, ← hg]
  exact ⟨fun hy h => hy ((projHomeomorph n g).injective (by simpa [projHomeomorph_apply] using h)),
    fun hy h => hy (by rw [h])⟩

end

end Work.Projective
