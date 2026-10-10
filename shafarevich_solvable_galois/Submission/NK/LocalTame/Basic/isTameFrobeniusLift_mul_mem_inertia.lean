import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Subgroup.Defs
import Submission.NK.LocalTame.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalTame.Basic

/-- **The set of Frobenius lifts is a union of cosets of the inertia subgroup**: multiplying a
Frobenius lift `x` on the left by an element `y` of the inertia subgroup `I` gives again a
Frobenius lift.

Both required properties survive the perturbation, and neither needs `I` to be normal:

* `y * x ∉ I`, because `y⁻¹ ∈ I` and `I` is a subgroup;
* the conjugation action on `I` is unchanged modulo `V`: writing `v = x z x⁻¹ (z^q)⁻¹ ∈ V` for
  `z ∈ I`, we get `x z x⁻¹ = v z^q`, whence
  `(y x) z (y x)⁻¹ (z^q)⁻¹ = (y v y⁻¹) · (y z^q y⁻¹ (z^q)⁻¹)`.
  The first factor lies in `V` because `V` is normal, and the second lies in `V` by the
  commutator hypothesis `hab`, applied to the two elements `y, z^q ∈ I`. -/
theorem isTameFrobeniusLift_mul_mem_inertia {G : Type*} [Group G] {q : ℕ} {V I : Subgroup G}
    (hV : V.Normal) (hVI : V ≤ I)
    (hab : ∀ y ∈ I, ∀ z ∈ I, y * z * y⁻¹ * z⁻¹ ∈ V) {x y : G}
    (h : IsTameFrobeniusLift q V I x) (hy : y ∈ I) : IsTameFrobeniusLift q V I (y * x) := by
  obtain ⟨hxI, hact⟩ := h
  refine ⟨?_, ?_⟩
  · -- `y * x ∉ I`, since `x = y⁻¹ * (y * x)` and `y⁻¹ ∈ I`.
    intro hmem
    refine hxI ?_
    have hx_eq : x = y⁻¹ * (y * x) := by group
    rw [hx_eq]
    exact I.mul_mem (I.inv_mem hy) hmem
  · -- `(y * x) z (y * x)⁻¹ (z ^ q)⁻¹ ∈ V` for every `z ∈ I`.
    intro z hz
    have hv : x * z * x⁻¹ * (z ^ q)⁻¹ ∈ V := hact z hz
    have h1 : y * (x * z * x⁻¹ * (z ^ q)⁻¹) * y⁻¹ ∈ V := hV.conj_mem _ hv y
    have h2 : y * z ^ q * y⁻¹ * (z ^ q)⁻¹ ∈ V := hab y hy (z ^ q) (I.pow_mem hz q)
    have heq : (y * x) * z * (y * x)⁻¹ * (z ^ q)⁻¹
        = y * (x * z * x⁻¹ * (z ^ q)⁻¹) * y⁻¹ * (y * z ^ q * y⁻¹ * (z ^ q)⁻¹) := by
      group
    rw [heq]
    exact V.mul_mem h1 h2

end NK.LocalTame.Basic
