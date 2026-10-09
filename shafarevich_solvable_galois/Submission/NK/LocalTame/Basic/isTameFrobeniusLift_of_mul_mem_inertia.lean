import Mathlib
import Submission.NK.LocalTame.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalTame.Basic

/-- **The set of Frobenius lifts is a union of cosets of the inertia subgroup** (the converse
direction of `isTameFrobeniusLift_mul_mem_inertia`): if `y * x` is a Frobenius lift and `y` lies
in the inertia subgroup `I`, then so is `x`, provided `I` is abelian modulo the wild inertia
`V` (i.e. `V` contains the commutators of `I`).

The hypothesis `hab` is what is needed: it makes `I / V` abelian, so that a normalised
perturbation by `y ∈ I` is invisible modulo `V`.

* `x ∉ I` is immediate: if `x ∈ I` then `y * x ∈ I`;
* writing `u = x z x⁻¹ (z^q)⁻¹` and `c = y z^q y⁻¹ (z^q)⁻¹ ∈ V` (this is exactly the
  commutator hypothesis `hab` applied to `y, z^q ∈ I`), the identity
  `(y x) z (y x)⁻¹ (z^q)⁻¹ = (y u y⁻¹) · c`
  shows `y u y⁻¹ ∈ V`, and then `u = y⁻¹ (y u y⁻¹) y ∈ V` because `V` is normal. -/
theorem isTameFrobeniusLift_of_mul_mem_inertia {G : Type*} [Group G] {q : ℕ} {V I : Subgroup G}
    (hV : V.Normal) (hVI : V ≤ I)
    (hab : ∀ y ∈ I, ∀ z ∈ I, y * z * y⁻¹ * z⁻¹ ∈ V) {x y : G} (hy : y ∈ I)
    (h : IsTameFrobeniusLift q V I (y * x)) : IsTameFrobeniusLift q V I x := by
  obtain ⟨hnotin, hact⟩ := h
  refine ⟨fun hx => hnotin (I.mul_mem hy hx), fun z hz => ?_⟩
  -- The action of the lifted element `y * x` on `z ∈ I`, split into the `V`-part `y u y⁻¹`
  -- and the commutator `c = y z^q y⁻¹ (z^q)⁻¹ ∈ V`.
  have hv : (y * x) * z * (y * x)⁻¹ * (z ^ q)⁻¹ ∈ V := hact z hz
  have hc : y * z ^ q * y⁻¹ * (z ^ q)⁻¹ ∈ V := hab y hy (z ^ q) (I.pow_mem hz q)
  have heq : (y * x) * z * (y * x)⁻¹ * (z ^ q)⁻¹
      = y * (x * z * x⁻¹ * (z ^ q)⁻¹) * y⁻¹ * (y * z ^ q * y⁻¹ * (z ^ q)⁻¹) := by
    group
  rw [heq] at hv
  have hconj : y * (x * z * x⁻¹ * (z ^ q)⁻¹) * y⁻¹ ∈ V := by
    have h2 : (y * (x * z * x⁻¹ * (z ^ q)⁻¹) * y⁻¹ * (y * z ^ q * y⁻¹ * (z ^ q)⁻¹))
        * (y * z ^ q * y⁻¹ * (z ^ q)⁻¹)⁻¹ ∈ V := V.mul_mem hv (V.inv_mem hc)
    convert h2 using 1
    group
  have hu_eq : x * z * x⁻¹ * (z ^ q)⁻¹
      = y⁻¹ * (y * (x * z * x⁻¹ * (z ^ q)⁻¹) * y⁻¹) * y := by
    group
  rw [hu_eq]
  simpa using hV.conj_mem (y * (x * z * x⁻¹ * (z ^ q)⁻¹) * y⁻¹) hconj y⁻¹

end NK.LocalTame.Basic
