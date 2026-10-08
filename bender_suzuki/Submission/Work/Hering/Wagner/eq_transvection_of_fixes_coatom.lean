import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A linear map fixing a hyperplane and moving one vector is a transvection

Let `U` be a finite-dimensional `𝔽₂`-vector space, `X` a codimension-one subspace written as
`X = ker f` for a linear form `f`, and `g` a linear automorphism of `U` that fixes `X`
pointwise.  If `g` sends a vector `c ∉ X` to `c + v` with `v ∈ ker f` (`f v = 0`), then `g` is
the transvection `y ↦ y + f y • v`.

The point is that `U = X ⊕ ⟨c⟩`, so every `y` can be written `y = (y - f y • c) + f y • c` with
`y - f y • c ∈ X = ker f`; the hypothesis `f v = 0` makes `y ↦ y + f y • v` an automorphism.
-/

namespace Work.Hering.Wagner

/-- In `ZMod 2` every nonzero element is `1`. -/
theorem zmod_two_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  have hval : a.val ≠ 0 := fun h0 => h ((ZMod.val_eq_zero a).mp h0)
  have hlt : a.val < 2 := ZMod.val_lt a
  have h1 : a.val = 1 := by omega
  rw [← ZMod.natCast_zmod_val a, h1, Nat.cast_one]

/-- **A linear automorphism of a finite-dimensional `𝔽₂`-space that fixes a hyperplane
`X = ker f` pointwise and sends `c ∉ X` to `c + v` with `v ∈ ker f` is the transvection
`y ↦ y + f y • v`.** -/
theorem eq_transvection_of_fixes_coatom {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Module.Finite (ZMod 2) U] {X : Submodule (ZMod 2) U}
    (hX : Module.finrank (ZMod 2) X + 1 = Module.finrank (ZMod 2) U)
    {f : Module.Dual (ZMod 2) U} (hker : LinearMap.ker f = X)
    {g : U ≃ₗ[ZMod 2] U} (hg : ∀ x ∈ X, g x = x) {c : U} (hc : c ∉ X)
    {v : U} (hv : f v = 0) (hgc : g c = c + v) :
    g = LinearEquiv.transvection hv := by
  ext y
  -- Over `𝔽₂` a nonzero value of `f` is `1`; in particular `f c = 1` since `c ∉ ker f = X`.
  have hfc : f c = 1 := zmod_two_eq_one_of_ne_zero (by
    intro h0
    exact hc (by rw [← hker]; exact LinearMap.mem_ker.mpr h0))
  -- `y - f y • c` lies in `ker f = X`, hence is fixed by `g`.
  have hmem : y - f y • c ∈ X := by
    rw [← hker, LinearMap.mem_ker]
    simp [map_sub, map_smul, hfc]
  have hgy : g y = y + f y • v := by
    have h1 : g (y - f y • c) = y - f y • c := hg _ hmem
    rw [map_sub, map_smul, hgc, smul_add] at h1
    have h2 : g y = (y - f y • c) + (f y • c + f y • v) := sub_eq_iff_eq_add.mp h1
    rw [h2, ← add_assoc, sub_add_cancel]
  rw [hgy]
  show y + f y • v = (LinearEquiv.transvection hv) y
  simp [LinearEquiv.transvection, LinearMap.transvection]

end Work.Hering.Wagner
