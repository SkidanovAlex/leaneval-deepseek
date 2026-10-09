import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The value of a `2`-torsion `2`-cocycle at conjugate elements

Let `Γ` be a group and `V` a module over `ZMod 2` (so the additive group of `V` has exponent `2`).
Let `z : Γ → Γ → V` be a *normalized* `2`-cocycle for the **trivial** action of `Γ` on `V`, i.e.

* `z (g * h) l + z g h = z h l + z (g * (h * l))` (the cocycle law),
* `z 1 g = 0` and `z g 1 = 0` (normalization).

Then for every involution `u` (`u * u = 1`) and every `σ : Γ` the value of `z` at the pair
`(σ * u * σ⁻¹, σ * u * σ⁻¹)` agrees with the value at `(u, u)`:

  `z (σ * u * σ⁻¹) (σ * u * σ⁻¹) = z u u`.

This is the algebraic heart of the archimedean matching
(`Work.SSGRoute.HRec.cupKummer_archMatchK`): the local cup class of the cup datum at an involution
depends only on the **conjugacy class** of the involution.  The proof is the explicit computation

  `z t t = z u u + 2 • z σ⁻¹ σ - 2 • z u σ⁻¹ - 2 • z σ (u * σ⁻¹)`,  where `t = σ * u * σ⁻¹`,

in which the correction terms are killed by `2 • x = 0`.
-/

namespace Work.SSGRoute.HRec

variable {Γ V : Type} [Group Γ] [AddCommGroup V] [Module (ZMod 2) V]

/-- In a module over `ZMod 2` every element is killed by `2`. -/
lemma two_nsmul_eq_zero (x : V) : (2 : ℕ) • x = 0 := by
  have h : ((2 : ℕ) : ZMod 2) = 0 := by decide
  calc (2 : ℕ) • x = ((2 : ℕ) : ZMod 2) • x := (Nat.cast_smul_eq_nsmul (ZMod 2) 2 x).symm
    _ = (0 : ZMod 2) • x := by rw [h]
    _ = 0 := zero_smul _ _

/-- In a module over `ZMod 2` every element is killed by the integer `2`. -/
lemma int_two_smul_eq_zero (x : V) : (2 : ℤ) • x = 0 := by
  rw [← Int.cast_smul_eq_zsmul (ZMod 2) (2 : ℤ) x,
    show (((2 : ℤ) : ZMod 2)) = 0 from by decide, zero_smul]

/-- In a module over `ZMod 2` every element is killed by the integer `-2`. -/
lemma int_neg_two_smul_eq_zero (x : V) : (-2 : ℤ) • x = 0 := by
  rw [← Int.cast_smul_eq_zsmul (ZMod 2) (-2 : ℤ) x,
    show (((-2 : ℤ) : ZMod 2)) = 0 from by decide, zero_smul]

/-- In a module over `ZMod 2` every element is its own negative, additively: `x + x = 0`. -/
lemma two_torsion_add_self (x : V) : x + x = 0 := by
  rw [← two_nsmul]; exact two_nsmul_eq_zero x

/-- **The value of a normalized `2`-torsion `2`-cocycle at conjugate elements.** -/
theorem cocycle2_conj_value (z : Γ → Γ → V)
    (hz : ∀ g h l : Γ, z (g * h) l + z g h = z h l + z g (h * l))
    (hz1 : ∀ g : Γ, z 1 g = 0) (hz2 : ∀ g : Γ, z g 1 = 0)
    (u σ : Γ) (hu : u * u = 1) :
    z (σ * u * σ⁻¹) (σ * u * σ⁻¹) = z u u := by
  -- the six cocycle identities, with the trivial arguments simplified
  have hA : z (σ * u * σ⁻¹) (σ * u * σ⁻¹) + z (σ * u) σ⁻¹
      = z σ⁻¹ (σ * u * σ⁻¹) + z (σ * u) (u * σ⁻¹) := by
    have h := hz (σ * u) σ⁻¹ (σ * u * σ⁻¹)
    simpa only [show σ⁻¹ * (σ * u * σ⁻¹) = u * σ⁻¹ from by group] using h
  have hB : z (σ * u) (u * σ⁻¹) + z σ u = z u (u * σ⁻¹) + z σ σ⁻¹ := by
    have h := hz σ u (u * σ⁻¹)
    simpa only [show u * (u * σ⁻¹) = σ⁻¹ from by rw [← mul_assoc, hu, one_mul],
      mul_inv_cancel, hz1, add_zero] using h
  have hC : z u u = z u σ⁻¹ + z u (u * σ⁻¹) := by
    have h := hz u u σ⁻¹
    simpa only [hu, hz1, zero_add] using h
  have hD : z (σ * u) σ⁻¹ + z σ u = z u σ⁻¹ + z σ (u * σ⁻¹) := hz σ u σ⁻¹
  have hE : z σ⁻¹ σ = z σ (u * σ⁻¹) + z σ⁻¹ (σ * u * σ⁻¹) := by
    have h := hz σ⁻¹ σ (u * σ⁻¹)
    simpa only [inv_mul_cancel, hz1, zero_add,
      show σ * (u * σ⁻¹) = σ * u * σ⁻¹ from by group] using h
  have hF : z σ σ⁻¹ = z σ⁻¹ σ := by
    have h := hz σ σ⁻¹ σ
    simpa only [mul_inv_cancel, inv_mul_cancel, hz1, hz2, add_zero, zero_add] using h
  -- solved forms
  have eA : z (σ * u * σ⁻¹) (σ * u * σ⁻¹)
      = z σ⁻¹ (σ * u * σ⁻¹) + z (σ * u) (u * σ⁻¹) - z (σ * u) σ⁻¹ :=
    eq_sub_iff_add_eq.mpr hA
  have eB : z (σ * u) (u * σ⁻¹) = z u (u * σ⁻¹) + z σ σ⁻¹ - z σ u :=
    eq_sub_iff_add_eq.mpr hB
  have eC : z u (u * σ⁻¹) = z u u - z u σ⁻¹ := eq_sub_iff_add_eq.mpr (by
    rw [add_comm]; exact hC.symm)
  have eD : z (σ * u) σ⁻¹ = z u σ⁻¹ + z σ (u * σ⁻¹) - z σ u :=
    eq_sub_iff_add_eq.mpr hD
  have eE : z σ⁻¹ (σ * u * σ⁻¹) = z σ⁻¹ σ - z σ (u * σ⁻¹) := eq_sub_iff_add_eq.mpr (by
    rw [add_comm]; exact hE.symm)
  have eF : z σ σ⁻¹ = z σ⁻¹ σ := hF
  rw [eA, eB, eC, eD, eE, eF]
  abel_nf
  try (simp only [int_two_smul_eq_zero, int_neg_two_smul_eq_zero, neg_zero, add_zero, sub_zero,
    zero_add, sub_self])

end Work.SSGRoute.HRec
