/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The period lattice `(πi/a)ℤ` is the model `ℤ ⊂ ℂ`

The Écalle cylinder of the implosion is modelled by `ℂ/ℤ` (HS Prop. 4.2): after
rescaling the coordinate the period lattice `periodZMod a = (πi/a)ℤ` of the
Écalle coordinate becomes the standard lattice `ℤ = zmultiples 1 ⊂ ℂ`.  This
file records the `ℤ`-linear (i.e. additive) equivalence

  `periodZMod a ≃₊ zmultiples 1`

for `a ≠ 0`, obtained from the general fact that any two nonzero cyclic
subgroups of `ℂ` are isomorphic by `x ↦ z⁻¹ x`.
-/
import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Cylinder

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Cylinder

/-- Every nonzero cyclic (i.e. `zmultiples`) additive subgroup of `ℂ` is
isomorphic, as an additive group, to the standard one `zmultiples 1 = ℤ ⊂ ℂ`.
The isomorphism is multiplication by `z⁻¹ ∈ ℂ`, with inverse multiplication by
`z`. -/
theorem zmultiples_equiv_zmultiples_one (z : ℂ) (hz : z ≠ 0) :
    Nonempty (AddSubgroup.zmultiples z ≃+ AddSubgroup.zmultiples (1 : ℂ)) := by
  refine ⟨{ toFun := fun x => ⟨z⁻¹ * x.1, ?_⟩
            invFun := fun w => ⟨z * w.1, ?_⟩
            left_inv := ?_
            right_inv := ?_
            map_add' := ?_ }⟩
  · -- `z⁻¹ x` is an integer multiple of `1` when `x` is an integer multiple of `z`
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp x.2
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    have hx : (x.1 : ℂ) = (n : ℂ) * z := by rw [← hn, zsmul_eq_mul]
    rw [zsmul_eq_mul, hx, mul_comm (n : ℂ) z, ← mul_assoc, inv_mul_cancel₀ hz, one_mul,
      mul_one]
  · -- `z w` is an integer multiple of `z` when `w` is an integer multiple of `1`
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp w.2
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    have hw : (w.1 : ℂ) = (n : ℂ) := by rw [← hn, zsmul_eq_mul, mul_one]
    rw [zsmul_eq_mul, hw, mul_comm z (n : ℂ)]
  · intro x
    ext
    simp only
    rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]
  · intro w
    ext
    simp only
    rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]
  · intro x y
    ext
    simp only [AddSubgroup.coe_add]
    ring

/-- **The period lattice of the Écalle coordinate is the model lattice `ℤ ⊂ ℂ`.**
For `a ≠ 0` the lattice `periodZMod a = (πi/a)ℤ` of periods of the Écalle
coordinate `u ↦ e^{2au}` is isomorphic, as an additive group, to the standard
lattice `zmultiples 1 = ℤ ⊂ ℂ` of the model cylinder `ℂ/ℤ`. -/
theorem periodZMod_equiv_model (a : ℂ) (ha : a ≠ 0) :
    Nonempty (periodZMod a ≃+ AddSubgroup.zmultiples (1 : ℂ)) := by
  have hz : Real.pi * Complex.I / a ≠ 0 :=
    div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero) ha
  exact zmultiples_equiv_zmultiples_one (Real.pi * Complex.I / a) hz

end Work.Implosion.Cylinder
