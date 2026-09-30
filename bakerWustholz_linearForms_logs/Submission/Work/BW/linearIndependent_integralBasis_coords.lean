import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open NumberField

/-- Integer-basis coordinates of a `ℚ`-linearly independent family in `F^N`.

The `ℤ`-basis `NumberField.integralBasis F` of the ring of integers of `F` is in
particular a `ℚ`-basis of `F`, so the coordinate map
`x ↦ (fun j l => (integralBasis F).repr (x j) l)` is an injective `ℚ`-linear map
`(Fin N → F) → (Fin N → ι → ℚ)`.  Hence it preserves linear independence. -/
theorem linearIndependent_integralBasis_coords {F : Type*} [Field F] [NumberField F]
    {k N : ℕ} (w : Fin k → Fin N → F) (h : LinearIndependent ℚ w) :
    LinearIndependent ℚ (fun i => fun (j : Fin N)
      (l : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F)) =>
        (NumberField.integralBasis F).repr (w i j) l) := by
  let φ : (Fin N → F) →ₗ[ℚ]
      (Fin N → Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F) → ℚ) :=
    { toFun := fun x j l => (NumberField.integralBasis F).repr (x j) l
      map_add' := by intro x y; funext j l; simp
      map_smul' := by intro c x; funext j l; simp }
  have hφ : Function.Injective φ := by
    intro x y hxy
    funext j
    apply (NumberField.integralBasis F).repr.injective
    refine Finsupp.ext (fun l => ?_)
    have := congr_fun (congr_fun hxy j) l
    simpa [φ] using this
  have h2 : LinearIndependent ℚ (fun i (j : Fin N)
      (l : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F)) =>
        (NumberField.integralBasis F).repr (w i j) l) :=
    h.map' φ (by rw [LinearMap.ker_eq_bot]; exact hφ)
  exact h2

end Work.BW
