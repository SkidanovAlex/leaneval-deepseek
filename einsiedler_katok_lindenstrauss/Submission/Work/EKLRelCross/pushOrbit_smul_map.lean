import Mathlib
import Submission.Work.EKLRelCross.pushOrbit_apply_of_injective

namespace Work.EKLRelCross

open MeasureTheory
open Work.EKLContract

/-! ## A change of base point for the orbit parametrisation

For a subgroup `U ≤ SL₃(ℝ)`, a base point `x ∈ X₃` and an element `u ∈ U`, the orbit piece
over a set `B ⊆ SL₃(ℝ)` parametrised at `u • x` is the orbit piece over `B` parametrised at
`x`, transported by right multiplication by `u`. -/
private lemma orbit_image_mul (U : Subgroup SL3) (u : U) (x : X3) (B : Set SL3) :
    (fun w : SL3 => w • x) '' (B ∩ (U : Set SL3))
      = (fun v : SL3 => v • ((u : SL3) • x)) ''
          (((fun g : SL3 => g * (u : SL3)) ⁻¹' B) ∩ (U : Set SL3)) := by
  ext y
  constructor
  · rintro ⟨w, ⟨hwB, hwU⟩, rfl⟩
    refine ⟨w * (u : SL3)⁻¹, ⟨?_, ?_⟩, ?_⟩
    · show (w * (u : SL3)⁻¹) * (u : SL3) ∈ B
      rw [mul_assoc, inv_mul_cancel, mul_one]
      exact hwB
    · exact U.mul_mem hwU (U.inv_mem u.2)
    · show (w * (u : SL3)⁻¹) • ((u : SL3) • x) = w • x
      rw [← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
  · rintro ⟨v, ⟨hvB, hvU⟩, rfl⟩
    exact ⟨v * (u : SL3), ⟨hvB, U.mul_mem hvU u.2⟩, (mul_smul v (u : SL3) x)⟩

/-- Injectivity of the orbit parametrisation at `x` transfers to the base point `u • x`,
because `v ↦ v • (u • x) = (v * u) • x` factors through `w ↦ w • x` composed with the
bijection `v ↦ v * u` of `U`. -/
private lemma injective_smul_orbit (U : Subgroup SL3) {x : X3}
    (hinj : Function.Injective (fun u : U => (u : SL3) • x)) (u : U) :
    Function.Injective (fun v : U => (v : SL3) • ((u : SL3) • x)) := by
  intro a b hab
  have hab' : ((a * u : U) : SL3) • x = ((b * u : U) : SL3) • x := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul]
    exact hab
  exact mul_right_cancel (hinj hab')

/-- **Change of base point for `pushOrbit`.** Moving the base point of the orbit
parametrisation from `x` to `u • x` is undone by right multiplication by `u` on the group:
`pushOrbit U x κ = (pushOrbit U (u • x) κ).map (g ↦ g * u)`.

On a measurable set `B`, both sides compute (via `pushOrbit_apply_of_injective`) the `κ`-mass of
the orbit piece `{g • x | g ∈ B ∩ U}`; the parametrisations at `x` and at `u • x` differ
precisely by the bijection `g ↦ g ↦ g * u` of `U` (with inverse `g ↦ g * u⁻¹`). -/
theorem pushOrbit_smul_map {U : Subgroup Work.EKLContract.SL3}
    (hUcl : IsClosed (U : Set Work.EKLContract.SL3))
    [StandardBorelSpace Work.EKLContract.X3] {x : Work.EKLContract.X3}
    (hinj : Function.Injective (fun u : U => (u : Work.EKLContract.SL3) • x))
    (u : U) (κ : MeasureTheory.Measure Work.EKLContract.X3) :
    Work.EKLRelCross.pushOrbit U x κ =
      (Work.EKLRelCross.pushOrbit U ((u : Work.EKLContract.SL3) • x) κ).map
        (fun g => g * (u : Work.EKLContract.SL3)) := by
  ext B hB
  rw [pushOrbit_apply_of_injective hUcl hinj κ hB]
  rw [Measure.map_apply (by fun_prop : Measurable (fun g : SL3 => g * (u : SL3))) hB]
  rw [pushOrbit_apply_of_injective hUcl (injective_smul_orbit U hinj u) κ
        (hB.preimage (by fun_prop))]
  congr 1
  exact orbit_image_mul U u x B

end Work.EKLRelCross
