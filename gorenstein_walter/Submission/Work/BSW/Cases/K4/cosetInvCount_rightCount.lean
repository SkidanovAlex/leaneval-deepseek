import Mathlib
import Submission.Work.BSW.Defs

/-!
# `cosetInvCount` counted over the right coset

`Work.GW2.cosetInvCount H u` counts the involutions of the **left** coset `u H` (an element `x`
has `u⁻¹ * x ∈ H` exactly when `x ∈ u H`).  Bender works with the right coset `H u`, and this
lemma records that the two counts agree:

`cosetInvCount H u = #{y | orderOf y = 2 ∧ y ∈ H u}`.

The two sets are equinumerous through conjugation by `u`: the map `x ↦ u⁻¹ * x * u` sends the
left coset `u H` onto the right coset `H u` (indeed `u⁻¹ * (u * h) * u = h * u`), is a bijection
of `G`, and preserves the order of an element.  Conjugation by `u` is its inverse.
-/

namespace Work.BSW.Cases.K4

/-- Counting involutions in the left coset `u H` is the same as counting involutions in the
right coset `H u`. -/
theorem cosetInvCount_rightCount {G : Type} [Group G] (H : Subgroup G) (u : G) :
    Work.GW2.cosetInvCount H u =
      ({y : G | orderOf y = 2 ∧ ∃ h ∈ H, y = h * u} : Set G).ncard := by
  unfold Work.GW2.cosetInvCount
  refine Set.ncard_congr (fun x _ => u⁻¹ * x * u) ?_ ?_ ?_
  · rintro a ⟨ha2, haH⟩
    refine ⟨?_, u⁻¹ * a, haH, rfl⟩
    have h1 : orderOf (u⁻¹ * a * u) = orderOf ((MulAut.conj u⁻¹) a) := by
      simp
    rw [h1, MulEquiv.orderOf_eq]
    exact ha2
  · intro a b _ _ hab
    have h : u * (u⁻¹ * a * u) * u⁻¹ = a := by group
    have h' : u * (u⁻¹ * b * u) * u⁻¹ = b := by group
    have := congrArg (fun z => u * z * u⁻¹) hab
    rw [h, h'] at this
    exact this
  · rintro b ⟨hb2, h, hhH, rfl⟩
    refine ⟨u * (h * u) * u⁻¹, ⟨?_, ?_⟩, ?_⟩
    · have h1 : u * (h * u) * u⁻¹ = (MulAut.conj u) (h * u) := by
        simp [MulAut.conj_apply]
      rw [h1, MulEquiv.orderOf_eq]
      exact hb2
    · have : u⁻¹ * (u * (h * u) * u⁻¹) = h := by group
      rw [this]
      exact hhH
    · have : u⁻¹ * (u * (h * u) * u⁻¹) * u = h * u := by group
      exact this

end Work.BSW.Cases.K4
