import Mathlib
import Submission.Work.Clifford.Orbit

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.card_charOrbit`: orbit–stabiliser for the conjugation action on `N → ℂ`

For `N ⊴ G` and an arbitrary function `θ : N → ℂ`, let `charOrbit N θ` be the `G`-orbit of `θ`
for the conjugation action `θ ↦ θ^g = conjFun N g θ` (`θ^g(x) = θ (g x g⁻¹)`), and let
`inertia N θ = {g : G | θ^g = θ}` be its inertia group.  The content of this file is the
orbit–stabiliser theorem

  `(charOrbit N θ).card = (inertia N θ).index`,

i.e. the number of distinct conjugates of `θ` equals the index in `G` of the subgroup fixing `θ`.

The orbit–stabiliser theorem is applied to the *left* action `g • f = f^{g⁻¹}` of `G` on the set
of all functions `N → ℂ`; the inversion is what turns the right action `conjFun_mul` into a left
action, and with this convention the stabiliser of `θ` is *exactly* the inertia group
`inertia N θ` (not merely conjugate to it).  No hypothesis whatsoever is imposed on `θ`: it need
not be a class function, an irreducible character, or even nonzero.

The `MulAction` instance is introduced with `letI` inside the proof of the main theorem so that it
does not leak into the instance graph of the modules importing this file.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical

namespace Work.Clifford

/-- Two conjugates of `θ` coincide exactly when the quotient of the conjugating elements lies in
the inertia group: `θ^g = θ^h ↔ g * h⁻¹ ∈ I_G(θ)`. -/
theorem conjFun_eq_conjFun_iff {G : Type*} [Group G] {N : Subgroup G} [N.Normal] (θ : N → ℂ)
    (g h : G) : conjFun N g θ = conjFun N h θ ↔ g * h⁻¹ ∈ inertia N θ := by
  constructor
  · intro hgh
    refine (mem_inertia N θ (g * h⁻¹)).mpr ?_
    rw [conjFun_mul, hgh, ← conjFun_mul, mul_inv_cancel, conjFun_one]
  · intro hmem
    have h1 : conjFun N (g * h⁻¹) θ = θ := (mem_inertia N θ (g * h⁻¹)).mp hmem
    have h3 : conjFun N h (conjFun N (g * h⁻¹) θ) = conjFun N h θ := by rw [h1]
    rw [← conjFun_mul] at h3
    rwa [show (g * h⁻¹) * h = g by group] at h3

theorem card_charOrbit {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal] (θ : N → ℂ) :
    (Work.Clifford.charOrbit N θ).card = (Work.Clifford.inertia N θ).index := by
  -- the left action `g • f = f^{g⁻¹}` of `G` on all functions `N → ℂ`
  letI : MulAction G (N → ℂ) :=
    { smul := fun g f => conjFun N g⁻¹ f
      one_smul := fun f => by
        show conjFun N (1 : G)⁻¹ f = f
        rw [inv_one, conjFun_one]
      mul_smul := fun g h f => by
        show conjFun N (g * h)⁻¹ f = conjFun N g⁻¹ (conjFun N h⁻¹ f)
        rw [mul_inv_rev, conjFun_mul] }
  have hsmul : ∀ (g : G) (f : N → ℂ), g • f = conjFun N g⁻¹ f := fun _ _ => rfl
  -- the stabiliser of `θ` is the inertia group of `θ`
  have hstab : MulAction.stabilizer G θ = inertia N θ := by
    ext g
    rw [MulAction.mem_stabilizer_iff, hsmul]
    exact (mem_inertia N θ g⁻¹).symm.trans (Subgroup.inv_mem_iff _)
  -- the orbit of `θ` is `charOrbit N θ`
  have horbit : (MulAction.orbit G θ : Set (N → ℂ)) = (charOrbit N θ : Set (N → ℂ)) := by
    ext φ
    rw [MulAction.mem_orbit_iff, Finset.mem_coe, mem_charOrbit]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g⁻¹, (hsmul g θ).symm⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h⁻¹, by rw [hsmul, inv_inv]⟩
  rw [← hstab, MulAction.index_stabilizer, horbit, Set.ncard_coe_finset]

end Work.Clifford
