import Mathlib
import Submission.Work.ThompsonFrobenius.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThompsonFrobenius`: the elementary cases and the reduction

This module collects the parts of Thompson's theorem that are provable from the delivered
Feit--Thompson libraries:

* `isNilpotent_of_orderOf_eq_two`: the case of a fixed-point-free automorphism of order two
  (then the group is commutative);
* `isNilpotent_of_fpf_of_odd`: the case of odd order, via `FeitThompsonProp` and the delivered
  `Work.Frobenius.Fpf.isNilpotent_of_fpf_prime`;
* `isNilpotent_of_fpf_of_solvable`: the solvable case (the delivered theorem, restated);
* `hasNormalPComplement_of_normalizers`: the "`N_G(Q)` has a normal `p`-complement for all
  non-trivial `p`-subgroups `Q`" criterion (`Work.NPC.npc_of_normalizer_npc`), which is the form
  in which Thompson's normal `p`-complement theorem is consumed in this area.

The main theorem of the area is assembled in `Submission.Work.ThompsonFrobenius.Main` from
`Submission.Blueprint.ThompsonFrobeniusProp`'s two inputs: the solvability step
(`SolvabilityStep` in `Submission.Work.ThompsonFrobenius.Defs`) and the delivered solvable case.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

open Work.NPC.Fpf

variable {G : Type*}

/-- **Thompson's theorem, order two case.**  A fixed-point-free automorphism of order two inverts
every element (the finite group is a disjoint union of 2-element orbits under `α`), hence the
group is commutative, hence nilpotent. -/
theorem isNilpotent_of_orderOf_eq_two [Group G] [Finite G] {α : MulAut G}
    (h2 : orderOf α = 2) (hfpf : IsFpf α) : Group.IsNilpotent G := by
  have hα2 : α ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one α
  have hαα : ∀ x : G, α (α x) = x := by
    intro x
    have h : (α ^ 2) x = x := by rw [hα2]; rfl
    simpa [pow_two, MulAut.mul_apply] using h
  -- `α` inverts every element: every `y` is `x⁻¹ * α x` (the commutator map is bijective).
  have hinv : ∀ y : G, α y = y⁻¹ := by
    intro y
    obtain ⟨x, hx⟩ := (Work.Frobenius.Fpf.isFpf_mulInv_bijective hfpf).2 y
    have hxy : x⁻¹ * α x = y := hx
    calc α y = α (x⁻¹ * α x) := by rw [hxy]
      _ = (α x)⁻¹ * α (α x) := by rw [map_mul, map_inv]
      _ = (α x)⁻¹ * x := by rw [hαα x]
      _ = (x⁻¹ * α x)⁻¹ := by group
      _ = y⁻¹ := by rw [hxy]
  -- commutativity
  have hcomm : ∀ x y : G, x * y = y * x := by
    intro x y
    have h1 : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by rw [← hinv (x * y), map_mul, hinv x, hinv y]
    have h2' : y⁻¹ * x⁻¹ = x⁻¹ * y⁻¹ := by rw [← mul_inv_rev x y, h1]
    calc x * y = (y⁻¹ * x⁻¹)⁻¹ := by group
      _ = (x⁻¹ * y⁻¹)⁻¹ := by rw [h2']
      _ = y * x := by group
  haveI : IsMulCommutative G := isMulCommutative_iff.mpr hcomm
  infer_instance

/-- The solvable case of Thompson's theorem (the delivered
`Work.Frobenius.Fpf.isNilpotent_of_fpf_prime`). -/
theorem isNilpotent_of_fpf_of_solvable [Group G] [Finite G] [Group.IsSolvable G] {α : MulAut G}
    (hprime : (orderOf α).Prime) (hfpf : IsFpf α) : Group.IsNilpotent G :=
  Work.Frobenius.Fpf.isNilpotent_of_fpf_prime hprime (pow_orderOf_eq_one α) hfpf

/-- **Thompson's theorem for groups of odd order**, via `FeitThompsonProp` (odd order
⇒ solvable) and the delivered solvable case. -/
theorem isNilpotent_of_fpf_of_odd (hFT : Submission.Blueprint.FeitThompsonProp) {G : Type}
    [Group G] [Finite G] {α : MulAut G} (hprime : (orderOf α).Prime) (hfpf : IsFpf α)
    (hodd : Odd (Nat.card G)) : Group.IsNilpotent G := by
  haveI : Group.IsSolvable G := hFT G hodd
  exact isNilpotent_of_fpf_of_solvable hprime hfpf

/-- **The normal `p`-complement criterion** used for Thompson's theorem: if `N_G(Q)` has a normal
`p`-complement for every non-trivial `p`-subgroup `Q ≤ G`, then so does `G`
(`Work.NPC.npc_of_normalizer_npc`). -/
theorem hasNormalPComplement_of_normalizers [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : ∀ A : Subgroup G, IsPGroup p A → A ≠ ⊥ →
      Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (A : Set G))) :
    Work.NPC.HasNormalPComplement p G :=
  Work.NPC.npc_of_normalizer_npc hp h

end Work.ThompsonFrobenius
