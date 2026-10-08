import Mathlib
import Submission.Work.COPR.Defs
import Submission.Work.COPR.BenderDefs
import Submission.Work.COPR.card_mul_of_fibers
import Submission.Work.COPR.bender_map_surj
import Submission.Work.COPR.fiber_phi_card

namespace Work.COPR

open Subgroup

/-- Bender 1981, 1.5(i)+(ii): if an involution `s` acts on a `2'`-group `X` (i.e. `X` has odd
order and `s` normalizes it), then the inversion set `I_X(s) = {x ∈ X | x^s = x⁻¹}` is the set of
"generators" `x⁻¹·x^s`, `x ∈ X`, and `|I_X(s)|·|C_X(s)| = |X|`.
(Deliverable `Work.GW2.Coprime15Prop`, first two conjuncts, of area COPR.) -/
theorem coprime15_gen (G : Type) [Group G] [Finite G] (X : Subgroup G) (s : G)
    (hs : orderOf s = 2) (hodd : Odd (Nat.card X))
    (hN : s ∈ Subgroup.normalizer (X : Set G)) :
    Work.GW2.invSet X s = {y | ∃ x ∈ X, y = x⁻¹ * (s * x * s⁻¹)} ∧
    (Work.GW2.invSet X s).ncard *
        Nat.card (X ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) = Nat.card X := by
  -- `s` has order two, so `s * s = 1`.
  have hs2 : s * s = 1 := by
    have h := (orderOf_eq_iff (by norm_num : 0 < 2)).mp hs
    simpa [pow_two] using h.1
  -- The inversion set is the image of Bender's map `phi`.
  have h1 : Work.GW2.invSet X s = ((↑) '' Set.range (phi X s hN) : Set G) := by
    ext y
    constructor
    · intro hy
      -- `y ∈ X` is inverted by `s`, so by oddness it is a value of `phi`.
      obtain ⟨x, hx⟩ := bender_map_surj (sigma X s hN) hodd ⟨y, hy.1⟩
        ((sigma_eq_inv_iff X s hN ⟨y, hy.1⟩).mpr hy.2)
      exact ⟨phi X s hN x, ⟨x, rfl⟩, congrArg Subtype.val hx⟩
    · rintro ⟨u, ⟨x, rfl⟩, rfl⟩
      exact ⟨(phi X s hN x).2, by
        have h := congrArg Subtype.val (sigma_phi X s hN hs2 x)
        simpa [sigma_coe, Subgroup.coe_inv] using h⟩
  -- Spelling out `phi` on elements of `G`.
  have h2 : ((↑) '' Set.range (phi X s hN) : Set G)
      = {y | ∃ x ∈ X, y = x⁻¹ * (s * x * s⁻¹)} := by
    ext y
    constructor
    · rintro ⟨u, ⟨x, hxu⟩, hyu⟩
      refine ⟨x, x.2, ?_⟩
      rw [← hyu, ← hxu, phi_coe]
    · rintro ⟨x, hx, hxy⟩
      refine ⟨phi X s hN ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
      rw [phi_coe]
      exact hxy.symm
  constructor
  · rw [h1, h2]
  · -- Counting: the fibres of `phi` are the cosets of `C_X(s)`.
    have hI : (Work.GW2.invSet X s).ncard
        = Nat.card ↥(Set.range (phi X s hN)) := by
      rw [h1, Nat.card_coe_set_eq]
      exact Set.ncard_image_of_injective (Set.range (phi X s hN)) Subtype.val_injective
    rw [hI]
    refine (card_mul_of_fibers
      (f := fun v : X => (⟨phi X s hN v, ⟨v, rfl⟩⟩ :
          ↥(Set.range (phi X s hN))))
      (k := Nat.card (X ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G)) ?_).symm
    intro b
    obtain ⟨x₀, hx₀⟩ := b.2
    have hset : {u : X | (⟨phi X s hN u, ⟨u, rfl⟩⟩ :
          ↥(Set.range (phi X s hN))) = b}
        = {u : X | phi X s hN u = phi X s hN x₀} := by
      ext u
      constructor
      · intro h
        have := congrArg Subtype.val h
        simpa [hx₀] using this
      · intro h
        apply Subtype.ext
        simpa [hx₀] using h
    rw [hset]
    exact fiber_phi_card X s hN x₀

end Work.COPR
