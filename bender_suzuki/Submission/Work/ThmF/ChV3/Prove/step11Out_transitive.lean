import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

theorem step11Out_transitive {G : Type} [Group G] [Finite G]
    {T D : Subgroup G} (hcardD : Nat.card ↥D = Nat.card ↥T - 1)
    (hDT : D ≤ Subgroup.normalizer (T : Set G))
    (hfree : ∀ y ∈ D, ∀ x ∈ T, x ≠ 1 → y * x * y⁻¹ = x → y = 1) :
    ∀ w ∈ T, w ≠ 1 → ∀ z ∈ T, z ≠ 1 → ∃ y ∈ D, y * w * y⁻¹ = z := by
  classical
  -- `D` acts on the set `X` of nonidentity elements of `T` by conjugation.
  -- The action is free, so every orbit has exactly `|D| = |T| - 1 = |X|` elements,
  -- hence there can be only one orbit: the action is transitive.
  intro w hwT hw1 z hzT hz1
  -- the set of nonidentity elements of `T`
  set X : Set G := (T : Set G) \ {1} with hXdef
  have hXmem : ∀ x : G, x ∈ X ↔ x ∈ T ∧ x ≠ 1 := by
    intro x; rw [hXdef]; simp
  have hTncard : (T : Set G).ncard = Nat.card ↥T := (Nat.card_coe_set_eq (T : Set G)).symm
  have hXcard : X.ncard = Nat.card ↥D := by
    rw [hXdef, Set.ncard_sdiff (s := ({1} : Set G)) (t := (T : Set G)) (by simp),
        Set.ncard_singleton, hTncard, hcardD]
  -- the conjugation map `y ↦ y * w * y⁻¹` on `D`
  let f : ↥D → G := fun y => y.1 * w * y.1⁻¹
  -- it takes values in `X`
  have hf_mem : ∀ y : ↥D, f y ∈ X := by
    intro y
    rw [hXmem]
    refine ⟨?_, ?_⟩
    · have hyN : (y : G) ∈ Subgroup.normalizer (T : Set G) := hDT y.2
      exact (Subgroup.mem_normalizer_iff.mp hyN w).mp hwT
    · intro h
      apply hw1
      have hthis : w = y.1⁻¹ * f y * y.1 := by simp only [f]; group
      rw [h] at hthis
      simpa using hthis
  -- it is injective, because the action is free
  have hf_inj : Function.Injective f := by
    intro y1 y2 hy
    have hval : y1.1 * w * y1.1⁻¹ = y2.1 * w * y2.1⁻¹ := hy
    have hcw : (y2.1⁻¹ * y1.1) * w * (y2.1⁻¹ * y1.1)⁻¹ = w := by
      have heq : (y2.1⁻¹ * y1.1) * w * (y2.1⁻¹ * y1.1)⁻¹
          = y2.1⁻¹ * (y1.1 * w * y1.1⁻¹) * y2.1 := by group
      rw [heq, hval]; group
    have hc1 : y2.1⁻¹ * y1.1 = 1 :=
      hfree (y2.1⁻¹ * y1.1) (D.mul_mem (D.inv_mem y2.2) y1.2) w hwT hw1 hcw
    apply Subtype.ext
    show y1.1 = y2.1
    calc y1.1 = y2.1 * (y2.1⁻¹ * y1.1) := by group
      _ = y2.1 := by rw [hc1, mul_one]
  -- counting: the image has `|D| = |X|` elements and is contained in `X`, so it is all of `X`
  have hrange : Set.range f = X := by
    apply Set.eq_of_subset_of_ncard_le
    · rw [Set.range_subset_iff]; exact hf_mem
    · rw [Set.ncard_range_of_injective hf_inj, hXcard]
    · exact Set.toFinite X
  have hzX : z ∈ X := (hXmem z).mpr ⟨hzT, hz1⟩
  rw [← hrange] at hzX
  obtain ⟨y, hy⟩ := Set.mem_range.mp hzX
  exact ⟨y.1, y.2, hy⟩

end Work.ThmF.ChV3.Prove
