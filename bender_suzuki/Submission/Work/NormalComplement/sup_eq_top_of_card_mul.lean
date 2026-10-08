import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- If `H` and `N` are subgroups of a finite group `G` with trivial intersection and
`|H| * |N| = |G|`, then together they generate `G`.

The proof exhibits an injection `H × N → G`, `(h, n) ↦ h * n`, whose image lies in
`H ⊔ N`; injectivity uses `H ⊓ N = ⊥`.  Hence `|H| * |N| ≤ |H ⊔ N| ≤ |G| = |H| * |N|`,
so `|H ⊔ N| = |G|` and a subgroup with as many elements as the whole group is everything. -/
theorem sup_eq_top_of_card_mul {G : Type*} [Group G] [Fintype G] {H N : Subgroup G}
    (hbot : H ⊓ N = ⊥) (hcard : Nat.card ↥H * Nat.card ↥N = Nat.card G) : H ⊔ N = ⊤ := by
  -- The multiplication map `H × N → G`, whose image lies in `H ⊔ N`.
  let f : ↥H × ↥N → ↥(H ⊔ N) :=
    fun a => ⟨(a.1 : G) * a.2, mul_mem (Subgroup.mem_sup_left a.1.2) (Subgroup.mem_sup_right a.2.2)⟩
  -- It is injective because `H ⊓ N = ⊥`.
  have hinj : Function.Injective f := by
    intro a b hab
    have h : (a.1 : G) * a.2 = b.1 * b.2 := congrArg Subtype.val hab
    -- Rearranged: `b.1⁻¹ * a.1 = b.2 * a.2⁻¹`, an element of `H ⊓ N = ⊥`, so it is `1`.
    have key : (b.1 : G)⁻¹ * a.1 = b.2 * (a.2)⁻¹ := by
      have hh := congrArg (fun x => (b.1 : G)⁻¹ * x * (a.2 : G)⁻¹) h
      simpa [mul_assoc] using hh
    have hmem : (b.1 : G)⁻¹ * a.1 ∈ H ⊓ N := by
      refine ⟨?_, ?_⟩
      · exact H.mul_mem (H.inv_mem b.1.2) a.1.2
      · rw [key]; exact N.mul_mem b.2.2 (N.inv_mem a.2.2)
    rw [hbot] at hmem
    have hone : (b.1 : G)⁻¹ * a.1 = 1 := by simpa using hmem
    have ha : a.1 = b.1 := Subtype.ext (inv_mul_eq_one.mp hone).symm
    have hb : a.2 = b.2 := by
      have h2 : (a.1 : G) * a.2 = a.1 * b.2 := by rw [h, ha]
      exact Subtype.ext (mul_left_cancel h2)
    exact Prod.ext ha hb
  -- Cardinality count: `|H| * |N| = |H × N| ≤ |H ⊔ N|`.
  have hle : Nat.card ↥H * Nat.card ↥N ≤ Nat.card ↥(H ⊔ N) := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective f hinj
  have hcardK : Nat.card ↥(H ⊔ N) = Nat.card G := by
    apply le_antisymm (Subgroup.card_le_card_group _)
    rw [← hcard]; exact hle
  exact Subgroup.eq_top_of_card_eq _ hcardK

end Work.NormalComplement
