import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA.BranchTwo

theorem ncard_modEq_fixed_of_prime_normalizer {G : Type} [Group G] [Finite G]
    {P : Subgroup G} (hp : (Nat.card P).Prime) (X : Set G)
    (hN : ∀ p ∈ P, ∀ x ∈ X, p * x * p⁻¹ ∈ X) :
    X.ncard ≡ (X ∩ {x : G | ∀ p ∈ P, p * x * p⁻¹ = x}).ncard [MOD Nat.card P] := by
  haveI : Fact (Nat.card P).Prime := ⟨hp⟩
  haveI hPG : IsPGroup (Nat.card P) P := IsPGroup.of_card (n := 1) (by simp)
  let Y : Set G := X ∩ {x : G | ∀ p ∈ P, p * x * p⁻¹ = x}
  change X.ncard ≡ Y.ncard [MOD Nat.card P]
  -- The conjugation action of `P` on the element set `X`, which is `P`-invariant by `hN`.
  letI smulX : SMul P ↥X := ⟨fun q x => ⟨(q : G) * (x : G) * (q : G)⁻¹, hN q q.2 x x.2⟩⟩
  have h1 : ∀ x : ↥X, (1 : P) • x = x := by
    intro x; apply Subtype.ext; change (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G); simp
  have hmul : ∀ q r : P, ∀ x : ↥X, (q * r) • x = q • (r • x) := by
    intro q r x; apply Subtype.ext
    change ((q : G) * (r : G)) * (x : G) * ((q : G) * (r : G))⁻¹ =
      (q : G) * ((r : G) * (x : G) * (r : G)⁻¹) * (q : G)⁻¹
    group
  letI : MulAction P ↥X := { one_smul := h1, mul_smul := hmul }
  -- `P` is a `p`-group acting on the finite set `X`, so fixed points count the same mod `p`.
  have key := hPG.card_modEq_card_fixedPoints ↥X
  have hcard : Nat.card (MulAction.fixedPoints P ↥X) = Nat.card ↥Y := by
    apply Nat.card_congr
    refine { toFun := fun z => ⟨z.1.1, ⟨z.1.2, ?_⟩⟩,
             invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩,
             left_inv := fun z => Subtype.ext rfl,
             right_inv := fun y => Subtype.ext rfl }
    · intro p hp
      exact congrArg Subtype.val ((MulAction.mem_fixedPoints.mp z.2) ⟨p, hp⟩)
    · rw [MulAction.mem_fixedPoints]
      intro q
      apply Subtype.ext
      change (q : G) * y.1 * (q : G)⁻¹ = y.1
      exact y.2.2 q.1 q.2
  rw [← Nat.card_coe_set_eq X, ← Nat.card_coe_set_eq Y, ← hcard]
  exact key

end Work.PSU3.StageA.BranchTwo
