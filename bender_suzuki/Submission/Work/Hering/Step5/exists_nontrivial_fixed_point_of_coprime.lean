import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.Hering.Step5

/-- Let `A` be a group of prime order `p` acting by group automorphisms on a finite group `U`.
If `p ∤ |U|` and `|U| ≢ 1 (mod p)`, then `A` has a nontrivial fixed point in `U`.

The proof is a counting argument. `A` is a `p`-group, so for its action on the finite set `U`
the number of fixed points satisfies `|U| ≡ |U^A| (mod p)`
(`IsPGroup.card_modEq_card_fixedPoints`). If `|U^A| = 1` this would force `|U| ≡ 1 (mod p)`,
contradicting the hypothesis; since `1` is always fixed, `|U^A| ≥ 2` and a nontrivial fixed
point exists. -/
theorem exists_nontrivial_fixed_point_of_coprime {A U : Type*} [Group A] [Finite A] [Group U]
    [Finite U] [MulDistribMulAction A U] (p : ℕ) (hp : p.Prime) (hA : Nat.card A = p)
    (hcop : ¬ p ∣ Nat.card U) (hU : 1 < Nat.card U) (hmod : Nat.card U % p ≠ 1) :
    ∃ u : U, u ≠ 1 ∧ ∀ a : A, a • u = u := by
  have hfact : Fact p.Prime := ⟨hp⟩
  -- `A` has order `p = p ^ 1`, hence is a `p`-group.
  have hpg : IsPGroup p A := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hA)
  -- Counting mod `p`: `|U| ≡ |U^A|`.
  have hcong : Nat.card U ≡ Nat.card (MulAction.fixedPoints A U) [MOD p] :=
    hpg.card_modEq_card_fixedPoints (hp := hfact) U
  -- The identity is a fixed point, so `U^A` is nonempty.
  have hone : (1 : U) ∈ MulAction.fixedPoints A U := by
    rw [MulAction.mem_fixedPoints]; intro a; exact smul_one a
  -- If `|U^A| = 1` then `|U| % p = 1`, contradicting `hmod`.
  have hne1 : Nat.card (MulAction.fixedPoints A U) ≠ 1 := by
    intro h1
    apply hmod
    rw [Nat.ModEq] at hcong
    rw [hcong, h1, Nat.mod_eq_of_lt hp.one_lt]
  have hpos : 0 < Nat.card (MulAction.fixedPoints A U) :=
    Finite.card_pos_iff.mpr ⟨⟨1, hone⟩⟩
  -- Hence `|U^A| ≥ 2`, giving two distinct fixed points, one of which differs from `1`.
  have hgt1 : 1 < Nat.card (MulAction.fixedPoints A U) := by omega
  have hnt : Nontrivial (MulAction.fixedPoints A U) :=
    Finite.one_lt_card_iff_nontrivial.mp hgt1
  obtain ⟨x, y, hxy⟩ := hnt.exists_pair_ne
  by_cases hx : (x : U) = 1
  · exact ⟨(y : U), by intro hy; exact hxy (Subtype.ext (by rw [hx, hy])),
      (MulAction.mem_fixedPoints).mp y.2⟩
  · exact ⟨(x : U), hx, (MulAction.mem_fixedPoints).mp x.2⟩

end Work.Hering.Step5
