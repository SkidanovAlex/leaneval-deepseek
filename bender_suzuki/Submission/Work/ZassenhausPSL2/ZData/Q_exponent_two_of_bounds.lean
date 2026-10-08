import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.ZData.Q_exponent_two_of_bounds`

For a finite abelian `2`-subgroup `Q` of a finite group `G`, if the number `D` of involutions
of `Q` satisfies the bound `2 * D + 1 ≥ |Q|`, then `Q` is elementary abelian
(`∀ x : Q, x ^ 2 = 1`).

The argument is elementary and does not use the `2`-group hypothesis (it is only asked for):
the set `S = {x : Q | x ^ 2 = 1}` is a subgroup (here the commutativity of `Q` is used, and it
is essential: the bound holds for the dihedral group `D₈` of order `8`, which has `6` elements
with `x ^ 2 = 1` and `5` involutions, but is not of exponent two).  Its complement of the
identity is exactly the set of elements of order two, which the coercion `Q → G` identifies
with the involutions `Inv(Q) ⊆ G`, so `|S| = D + 1`.  If `S` were proper, `[Q : S] ≥ 2` would
give `|Q| ≥ 2|S| = 2D + 2 > 2D + 1`, contradicting the bound.  Hence `S = Q`, i.e. every
element of `Q` has `x ^ 2 = 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Work.ZassenhausPSL2.ZData

theorem Q_exponent_two_of_bounds {G : Type} [Group G] [Finite G] (Q : Subgroup G)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) (D : ℕ)
    (hcard : D = (Submission.Blueprint.involutions (Q : Set G)).ncard)
    (hbound : 2 * D + 1 ≥ Nat.card Q) :
    ∀ x : Q, x ^ 2 = 1 := by
  -- The subgroup of elements of order dividing two.
  let S : Subgroup Q :=
    { carrier := {x : Q | x ^ 2 = 1}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        have hc : x * y = y * x := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          exact hab x x.2 y y.2
        rw [Commute.mul_pow hc, hx, hy, mul_one]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [inv_pow, hx, inv_one] }
  have hS : ∀ x : Q, x ∈ S ↔ x ^ 2 = 1 := fun x => Iff.rfl
  have hmem1 : (1 : Q) ∈ (S : Set Q) := by simp [S]
  -- `S \ {1}` is the set of involutions of `Q`, transported along `Q ↪ G`.
  have hbij : ((S : Set Q) \ {(1 : Q)}).ncard
      = (Submission.Blueprint.involutions (Q : Set G)).ncard := by
    refine Set.ncard_congr (fun a _ => (a : G)) ?_ ?_ ?_
    · intro a ha
      obtain ⟨haS, ha1⟩ := ha
      have ha2 : a ^ 2 = 1 := (hS a).mp haS
      have hne : a ≠ 1 := by simpa [Set.mem_singleton_iff] using ha1
      refine ⟨a.2, ?_⟩
      rw [Subgroup.orderOf_coe]
      have hdvd : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr ha2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hne
      · exact h
    · intro a b _ _ hab'
      exact Subtype.ext hab'
    · intro b hb
      obtain ⟨hbQ, hborder⟩ := hb
      refine ⟨⟨b, hbQ⟩, ?_, rfl⟩
      refine ⟨?_, ?_⟩
      · exact (hS ⟨b, hbQ⟩).mpr (by
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          rw [← hborder]
          exact pow_orderOf_eq_one b)
      · intro h
        have hb1 : b = 1 := congrArg Subtype.val h
        rw [hb1, orderOf_one] at hborder
        exact absurd hborder (by norm_num)
  -- hence `|S| = D + 1`.
  have hAcard : (S : Set Q).ncard = D + 1 := by
    have hdiff : ((S : Set Q) \ {(1 : Q)}).ncard = (S : Set Q).ncard - 1 :=
      Set.ncard_sdiff_singleton_of_mem hmem1
    rw [hbij] at hdiff
    have hpos : 0 < (S : Set Q).ncard := by
      rw [Set.ncard_pos]
      exact ⟨1, hmem1⟩
    omega
  have hSD : Nat.card S = D + 1 := by
    calc Nat.card S = (S : Set Q).ncard := Nat.card_coe_set_eq (S : Set Q)
      _ = D + 1 := hAcard
  by_cases htop : S = ⊤
  · intro x
    have hxS : x ∈ S := by rw [htop]; exact Subgroup.mem_top x
    exact (hS x).mp hxS
  · -- a proper `S` would force `|Q| ≥ 2|S| = 2D + 2`, contradicting the bound.
    exfalso
    have hmul : Nat.card S * S.index = Nat.card Q := Subgroup.card_mul_index S
    have hidx_ne1 : S.index ≠ 1 := fun h => htop ((Subgroup.index_eq_one).mp h)
    have hidx_ne0 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hidx_ge2 : 2 ≤ S.index := by omega
    have hle : 2 * Nat.card S ≤ Nat.card Q := by
      rw [← hmul]
      calc 2 * Nat.card S = Nat.card S * 2 := by ring
        _ ≤ Nat.card S * S.index := Nat.mul_le_mul_left _ hidx_ge2
    omega

end Work.ZassenhausPSL2.ZData
