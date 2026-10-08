import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.CharCore.Defs
import Submission.Work.Induction.Defs
import Submission.Work.Coherence.Defs
import Submission.Work.ZassenhausPSL2.Feit.card_excl
import Submission.Work.ZassenhausPSL2.ZData.three_le_card_twoPoint
import Submission.Work.ZassenhausTwoGroup.even_card_Q
import Submission.Work.ZassenhausPSL2.FeitCln.exists_exceptional
import Submission.Work.ZassenhausPSL2.Feit.exceptional_res
import Submission.Work.ZassenhausPSL2.Feit.final_ineq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Classical
open Submission.Blueprint

namespace Work.ZassenhausPSL2.FeitCln

open Work.ZassenhausPSL2.Feit

/-!
# `Work.ZassenhausPSL2.FeitCln.card_excl_eq_one` (Feit's leaf F8)

In a split rank-one Zassenhaus configuration `(H, Q, t)` with `Q` an abelian `2`-group inside a
finite simple group `G`, the set `𝒮 = excludingKernel H Q = {χ ∈ Irr H | Q ⊄ ker χ}` has exactly
one element.

Writing `k = |𝒮|`, `d = |D|` (`D = twoPoint H t = H ∩ Hᵗ`) and `m = |Q|`, the inputs are

* `card_excl` (F2b): `k · d = m - 1`;
* `d ≥ 3` (`three_le_card_twoPoint`), `d` odd (strong embedding), `m` even (a `2`-group):
  hence `m - 1` is odd and, since `k · d = m - 1`, `k` is odd;
* `exists_exceptional` (F5), `exceptional_res` (F6), `final_ineq` (F7): if `2 ≤ k`, there is an
  irreducible `ξ` of `G` with `ξ|_H = χ₁` for some `χ₁ ∈ 𝒮`, and then
  `2 + (d - 1)(m + 1) ≤ 2 d²`.

If `2 ≤ k`, oddness gives `k ≥ 3`, so `m - 1 = k d ≥ 3 d` and `m + 1 ≥ 3 d + 2`; with `d ≥ 3`
the inequality of F7 reads `2 + (d - 1)(3d + 2) ≤ 2 d²`, i.e. `d² ≤ d`, contradicting `d ≥ 3`.
Hence `k ≤ 1`; and `k ≥ 1` because `k · d = m - 1 ≠ 0`.
-/

/-- An even positive natural number is at least `2`. -/
private theorem two_le_of_even_pos {m : ℕ} (hm : Even m) (hpos : 0 < m) : 2 ≤ m := by
  rcases hm with ⟨j, hj⟩
  omega

/-- An even positive natural number minus one is odd. -/
private theorem odd_sub_one_of_even {m : ℕ} (hm : Even m) (hpos : 0 < m) : Odd (m - 1) := by
  obtain ⟨j, hj⟩ := hm
  exact ⟨j - 1, by omega⟩

/-- **The arithmetic core of F8.**  For `d ≥ 3`, `2 + (d - 1)(3d + 2) > 2 d²`. -/
private theorem not_le_arith {d : ℕ} (hd : 3 ≤ d) :
    ¬ (2 + (d - 1) * (3 * d + 2) ≤ 2 * d * d) := by
  intro h
  have hd1 : 1 ≤ d := by omega
  have hcast : (2 : ℤ) + ((d : ℤ) - 1) * (3 * (d : ℤ) + 2) ≤ 2 * (d : ℤ) * (d : ℤ) := by
    have h' : ((2 + (d - 1) * (3 * d + 2) : ℕ) : ℤ) ≤ ((2 * d * d : ℕ) : ℤ) := by
      exact_mod_cast h
    push_cast at h'
    rw [Nat.cast_sub hd1, Nat.cast_one] at h'
    exact h'
  have hx : (3 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  nlinarith [hcast, hx]

theorem card_excl_eq_one {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    [IsSimpleGroup G] (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hz : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q) :
    (Submission.Blueprint.excludingKernel H Q).card = 1 := by
  classical
  -- ## The two inputs of the count
  have hcard : (excludingKernel H Q).card * Nat.card (twoPoint H t) = Nat.card Q - 1 :=
    card_excl h hz h2 hab
  have hd_odd : Odd (Nat.card (twoPoint H t)) :=
    Work.ZassenhausPSL2.dStab_odd H t h.stronglyEmbedded h.not_mem
  have hm_even : Even (Nat.card Q) := Work.ZassenhausTwoGroup.even_card_Q h
  have hm_pos : 0 < Nat.card Q := Nat.card_pos
  have hm1_odd : Odd (Nat.card Q - 1) := odd_sub_one_of_even hm_even hm_pos
  -- ## `k` is odd
  have hk_odd : Odd (excludingKernel H Q).card := by
    rcases Nat.even_or_odd (excludingKernel H Q).card with he | ho
    · exfalso
      have h2e : Even ((excludingKernel H Q).card * Nat.card (twoPoint H t)) :=
        Even.mul_right he _
      rw [hcard] at h2e
      exact (Nat.not_even_iff_odd.mpr hm1_odd) h2e
    · exact ho
  -- ## `1 ≤ k`
  have hk_one : 1 ≤ (excludingKernel H Q).card := by
    by_contra hlt
    have hk0 : (excludingKernel H Q).card = 0 := by omega
    rw [hk0, zero_mul] at hcard
    have : 2 ≤ Nat.card Q := two_le_of_even_pos hm_even hm_pos
    omega
  -- ## `¬ 2 ≤ k`
  have hk_le : ¬ (2 ≤ (excludingKernel H Q).card) := by
    intro hk
    -- an element of `𝒮`, and the exceptional character it produces
    obtain ⟨χ₁, hχ₁⟩ := Finset.card_pos.mp (show 0 < (excludingKernel H Q).card by omega)
    obtain ⟨ξ, hξ, h1, h0⟩ := Work.ZassenhausPSL2.FeitCln.exists_exceptional h hz h2 hab hk hχ₁
    have hres : ∀ x : H, ξ x = χ₁ x := exceptional_res h hz h2 hab hk hχ₁ hξ h1 h0
    have hF7 : 2 + (Nat.card (twoPoint H t) - 1) * (Nat.card Q + 1) ≤
        2 * Nat.card (twoPoint H t) * Nat.card (twoPoint H t) :=
      final_ineq h hz h2 hab hχ₁ hξ hres
    -- `3 ≤ k`
    obtain ⟨j, hj⟩ := hk_odd
    have hk3 : 3 ≤ (excludingKernel H Q).card := by omega
    -- `3 d ≤ m - 1` and `3 d + 2 ≤ m + 1`
    have hmul : 3 * Nat.card (twoPoint H t) ≤ Nat.card Q - 1 := by
      rw [← hcard]
      exact Nat.mul_le_mul_right _ hk3
    have hm1 : 3 * Nat.card (twoPoint H t) + 2 ≤ Nat.card Q + 1 := by omega
    -- the two-point stabiliser has order at least `3`
    have hd3 : 3 ≤ Nat.card (twoPoint H t) :=
      Work.ZassenhausPSL2.ZData.three_le_card_twoPoint h hz
    -- combine F7 with the monotonicity in `m`
    have hmono : (Nat.card (twoPoint H t) - 1) * (3 * Nat.card (twoPoint H t) + 2) ≤
        (Nat.card (twoPoint H t) - 1) * (Nat.card Q + 1) :=
      Nat.mul_le_mul_left _ hm1
    have hcomb : 2 + (Nat.card (twoPoint H t) - 1) * (3 * Nat.card (twoPoint H t) + 2) ≤
        2 * Nat.card (twoPoint H t) * Nat.card (twoPoint H t) :=
      le_trans (Nat.add_le_add_left hmono 2) hF7
    exact not_le_arith hd3 hcomb
  omega

end Work.ZassenhausPSL2.FeitCln
