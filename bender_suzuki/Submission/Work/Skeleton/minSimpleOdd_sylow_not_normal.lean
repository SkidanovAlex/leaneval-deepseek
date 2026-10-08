import Mathlib
import Submission.Work.Skeleton.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A0 — No Sylow subgroup of a minimal counterexample is normal

In a minimal counterexample `G` (a finite simple nonabelian group of odd order all of whose
proper subgroups are solvable), for every prime `p` dividing `|G|` no Sylow `p`-subgroup of
`G` is normal.

Indeed, a normal subgroup of a simple group is trivial or the whole group.  If a Sylow
`p`-subgroup `P` were normal then `P = ⊥` or `P = ⊤`.  In the first case `|P| = 1`, but
`P.index` is prime to `p` while `p ∣ |G| = P.index * |P|`, so `p ∣ |P| = 1`, absurd.  In the
second case `G` itself is a `p`-group, hence nilpotent and solvable, contradicting the
non-solvability of a minimal counterexample.
-/

set_option linter.style.haveILetI false

namespace Work.Skeleton

/-- For a prime `p` dividing `|G|`, a Sylow `p`-subgroup of `G` has order divisible by `p`
(equivalently, is nontrivial): its index is prime to `p` while `p ∣ |G|`. -/
theorem sylow_order_dvd_of_dvd_card {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hp : p ∣ Nat.card G) : p ∣ Nat.card (P : Subgroup G) := by
  have hnd : ¬ p ∣ (P : Subgroup G).index := P.not_dvd_index
  have hmul : p ∣ (P : Subgroup G).index * Nat.card (P : Subgroup G) := by
    rw [Subgroup.index_mul_card]; exact hp
  rcases (Fact.out : p.Prime).dvd_mul.mp hmul with h1 | h2
  · exact absurd h1 hnd
  · exact h2

theorem minSimpleOdd_sylow_not_normal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (h : MinSimpleOdd G) (P : Sylow p G) (hp : p ∣ Nat.card G) : ¬ P.Normal := by
  intro hPN
  have hN : (P : Subgroup G).Normal := hPN
  haveI := hN
  rcases h.normal_eq_bot_or_eq_top (P : Subgroup G) with hbot | htop
  · -- `P = ⊥` would force `p ∣ 1`
    have hcard : Nat.card (P : Subgroup G) = 1 := by rw [hbot]; simp
    have hdvd : p ∣ Nat.card (P : Subgroup G) := sylow_order_dvd_of_dvd_card P hp
    rw [hcard] at hdvd
    exact (Fact.out : p.Prime).not_dvd_one hdvd
  · -- `P = ⊤` makes `G` a `p`-group, hence solvable, a contradiction
    have hpg : IsPGroup p G := by
      rw [IsPGroup.iff_card]
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
      exact ⟨n, by rw [← hn, htop]; simp⟩
    have hnotpg : ¬ IsPGroup p G := by
      intro hpg'
      haveI : Group.IsNilpotent G := hpg'.isNilpotent
      haveI : Group.IsSolvable G := inferInstance
      exact h.not_solvable inferInstance
    exact hnotpg hpg

end Work.Skeleton
