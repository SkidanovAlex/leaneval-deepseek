/-
# Frobenius' hypothesis at `p = 2` for a cyclic Sylow `2`-subgroup

If a finite group `G` has a cyclic Sylow `2`-subgroup `S`, then `G` satisfies Frobenius'
hypothesis for `p = 2`: for every non-identity `2`-subgroup `Q ≤ G` the quotient
`N_G(Q)/C_G(Q)` is a `2`-group.

The mathematical content is the following chain of remarks.

* Every `2`-subgroup `Q ≤ G` lies in a Sylow `2`-subgroup of `G` (Sylow's first theorem) and
  all Sylow `2`-subgroups of `G` are conjugate (Sylow's second theorem); since `S` is cyclic,
  every Sylow `2`-subgroup of `G` is cyclic, hence `Q` is cyclic.
* Conjugation gives a homomorphism `N_G(Q) →* MulAut Q` whose kernel is `C_G(Q)`; consequently
  `N_G(Q)/C_G(Q)` is isomorphic to a subgroup of `Aut(Q)`, so its order divides `|Aut(Q)|`.
* For a cyclic group the automorphism group is isomorphic to the unit group of `ℤ/n` with
  `n = |Q|` (Mathlib: `IsCyclic.mulAutMulEquiv`, `IsCyclic.card_mulAut`).  Since `Q` is a
  `2`-group, `|Q| = 2 ^ k`, and `φ(2 ^ k) = 2 ^ (k - 1)` is a power of `2`.

Hence `|N_G(Q)/C_G(Q)|` divides `2 ^ (k - 1)`, so `N_G(Q)/C_G(Q)` is a `2`-group.

This is the easy half of the Brauer–Suzuki setting: for `Q` non-cyclic (e.g. `Q` a Klein
four group) the automorphism group has odd order part and the conclusion fails.
-/
import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open scoped Pointwise

namespace Work.BrauerSuzuki.Sylow

variable {G : Type*} [Group G]

/-- The Euler totient function of a power of two: `φ (2 ^ k) = 2 ^ (k - 1)`. -/
lemma totient_two_pow (k : ℕ) : (2 ^ k).totient = 2 ^ (k - 1) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  · rw [Nat.totient_prime_pow (by norm_num : Nat.Prime 2) hk]
    norm_num

/-- Conjugation gives a homomorphism `N_G(Q) →* MulAut Q` with kernel `C_G(Q)`; hence
`N_G(Q)/C_G(Q)` embeds into `Aut(Q)` and the order of `N_G(Q)/C_G(Q)` divides the order of
`Aut(Q)`. -/
lemma card_normalizerQuotientCentralizer_dvd_card_mulAut (Q : Subgroup G) :
    Nat.card (Subgroup.normalizer (Q : Set G) ⧸
        (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)))
      ∣ Nat.card (MulAut ↥Q) := by
  have h := Subgroup.card_subgroup_dvd_card (Subgroup.normalizerMonoidHom Q).range
  rw [← Subgroup.normalizerMonoidHom_ker Q,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (Subgroup.normalizerMonoidHom Q)).toEquiv]
  exact h

/-- If a Sylow `2`-subgroup of the finite group `G` is cyclic, then every `2`-subgroup of `G`
is cyclic (it is contained in some Sylow `2`-subgroup, and all of those are conjugate). -/
lemma isCyclic_of_isPGroup_two_of_cyclic_sylow [Finite G]
    (S : Sylow 2 G) (hS : IsCyclic ↥S) (Q : Subgroup G) (hQ : IsPGroup 2 Q) : IsCyclic ↥Q := by
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  have hSP : IsCyclic ↥(P : Subgroup G) := ((Sylow.equiv P S).isCyclic).mpr hS
  exact @Subgroup.isCyclic_of_le G _ Q (P : Subgroup G) hP hSP

theorem hasFrobeniusCondition_two_of_cyclic_sylow {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : IsCyclic ↥S) : Work.NPC.HasFrobeniusCondition 2 G := by
  intro Q hQ _
  show IsPGroup 2 (Subgroup.normalizer (Q : Set G) ⧸
    (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)))
  have hQcyc : IsCyclic ↥Q := isCyclic_of_isPGroup_two_of_cyclic_sylow S hS Q hQ
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  refine IsPGroup.of_card_dvd_pow (n := k - 1) ?_
  have h := card_normalizerQuotientCentralizer_dvd_card_mulAut Q
  rwa [@IsCyclic.card_mulAut ↥Q _ _ hQcyc, hk, totient_two_pow] at h

end Work.BrauerSuzuki.Sylow
