import Submission.Work.Skeleton.Basic
import Submission.Work.Skeleton.odd_orderOf
import Submission.Work.Skeleton.eq_one_of_mul_self_eq_one
import Submission.Work.Skeleton.eq_one_of_conj_eq_inv
import Submission.Work.Skeleton.eq_one_of_isConj_inv
import Submission.Work.Skeleton.card_subgroup_lt_card
import Submission.Work.Skeleton.card_quotient_lt_card
import Submission.Work.Skeleton.odd_card_subgroup
import Submission.Work.Skeleton.odd_index
import Submission.Work.Skeleton.odd_card_quotient
import Submission.Work.Skeleton.odd_card_of_injective
import Submission.Work.Skeleton.minSimpleOdd_one_lt_card
import Submission.Work.Skeleton.minSimpleOdd_not_isCoatom_bot
import Submission.Work.Skeleton.minSimpleOdd_normalizer_lt_top
import Submission.Work.Skeleton.minSimpleOdd_normalizer_eq_self_of_isCoatom
import Submission.Work.Skeleton.minSimpleOdd_sylow_not_normal
import Submission.Work.Skeleton.odd_card_of_surjective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A0 — Skeleton: the `MinSimpleOdd` API

This module collects the usable API of the minimal-counterexample hypothesis
`Work.Skeleton.MinSimpleOdd`, on top of the elementary odd-order lemmas of this area.

Everything downstream of A0 (local analysis, coprime action, character theory) is carried
out under a hypothesis `h : MinSimpleOdd G` and uses the lemmas below to conclude that
subgroups/quotients have odd order and are solvable, that normal subgroups are trivial or
everything, that maximal subgroups are self-normalizing, and that no non-identity element
is an involution or is conjugate to its inverse.
-/

set_option linter.unusedVariables false

namespace Work.Skeleton

variable {G : Type*} [Group G] [Finite G]

/-! ### Order facts -/

/-- Every subgroup of a minimal counterexample has odd order. -/
theorem MinSimpleOdd.odd_card_subgroup (h : MinSimpleOdd G) (H : Subgroup G) :
    Odd (Nat.card H) := Work.Skeleton.odd_card_subgroup h.odd H

/-- Every subgroup of a minimal counterexample has odd index. -/
theorem MinSimpleOdd.odd_index (h : MinSimpleOdd G) (H : Subgroup G) : Odd H.index :=
  Work.Skeleton.odd_index h.odd H

/-- Every element of a minimal counterexample has odd order. -/
theorem MinSimpleOdd.odd_orderOf (h : MinSimpleOdd G) (x : G) : Odd (orderOf x) :=
  Work.Skeleton.odd_orderOf h.odd x

/-- Every quotient of a minimal counterexample has odd order. -/
theorem MinSimpleOdd.odd_card_quotient (h : MinSimpleOdd G) (N : Subgroup G) [N.Normal] :
    Odd (Nat.card (G ⧸ N)) := Work.Skeleton.odd_card_quotient h.odd N

/-- `1 < |G|` for a minimal counterexample. -/
theorem MinSimpleOdd.one_lt_card (h : MinSimpleOdd G) : 1 < Nat.card G :=
  minSimpleOdd_one_lt_card h

/-- Every proper subgroup of a minimal counterexample has strictly smaller order. -/
theorem MinSimpleOdd.card_subgroup_lt_card (h : MinSimpleOdd G) {H : Subgroup G} (hH : H ≠ ⊤) :
    Nat.card H < Nat.card G := Work.Skeleton.card_subgroup_lt_card H hH

/-- Every proper subgroup of a minimal counterexample has strictly smaller order. -/
theorem MinSimpleOdd.card_subgroup_lt_card' (h : MinSimpleOdd G) {H : Subgroup G} (hH : H < ⊤) :
    Nat.card H < Nat.card G := Work.Skeleton.card_subgroup_lt_card H hH.ne

/-! ### No involutions, no elements conjugate to their inverse -/

/-- A minimal counterexample has no involutions. -/
theorem MinSimpleOdd.eq_one_of_mul_self_eq_one (h : MinSimpleOdd G) {x : G} (hx : x * x = 1) :
    x = 1 := Work.Skeleton.eq_one_of_mul_self_eq_one h.odd hx

/-- Restatement: `x * x = 1 ↔ x = 1` in a minimal counterexample. -/
theorem MinSimpleOdd.mul_self_eq_one_iff (h : MinSimpleOdd G) {x : G} : x * x = 1 ↔ x = 1 :=
  ⟨h.eq_one_of_mul_self_eq_one, fun hx => by rw [hx, mul_one]⟩

/-- No non-identity element of a minimal counterexample is conjugate to its inverse. -/
theorem MinSimpleOdd.eq_one_of_isConj_inv (h : MinSimpleOdd G) {x : G} (hx : IsConj x x⁻¹) :
    x = 1 := Work.Skeleton.eq_one_of_isConj_inv h.odd hx

/-- No non-identity element of a minimal counterexample is conjugate to its inverse. -/
theorem MinSimpleOdd.not_isConj_inv (h : MinSimpleOdd G) {x : G} (hx : x ≠ 1) :
    ¬ IsConj x x⁻¹ := fun hc => hx (h.eq_one_of_isConj_inv hc)

/-! ### Normal subgroups, maximal subgroups, normalizers -/

/-- A nontrivial normal subgroup of a minimal counterexample is the whole group (convenience
restatement of `MinSimpleOdd.normal_eq_top_of_ne_bot`). -/
theorem MinSimpleOdd.normal_eq_top {G : Type*} [Group G] [Finite G] (h : MinSimpleOdd G)
    {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) : N = ⊤ := h.normal_eq_top_of_ne_bot hN

/-- A minimal counterexample has a proper nontrivial subgroup. -/
theorem MinSimpleOdd.exists_proper_nontrivial_subgroup (h : MinSimpleOdd G) :
    ∃ K : Subgroup G, K ≠ ⊥ ∧ K ≠ ⊤ := by
  have : Nontrivial G := h.nontrivial
  by_contra hcon
  refine minSimpleOdd_not_isCoatom_bot h ⟨?_, fun K hK => ?_⟩
  · intro hbot
    obtain ⟨a, ha⟩ : ∃ a : G, a ≠ 1 := exists_ne 1
    have : a ∈ (⊥ : Subgroup G) := by rw [hbot]; exact Subgroup.mem_top a
    exact ha (by simpa using this)
  · by_contra hKtop
    exact hcon ⟨K, fun hKbot => by rw [hKbot] at hK; exact (lt_irrefl ⊥) hK, hKtop⟩

/-- `⊥` is not a maximal subgroup of a minimal counterexample. -/
theorem MinSimpleOdd.not_isCoatom_bot (h : MinSimpleOdd G) : ¬ IsCoatom (⊥ : Subgroup G) :=
  minSimpleOdd_not_isCoatom_bot h

/-- Every maximal subgroup of a minimal counterexample is self-normalizing. -/
theorem MinSimpleOdd.normalizer_eq_self_of_isCoatom (h : MinSimpleOdd G) {M : Subgroup G}
    (hM : IsCoatom M) : Subgroup.normalizer (M : Set G) = M :=
  minSimpleOdd_normalizer_eq_self_of_isCoatom h hM

/-- Every maximal subgroup of a minimal counterexample is self-normalizing: restatement with
the maximality hypothesis spelled out. -/
theorem MinSimpleOdd.normalizer_eq_self_of_maximal (h : MinSimpleOdd G) {M : Subgroup G}
    (hlt : M ≠ ⊤) (hmax : ∀ K : Subgroup G, M < K → K = ⊤) :
    Subgroup.normalizer (M : Set G) = M :=
  h.normalizer_eq_self_of_isCoatom ⟨hlt, hmax⟩

/-- The normalizer of a nontrivial proper subgroup of a minimal counterexample is a proper
subgroup. -/
theorem MinSimpleOdd.normalizer_lt_top (h : MinSimpleOdd G) {H : Subgroup G} (hbot : H ≠ ⊥)
    (htop : H ≠ ⊤) : Subgroup.normalizer (H : Set G) < ⊤ :=
  minSimpleOdd_normalizer_lt_top h hbot htop

/-! ### The minimal counterexample is not a `p`-group -/

/-- A minimal counterexample is not a `p`-group: a finite `p`-group is nilpotent, hence
solvable, contradicting `MinSimpleOdd.not_solvable`. -/
theorem MinSimpleOdd.not_isPGroup {p : ℕ} [Fact p.Prime] (h : MinSimpleOdd G) :
    ¬ IsPGroup p G := by
  intro hp
  have : Group.IsNilpotent G := hp.isNilpotent
  have : Group.IsSolvable G := inferInstance
  exact h.not_solvable inferInstance

/-- No Sylow `p`-subgroup of a minimal counterexample is normal (when `p` divides `|G|`). -/
theorem MinSimpleOdd.sylow_not_normal {p : ℕ} [Fact p.Prime] (h : MinSimpleOdd G)
    (P : Sylow p G) (hp : p ∣ Nat.card G) : ¬ P.Normal :=
  minSimpleOdd_sylow_not_normal h P hp

/-- Every cyclic subgroup of a minimal counterexample is proper. -/
theorem MinSimpleOdd.zpowers_lt_top (h : MinSimpleOdd G) (x : G) : Subgroup.zpowers x < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  refine h.not_isMulCommutative ⟨⟨fun a b => ?_⟩⟩
  have ha : a ∈ Subgroup.zpowers x := htop ▸ Subgroup.mem_top a
  have hb : b ∈ Subgroup.zpowers x := htop ▸ Subgroup.mem_top b
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← zpow_add, ← zpow_add, add_comm]

/-- A minimal counterexample is not cyclic: a cyclic group is commutative. -/
theorem MinSimpleOdd.not_isCyclic (h : MinSimpleOdd G) : ¬ IsCyclic G := by
  intro hc
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hc
  exact absurd hx (h.zpowers_lt_top x).ne

/-! ### Solvability of proper subgroups and sections -/

/-- Every section of a proper subgroup of a minimal counterexample is solvable. -/
theorem MinSimpleOdd.solvable_quotient_of_lt_top (h : MinSimpleOdd G) {H : Subgroup G}
    (hH : H < ⊤) (N : Subgroup H) [N.Normal] : Group.IsSolvable (↥H ⧸ N) := by
  have : Group.IsSolvable H := h.solvable_of_lt_top hH
  exact inferInstance

/-- Every subgroup of a proper subgroup of a minimal counterexample is solvable. -/
theorem MinSimpleOdd.solvable_subgroup_of_lt_top (h : MinSimpleOdd G) {H : Subgroup G}
    (hH : H < ⊤) (K : Subgroup H) : Group.IsSolvable K := by
  have : Group.IsSolvable H := h.solvable_of_lt_top hH
  exact inferInstance

/-! ### Existence of maximal subgroups -/

/-- Every proper subgroup of a finite group is contained in a maximal proper subgroup. -/
theorem exists_isCoatom_subgroup_ge (G : Type*) [Group G] [Finite G] {H : Subgroup G}
    (hH : H < ⊤) : ∃ M : Subgroup G, H ≤ M ∧ IsCoatom M := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G))
      (fun A B h => Subgroup.ext fun x => by
        have hx := congrArg (fun (S : Set G) => x ∈ S) h
        simpa using hx)
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  have hne : (Finset.univ.filter (fun K : Subgroup G => H ≤ K ∧ K < ⊤)).Nonempty := by
    refine ⟨H, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_rfl, hH⟩
  obtain ⟨M, hMmem, hMmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun K : Subgroup G => H ≤ K ∧ K < ⊤)) (fun K => Nat.card K) hne
  obtain ⟨-, hHM, hMlt⟩ := Finset.mem_filter.mp hMmem
  refine ⟨M, hHM, hMlt.ne, fun K hK => ?_⟩
  by_contra hKtop
  have hKf : K ∈ Finset.univ.filter (fun K : Subgroup G => H ≤ K ∧ K < ⊤) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hHM.trans hK.le, lt_top_iff_ne_top.mpr hKtop⟩
  have hle : Nat.card K ≤ Nat.card M := hMmax K hKf
  have hdvd : Nat.card M ∣ Nat.card K := Subgroup.card_dvd_of_le hK.le
  have hlt : Nat.card M < Nat.card K := by
    rcases lt_or_eq_of_le (Nat.le_of_dvd Nat.card_pos hdvd) with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hK.le h.ge) hK.ne
  omega

/-- A nontrivial finite group has a maximal proper subgroup. -/
theorem exists_isCoatom_subgroup (G : Type*) [Group G] [Finite G] [Nontrivial G] :
    ∃ M : Subgroup G, IsCoatom M := by
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  have hbot : (⊥ : Subgroup G) < ⊤ := lt_of_le_of_ne bot_le fun h =>
    ha (show a = 1 from by
      have : a ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_top a
      simpa using this)
  obtain ⟨M, -, hM⟩ := exists_isCoatom_subgroup_ge G hbot
  exact ⟨M, hM⟩

/-- A minimal counterexample has a maximal subgroup. -/
theorem MinSimpleOdd.exists_isCoatom (h : MinSimpleOdd G) : ∃ M : Subgroup G, IsCoatom M := by
  have : Nontrivial G := h.nontrivial
  exact exists_isCoatom_subgroup G

/-- Every proper subgroup of a minimal counterexample is contained in a maximal subgroup. -/
theorem MinSimpleOdd.exists_isCoatom_ge (h : MinSimpleOdd G) {H : Subgroup G} (hH : H < ⊤) :
    ∃ M : Subgroup G, H ≤ M ∧ IsCoatom M := exists_isCoatom_subgroup_ge G hH

end Work.Skeleton
