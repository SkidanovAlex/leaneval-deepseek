import Mathlib
import Submission.Work.SmallRank.Defs
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.frattini_eq_agemo_sup_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# FT 3.4 (i): the non abelian group of order `p³` and exponent `p` is extraspecial

A group `X` of order `p ^ 3` (`p` prime), all of whose elements have order dividing `p`, and
which is not abelian, is extraspecial: `Z(X) = [X, X] = Φ(X)` has order `p`.

The relevant facts are all elementary once the machinery of `Submission.Work.PGroup` is available:

* a finite `p`-group has centre of order `p ^ k` with `k > 0` (`IsPGroup.card_center_eq_prime_pow`);
* since `X` is not abelian the centre is a proper nontrivial subgroup, and it cannot have order
  `p ^ 2` because then `X / Z(X)` would be cyclic of prime order, forcing `X` abelian
  (`isMulCommutative_of_isCyclic_quotient_center_self`);
* hence `|Z(X)| = p`, so `X / Z(X)` has order `p ^ 2` and is abelian
  (`IsPGroup.isMulCommutative_of_card_eq_prime_sq`), giving `[X, X] ≤ Z(X)`; as `X` is not abelian
  the derived subgroup is nontrivial, so it equals the centre;
* finally the Frattini subgroup equals the derived subgroup because the group has exponent `p`:
  `Φ(X) = X^p · [X, X]` (`Work.PGroup.frattini_eq_agemo_sup_commutator`) and `X^p = 1`.

The exponent hypothesis is used only in the last step.
-/

open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.SmallRank

/-- The centre of the top subgroup is the centre of the group. -/
lemma centerIn_top_eq_center {G : Type*} [Group G] :
    Work.PGroup.centerIn (⊤ : Subgroup G) = Subgroup.center G := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : (⟨g, trivial⟩ : ↥(⊤ : Subgroup G)) * a = a * ⟨g, trivial⟩ :=
      Subgroup.mem_center_iff.mp ha ⟨g, trivial⟩
    have h2 := congrArg (fun t : ↥(⊤ : Subgroup G) => (t : G)) h1
    simp only [Subgroup.coe_mul] at h2
    rw [← haz]
    exact h2
  · intro hx
    refine Subgroup.mem_map.mpr ⟨⟨x, trivial⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp hx (g : G)

/-- If every `p`-th power in `X` is trivial then `℧¹(X) = X^p` is trivial. -/
lemma agemo_one_top_eq_bot {p : ℕ} {X : Type*} [Group X] (hexp : ∀ x : X, x ^ p = 1) :
    Work.PGroup.agemo p 1 (⊤ : Subgroup X) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [Work.PGroup.agemo, Subgroup.closure_le]
  rintro y ⟨x, -, hx⟩
  exact Subgroup.mem_bot.mpr (by rw [← hx, pow_one]; exact hexp x)

theorem isExtraspecial_of_isGroupOfOrderP3ExpP {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    (h : IsGroupOfOrderP3ExpP p X) :
    Work.PGroup.IsExtraspecial p (⊤ : Subgroup X) ∧ Nat.card (Subgroup.center X) = p := by
  obtain ⟨hcard, hexp, hnc⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  have hPgroupX : IsPGroup p X := IsPGroup.of_card hcard
  haveI : Nontrivial X := (IsPGroup.nontrivial_iff_card hPgroupX).2 ⟨3, by norm_num, hcard⟩
  -- The centre has order `p`.
  obtain ⟨k, hkpos, hk⟩ := IsPGroup.card_center_eq_prime_pow (G := X) (n := 3) hcard (by norm_num)
  have hdvd : p ^ k ∣ p ^ 3 := by
    rw [← hk, ← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hkle : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  have hZ : Nat.card ↥(Subgroup.center X) = p := by
    have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk_cases with rfl | rfl | rfl
    · rw [hk, pow_one]
    · exfalso
      have hcardZ : Nat.card ↥(Subgroup.center X) = p ^ 2 := by rw [hk]
      have hcardQ : Nat.card (X ⧸ Subgroup.center X) = p := by
        have h1 : Nat.card ↥(Subgroup.center X) * (Subgroup.center X).index = Nat.card X :=
          Subgroup.card_mul_index _
        rw [Subgroup.index_eq_card, hcardZ, hcard] at h1
        have h2 : p ^ 2 * Nat.card (X ⧸ Subgroup.center X) = p ^ 2 * p := by
          rw [h1]; ring
        exact Nat.mul_left_cancel (pow_pos hp.pos 2) h2
      haveI : IsCyclic (X ⧸ Subgroup.center X) := isCyclic_of_prime_card hcardQ
      exact hnc (isMulCommutative_of_isCyclic_quotient_center_self X)
    · exfalso
      have hcardZ : Nat.card ↥(Subgroup.center X) = p ^ 3 := by rw [hk]
      have htop : Subgroup.center X = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcardZ, hcard])
      exact hnc (Subgroup.center_eq_top_iff.mp htop)
  -- The commutator subgroup is contained in the centre, and in fact equals it.
  have hcardQ2 : Nat.card (X ⧸ Subgroup.center X) = p ^ 2 := by
    have h1 : Nat.card ↥(Subgroup.center X) * (Subgroup.center X).index = Nat.card X :=
      Subgroup.card_mul_index _
    rw [Subgroup.index_eq_card, hZ, hcard] at h1
    have h2 : p * Nat.card (X ⧸ Subgroup.center X) = p * p ^ 2 := by
      rw [h1]; ring
    exact Nat.mul_left_cancel hp.pos h2
  have hC_le_Z : commutator X ≤ Subgroup.center X :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Subgroup.center X)).mp
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq hcardQ2)
  have hC_ne_bot : commutator X ≠ ⊥ := by
    intro hc
    exact hnc ((commutator_eq_bot_iff X).mp hc)
  have hCcard : Nat.card ↥(commutator X) = p := by
    have hdvd2 : Nat.card ↥(commutator X) ∣ p := by
      rw [← hZ]
      exact Subgroup.card_dvd_of_le hC_le_Z
    rcases (Nat.dvd_prime hp).mp hdvd2 with h1 | h1
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1 ▸ hC_ne_bot) (by simp)
    · exact h1
  have hC_eq_Z : commutator X = Subgroup.center X :=
    Subgroup.eq_of_le_of_card_ge hC_le_Z (by rw [hZ, hCcard])
  -- The Frattini subgroup of the top subgroup is the derived subgroup.
  have hPtop : IsPGroup p ↥(⊤ : Subgroup X) := IsPGroup.of_card (by rw [Subgroup.card_top, hcard])
  have hfratt : Work.PGroup.frattiniIn (⊤ : Subgroup X) = ⁅(⊤ : Subgroup X), ⊤⁆ := by
    rw [Work.PGroup.frattini_eq_agemo_sup_commutator hp (⊤ : Subgroup X) hPtop]
    rw [agemo_one_top_eq_bot hexp, bot_sup_eq]
  have hNC : ¬ IsMulCommutative (⊤ : Subgroup X) := by
    intro hcomm
    apply hnc
    rw [isMulCommutative_iff] at hcomm ⊢
    intro a b
    have h2 := hcomm ⟨a, trivial⟩ ⟨b, trivial⟩
    simpa using congrArg (fun t : ↥(⊤ : Subgroup X) => (t : X)) h2
  have hElemZ : Work.PGroup.IsElementaryAbelian p (Subgroup.center X) := by
    constructor
    · rw [isMulCommutative_iff]
      intro a b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (Subgroup.mem_center_iff.mp a.2 (b : X)).symm
    · intro x
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center X) x.2
      rw [hZ] at h
      have h2 : (x : X) ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp h
      exact Subtype.ext (by simpa using h2)
  refine ⟨?_, hZ⟩
  refine ⟨hNC, ?_, ?_⟩
  · right
    refine ⟨hPtop, hNC, ?_, ?_, ?_⟩
    · rw [centerIn_top_eq_center]; exact hC_eq_Z.symm
    · rw [centerIn_top_eq_center, hfratt]; exact hC_eq_Z.symm
    · rw [centerIn_top_eq_center]; exact hElemZ
  · rw [centerIn_top_eq_center]; exact hZ

end Work.SmallRank
