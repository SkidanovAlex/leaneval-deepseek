import Mathlib
import Submission.Work.ZassenhausSuzuki.SelfCent.SingerCent
import Submission.Work.ZassenhausSuzuki.SelfCent.Counts
import Submission.Work.ZassenhausSuzuki.numClasses_stronglyReal
import Submission.Work.ZassenhausSuzuki.singer_conj_inf_eq_bot
import Submission.Work.ZassenhausSuzuki.SingerAux
import Submission.Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `C_G(S.V) = S.V` and `|N_G(S.V)| = 2(q+1)`

This module assembles the two halves of Suzuki 1962, §8, pp. 117–118:

* `SelfCent.singerV_selfcentralizing` (the self-centralising half, extracted from
  `Work.ZassenhausSuzuki.singerV_conj_inf_eq_bot`'s `W = S.V` argument), and
* the class count of `SelfCent.Counts` together with the (proved) total count
  `Work.ZassenhausSuzuki.numClasses_stronglyReal`,

i.e. the conclusion of `Work.ZassenhausSuzuki.singer_centralizer_eq`, in the form consumed by
`Submission/Work/ZassenhausSuzuki/QSZThm1.lean`.

The arithmetic is Suzuki's: with `k_V := #(classes meeting S.V#)`, `l := [N_G(S.V) : S.V]`,
`q := |Q0sub H| = |S.V| - 1 = |twoPoint H t| + 1`,

* the classes of strongly real `x ≠ 1` with `x * x ≠ 1` number `q - 1`
  (`numClasses_stronglyReal`), and each meets `D#` or `S.V#` (`numClasses_stronglyReal_le`);
* at most `(q-2)/2` of them meet `D#` (`two_mul_numClasses_nonzero_twoPoint_le`),

so `q ≤ 2 k_V`; on the other hand `k_V * l ≤ q` (`mul_index_le_card_nonzero`), whence
`l ≤ 2`; and `l ≥ 2` since `|N_G(S.V)| ≥ |N_{X5}(S.V)| = 2|S.V|`. Hence `l = 2` and
`|N_G(S.V)| = 2(q+1)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ZassenhausSuzuki.SelfCent

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-- **Suzuki 1962, §8, pp. 117–118** (the conclusion of `Work.ZassenhausSuzuki.singer_centralizer_eq`):
in the Zassenhaus split rank-one setting with `Q` a non-abelian `2`-group and `σ = ρ`
(`SzHyp`, `hnab`), the Singer cycle `S.V` of `SingerCycle.Data` is self-centralising in `G` and
its normaliser has twice its order. -/
theorem singerV_centralizer_normalizer (h : SzHyp H Q t s) (hnab : ¬ IsAbelianSubgroup Q)
    (S : SingerCycle.Data G H t)
    (hD3 : ∀ x : G, x * x ≠ 1 → IsStronglyReal x →
      (∃ g : G, g * x * g⁻¹ ∈ Q) ∨
        (∃ g : G, g * x * g⁻¹ ∈ twoPoint H t) ∨
        (∃ g : G, g * x * g⁻¹ ∈ S.V))
    (hC1 : ∀ k : G, k ∈ twoPoint H t → k ≠ 1 →
      Subgroup.centralizer ({k} : Set G) = twoPoint H t) :
    Subgroup.centralizer (S.V : Set G) = S.V ∧
      Nat.card ↥(Subgroup.normalizer (S.V : Set G)) =
        2 * (Nat.card ↥(Work.ThmF.Q0sub H) + 1) := by
  classical
  haveI hCj : Fintype (ConjClasses G) := Fintype.ofFinite _
  have hcent : Subgroup.centralizer (S.V : Set G) = S.V :=
    singerV_selfcentralizing h hnab S hD3 hC1
  -- `q := |Q0sub H|`
  set q : ℕ := Nat.card ↥(Work.ThmF.Q0sub H) with hqdef
  have hVcard : Nat.card ↥(S.V) = q + 1 := by rw [hqdef]; exact S.card_V
  have hDcard : Nat.card ↥(twoPoint H t) = q - 1 := by
    rw [hqdef]; exact twoPoint_card_eq_Q0sub_sub_one h
  have hVodd : Odd (Nat.card ↥(S.V)) := singer_odd_card_V h S
  have hq4 : 4 ≤ q := four_le_Q0sub_card h
  -- every non-identity element of `S.V` is self-centralising in `G`
  have hcent_el : ∀ v : G, v ∈ (S.V : Set G) → v ≠ 1 →
      Subgroup.centralizer ({v} : Set G) = S.V := by
    intro v hv hv1
    have hv2 : v * v ≠ 1 := by
      intro hsq
      have hdvd2 : orderOf v ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using hsq
      have hoddv : Odd (orderOf v) := hVodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard S.V hv)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h2 | h2
      · exact hv1 (orderOf_eq_one_iff.mp h2)
      · rw [h2] at hoddv; exact absurd hoddv (by decide)
    obtain ⟨hcom, -, -⟩ :=
      centralizer_abelian_of_strongly_real h.split h.zass h.two hv2 (S.stronglyReal v hv)
    haveI : IsMulCommutative ↥(Subgroup.centralizer ({v} : Set G)) := hcom
    haveI hcyc : IsCyclic ↥(S.V) := S.cyclic
    haveI : IsMulCommutative ↥(S.V) := IsCyclic.isMulCommutative
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [← hcent]
      have hmem : ∀ w : G, w ∈ S.V → w ∈ Subgroup.centralizer ({v} : Set G) := by
        intro w hw
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val
          (mul_comm' (⟨w, hw⟩ : ↥S.V) (⟨v, hv⟩ : ↥S.V))
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(Subgroup.centralizer ({v} : Set G)))
        (⟨w, hmem w hw⟩ : ↥(Subgroup.centralizer ({v} : Set G)))).symm
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥S.V) (⟨v, hv⟩ : ↥S.V))
  -- the two counts
  have htotal : numClasses {x : G | IsStronglyReal x ∧ x ≠ 1 ∧ x * x ≠ 1} = q - 1 := by
    rw [hqdef]; exact numClasses_stronglyReal h
  have hcover := numClasses_stronglyReal_le h S hD3
    (fun x hx2 hsr => not_conj_mem_Q_of_stronglyReal h hx2 hsr)
  have hkD : 2 * numClasses (nonzero (twoPoint H t : Set G)) ≤ q - 2 := by
    have h1 := two_mul_numClasses_nonzero_twoPoint_le h
    rw [hDcard] at h1
    omega
  have hkV : q ≤ 2 * numClasses (nonzero (S.V : Set G)) := by
    have h2 : q - 1 ≤ numClasses (nonzero (twoPoint H t : Set G)) +
        numClasses (nonzero (S.V : Set G)) := by
      rw [← htotal]; exact hcover
    omega
  have hfib : numClasses (nonzero (S.V : Set G)) *
      (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index ≤ q := by
    have h1 := mul_index_le_card_nonzero (S.V) hcent_el
    rw [hVcard] at h1
    omega
  have hqpos : 0 < q := by omega
  -- `l ≤ 2`
  have hl_le : (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index ≤ 2 := by
    have hA : (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index * q ≤
        (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index *
          (2 * numClasses (nonzero (S.V : Set G))) := Nat.mul_le_mul_left _ hkV
    have hB : 2 * (numClasses (nonzero (S.V : Set G)) *
        (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index) ≤ 2 * q :=
      Nat.mul_le_mul_left 2 hfib
    have hC : (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index *
        (2 * numClasses (nonzero (S.V : Set G))) =
        2 * (numClasses (nonzero (S.V : Set G)) *
          (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index) := by ring
    rw [hC] at hA
    have hD : (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index * q ≤ 2 * q :=
      le_trans hA hB
    have hE : q * (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index ≤ q * 2 := by
      rw [Nat.mul_comm q (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index,
        Nat.mul_comm q 2]
      exact hD
    exact Nat.le_of_mul_le_mul_left hE hqpos
  -- `l ≥ 2` : `|N_G(S.V)| ≥ |N_{X5}(S.V)| = 2(q+1) = 2|S.V|`
  have hcardN : Nat.card ↥(Subgroup.normalizer (S.V : Set G)) =
      (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index * Nat.card ↥(S.V) := by
    have h1 := Subgroup.card_mul_index
      (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G)))
    have h2 : Nat.card ↥(S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))) =
        Nat.card ↥(S.V) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer)).toEquiv
    rw [h2, Nat.mul_comm] at h1
    exact h1.symm
  have hbig : 2 * (q + 1) ≤ Nat.card ↥(Subgroup.normalizer (S.V : Set G)) := by
    have h1 := S.normalizer_in_X5
    have h2 : Nat.card ↥(Subgroup.normalizer (S.V : Set G) ⊓ Work.ThmF.Lemma5.X5 H t) =
        2 * (q + 1) := by rw [hqdef]; exact h1
    rw [← h2]
    exact Subgroup.card_le_of_le inf_le_left
  have hl_ge : 2 ≤ (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index := by
    have h1 : (q + 1) * 2 ≤ (q + 1) *
        (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index := by
      calc (q + 1) * 2 = 2 * (q + 1) := Nat.mul_comm _ _
        _ ≤ Nat.card ↥(Subgroup.normalizer (S.V : Set G)) := hbig
        _ = (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index * Nat.card ↥(S.V) :=
              hcardN
        _ = (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index * (q + 1) := by
              rw [hVcard]
        _ = (q + 1) * (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index :=
              Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have hl : (S.V.subgroupOf (Subgroup.normalizer (S.V : Set G))).index = 2 :=
    le_antisymm hl_le hl_ge
  refine ⟨hcent, ?_⟩
  rw [hcardN, hl, hVcard, Nat.mul_comm]

end Work.ZassenhausSuzuki.SelfCent
