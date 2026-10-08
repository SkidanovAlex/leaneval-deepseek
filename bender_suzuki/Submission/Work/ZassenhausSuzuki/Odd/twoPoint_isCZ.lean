import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.q_structure
import Submission.Work.ZassenhausSuzuki.card_normalizer_twoPoint

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The two-point stabiliser is a `ℱ`-subgroup

In the split rank-one Zassenhaus configuration `H = Q ⋊ D`, `D = twoPoint H t = H ⊓ Hᵗ`, the
two-point stabiliser `D` belongs to the Bender–Suzuki family `ℱ` of
`Work.ZassenhausSuzuki.Odd.IsCZ`: the centraliser of a non-identity strongly real element that is
not an involution.  Concretely

* `D` has order `q - 1` (`q = |Z(Q)|`, computed in `Odd.q_structure`);
* every non-identity `d ∈ D` is strongly real: `t` inverts `D`, so `d = t * (t * d)` is a product
  of the two involutions `t` and `t * d`;
* `D = C_G(d)` for every non-identity `d ∈ D` (Suzuki 1962 §8, proved in
  `Work.ZassenhausSuzuki.centralizer_twoPoint_eq`), so `D ∈ ℱ` — the witness `k` exists because
  `|D| = q - 1 ≥ 3`;
* `[N_G(D) : D] = 2` (Suzuki 1962, Prop. 14: `N_G(D) = D ⋊ ⟨t⟩`,
  `Work.ZassenhausSuzuki.card_normalizer_twoPoint`), i.e. `kA D = 2`.
-/

set_option maxHeartbeats 1000000

namespace Work.ZassenhausSuzuki.Odd

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- **Every element of the two-point stabiliser is strongly real.**  The Weyl element `t` is an
involution (`hsplit.invol`) and inverts `D = twoPoint H t`
(`Work.ZassenhausSuzuki.twoPoint_inverted_of_zass`), so `d = t * (t * d)` exhibits `d` as a
product of the involutions `t` and `t * d`. -/
theorem isStronglyReal_of_mem_twoPoint (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    {d : G} (hd : d ∈ twoPoint H t) : Work.ZassenhausSuzuki.IsStronglyReal d := by
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hsplit.invol]
    exact pow_orderOf_eq_one t
  have htd : t * d * t = d⁻¹ := by
    have h := Work.ZassenhausSuzuki.twoPoint_inverted_of_zass hsplit hzass d hd
    rwa [inv_eq_of_mul_eq_one_right ht2] at h
  refine ⟨t, t * d, ht2, ?_, by rw [← mul_assoc, ht2, one_mul]⟩
  calc (t * d) * (t * d) = (t * d * t) * d := by group
    _ = d⁻¹ * d := by rw [htd]
    _ = 1 := inv_mul_cancel d

/-- **The index of a subgroup in its normaliser**, given that the normaliser has twice the order
of the subgroup.  This is the bookkeeping behind `kA D = 2`. -/
private lemma index_subgroupOf_normalizer_eq_two {G : Type} [Group G] [Finite G]
    (D : Subgroup G)
    (hcard : Nat.card ↥(Subgroup.normalizer (D : Set G)) = 2 * Nat.card ↥D) :
    (D.subgroupOf (Subgroup.normalizer (D : Set G))).index = 2 := by
  have hcardSub : Nat.card ↥(D.subgroupOf (Subgroup.normalizer (D : Set G))) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  have hmul := Subgroup.card_mul_index (D.subgroupOf (Subgroup.normalizer (D : Set G)))
  have hpos : 0 < Nat.card ↥(D.subgroupOf (Subgroup.normalizer (D : Set G))) := Nat.card_pos
  exact Nat.mul_left_cancel hpos
    (by rw [hmul, hcard, hcardSub]; ring)

theorem twoPoint_isCZ (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) :
    Work.ZassenhausSuzuki.Odd.IsCZ (Submission.Blueprint.twoPoint H t) ∧
      Nat.card ↥(Submission.Blueprint.twoPoint H t) = Work.ZassenhausSuzuki.Odd.q H - 1 ∧
      Work.ZassenhausSuzuki.Odd.kA (Submission.Blueprint.twoPoint H t) = 2 ∧
      ∀ d ∈ Submission.Blueprint.twoPoint H t, d ≠ 1 → Work.ZassenhausSuzuki.IsStronglyReal d := by
  classical
  obtain ⟨hQcard, hDcard, hfour, hpow, hnot3, hindex⟩ := q_structure h
  -- `D ≠ ⊥`, since `|D| = q - 1 ≥ 3`
  have hDne : Submission.Blueprint.twoPoint H t ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hDcard
    omega
  -- `D` has odd order, hence so do its elements
  have hoddD : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    h.hsplit.stronglyEmbedded.2.2 t h.hsplit.not_mem
  -- (4) every element of `D` is strongly real
  have hSR : ∀ d ∈ Submission.Blueprint.twoPoint H t, d ≠ 1 →
      Work.ZassenhausSuzuki.IsStronglyReal d :=
    fun d hd _ => isStronglyReal_of_mem_twoPoint h.hsplit h.hzass hd
  -- (1) `D ∈ ℱ`, witnessed by any non-identity element (there is one: `D ≠ ⊥`)
  have hCZ : Work.ZassenhausSuzuki.Odd.IsCZ (Submission.Blueprint.twoPoint H t) := by
    obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
    have hkD : (k : G) ∈ Submission.Blueprint.twoPoint H t := k.2
    have hkne : (k : G) ≠ 1 := fun hc => hk1 (Subtype.ext (by simpa using hc))
    have hkk : (k : G) * (k : G) ≠ 1 := by
      have hodd : Odd (orderOf ((k : G))) :=
        hoddD.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hkD)
      intro h2
      have h2' : (k : G) ^ 2 = 1 := by rw [pow_two]; exact h2
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr h2') with h1 | h1
      · exact hkne (orderOf_eq_one_iff.mp h1)
      · obtain ⟨m, hm⟩ := hodd
        omega
    exact ⟨(k : G), hSR (k : G) hkD hkne, hkne, hkk,
      Work.ZassenhausSuzuki.centralizer_twoPoint_eq h.hsplit h.hzass h.h2 hkD hkne⟩
  -- (3) `[N_G(D) : D] = 2`
  have hkA : Work.ZassenhausSuzuki.Odd.kA (Submission.Blueprint.twoPoint H t) = 2 := by
    unfold Work.ZassenhausSuzuki.Odd.kA
    exact index_subgroupOf_normalizer_eq_two (Submission.Blueprint.twoPoint H t)
      (Work.ZassenhausSuzuki.card_normalizer_twoPoint h.hsplit h.hzass hDne)
  exact ⟨hCZ, hDcard, hkA, hSR⟩

end Work.ZassenhausSuzuki.Odd
