import Mathlib
import Submission.Work.ProP.Defs
import Submission.Work.ProP.pCentralStep_eq_self_iff
import Submission.Work.Shrinking.map_pCentralSeries_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

open Work.Shrinking

/-! ## Auxiliary lemmas

The target lemma reduces, by the compatibility of the `p`-central series with the surjection
`P →* P ⧸ K`, to the statement that the descending `p`-central series of a finite `p`-group `Q`
of order `p ^ k` reaches `⊥` at step `k`.  This is proved here by a cardinality count: each
step of the filtration is strictly smaller (the Nakayama property
`Work.ProP.pCentralStep_eq_self_iff`), so the order of the `i`-th term is at most `p ^ (k - i)`.
-/

/-- Proper subgroups of a finite group have strictly smaller cardinality: the inclusion of
`H'` into `H` is injective but not surjective. -/
theorem card_lt_card_of_lt {Q : Type*} [Group Q] [Finite Q] {H' H : Subgroup Q} (h : H' < H) :
    Nat.card ↥H' < Nat.card ↥H := by
  have hss : (H' : Set Q) ⊂ (H : Set Q) := h
  have hlt := Set.ncard_lt_ncard hss
  rwa [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at hlt

/-- The descending `p`-central series of a finite `p`-group `Q` of order `p ^ k` reaches `⊥`
at step `k`.

By `Work.ProP.pCentralStep_eq_self_iff` the series is strictly decreasing as long as it has not
reached `⊥`: if `pCentralSeries p Q i ≠ ⊥` then `pCentralSeries p Q (i+1) < pCentralSeries p Q i`
(`Work.Shrinking.pCentralSeries_le_succ` plus the Nakayama property).  Hence
`Nat.card (pCentralSeries p Q i) ≤ p ^ (k - i)` by induction on `i`, and at `i = k` the term has
at most one element. -/
theorem pCentralSeries_eq_bot_of_card_dvd_aux {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) {k : ℕ} (hcard : Nat.card Q = p ^ k) :
    Work.Shrinking.pCentralSeries p Q k = ⊥ := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hmain : ∀ i ≤ k, Nat.card ↥(Work.Shrinking.pCentralSeries p Q i) ≤ p ^ (k - i) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [Work.Shrinking.pCentralSeries_zero, Subgroup.card_top]
      simp [hcard]
    | succ i ih =>
      intro hik
      have hik' : i ≤ k := Nat.le_of_succ_le hik
      have hle := ih hik'
      by_cases hbot : Work.Shrinking.pCentralSeries p Q i = ⊥
      · -- the series has already reached `⊥`, so it stays there
        have hbot' : Work.Shrinking.pCentralSeries p Q (i + 1) = ⊥ :=
          le_bot_iff.mp (by
            simpa [hbot] using Work.Shrinking.pCentralSeries_le_succ p Q i)
        rw [hbot', Subgroup.card_bot]
        exact Nat.one_le_pow (k - (i + 1)) p (Fact.out : p.Prime).pos
      · -- otherwise the next term is a proper subgroup
        have hnorm : (Work.Shrinking.pCentralSeries p Q i).Normal :=
          Work.Shrinking.pCentralSeries_normal p Q i
        have hne : Work.Shrinking.pCentralSeries p Q (i + 1) ≠
            Work.Shrinking.pCentralSeries p Q i := by
          intro heq
          have hstep : Work.Shrinking.pCentralStep p (Work.Shrinking.pCentralSeries p Q i) =
              Work.Shrinking.pCentralSeries p Q i := by
            rw [← Work.Shrinking.pCentralSeries_succ]
            exact heq
          exact hbot ((@pCentralStep_eq_self_iff p _ Q _ _ hQ
            (Work.Shrinking.pCentralSeries p Q i) hnorm).mp hstep)
        have hstrict : Work.Shrinking.pCentralSeries p Q (i + 1) <
            Work.Shrinking.pCentralSeries p Q i :=
          lt_of_le_of_ne (Work.Shrinking.pCentralSeries_le_succ p Q i) hne
        have hcardlt := card_lt_card_of_lt hstrict
        obtain ⟨b, hb⟩ :=
          (hQ.to_subgroup (Work.Shrinking.pCentralSeries p Q (i + 1))).exists_card_eq
        have hb_le : b ≤ k - (i + 1) := by
          rw [hb] at hcardlt
          have h2 : p ^ b < p ^ (k - i) := lt_of_lt_of_le hcardlt hle
          have h3 : b < k - i := (Nat.pow_lt_pow_iff_right hp1).mp h2
          omega
        rw [hb]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hb_le
  have hfin : Nat.card ↥(Work.Shrinking.pCentralSeries p Q k) ≤ 1 := by
    have := hmain k le_rfl
    simpa using this
  exact (Subgroup.card_le_one_iff_eq_bot _).mp hfin

/-- Variant of the cofinality statement with a divisibility hypothesis on the order of the
quotient: if `K ◁ P` with `P ⧸ K` a finite `p`-group of order dividing `p ^ k`, then
`pCentralSeries p P k ≤ K`.

Proof: `Nat.card (P ⧸ K) = p ^ j` for some `j` (`IsPGroup.exists_card_eq`, a finite `p`-group has
`p`-power order), and `j ≤ k` because `p ^ j ∣ p ^ k` (`Nat.pow_dvd_pow_iff_le_right`); then
`Work.ProP.pCentralSeries_eq_bot_of_card` gives `pCentralSeries p (P ⧸ K) j = ⊥` and
antitonicity of the filtration (`Work.Shrinking.pCentralSeries_antitone`) gives
`pCentralSeries p (P ⧸ K) k = ⊥`.  Finally the filtration is compatible with the surjection
`P →* P ⧸ K` (`Work.Shrinking.map_pCentralSeries_surjective`), so `pCentralSeries p P k ≤ K`. -/
theorem pCentralSeries_le_of_card_dvd {p : ℕ} [Fact p.Prime] {P : Type*} [Group P]
    (K : Subgroup P) [K.Normal] [Finite (P ⧸ K)] (hP : IsPGroup p (P ⧸ K)) {k : ℕ}
    (hcard : Nat.card (P ⧸ K) ∣ p ^ k) :
    Work.Shrinking.pCentralSeries p P k ≤ K := by
  obtain ⟨j, hj⟩ := hP.exists_card_eq
  rw [hj] at hcard
  have hjk : j ≤ k := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hcard
  have hQj : Work.Shrinking.pCentralSeries p (P ⧸ K) j = ⊥ :=
    pCentralSeries_eq_bot_of_card_dvd_aux hP hj
  have hbot : Work.Shrinking.pCentralSeries p (P ⧸ K) k = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hQj]
    exact Work.Shrinking.pCentralSeries_antitone p (P ⧸ K) hjk
  have hmap := Work.Shrinking.map_pCentralSeries_surjective p (QuotientGroup.mk' K)
    (QuotientGroup.mk'_surjective K) k
  rw [hbot] at hmap
  have hker : Work.Shrinking.pCentralSeries p P k ≤ (QuotientGroup.mk' K).ker :=
    (Subgroup.map_eq_bot_iff _).mp hmap
  rwa [QuotientGroup.ker_mk'] at hker

end Work.ProP
