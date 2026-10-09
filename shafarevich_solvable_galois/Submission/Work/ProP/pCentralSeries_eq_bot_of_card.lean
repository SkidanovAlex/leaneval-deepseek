import Mathlib
import Submission.Work.ProP.Defs
import Submission.Work.ProP.pCentralStep_eq_self_iff
import Submission.Work.ProP.card_quotient_lt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

open Work.Shrinking

/-- The descending `p`-central series of a finite `p`-group of order `p ^ k` reaches the trivial
subgroup at the `k`-th step: `pCentralSeries p Q k = ⊥`.

Two routes are available; the second is shorter.
(A) Counting, using the strictness of the filtration
(`Work.ProP.pCentralStep_eq_self_iff`, which is already proved and importable): if the series has
not reached `⊥` by step `k`, then `Q_i ≠ ⊥` for all `i ≤ k`, so each step is strict and
`[Q_i : Q_{i+1}]` is a nontrivial `p`-group index, hence `≥ p`; induction gives
`[Q : Q_i] ≥ p ^ i` (`Subgroup.index_mul_index`) and `[Q : Q_k] ≥ p ^ k = Nat.card Q`, while
`[Q : Q_k] * Nat.card Q_k = Nat.card Q` (`Subgroup.card_mul_index`) forces `Q_k = ⊥`.
(B) Induction on `k` through the centre: for `k = 0` the group is trivial; otherwise pick a
subgroup `C ≤ Subgroup.center Q` of order `p` (an element of the centre of order `p ^ e` raised to
the `p ^ (e-1)`-st power), apply the induction hypothesis to `Q ⧸ C` (of order `p ^ (k-1)`) to get
`pCentralSeries p (Q ⧸ C) (k-1) = ⊥`, i.e. the image of `pCentralSeries p Q (k-1)` lies in `C`
(use `Work.Shrinking.map_pCentralSeries_surjective`), and conclude
`pCentralSeries p Q k ⊆ C ^ p ⁅C, Q⁆ = ⊥` because `C` is central of order `p`. -/
theorem pCentralSeries_eq_bot_of_card {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) {k : ℕ} (hcard : Nat.card Q = p ^ k) :
    Work.Shrinking.pCentralSeries p Q k = ⊥ := by
  -- We follow route (A): the terms of the series are a strictly descending chain as long as they
  -- are nontrivial, and each strict step drops the order by a factor `≥ p`.
  by_contra hne
  have hp : p.Prime := Fact.out
  have hmono : Antitone (pCentralSeries p Q) := pCentralSeries_antitone p Q
  -- If the `k`-th term is nontrivial, so is every earlier term.
  have hne_i : ∀ i ≤ k, pCentralSeries p Q i ≠ ⊥ := by
    intro i hi h
    exact hne (le_bot_iff.mp (h ▸ hmono hi))
  -- Each relative index `[Q_i : Q_{i+1}]` is a nontrivial `p`-group index, hence `≥ p`.
  have hm_ge : ∀ i ≤ k, p ≤ (pCentralSeries p Q (i+1)).relIndex (pCentralSeries p Q i) := by
    intro i hi
    have hNi : (pCentralSeries p Q i).Normal := pCentralSeries_normal p Q i
    have hNi1 : (pCentralSeries p Q (i+1)).Normal := pCentralSeries_normal p Q (i+1)
    -- the step is strict, because a `p`-central step fixes a normal subgroup only when it is `⊥`
    have hne_step : pCentralSeries p Q (i+1) ≠ pCentralSeries p Q i := by
      intro h
      refine hne_i i hi ((Work.ProP.pCentralStep_eq_self_iff hQ (pCentralSeries p Q i)).mp ?_)
      rw [← pCentralSeries_succ p Q i]
      exact h
    have hntop : (pCentralSeries p Q (i+1)).subgroupOf (pCentralSeries p Q i) ≠ ⊤ := by
      intro h
      exact hne_step
        (le_antisymm (pCentralSeries_le_succ p Q i) (Subgroup.subgroupOf_eq_top.mp h))
    have hgt1 : 1 < (pCentralSeries p Q (i+1)).relIndex (pCentralSeries p Q i) := by
      have h := Subgroup.one_lt_index_of_ne_top
        (H := (pCentralSeries p Q (i+1)).subgroupOf (pCentralSeries p Q i)) hntop
      simpa [Subgroup.relIndex] using h
    -- `[Q_i : Q_{i+1}]` is the order of a quotient of the `p`-group `Q_i`, hence a power of `p`
    have hQi : IsPGroup p ↥(pCentralSeries p Q i) := hQ.to_subgroup _
    have hquot : IsPGroup p (↥(pCentralSeries p Q i) ⧸
        (pCentralSeries p Q (i+1)).subgroupOf (pCentralSeries p Q i)) :=
      hQi.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    obtain ⟨e, he⟩ := hquot.exists_card_eq
    have hm_eq : (pCentralSeries p Q (i+1)).relIndex (pCentralSeries p Q i) = p ^ e := by
      simp only [Subgroup.relIndex, Subgroup.index_eq_card]
      exact he
    rcases e with _ | e
    · rw [pow_zero] at hm_eq
      omega
    · rw [hm_eq]
      exact Nat.le_self_pow (Nat.succ_ne_zero e) p
  -- Hence `[Q : Q_i] ≥ p ^ i` for every `i ≤ k`.
  have hd : ∀ i ≤ k, p ^ i ≤ (pCentralSeries p Q i).index := by
    intro i
    induction i with
    | zero =>
        intro _
        simp [pCentralSeries_zero, Subgroup.index_top]
    | succ i ih =>
        intro hi
        have hi' : i ≤ k := Nat.le_of_succ_le hi
        have hrel := Subgroup.relIndex_mul_index
          (H := pCentralSeries p Q (i+1)) (K := pCentralSeries p Q i)
          (pCentralSeries_le_succ p Q i)
        calc p ^ (i+1) = p ^ i * p := by rw [pow_succ]
          _ ≤ (pCentralSeries p Q i).index
                * (pCentralSeries p Q (i+1)).relIndex (pCentralSeries p Q i) :=
              Nat.mul_le_mul (ih hi') (hm_ge i hi')
          _ = (pCentralSeries p Q (i+1)).relIndex (pCentralSeries p Q i)
                * (pCentralSeries p Q i).index := mul_comm _ _
          _ = (pCentralSeries p Q (i+1)).index := hrel
  -- So `[Q : Q_k] ≥ p ^ k = Nat.card Q`, which forces `Q_k = ⊥`.
  have hk : p ^ k ≤ (pCentralSeries p Q k).index := hd k le_rfl
  have hcardmul :
      (pCentralSeries p Q k).index * Nat.card ↥(pCentralSeries p Q k) = p ^ k := by
    rw [← hcard]
    exact Subgroup.index_mul_card _
  have hle1 : Nat.card ↥(pCentralSeries p Q k) ≤ 1 := by
    by_contra hc
    have h2 : 2 ≤ Nat.card ↥(pCentralSeries p Q k) := by omega
    have hle := Nat.mul_le_mul hk h2
    rw [hcardmul] at hle
    have hpos : 0 < p ^ k := pow_pos hp.pos k
    have : 2 ≤ 1 := le_of_mul_le_mul_left (by simpa using hle) hpos
    omega
  exact hne (Subgroup.eq_bot_of_card_le _ hle1)

end Work.ProP
