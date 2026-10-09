import Mathlib
import Submission.Work.ProP.Defs
import Submission.Work.Shrinking.map_pCentralSeries_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

universe u

/-- Monotonicity of the next term of the `p`-central series: a smaller normal subgroup generates
a smaller `H^p ⁅H, P⁆`. -/
private theorem pCentralStep_mono' (p : ℕ) {P : Type*} [Group P] {H K : Subgroup P} (h : H ≤ K) :
    Work.Shrinking.pCentralStep p H ≤ Work.Shrinking.pCentralStep p K := by
  unfold Work.Shrinking.pCentralStep
  exact sup_le_sup (Subgroup.closure_mono (Set.image_mono h)) (Subgroup.commutator_mono h le_rfl)

/-- The descending `p`-central series of a finite `p`-group `Q` of order `p ^ k` reaches `⊥` at
step `k`.

Proof by strong induction on `k`.  If `Q` is trivial (`k = 0`) this is clear.  Otherwise the
centre of `Q` is nontrivial (`IsPGroup.center_nontrivial`) and Cauchy's theorem inside it
produces a central subgroup `C` of order `p`; the quotient `Q ⧸ C` has order `p ^ (k-1)`, so the
induction hypothesis gives `pCentralSeries p (Q ⧸ C) (k-1) = ⊥`, which by functoriality of the
series under the surjection `Q →* Q ⧸ C` (`map_pCentralSeries_surjective`) means
`pCentralSeries p Q (k-1) ≤ C`.  Finally
`pCentralSeries p Q k = (Q_{k-1})^p ⁅Q_{k-1}, Q⁆ ≤ C^p ⁅C, Q⁆ = ⊥`: the subgroup `C` is central
(so `⁅C, Q⁆ = ⊥`) of order `p` (so `C^p = ⊥`). -/
private theorem pCentralSeries_eq_bot_of_card_aux (p : ℕ) [Fact p.Prime] :
    ∀ (k : ℕ) (Q : Type u) [Group Q] [Finite Q], IsPGroup p Q → Nat.card Q = p ^ k →
      Work.Shrinking.pCentralSeries p Q k = ⊥ := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro Q _ _ hQ hcard
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [Work.Shrinking.pCentralSeries_zero]
      rw [pow_zero] at hcard
      have hsub : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hcard).1
      exact Subgroup.eq_bot_of_subsingleton _
    · have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
      have hlt : 1 < Nat.card Q := by
        rw [hcard]
        exact one_lt_pow₀ hp1 (Nat.pos_iff_ne_zero.mp hkpos)
      have hnt : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp hlt
      have hZnt : Nontrivial ↥(Subgroup.center Q) := hQ.center_nontrivial
      have hcZ : IsPGroup p ↥(Subgroup.center Q) := hQ.to_subgroup (Subgroup.center Q)
      obtain ⟨m, hm⟩ := hcZ.exists_card_eq
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, pow_zero] at hm
          exact absurd (Finite.one_lt_card_iff_nontrivial.mpr hZnt)
            (by rw [hm]; exact Nat.lt_irrefl 1)
        · exact h
      have hpdvd : p ∣ Nat.card ↥(Subgroup.center Q) :=
        hm ▸ dvd_pow_self p (Nat.pos_iff_ne_zero.mp hmpos)
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpdvd
      let C : Subgroup Q := Subgroup.zpowers (z : Q)
      have hCcard : Nat.card C = p := by
        show Nat.card ↥(Subgroup.zpowers (z : Q)) = p
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
      have hCle : C ≤ Subgroup.center Q := by
        show Subgroup.zpowers (z : Q) ≤ Subgroup.center Q
        rw [Subgroup.zpowers_le]
        exact z.2
      have hCnormal : C.Normal := Subgroup.Normal.mk fun n hn g => by
        have h1 : g * n = n * g := (Subgroup.mem_center_iff.mp (hCle hn)) g
        rw [h1, mul_inv_cancel_right]
        exact hn
      have hCn : C.Normal := hCnormal
      have hcard_quot : Nat.card (Q ⧸ C) = p ^ (k - 1) := by
        rw [← Subgroup.index_eq_card]
        have h1 : C.index * p = p ^ k := by
          have := Subgroup.index_mul_card C
          rw [hCcard, hcard] at this
          exact this
        have h2 : p ^ k = p ^ (k - 1) * p := by
          conv_lhs => rw [show k = (k - 1) + 1 from by omega]
          rw [Nat.pow_succ]
        exact Nat.mul_right_cancel (Fact.out : p.Prime).pos (h1.trans h2)
      have hbotC : Work.Shrinking.pCentralSeries p (Q ⧸ C) (k - 1) = ⊥ :=
        ih (k - 1) (Nat.sub_lt hkpos (by norm_num)) (Q ⧸ C)
          (hQ.of_surjective (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)) hcard_quot
      have hleC : Work.Shrinking.pCentralSeries p Q (k - 1) ≤ C := by
        have hmap := Work.Shrinking.map_pCentralSeries_surjective p (QuotientGroup.mk' C)
          (QuotientGroup.mk'_surjective C) (k - 1)
        rw [hbotC, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
        exact hmap
      have hCbot : Work.Shrinking.pCentralStep p C = ⊥ := by
        have hpow : Work.Shrinking.powSubgroup p C = ⊥ := by
          rw [Work.Shrinking.powSubgroup, Subgroup.closure_eq_bot_iff]
          rintro x ⟨y, hy, rfl⟩
          simp only [Set.mem_singleton_iff]
          refine orderOf_dvd_iff_pow_eq_one.mp ?_
          have h1 : orderOf y ∣ Nat.card C := by
            rw [← Nat.card_zpowers y]
            exact Subgroup.card_dvd_of_le (by rw [Subgroup.zpowers_le]; exact hy)
          rwa [hCcard] at h1
        have hcomm : ⁅C, (⊤ : Subgroup Q)⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro x hx
          simpa only [Subgroup.coe_top, Subgroup.centralizer_univ] using hCle hx
        rw [Work.Shrinking.pCentralStep, hpow, hcomm, bot_sup_eq]
      have hk : k = (k - 1) + 1 := by omega
      rw [hk, Work.Shrinking.pCentralSeries_succ]
      exact le_antisymm (le_trans (pCentralStep_mono' p hleC) (le_of_eq hCbot)) bot_le

/-- The descending `p`-central series of a finite `p`-group of order `p ^ k` reaches `⊥` at
step `k`; equivalently, every finite `p`-group of order `p ^ k` is a quotient of
`F^(n)/F^(n)(k)` for `n` generators. -/
theorem pCentralSeries_eq_bot_of_card_explicit (p : ℕ) [Fact p.Prime] {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) (k : ℕ) (hcard : Nat.card Q = p ^ k) :
    Work.Shrinking.pCentralSeries p Q k = ⊥ :=
  pCentralSeries_eq_bot_of_card_aux p k Q hQ hcard

/-- **Cofinality of the descending `p`-central filtration among normal subgroups of finite
`p`-power index.**  If `K ◁ P` with `P ⧸ K` a `p`-group of order `p ^ k`, then the `k`-th term
of the filtration is contained in `K`.

This is the finiteness input of Schmidt–Wingberg's argument: the filtration is cofinal, so every
finite `p`-group quotient of `P` is a quotient of some `F^(n)/F^(n)(ν)`.  Note that `P` itself is
not assumed finite or finitely generated — only the quotient is.

Proof (induction on `k`, avoiding Frattini theory).  Write `Q = P ⧸ K`.
* `k = 0`: `Q` is trivial, so `K = ⊤` and the claim is trivial.
* `k ≥ 1`: pick a subgroup `C ≤ Subgroup.center Q` of order `p`, let `K' ≤ P` be the preimage of
  `C` (`Subgroup.comap (QuotientGroup.mk' K) C`), and observe `Nat.card (P ⧸ K') = p ^ (k - 1)`.
  By the induction hypothesis, `pCentralSeries p P (k-1) ≤ K'`; then
  `pCentralSeries p P k = P_{k-1} ^ p ⁅P_{k-1}, P⁆ ≤ K' ^ p ⁅K', P⁆ ≤ K`,
  because `K'/K = C` is central of order `p` in `Q`, so `K' ^ p ≤ K` and `⁅K', P⁆ ≤ K`.
Alternatively, use `Work.ProP.pCentralSeries_eq_bot_of_card` (the `p`-central series of a finite
`p`-group of order `p ^ k` reaches `⊥` at step `k`) together with the compatibility of the
filtration with the surjection `P →* P ⧸ K`
(`Work.Shrinking.map_pCentralSeries_surjective`) and `Subgroup.map_eq_bot_iff`. -/
theorem pCentralSeries_le_of_pgroup_quotient {p : ℕ} [Fact p.Prime] {P : Type*} [Group P]
    (K : Subgroup P) [K.Normal] (hP : IsPGroup p (P ⧸ K)) {k : ℕ}
    (hcard : Nat.card (P ⧸ K) = p ^ k) :
    Work.Shrinking.pCentralSeries p P k ≤ K := by
  have hfin : Finite (P ⧸ K) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero k (Fact.out : p.Prime).ne_zero)
  have hbot : Work.Shrinking.pCentralSeries p (P ⧸ K) k = ⊥ :=
    pCentralSeries_eq_bot_of_card_explicit p hP k hcard
  have hmap := Work.Shrinking.map_pCentralSeries_surjective p (QuotientGroup.mk' K)
    (QuotientGroup.mk'_surjective K) k
  rw [hbot, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
  exact hmap

end Work.ProP
