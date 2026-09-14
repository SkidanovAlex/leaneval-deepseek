import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators

noncomputable section

namespace Commons.Data.Int

/-- If each of the pairwise-coprime positive moduli `m i` divides the integer `N`, then their
product divides `N`. -/
private lemma int_prod_dvd_of_pairwise_coprime {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hcop : ∀ i j : ι, i ≠ j → Nat.Coprime (m i) (m j)) (N : ℤ)
    (h : ∀ i : ι, (m i : ℤ) ∣ N) : (∏ i : ι, (m i : ℤ)) ∣ N := by
  classical
  exact Fintype.prod_dvd_of_coprime (R := ℤ) (s := fun i : ι => (m i : ℤ)) (z := N)
    (fun i j hij => Nat.Coprime.cast (hcop i j hij)) h

/-- Chinese-remainder uniqueness for arbitrarily many pairwise-coprime moduli: agreeing in
every `ZMod (m i)` forces agreement in `ZMod (∏ m i)`. -/
private lemma zmod_prod_eq_of_forall {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hcop : ∀ i j : ι, i ≠ j → Nat.Coprime (m i) (m j)) (z₁ z₂ : ℤ)
    (h : ∀ i, (z₁ : ZMod (m i)) = (z₂ : ZMod (m i))) :
    (z₁ : ZMod (∏ i : ι, m i)) = (z₂ : ZMod (∏ i : ι, m i)) := by
  classical
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have hdvd : ∀ i : ι, (m i : ℤ) ∣ z₂ - z₁ := fun i =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub z₁ z₂ (m i)).mp (h i)
  have hprod : (∏ i : ι, (m i : ℤ)) ∣ z₂ - z₁ :=
    int_prod_dvd_of_pairwise_coprime m hcop (z₂ - z₁) hdvd
  simpa using hprod

/-- A set of naturals in `[0, t]` that are pairwise congruent modulo `C` has at most
`t / C + 1` elements (each pair of distinct elements is separated by a multiple of `C`, so the
map `e ↦ e / C` is injective into `{0, ..., t / C}`). -/
private lemma card_le_div_add_one_of_pairwise_modEq (t C : ℕ)
    {E : Finset ℕ} (hE : ∀ e ∈ E, e ≤ t)
    (hmod : ∀ ⦃a : ℕ⦄, a ∈ E → ∀ ⦃b : ℕ⦄, b ∈ E → a ≡ b [MOD C]) :
    E.card ≤ t / C + 1 := by
  classical
  let Q : Finset ℕ := E.image (fun e : ℕ => e / C)
  have hQcard : Q.card = E.card := by
    dsimp [Q]
    rw [Finset.card_image_of_injOn]
    intro a ha b hb hq
    have hq' : a / C = b / C := by simpa using hq
    have hm : a % C = b % C := hmod ha hb
    calc
      a = C * (a / C) + a % C := by rw [Nat.div_add_mod]
      _ = (a / C) * C + a % C := by rw [mul_comm]
      _ = (b / C) * C + b % C := by rw [hq', hm]
      _ = C * (b / C) + b % C := by rw [mul_comm]
      _ = b := by rw [Nat.div_add_mod]
  have hQle : Q.card ≤ t / C + 1 := by
    have hsub : Q ⊆ Finset.range (t / C + 1) := by
      intro q hq
      rw [Finset.mem_range]
      rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
      have hle : e / C ≤ t / C := Nat.div_le_div_right (hE e he)
      omega
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
  rw [← hQcard]
  exact hQle

/-- Any single residue class modulo `C = ∏ m i` meets the interval `[-H, H]` in at most
`(2H + 1) / C + 1` integers. -/
private lemma fiber_card_le (H : ℕ) {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm1 : ∀ i, 1 ≤ m i)
    (hcop : ∀ i j : ι, i ≠ j → Nat.Coprime (m i) (m j))
    (a : (i : ι) → ZMod (m i)) :
    ((Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (fun z => ∀ i : ι, (z : ZMod (m i)) = a i)).card ≤
      (2 * H + 1) / (∏ i : ι, m i) + 1 := by
  classical
  let C : ℕ := ∏ i : ι, m i
  have hC : 1 ≤ C := by
    dsimp [C]
    have h : 1 ≤ ∏ i ∈ (Finset.univ : Finset ι), m i := Finset.one_le_prod (fun i hi => hm1 i)
    simpa using h
  let F := (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (fun z => ∀ i : ι, (z : ZMod (m i)) = a i)
  let W : Finset ℕ := F.image (fun z : ℤ => (z + (H : ℤ)).toNat)
  have hWle : W.card ≤ (2 * H) / C + 1 := by
    apply card_le_div_add_one_of_pairwise_modEq (t := 2 * H) (C := C)
    · intro w hw
      rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
      have hzI : z ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) := (Finset.mem_filter.mp hz).1
      have hzle : z ≤ (H : ℤ) := (Finset.mem_Icc.mp hzI).2
      have hnonneg : 0 ≤ z + (H : ℤ) := by
        have hzge : -(H : ℤ) ≤ z := (Finset.mem_Icc.mp hzI).1
        omega
      have hzH' : z + (H : ℤ) ≤ ((2 * H : ℕ) : ℤ) := by
        have hzH2 : z + (H : ℤ) ≤ 2 * (H : ℤ) := by omega
        have hnorm : 2 * (H : ℤ) = (((2 * H : ℕ) : ℤ)) := by norm_num
        rwa [← hnorm]
      have hwle : ((z + (H : ℤ)).toNat : ℤ) ≤ ((2 * H : ℕ) : ℤ) := by
        rwa [Int.toNat_of_nonneg hnonneg]
      exact_mod_cast hwle
    · intro w1 hw1 w2 hw2
      rcases Finset.mem_image.mp hw1 with ⟨z1, hz1, rfl⟩
      rcases Finset.mem_image.mp hw2 with ⟨z2, hz2, rfl⟩
      have hres : ∀ i : ι, (z1 : ZMod (m i)) = (z2 : ZMod (m i)) := by
        intro i
        have h1i := (Finset.mem_filter.mp hz1).2 i
        have h2i := (Finset.mem_filter.mp hz2).2 i
        exact h1i.trans h2i.symm
      have hcl : (z1 : ZMod (∏ i : ι, m i)) = (z2 : ZMod (∏ i : ι, m i)) :=
        zmod_prod_eq_of_forall m hcop z1 z2 hres
      rw [Nat.modEq_iff_dvd]
      have hdvd : (C : ℤ) ∣ z2 - z1 := by
        simpa [C] using (ZMod.intCast_eq_intCast_iff_dvd_sub z1 z2 (∏ i : ι, m i)).mp hcl
      have hnon1 : 0 ≤ z1 + (H : ℤ) := by
        have hz1ge : -(H : ℤ) ≤ z1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hz1).1).1
        omega
      have hnon2 : 0 ≤ z2 + (H : ℤ) := by
        have hz2ge : -(H : ℤ) ≤ z2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hz2).1).1
        omega
      have hc1 : (((z1 + (H : ℤ)).toNat : ℕ) : ℤ) = z1 + (H : ℤ) := Int.toNat_of_nonneg hnon1
      have hc2 : (((z2 + (H : ℤ)).toNat : ℕ) : ℤ) = z2 + (H : ℤ) := Int.toNat_of_nonneg hnon2
      rw [hc2, hc1]
      have hdiff : (z2 + (H : ℤ)) - (z1 + (H : ℤ)) = z2 - z1 := by ring
      rwa [hdiff]
  have hcard : F.card = W.card := by
    dsimp [W, F]
    rw [Finset.card_image_of_injOn]
    intro z1 hz1 z2 hz2 hto
    have hnon1 : 0 ≤ z1 + (H : ℤ) := by
      have hz1ge : -(H : ℤ) ≤ z1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hz1).1).1
      omega
    have hnon2 : 0 ≤ z2 + (H : ℤ) := by
      have hz2ge : -(H : ℤ) ≤ z2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hz2).1).1
      omega
    have hto' := congrArg (fun n : ℕ => (n : ℤ)) hto
    have hsum : z1 + (H : ℤ) = z2 + (H : ℤ) := by
      rwa [Int.toNat_of_nonneg hnon1, Int.toNat_of_nonneg hnon2] at hto'
    omega
  calc
    F.card = W.card := hcard
    _ ≤ (2 * H) / C + 1 := hWle
    _ ≤ (2 * H + 1) / C + 1 := by
      have hmono : (2 * H) / C ≤ (2 * H + 1) / C := Nat.div_le_div_right (by omega)
      omega

/-- Counting integers of bounded absolute value by multi-prime residue sets (the
joint CRT counting step behind Bhargava's Case III, subcase (ii)).

For pairwise coprime positive moduli `m i` and arbitrary residue sets
`R i ⊆ ZMod (m i)` of size at most `d`, the number of integers `z` with `|z| ≤ H`
whose residue mod `m i` lies in `R i` for every `i` is at most
`d ^ (Fintype.card ι) * ((2H+1)/(∏_i m i) + 1)`.

Idea: each such `z` gives a tuple `(z mod m i)_i` in `∏_i R i`; by the Chinese
remainder bijection (`ZMod (∏ m i) ≃ ∏ ZMod (m i)`) each tuple determines a
residue class mod `C = ∏ m i`, and an interval of length `2H+1` meets any single
class mod `C` in at most `(2H+1)/C + 1` integers. -/
theorem interval_congruent_product_card_le (H : ℕ) {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm1 : ∀ i, 1 ≤ m i) (hcop : ∀ i j : ι, i ≠ j → Nat.Coprime (m i) (m j))
    (d : ℕ) (R : ∀ i : ι, Set (ZMod (m i))) (hR : ∀ i : ι, (R i).ncard ≤ d) :
    ({z : ℤ | |z| ≤ (H : ℤ) ∧ ∀ i : ι, (z : ZMod (m i)) ∈ R i} : Set ℤ).ncard ≤
      d ^ Fintype.card ι * ((2 * H + 1) / (∏ i : ι, m i) + 1) := by
  classical
  let C : ℕ := ∏ i : ι, m i
  let A := (i : ι) → ZMod (m i)
  letI : ∀ i : ι, NeZero (m i) := fun i => ⟨by have := hm1 i; omega⟩
  let S : Finset ℤ := (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter
    (fun z => ∀ i : ι, (z : ZMod (m i)) ∈ R i)
  let P : Finset A := (Finset.univ : Finset A).filter (fun a : A => ∀ i : ι, a i ∈ R i)
  let Ffib : A → Finset ℤ := fun a => (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter
    (fun z => ∀ i : ι, (z : ZMod (m i)) = a i)
  -- the set in the statement is exactly `S`
  have hS : ({z : ℤ | |z| ≤ (H : ℤ) ∧ ∀ i : ι, (z : ZMod (m i)) ∈ R i} : Set ℤ).ncard = S.card := by
    have hSe : ({z : ℤ | |z| ≤ (H : ℤ) ∧ ∀ i : ι, (z : ZMod (m i)) ∈ R i} : Set ℤ) = (S : Set ℤ) := by
      ext z
      simp only [S, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      rw [abs_le]
    rw [hSe, Set.ncard_coe_finset]
  -- each fiber (fixed residue tuple) is a single class mod C, hence small
  have hF : ∀ a : A, (Ffib a).card ≤ (2 * H + 1) / C + 1 := by
    intro a
    dsimp [Ffib, C]
    exact fiber_card_le H m hm1 hcop a
  -- at most d ^ card ι residue tuples can occur
  have hP : P.card ≤ d ^ Fintype.card ι := by
    let Rtf : ∀ i : ι, Finset (ZMod (m i)) := fun i => (Set.toFinite (R i)).toFinset
    let Q := (Finset.univ : Finset ι).pi Rtf
    let τ : ((i : ι) → i ∈ (Finset.univ : Finset ι) → ZMod (m i)) → A :=
      fun f i => f i (Finset.mem_univ i)
    have hRtf : ∀ i, (Rtf i).card ≤ d := by
      intro i
      dsimp [Rtf]
      rw [← Set.ncard_eq_toFinset_card (R i) (Set.toFinite (R i))]
      exact hR i
    have hQcard : Q.card ≤ d ^ Fintype.card ι := by
      calc
        Q.card = ∏ i ∈ (Finset.univ : Finset ι), (Rtf i).card := by simp [Q, Finset.card_pi]
        _ ≤ d ^ (Finset.univ : Finset ι).card :=
          Finset.prod_le_pow_card (Finset.univ : Finset ι) (fun i => (Rtf i).card) d
            (fun i hi => hRtf i)
        _ = d ^ Fintype.card ι := by simp
    have hsub : P ⊆ Q.image τ := by
      intro a ha
      rw [Finset.mem_image]
      refine ⟨(fun i hi => a i), ?_, ?_⟩
      · rw [Finset.mem_pi]
        intro i hi
        have hai : a i ∈ R i := (Finset.mem_filter.mp ha).2 i
        dsimp [Rtf]
        exact (Set.Finite.mem_toFinset (Set.toFinite (R i))).2 hai
      · ext i
        rfl
    calc
      P.card ≤ (Q.image τ).card := Finset.card_le_card hsub
      _ ≤ Q.card := Finset.card_image_le
      _ ≤ d ^ Fintype.card ι := hQcard
  -- every z ∈ S lies in the fiber over its own residue tuple, which lies in P
  have hcover : S ⊆ P.biUnion Ffib := by
    intro z hz
    have hzI : z ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) := (Finset.mem_filter.mp hz).1
    have hzmem : ∀ i : ι, (z : ZMod (m i)) ∈ R i := (Finset.mem_filter.mp hz).2
    let a : A := fun i => (z : ZMod (m i))
    refine Finset.mem_biUnion.mpr ⟨a, ?_, ?_⟩
    · dsimp [P]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i
      exact hzmem i
    · dsimp [Ffib]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact hzI
      · intro i
        rfl
  rw [hS]
  have hb1 : S.card ≤ ∑ a ∈ P, (Ffib a).card := by
    calc
      S.card ≤ (P.biUnion Ffib).card := Finset.card_le_card hcover
      _ ≤ ∑ a ∈ P, (Ffib a).card := Finset.card_biUnion_le
  have hb2 : (∑ a ∈ P, (Ffib a).card) ≤ P.card * ((2 * H + 1) / C + 1) := by
    calc
      (∑ a ∈ P, (Ffib a).card) ≤ ∑ a ∈ P, ((2 * H + 1) / C + 1) :=
        Finset.sum_le_sum (fun a ha => hF a)
      _ = P.card * ((2 * H + 1) / C + 1) := by
        simp [Finset.sum_const]
  have hb3 : P.card * ((2 * H + 1) / C + 1) ≤ d ^ Fintype.card ι * ((2 * H + 1) / C + 1) :=
    Nat.mul_le_mul_right ((2 * H + 1) / C + 1) hP
  have hfin : S.card ≤ d ^ Fintype.card ι * ((2 * H + 1) / C + 1) :=
    le_trans (le_trans hb1 hb2) hb3
  simpa [C] using hfin

end Commons.Data.Int
