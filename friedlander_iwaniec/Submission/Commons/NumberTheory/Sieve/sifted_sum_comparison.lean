import Mathlib
import Submission.Commons.Algebra.BigOperators.prod_sub_prod_eq_sum_split
import Submission.Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors

import Submission.Commons.NumberTheory.Nat.prod_pm1_pm2_eq_divisor_sum
set_option maxHeartbeats 1000000
namespace Commons.NumberTheory.Sieve

private lemma coprime_of_primeFactors_lt_gt {m ℓ p0 : ℕ} (hm : m ≠ 0) (hℓ : ℓ ≠ 0)
    (hm_lt : ∀ q ∈ m.primeFactors, q < p0) (hℓ_gt : ∀ q ∈ ℓ.primeFactors, p0 < q) :
    Nat.Coprime m ℓ := by
  by_contra hc
  rcases Nat.Prime.not_coprime_iff_dvd.mp hc with ⟨q, hq, hqm, hqℓ⟩
  have h1 : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqm, hm⟩
  have h2 : q ∈ ℓ.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqℓ, hℓ⟩
  have h3 := hm_lt q h1
  have h4 := hℓ_gt q h2
  omega

private lemma coprime_mul_prime_of_lt {m p0 : ℕ} (hm : m ≠ 0) (hp : Nat.Prime p0)
    (hm_lt : ∀ q ∈ m.primeFactors, q < p0) : Nat.Coprime m p0 := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hdvd
  have hm2 : p0 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdvd, hm⟩
  have h3 := hm_lt p0 hm2
  omega

private lemma coprime_prime_of_gt {p0 ℓ : ℕ} (hℓ : ℓ ≠ 0) (hp : Nat.Prime p0)
    (hℓ_gt : ∀ q ∈ ℓ.primeFactors, p0 < q) : Nat.Coprime p0 ℓ := by
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  have hℓ2 : p0 ∈ ℓ.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdvd, hℓ⟩
  have h3 := hℓ_gt p0 hℓ2
  omega

private lemma squarefree_mul_prime {m p ℓ : ℕ} (hm : Squarefree m) (hℓ : Squarefree ℓ) (hp : Nat.Prime p)
    (hmp : Nat.Coprime m p) (hpℓ : Nat.Coprime p ℓ) (hmℓ : Nat.Coprime m ℓ) :
    Squarefree (m * p * ℓ) := by
  rw [Nat.squarefree_mul (Nat.Coprime.mul_left hmℓ hpℓ)]
  refine ⟨?_, hℓ⟩
  rw [Nat.squarefree_mul hmp]
  exact ⟨hm, hp.squarefree⟩

private lemma pf_prod_filter (s : Finset ℕ) (hs : ∀ q ∈ s, Nat.Prime q) (P : ℕ → Prop) [DecidablePred P] :
    (∏ q ∈ s.filter P, q).primeFactors = s.filter P :=
  Nat.primeFactors_prod (fun q hq => hs q (Finset.mem_of_mem_filter q hq))

private lemma prod_split (s : Finset ℕ) (p : ℕ) (hp : p ∈ s) :
    ∏ q ∈ s, q = (∏ q ∈ s.filter (fun q => q < p), q) * p * (∏ q ∈ s.filter (fun q => p < q), q) := by
  have h1 : (∏ q ∈ s.erase p, q) * p = ∏ q ∈ s, q := Finset.prod_erase_mul s (fun q => q) hp
  have herase : s.erase p = s.filter (fun q => q < p) ∪ s.filter (fun q => p < q) := by
    ext q
    rw [Finset.mem_erase, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hne, hmem⟩
      rcases lt_trichotomy q p with h | h | h
      · exact Or.inl ⟨hmem, h⟩
      · exact absurd h hne
      · exact Or.inr ⟨hmem, h⟩
    · rintro (⟨hmem, h⟩ | ⟨hmem, h⟩)
      · exact ⟨by omega, hmem⟩
      · exact ⟨by omega, hmem⟩
  have hdisj : Disjoint (s.filter (fun q => q < p)) (s.filter (fun q => p < q)) := by
    rw [Finset.disjoint_left]
    intro q hq hq2
    rw [Finset.mem_filter] at hq hq2
    omega
  rw [← h1, herase, Finset.prod_union hdisj]
  ring

private lemma nat_primeFactors_of_squarefree {n p : ℕ} (hn : Squarefree n) (hp : p ∈ n.primeFactors) :
    n = (∏ q ∈ n.primeFactors.filter (fun q => q < p), q) * p * (∏ q ∈ n.primeFactors.filter (fun q => p < q), q) := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hn]
  exact prod_split n.primeFactors p hp

private lemma primeFactors_mul_prime {m p ℓ : ℕ} (hm : m ≠ 0) (hℓ : ℓ ≠ 0) (hp : Nat.Prime p) :
    (m * p * ℓ).primeFactors = m.primeFactors ∪ {p} ∪ ℓ.primeFactors := by
  rw [Nat.primeFactors_mul (Nat.mul_ne_zero hm hp.ne_zero) hℓ,
      Nat.primeFactors_mul hm hp.ne_zero, hp.primeFactors]

private lemma filter_lt_primeFactors_mul {m p ℓ : ℕ} (hm : m ≠ 0) (hℓ : ℓ ≠ 0) (hp : Nat.Prime p)
    (hm_lt : ∀ q ∈ m.primeFactors, q < p) (hℓ_gt : ∀ q ∈ ℓ.primeFactors, p < q) :
    (m * p * ℓ).primeFactors.filter (fun q => q < p) = m.primeFactors := by
  rw [primeFactors_mul_prime hm hℓ hp]
  ext q
  rw [Finset.mem_filter, Finset.mem_union, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨hmain, hq⟩
    rcases hmain with (hmem | hmem) | hmem
    · exact hmem
    · subst hmem; omega
    · exact absurd (hℓ_gt q hmem) (by omega)
  · intro hq
    exact ⟨Or.inl (Or.inl hq), hm_lt q hq⟩

private lemma filter_gt_primeFactors_mul {m p ℓ : ℕ} (hm : m ≠ 0) (hℓ : ℓ ≠ 0) (hp : Nat.Prime p)
    (hm_lt : ∀ q ∈ m.primeFactors, q < p) (hℓ_gt : ∀ q ∈ ℓ.primeFactors, p < q) :
    (m * p * ℓ).primeFactors.filter (fun q => p < q) = ℓ.primeFactors := by
  rw [primeFactors_mul_prime hm hℓ hp]
  ext q
  rw [Finset.mem_filter, Finset.mem_union, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨hmain, hq⟩
    rcases hmain with (hmem | hmem) | hmem
    · exact absurd (hm_lt q hmem) (by omega)
    · subst hmem; omega
    · exact hmem
  · intro hq
    exact ⟨Or.inr hq, hℓ_gt q hq⟩

open Finset
open scoped BigOperators

private lemma mu_mul_inv_mul (m k : ℕ) (h : Nat.Coprime m k) :
    (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * (1 / (n : ℝ))) (m * k)
      = (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * (1 / (n : ℝ))) m
        * (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * (1 / (n : ℝ))) k := by
  simp only
  have hmu : (ArithmeticFunction.moebius (m * k) : ℝ)
      = (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius k : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]
    push_cast
    ring
  rw [hmu]
  rw [show ((m * k : ℕ) : ℝ) = (m:ℝ) * (k:ℝ) from by push_cast; ring]
  rw [one_div, one_div, one_div, mul_inv]
  ring

private lemma moebius_mul_one_div_eq_prod (n : ℕ) (hn : Squarefree n) :
    (ArithmeticFunction.moebius n : ℝ) * (1 / (n : ℝ))
      = ∏ p ∈ n.primeFactors, (-(1 / (p : ℝ))) := by
  have hmul := mu_mul_inv_mul
  have h1 : (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * (1 / (n : ℝ))) 1 = 1 := by
    norm_num
  have hkey := Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors
      (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * (1 / (n : ℝ))) hmul h1 hn
  rw [hkey]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hmu : (ArithmeticFunction.moebius p : ℝ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hpp]
    norm_num
  rw [hmu]
  ring

private lemma gj_mul (g : ℕ → ℝ) (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (ν : ℕ) :
    ∀ m k : ℕ, Nat.Coprime m k →
      (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * g n * (if Nat.Coprime n ν then 1 else 0)) (m * k)
        = (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * g n * (if Nat.Coprime n ν then 1 else 0)) m
          * (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * g n * (if Nat.Coprime n ν then 1 else 0)) k := by
  intro m k h
  simp only
  have hmu : (ArithmeticFunction.moebius (m * k) : ℝ)
      = (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius k : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]
    push_cast
    ring
  have hg : g (m * k) = g m * g k := hgmul m k h
  have hind : (if Nat.Coprime (m * k) ν then (1:ℝ) else 0)
      = (if Nat.Coprime m ν then (1:ℝ) else 0) * (if Nat.Coprime k ν then (1:ℝ) else 0) := by
    rcases em (Nat.Coprime m ν) with hm | hm <;> rcases em (Nat.Coprime k ν) with hk | hk
    · rw [if_pos hm, if_pos hk, if_pos (by rw [Nat.coprime_mul_iff_left]; exact ⟨hm, hk⟩)]; ring
    · rw [if_pos hm, if_neg hk, if_neg (by rw [Nat.coprime_mul_iff_left]; exact fun hc => hk hc.2)]; ring
    · rw [if_neg hm, if_neg (by rw [Nat.coprime_mul_iff_left]; exact fun hc => hm hc.1)]; ring
    · rw [if_neg hm, if_neg (by rw [Nat.coprime_mul_iff_left]; exact fun hc => hm hc.1)]; ring
  rw [hmu, hg, hind]
  ring

private lemma moebius_mul_g_coprime_eq_prod (g : ℕ → ℝ)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (g1 : g 1 = 1)
    (ν n : ℕ) (hn : Squarefree n) :
    (ArithmeticFunction.moebius n : ℝ) * g n * (if Nat.Coprime n ν then 1 else 0)
      = ∏ p ∈ n.primeFactors, (-(g p) * (if p ∣ ν then 0 else 1)) := by
  have hmul := gj_mul g hgmul ν
  have h1 : (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * g n * (if Nat.Coprime n ν then 1 else 0)) 1 = 1 := by
    simp [g1]
  have hkey := Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors
      (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * g n * (if Nat.Coprime n ν then 1 else 0)) hmul h1 hn
  rw [hkey]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hmu : (ArithmeticFunction.moebius p : ℝ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hpp]
    norm_num
  have hcop : (if Nat.Coprime p ν then (1:ℝ) else 0) = (if p ∣ ν then (0:ℝ) else 1) := by
    rcases em (p ∣ ν) with hpv | hpv
    · rw [if_neg (fun hc => ((Nat.Prime.coprime_iff_not_dvd hpp).mp hc) hpv), if_pos hpv]
    · rw [if_pos ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpv), if_neg hpv]
  rw [hmu, hcop]
  ring

theorem sifted_sum_comparison
    (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (g1 : g 1 = 1)
    (ν : ℕ) {z w : ℝ} (hz : 2 ≤ z) (hw : 2 ≤ w) {h : ℝ} (hh : 0 ≤ h)
    (hrange : ∀ u v : ℕ, ⌈z⌉₊ ≤ u →
      |∑ p ∈ (Finset.Icc u v).filter Nat.Prime,
          (1 / (p : ℝ) - if p ∣ ν then 0 else g p)| ≤ h) :
    |(∑ n ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun n => ∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p : ℝ)),
          (ArithmeticFunction.moebius n : ℝ) * (1 / (n : ℝ))) -
      (∑ n ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun n =>
          (∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p : ℝ)) ∧ Nat.Coprime n ν),
          (ArithmeticFunction.moebius n : ℝ) * g n)|
    ≤ h * (∑ m ∈ (Finset.Icc 1 ⌊w⌋₊), 1 / (m : ℝ)) * (∑ n ∈ (Finset.Icc 1 ⌊w⌋₊), g n) := by
  classical
  set zz : ℕ := ⌈z⌉₊ with hzz
  have hzz2 : 2 ≤ zz := by
    have h : (2:ℝ) ≤ (⌈z⌉₊:ℝ) := le_trans hz (Nat.le_ceil z)
    rw [hzz]; exact Nat.cast_le.mp h
  set M : ℕ := ⌊w⌋₊ with hM
  set F : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ) * (1 / (n : ℝ)) with hF
  set Gt : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ) * g n * (if Nat.Coprime n ν then 1 else 0) with hGt
  set FR : Finset ℕ := (Finset.Icc 1 M).filter (fun n => ∀ p ∈ n.primeFactors, zz ≤ p) with hFR
  set T : Finset ℕ := FR.filter Squarefree with hT
  have hrough : ∀ n : ℕ, (∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p:ℝ)) ↔ (∀ p ∈ n.primeFactors, zz ≤ p) := by
    intro n
    constructor
    · intro hh p hp; rw [hzz]; exact Nat.ceil_le.mpr (hh p hp)
    · intro hh p hp; rw [hzz] at hh; exact Nat.ceil_le.mp (hh p hp)
  have hzero : ∀ n : ℕ, ¬ Squarefree n → (ArithmeticFunction.moebius n : ℝ) = 0 := by
    intro n hn
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
    simp
  -- Step A
  have hS1 : (∑ n ∈ (Finset.Icc 1 M).filter (fun n => ∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p:ℝ)), F n)
      = ∑ n ∈ T, F n := by
    have h1 : (Finset.Icc 1 M).filter (fun n => ∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p:ℝ)) = FR := by
      rw [hFR]; exact Finset.filter_congr (fun n _ => hrough n)
    rw [h1]
    symm
    refine Finset.sum_subset ?_ ?_
    · rw [hT]; exact Finset.filter_subset _ _
    · intro n hnFR hnT
      rw [hT, Finset.mem_filter] at hnT
      have hns : ¬ Squarefree n := fun hs => hnT ⟨hnFR, hs⟩
      rw [hF]
      simp [hzero n hns]
  have hS2 : (∑ n ∈ (Finset.Icc 1 M).filter (fun n =>
          (∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p:ℝ)) ∧ Nat.Coprime n ν),
          (ArithmeticFunction.moebius n : ℝ) * g n)
      = ∑ n ∈ T, Gt n := by
    have h1 : (Finset.Icc 1 M).filter (fun n =>
          (∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p:ℝ)) ∧ Nat.Coprime n ν)
        = FR.filter (fun n => Nat.Coprime n ν) := by
      ext n
      rw [Finset.mem_filter, Finset.mem_filter, hFR, Finset.mem_filter]
      constructor
      · rintro ⟨hn, hr, hc⟩; exact ⟨⟨hn, (hrough n).mp hr⟩, hc⟩
      · rintro ⟨⟨hn, hr⟩, hc⟩; exact ⟨hn, (hrough n).mpr hr, hc⟩
    have ha : (∑ n ∈ FR.filter (fun n => Nat.Coprime n ν), (ArithmeticFunction.moebius n : ℝ) * g n)
        = ∑ n ∈ (FR.filter (fun n => Nat.Coprime n ν)).filter Squarefree, (ArithmeticFunction.moebius n : ℝ) * g n := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro n hn hnt
      have hns : ¬ Squarefree n := fun hs => hnt (Finset.mem_filter.mpr ⟨hn, hs⟩)
      simp [hzero n hns]
    have hb : (FR.filter (fun n => Nat.Coprime n ν)).filter Squarefree
        = (FR.filter Squarefree).filter (fun n => Nat.Coprime n ν) := by
      rw [Finset.filter_filter (fun n => Nat.Coprime n ν) Squarefree FR,
          Finset.filter_filter Squarefree (fun n => Nat.Coprime n ν) FR]
      exact Finset.filter_congr (fun n _ => and_comm)
    have hc : (∑ n ∈ (FR.filter Squarefree).filter (fun n => Nat.Coprime n ν), (ArithmeticFunction.moebius n : ℝ) * g n)
        = ∑ n ∈ FR.filter Squarefree, Gt n := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro n hn
      rw [hGt]
      by_cases hcv : Nat.Coprime n ν <;> simp [hcv]
    rw [h1, ha, hb, hc, hT]
  have hD : (∑ n ∈ (Finset.Icc 1 M).filter (fun n => ∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p:ℝ)), F n)
      - (∑ n ∈ (Finset.Icc 1 M).filter (fun n =>
          (∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p:ℝ)) ∧ Nat.Coprime n ν),
          (ArithmeticFunction.moebius n : ℝ) * g n)
      = ∑ n ∈ T, (F n - Gt n) := by
    rw [hS1, hS2, ← Finset.sum_sub_distrib]
  rw [hD]
  set A1 : ℕ → ℝ := fun p => -(1 / (p : ℝ)) with hA1
  set B1 : ℕ → ℝ := fun p => -(g p) * (if p ∣ ν then 0 else 1) with hB1
  have htel : ∀ n ∈ T, F n - Gt n = ∑ p ∈ n.primeFactors,
      (∏ q ∈ n.primeFactors.filter (fun q => q < p), A1 q) * (A1 p - B1 p)
        * (∏ q ∈ n.primeFactors.filter (fun q => p < q), B1 q) := by
    intro n hn
    rw [hT, Finset.mem_filter] at hn
    obtain ⟨hnFR, hnsq⟩ := hn
    have hFn : F n = ∏ p ∈ n.primeFactors, A1 p := by
      rw [hF, hA1]; exact moebius_mul_one_div_eq_prod n hnsq
    have hGn : Gt n = ∏ p ∈ n.primeFactors, B1 p := by
      rw [hGt, hB1]; exact moebius_mul_g_coprime_eq_prod g hgmul g1 ν n hnsq
    rw [hFn, hGn]
    exact Commons.Algebra.BigOperators.prod_sub_prod_eq_sum_split n.primeFactors A1 B1
  have hD2 : ∑ n ∈ T, (F n - Gt n) = ∑ n ∈ T, ∑ p ∈ n.primeFactors,
      (∏ q ∈ n.primeFactors.filter (fun q => q < p), A1 q) * (A1 p - B1 p)
        * (∏ q ∈ n.primeFactors.filter (fun q => p < q), B1 q) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    exact htel n hn
  rw [hD2]

  -- Step C
  set Φ : (Σ _ : ℕ, ℕ) → ℝ := fun x =>
      (∏ q ∈ x.1.primeFactors.filter (fun q => q < x.2), A1 q) * (A1 x.2 - B1 x.2)
        * (∏ q ∈ x.1.primeFactors.filter (fun q => x.2 < q), B1 q) with hΦ
  have hSig : (∑ n ∈ T, ∑ p ∈ n.primeFactors,
        (∏ q ∈ n.primeFactors.filter (fun q => q < p), A1 q) * (A1 p - B1 p)
          * (∏ q ∈ n.primeFactors.filter (fun q => p < q), B1 q))
      = ∑ x ∈ T.sigma (fun n => n.primeFactors), Φ x := by
    rw [Finset.sum_sigma]
  rw [hSig]

  -- Step C: Trip and reindexing
  set iFn : (Σ _ : ℕ, ℕ) → (ℕ × ℕ × ℕ) := fun x =>
      ((∏ q ∈ x.1.primeFactors.filter (fun q => q < x.2), q), x.2,
        (∏ q ∈ x.1.primeFactors.filter (fun q => x.2 < q), q)) with hiFn
  set Trip : Finset (ℕ × ℕ × ℕ) :=
      ((Finset.Icc 1 M) ×ˢ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M))).filter (fun x =>
        Nat.Prime x.2.1 ∧ zz ≤ x.2.1 ∧ Squarefree x.1 ∧ Squarefree x.2.2
          ∧ (∀ q ∈ x.1.primeFactors, zz ≤ q) ∧ (∀ q ∈ x.2.2.primeFactors, zz ≤ q)
          ∧ (∀ q ∈ x.1.primeFactors, q < x.2.1) ∧ (∀ q ∈ x.2.2.primeFactors, x.2.1 < q)
          ∧ x.1 * x.2.1 * x.2.2 ≤ M) with hTrip
  set Ψ : (ℕ × ℕ × ℕ) → ℝ := fun y => F y.1 * (A1 y.2.1 - B1 y.2.1) * Gt y.2.2 with hΨ
  have hTrip_mem : ∀ m p ℓ : ℕ, (m, p, ℓ) ∈ Trip ↔
      1 ≤ m ∧ m ≤ M ∧ 1 ≤ p ∧ p ≤ M ∧ 1 ≤ ℓ ∧ ℓ ≤ M ∧ Nat.Prime p ∧ zz ≤ p
        ∧ Squarefree m ∧ Squarefree ℓ
        ∧ (∀ q ∈ m.primeFactors, zz ≤ q) ∧ (∀ q ∈ ℓ.primeFactors, zz ≤ q)
        ∧ (∀ q ∈ m.primeFactors, q < p) ∧ (∀ q ∈ ℓ.primeFactors, p < q)
        ∧ m * p * ℓ ≤ M := by
    intro m p ℓ
    rw [hTrip, Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_Icc, Finset.mem_Icc]
    tauto
  have hCard : ∑ x ∈ T.sigma (fun n => n.primeFactors), Φ x = ∑ y ∈ Trip, Ψ y := by
    refine Finset.sum_bij (fun x _ => iFn x) ?_ ?_ ?_ ?_
    · rintro ⟨n, p⟩ hx
      rw [Finset.mem_sigma] at hx
      obtain ⟨hnT, hp⟩ := hx
      rw [hT, Finset.mem_filter] at hnT
      obtain ⟨hnFR, hnsq⟩ := hnT
      rw [hFR, Finset.mem_filter, Finset.mem_Icc] at hnFR
      obtain ⟨⟨hn1, hnM⟩, hnrough⟩ := hnFR
      have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
      have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      rw [hiFn]
      simp only []
      rw [hTrip_mem]
      set m : ℕ := ∏ q ∈ n.primeFactors.filter (fun q => q < p), q with hm
      set ℓ : ℕ := ∏ q ∈ n.primeFactors.filter (fun q => p < q), q with hℓ
      have hpfm : m.primeFactors = n.primeFactors.filter (fun q => q < p) := by
        rw [hm]; exact pf_prod_filter n.primeFactors (fun q hq => Nat.prime_of_mem_primeFactors hq) (fun q => q < p)
      have hpfℓ : ℓ.primeFactors = n.primeFactors.filter (fun q => p < q) := by
        rw [hℓ]; exact pf_prod_filter n.primeFactors (fun q hq => Nat.prime_of_mem_primeFactors hq) (fun q => p < q)
      have hsqm : Squarefree m := by
        rw [hm]; exact Commons.NumberTheory.Nat.squarefree_prod_of_prime
          (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq))
      have hsqℓ : Squarefree ℓ := by
        rw [hℓ]; exact Commons.NumberTheory.Nat.squarefree_prod_of_prime
          (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq))
      have hm1 : 1 ≤ m := by
        rw [hm]; exact Finset.one_le_prod₀ (fun q hq => (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq)).one_le)
      have hℓ1 : 1 ≤ ℓ := by
        rw [hℓ]; exact Finset.one_le_prod₀ (fun q hq => (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq)).one_le)
      have hmprod : m * p * ℓ = n := (nat_primeFactors_of_squarefree hnsq hp).symm
      have hmM : m ≤ M := by
        have hdvd : m ∣ n := ⟨p * ℓ, by rw [← hmprod]; ring⟩
        calc m ≤ n := Nat.le_of_dvd (by omega) hdvd
          _ ≤ M := hnM
      have hℓM : ℓ ≤ M := by
        have hdvd : ℓ ∣ n := ⟨m * p, by rw [← hmprod]; ring⟩
        calc ℓ ≤ n := Nat.le_of_dvd (by omega) hdvd
          _ ≤ M := hnM
      have hp1 : 1 ≤ p := hpp.one_le
      have hpM : p ≤ M := by
        have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
        calc p ≤ n := Nat.le_of_dvd (by omega) hdvd
          _ ≤ M := hnM
      have hzzp : zz ≤ p := hnrough p hp
      refine ⟨hm1, hmM, hp1, hpM, hℓ1, hℓM, hpp, hzzp, hsqm, hsqℓ, ?_, ?_, ?_, ?_, ?_⟩
      · intro q hq; rw [hpfm] at hq; exact hnrough q (Finset.mem_of_mem_filter q hq)
      · intro q hq; rw [hpfℓ] at hq; exact hnrough q (Finset.mem_of_mem_filter q hq)
      · intro q hq; rw [hpfm] at hq; exact (Finset.mem_filter.mp hq).2
      · intro q hq; rw [hpfℓ] at hq; exact (Finset.mem_filter.mp hq).2
      · rw [hmprod]; exact hnM
    · rintro ⟨n1, p1⟩ hx1 ⟨n2, p2⟩ hx2 heq
      rw [Finset.mem_sigma] at hx1 hx2
      obtain ⟨hn1T0, hp10⟩ := hx1
      obtain ⟨hn2T0, hp20⟩ := hx2
      have hn1T : n1 ∈ T := hn1T0
      have hn2T : n2 ∈ T := hn2T0
      have hp1 : p1 ∈ n1.primeFactors := hp10
      have hp2 : p2 ∈ n2.primeFactors := hp20
      rw [hT, Finset.mem_filter] at hn1T hn2T
      obtain ⟨_, hnsq1⟩ := hn1T
      obtain ⟨_, hnsq2⟩ := hn2T
      rw [hiFn] at heq
      have hp_eq : p1 = p2 := by
        have h := congrArg (fun y : ℕ × ℕ × ℕ => y.2.1) heq
        simpa using h
      have hm_eq : (∏ q ∈ n1.primeFactors.filter (fun q => q < p1), q)
          = (∏ q ∈ n2.primeFactors.filter (fun q => q < p2), q) := by
        have h := congrArg (fun y : ℕ × ℕ × ℕ => y.1) heq
        simpa using h
      have hℓ_eq : (∏ q ∈ n1.primeFactors.filter (fun q => p1 < q), q)
          = (∏ q ∈ n2.primeFactors.filter (fun q => p2 < q), q) := by
        have h := congrArg (fun y : ℕ × ℕ × ℕ => y.2.2) heq
        simpa using h
      have hn_eq : n1 = n2 := by
        rw [nat_primeFactors_of_squarefree hnsq1 hp1, nat_primeFactors_of_squarefree hnsq2 hp2,
            hm_eq, hℓ_eq, hp_eq]
      rw [hn_eq, hp_eq]
    · rintro ⟨m, p, ℓ⟩ hy
      rw [hTrip_mem] at hy
      obtain ⟨hm1, hmM, hp1, hpM, hℓ1, hℓM, hpp, hzzp, hsqm, hsqℓ, hrm, hrℓ, hmlt, hℓgt, hprod⟩ := hy
      have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm1
      have hℓ0 : ℓ ≠ 0 := Nat.one_le_iff_ne_zero.mp hℓ1
      have hp0 : p ≠ 0 := hpp.ne_zero
      have hn0 : m * p * ℓ ≠ 0 := Nat.mul_ne_zero (Nat.mul_ne_zero hm0 hp0) hℓ0
      have hcmp : Nat.Coprime m p := coprime_mul_prime_of_lt hm0 hpp hmlt
      have hcpℓ : Nat.Coprime p ℓ := coprime_prime_of_gt hℓ0 hpp hℓgt
      have hmℓ : Nat.Coprime m ℓ := coprime_of_primeFactors_lt_gt hm0 hℓ0 hmlt hℓgt
      have hsqn : Squarefree (m * p * ℓ) := squarefree_mul_prime hsqm hsqℓ hpp hcmp hcpℓ hmℓ
      refine ⟨⟨m * p * ℓ, p⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma]
        refine ⟨?_, Nat.mem_primeFactors.mpr ⟨hpp, ⟨m * ℓ, by ring⟩, hn0⟩⟩
        rw [hT, Finset.mem_filter]
        refine ⟨?_, hsqn⟩
        rw [hFR, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.one_le_iff_ne_zero.mpr hn0, hprod⟩, ?_⟩
        rw [primeFactors_mul_prime hm0 hℓ0 hpp]
        intro q hq
        rw [Finset.mem_union, Finset.mem_union, Finset.mem_singleton] at hq
        rcases hq with (hq | hq) | hq
        · exact hrm q hq
        · rw [hq]; exact hzzp
        · exact hrℓ q hq
      · rw [hiFn]
        simp only []
        have hfl : (m * p * ℓ).primeFactors.filter (fun q => q < p) = m.primeFactors :=
          filter_lt_primeFactors_mul hm0 hℓ0 hpp hmlt hℓgt
        have hfg : (m * p * ℓ).primeFactors.filter (fun q => p < q) = ℓ.primeFactors :=
          filter_gt_primeFactors_mul hm0 hℓ0 hpp hmlt hℓgt
        rw [hfl, hfg, Nat.prod_primeFactors_of_squarefree hsqm,
            Nat.prod_primeFactors_of_squarefree hsqℓ]
    · rintro ⟨n, p⟩ hx
      rw [Finset.mem_sigma] at hx
      obtain ⟨hnT, hp⟩ := hx
      rw [hT, Finset.mem_filter] at hnT
      obtain ⟨hnFR, hnsq⟩ := hnT
      rw [hFR, Finset.mem_filter] at hnFR
      obtain ⟨hnIcc, hnrough⟩ := hnFR
      set m : ℕ := ∏ q ∈ n.primeFactors.filter (fun q => q < p), q with hm
      set ℓ : ℕ := ∏ q ∈ n.primeFactors.filter (fun q => p < q), q with hℓ
      have hpfm : m.primeFactors = n.primeFactors.filter (fun q => q < p) := by
        rw [hm]; exact pf_prod_filter n.primeFactors (fun q hq => Nat.prime_of_mem_primeFactors hq) (fun q => q < p)
      have hpfℓ : ℓ.primeFactors = n.primeFactors.filter (fun q => p < q) := by
        rw [hℓ]; exact pf_prod_filter n.primeFactors (fun q hq => Nat.prime_of_mem_primeFactors hq) (fun q => p < q)
      have hsqm : Squarefree m := by
        rw [hm]; exact Commons.NumberTheory.Nat.squarefree_prod_of_prime
          (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq))
      have hsqℓ : Squarefree ℓ := by
        rw [hℓ]; exact Commons.NumberTheory.Nat.squarefree_prod_of_prime
          (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq))
      rw [hΦ, hΨ, hiFn]
      simp only []
      have hFm : F m = ∏ q ∈ n.primeFactors.filter (fun q => q < p), A1 q := by
        rw [hF, hA1, ← hpfm]
        exact moebius_mul_one_div_eq_prod m hsqm
      have hGℓ : Gt ℓ = ∏ q ∈ n.primeFactors.filter (fun q => p < q), B1 q := by
        rw [hGt, hB1, ← hpfℓ]
        exact moebius_mul_g_coprime_eq_prod g hgmul g1 ν ℓ hsqℓ
      rw [← hFm, ← hGℓ]
  rw [hCard]
  set P : Finset (ℕ × ℕ) := Trip.image (fun y => (y.1, y.2.2)) with hP
  have hgroup : ∑ y ∈ Trip, Ψ y
      = ∑ ml ∈ P, F ml.1 * Gt ml.2
          * (∑ y ∈ Trip.filter (fun y => (y.1, y.2.2) = ml), (A1 y.2.1 - B1 y.2.1)) := by
    have key : (∑ ml ∈ P, F ml.1 * Gt ml.2
          * (∑ y ∈ Trip.filter (fun y => (y.1, y.2.2) = ml), (A1 y.2.1 - B1 y.2.1)))
        = ∑ ml ∈ P, ∑ y ∈ Trip.filter (fun y => (y.1, y.2.2) = ml),
            F ml.1 * Gt ml.2 * (A1 y.2.1 - B1 y.2.1) := by
      refine Finset.sum_congr rfl (fun ml _ => ?_)
      rw [Finset.mul_sum]
    rw [key, Finset.sum_sigma']
    refine Finset.sum_bij
      (fun y _ => (⟨(y.1, y.2.2), y⟩ : Sigma (fun _ : ℕ × ℕ => ℕ × ℕ × ℕ))) ?_ ?_ ?_ ?_
    · intro y hy
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_image.mpr ⟨y, hy, rfl⟩, Finset.mem_filter.mpr ⟨hy, rfl⟩⟩
    · intro y1 hy1 y2 hy2 heq
      exact congrArg Sigma.snd heq
    · intro x hx
      rw [Finset.mem_sigma] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [Finset.mem_filter] at hx2
      refine ⟨x.2, hx2.1, ?_⟩
      rw [hx2.2]
    · intro y hy
      rw [hΨ]
      show F y.1 * (A1 y.2.1 - B1 y.2.1) * Gt y.2.2
        = F y.1 * Gt y.2.2 * (A1 y.2.1 - B1 y.2.1)
      ring
  rw [hgroup]
  have hAB : ∀ p : ℕ, A1 p - B1 p = -(1/(p:ℝ) - (if p ∣ ν then 0 else g p)) := by
    intro p; rw [hA1, hB1]; by_cases h : p ∣ ν
    · simp [h]
    · simp [h]; ring
  have hfb : ∀ ml ∈ P, |∑ y ∈ Trip.filter (fun y => (y.1, y.2.2) = ml), (A1 y.2.1 - B1 y.2.1)| ≤ h := by
    rintro ⟨m, ℓ⟩ hml
    obtain ⟨y0, hy0, hy0eq⟩ := Finset.mem_image.mp hml
    obtain ⟨h1, h2⟩ := Prod.mk.inj hy0eq
    rw [hTrip_mem] at hy0
    rw [h1, h2] at hy0
    obtain ⟨hym1, hymM, _, _, hyℓ1, hyℓM, _, _, hsqm, hsqℓ, hrm, hrℓ, _, _, _⟩ := hy0
    set lo : ℕ := max zz (m.primeFactors.sup id + 1) with hlo
    have hInj : Set.InjOn (fun y : ℕ × ℕ × ℕ => y.2.1)
        ↑(Trip.filter (fun y => (y.1, y.2.2) = (m, ℓ))) := by
      intro y hy y' hy' heq
      rw [Finset.mem_coe, Finset.mem_filter] at hy hy'
      obtain ⟨g1, g2⟩ := Prod.mk.inj hy.2
      obtain ⟨g1', g2'⟩ := Prod.mk.inj hy'.2
      exact Prod.ext (by rw [g1, g1']) (Prod.ext heq (by rw [g2, g2']))
    have hsum : ∑ y ∈ Trip.filter (fun y => (y.1, y.2.2) = (m, ℓ)), (A1 y.2.1 - B1 y.2.1)
        = ∑ p ∈ (Trip.filter (fun y => (y.1, y.2.2) = (m, ℓ))).image (fun y => y.2.1), (A1 p - B1 p) := by
      exact (Finset.sum_image (f := fun p : ℕ => A1 p - B1 p) hInj).symm
    rw [hsum]
    have hbase : ∀ p, (m, p, ℓ) ∈ Trip ↔ Nat.Prime p ∧ zz ≤ p ∧ (∀ q ∈ m.primeFactors, q < p)
        ∧ (∀ q ∈ ℓ.primeFactors, p < q) ∧ m * p * ℓ ≤ M := by
      intro p
      rw [hTrip_mem]
      constructor
      · rintro ⟨_, _, _, _, _, _, hpp, hzz, _, _, _, _, hmlt, hℓgt, hprod⟩
        exact ⟨hpp, hzz, hmlt, hℓgt, hprod⟩
      · rintro ⟨hpp, hzz, hmlt, hℓgt, hprod⟩
        refine ⟨hym1, hymM, hpp.one_le, ?_, hyℓ1, hyℓM, hpp, hzz, hsqm, hsqℓ, hrm, hrℓ, hmlt, hℓgt, hprod⟩
        calc p ≤ m * p := Nat.le_mul_of_pos_left p (by omega)
          _ ≤ m * p * ℓ := Nat.le_mul_of_pos_right (m * p) (by omega)
          _ ≤ M := hprod
    have hImg : ∀ p, p ∈ (Trip.filter (fun y => (y.1, y.2.2) = (m, ℓ))).image (fun y => y.2.1)
        ↔ (m, p, ℓ) ∈ Trip := by
      intro p
      rw [Finset.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Finset.mem_filter] at hy
        obtain ⟨hyTrip, hyeq⟩ := hy
        obtain ⟨g1, g2⟩ := Prod.mk.inj hyeq
        have hy_eq : y = (m, y.2.1, ℓ) := Prod.ext g1 (Prod.ext rfl g2)
        rwa [hy_eq] at hyTrip
      · intro hp
        exact ⟨(m, p, ℓ), Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩
    have hlo_iff : ∀ p, lo ≤ p ↔ zz ≤ p ∧ (∀ q ∈ m.primeFactors, q < p) := by
      intro p
      rw [hlo, max_le_iff]
      constructor
      · rintro ⟨hzzp, hsupp⟩
        refine ⟨hzzp, ?_⟩
        intro q hq
        have h1 : q ≤ m.primeFactors.sup id := Finset.le_sup (f := id) hq
        omega
      · rintro ⟨hzzp, hlt⟩
        have hp1 : 1 ≤ p := by omega
        refine ⟨hzzp, ?_⟩
        have hle : m.primeFactors.sup id ≤ p - 1 :=
          Finset.sup_le (fun q hq => Nat.le_sub_one_of_lt (hlt q hq))
        calc m.primeFactors.sup id + 1 ≤ (p - 1) + 1 := Nat.add_le_add_right hle 1
          _ = p := Nat.sub_add_cancel hp1
    by_cases hℓne : ℓ.primeFactors.Nonempty
    · set hi : ℕ := min (M / (m * ℓ)) (ℓ.primeFactors.min' hℓne - 1) with hhi
      have hmin1 : 1 ≤ ℓ.primeFactors.min' hℓne :=
        (Nat.prime_of_mem_primeFactors (Finset.min'_mem _ hℓne)).one_le
      have hhi_iff : ∀ p, p ≤ hi ↔ (∀ q ∈ ℓ.primeFactors, p < q) ∧ m * p * ℓ ≤ M := by
        intro p
        rw [hhi, le_min_iff]
        constructor
        · rintro ⟨hdiv, hinf⟩
          refine ⟨?_, ?_⟩
          · have hp_lt : p < ℓ.primeFactors.min' hℓne := by omega
            exact (Finset.lt_min'_iff ℓ.primeFactors hℓne).mp hp_lt
          · rw [Nat.le_div_iff_mul_le (by positivity)] at hdiv
            nlinarith [hdiv]
        · rintro ⟨hlt, hprod'⟩
          refine ⟨?_, ?_⟩
          · rw [Nat.le_div_iff_mul_le (by positivity)]
            nlinarith [hprod']
          · have : p < ℓ.primeFactors.min' hℓne := (Finset.lt_min'_iff _ hℓne).mpr hlt
            omega
      have himg : (Trip.filter (fun y => (y.1, y.2.2) = (m, ℓ))).image (fun y => y.2.1)
          = (Finset.Icc lo hi).filter Nat.Prime := by
        ext p
        rw [hImg p, hbase p, Finset.mem_filter, Finset.mem_Icc, hlo_iff p, hhi_iff p]
        tauto
      rw [himg]
      have hkey : (∑ p ∈ (Finset.Icc lo hi).filter Nat.Prime, (A1 p - B1 p))
          = -∑ p ∈ (Finset.Icc lo hi).filter Nat.Prime,
              (1/(p:ℝ) - (if p ∣ ν then 0 else g p)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun p _ => hAB p)
      rw [hkey, abs_neg]
      exact hrange lo hi (by rw [hlo]; exact le_max_left _ _)
    · have hℓ1 : ℓ = 1 := by
        have hempty : ℓ.primeFactors = ∅ := Finset.not_nonempty_iff_eq_empty.mp hℓne
        rcases (Nat.primeFactors_eq_empty.mp hempty) with h | h
        · omega
        · exact h
      set hi : ℕ := M / (m * ℓ) with hhi
      have hhi_iff : ∀ p, p ≤ hi ↔ (∀ q ∈ ℓ.primeFactors, p < q) ∧ m * p * ℓ ≤ M := by
        intro p
        rw [hhi, Nat.le_div_iff_mul_le (by positivity)]
        constructor
        · intro hdiv
          refine ⟨?_, by nlinarith [hdiv]⟩
          intro q hq
          rw [hℓ1] at hq
          simp at hq
        · rintro ⟨_, hprod'⟩
          nlinarith [hprod']
      have himg : (Trip.filter (fun y => (y.1, y.2.2) = (m, ℓ))).image (fun y => y.2.1)
          = (Finset.Icc lo hi).filter Nat.Prime := by
        ext p
        rw [hImg p, hbase p, Finset.mem_filter, Finset.mem_Icc, hlo_iff p, hhi_iff p]
        tauto
      rw [himg]
      have hkey : (∑ p ∈ (Finset.Icc lo hi).filter Nat.Prime, (A1 p - B1 p))
          = -∑ p ∈ (Finset.Icc lo hi).filter Nat.Prime,
              (1/(p:ℝ) - (if p ∣ ν then 0 else g p)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun p _ => hAB p)
      rw [hkey, abs_neg]
      exact hrange lo hi (by rw [hlo]; exact le_max_left _ _)
  have hFabs : ∀ n : ℕ, |F n| ≤ 1/(n:ℝ) := by
    intro n
    rw [hF]
    have hmu1 : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num
    calc |(ArithmeticFunction.moebius n : ℝ) * (1/(n:ℝ))|
        = |(ArithmeticFunction.moebius n : ℝ)| * |1/(n:ℝ)| := abs_mul _ _
      _ ≤ 1 * (1/(n:ℝ)) := by
          refine mul_le_mul hmu1 ?_ (abs_nonneg _) (by norm_num)
          rw [abs_of_nonneg (by positivity)]
      _ = 1/(n:ℝ) := one_mul _
  have hGabs : ∀ n : ℕ, |Gt n| ≤ g n := by
    intro n
    rw [hGt]
    have hind : |(if Nat.Coprime n ν then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    have hmu1 : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num
    rw [abs_mul, abs_mul, abs_of_nonneg (hg0 n)]
    calc |(ArithmeticFunction.moebius n : ℝ)| * g n * |(if Nat.Coprime n ν then (1:ℝ) else 0)|
        ≤ 1 * g n * 1 := by
          refine mul_le_mul (mul_le_mul hmu1 le_rfl (hg0 n) (by norm_num)) hind (abs_nonneg _) (by simpa using hg0 n)
      _ = g n := by ring
  have hPsub : P ⊆ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M) := by
    intro ml hml
    obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hml
    obtain ⟨g1, g2⟩ := Prod.mk.inj hyeq
    rw [hTrip_mem] at hy
    obtain ⟨hy1, hyM, _, _, hyℓ1, hyℓM, _, _, _, _, _, _, _, _, _⟩ := hy
    rw [Finset.mem_product]
    exact ⟨by rw [← g1]; exact Finset.mem_Icc.mpr ⟨hy1, hyM⟩,
           by rw [← g2]; exact Finset.mem_Icc.mpr ⟨hyℓ1, hyℓM⟩⟩
  calc |∑ ml ∈ P, F ml.1 * Gt ml.2
          * (∑ y ∈ Trip.filter (fun y => (y.1, y.2.2) = ml), (A1 y.2.1 - B1 y.2.1))|
      ≤ ∑ ml ∈ P, |F ml.1 * Gt ml.2
          * (∑ y ∈ Trip.filter (fun y => (y.1, y.2.2) = ml), (A1 y.2.1 - B1 y.2.1))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ ml ∈ P, (1/(ml.1:ℝ)) * g ml.2 * h := by
        refine Finset.sum_le_sum (fun ml hml => ?_)
        rw [abs_mul, abs_mul]
        have hmlI : ml.1 ∈ Finset.Icc 1 M := (Finset.mem_product.mp (hPsub hml)).1
        have hml1' : 1 ≤ ml.1 := (Finset.mem_Icc.mp hmlI).1
        have hfac1 : (0:ℝ) ≤ 1/(ml.1:ℝ) := by
          apply div_nonneg zero_le_one
          exact_mod_cast (by omega : 0 ≤ ml.1)
        have hfac2 : (0:ℝ) ≤ g ml.2 := hg0 ml.2
        have hfac3 : (0:ℝ) ≤ (1/(ml.1:ℝ)) * g ml.2 := mul_nonneg hfac1 hfac2
        have hfib : |∑ y ∈ Trip.filter (fun y => (y.1, y.2.2) = ml), (A1 y.2.1 - B1 y.2.1)| ≤ h :=
          hfb ml hml
        exact mul_le_mul (mul_le_mul (hFabs ml.1) (hGabs ml.2) (abs_nonneg _) hfac1) hfib
          (abs_nonneg _) hfac3
    _ ≤ ∑ ml ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M), (1/(ml.1:ℝ)) * g ml.2 * h := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hPsub (fun ml hml2 hmlP => ?_)
        rw [Finset.mem_product] at hml2
        have h1 : (0:ℝ) ≤ 1/(ml.1:ℝ) := by
          apply div_nonneg zero_le_one
          exact_mod_cast (by omega : 0 ≤ ml.1)
        exact mul_nonneg (mul_nonneg h1 (hg0 ml.2)) hh
    _ = h * (∑ m ∈ Finset.Icc 1 M, 1/(m:ℝ)) * (∑ n ∈ Finset.Icc 1 M, g n) := by
        rw [Finset.sum_product]
        have hinner : ∀ m : ℕ,
            (∑ ℓ ∈ Finset.Icc 1 M, (1/(m:ℝ))*g ℓ*h) = h * (1/(m:ℝ)) * (∑ ℓ ∈ Finset.Icc 1 M, g ℓ) := by
          intro m
          rw [show (∑ ℓ ∈ Finset.Icc 1 M, (1/(m:ℝ))*g ℓ*h)
              = ∑ ℓ ∈ Finset.Icc 1 M, (h * (1/(m:ℝ))) * g ℓ from
                Finset.sum_congr rfl (fun ℓ _ => by ring)]
          rw [← Finset.mul_sum]
        simp_rw [hinner]
        rw [← Finset.sum_mul, ← Finset.mul_sum]

end Commons.NumberTheory.Sieve
