/-
  Companion paper, §9: the `g`-part of (9.12) and the `(R′)`-chain for the Friedlander–Iwaniec
  sequence.

  This file starts with the estimate of `EtwoG`, the `g`-weighted half of `E₂`.  The companion
  bounds the contribution `A(x)∑♭_{ν>L}∑♭_{d≤D} g([ν²,d])` by `O(A(x)(log x)L^{-1}(log L)^B)`
  "using (1.8), (1.9) and (9.1)".  Here we make this explicit:

  * for squarefree `d`, `g([ν²,d]) = g(ν²)·∏_{p|d, p∤ν} g(p) ≤ g(ν²)·3^{ω(d)}·gcd(d,ν)/d`;
  * `∑♭_{d≤D} 3^{ω(d)}gcd(d,ν)/d ≤ C(log(D+2))^4·6^{ω(ν)}`, by writing
    `gcd(d,ν) = ∑_{e | gcd(d,ν)} φ(e)` and exchanging the two sums;
  * for squarefree `ν`, `g(ν²) ≤ 3^{ω(ν)}/ν²`, so `g(ν²)·6^{ω(ν)} ≤ τ(ν)^5/ν²` and
    `∑♭_{ν>L} τ(ν)^5/ν² ≪ (log L)^{32}/L`.
-/
import Mathlib
import Submission.ASP.S34
import Submission.ASP.S9d
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_totient_div_divisors_le_two_pow_omega
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_sq_tail_le

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-! ### Elementary bounds for `3^{ω}` -/

/-- `3^{ω(d)} ≤ τ(d)²`. -/
lemma three_pow_card_primeFactors_le_card_divisors_sq (d : ℕ) (hd : 0 < d) :
    (3 : ℝ) ^ (d.primeFactors.card) ≤ ((d.divisors.card : ℝ)) ^ 2 := by
  have h1 : (3 : ℝ) ^ (d.primeFactors.card) ≤ (4 : ℝ) ^ (d.primeFactors.card) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h2 : ((2 : ℝ) ^ (d.primeFactors.card)) ^ 2 = (4 : ℝ) ^ (d.primeFactors.card) := by
    rw [← pow_mul, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
    congr 1
    ring
  have h3 : ((2 : ℝ) ^ (d.primeFactors.card)) ≤ (d.divisors.card : ℝ) := by
    have h := Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors hd
    have h' : ((2 ^ d.primeFactors.card : ℕ) : ℝ) ≤ ((d.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa using h'
  calc (3 : ℝ) ^ (d.primeFactors.card)
      ≤ (4 : ℝ) ^ (d.primeFactors.card) := h1
    _ = ((2 : ℝ) ^ (d.primeFactors.card)) ^ 2 := h2.symm
    _ ≤ ((d.divisors.card : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2

/-- `∑_{d ≤ D} 3^{ω(d)}/d ≤ C(log(D+2))^4`. -/
lemma sum_three_pow_omega_div_le :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
      (∑ d ∈ Finset.Icc 1 D, (3 : ℝ) ^ (d.primeFactors.card) / (d : ℝ))
        ≤ C * (Real.log ((D : ℝ) + 2)) ^ 4 := by
  obtain ⟨C4, hC4, h4⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 2
  refine ⟨C4, hC4, fun D hD => ?_⟩
  refine le_trans (Finset.sum_le_sum (fun d hd => ?_)) (h4 D hD)
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hd0 : 0 < d := by omega
  have h5 : (3 : ℝ) ^ (d.primeFactors.card) ≤ ((d.divisors.card : ℝ)) ^ 2 :=
    three_pow_card_primeFactors_le_card_divisors_sq d hd0
  exact div_le_div_of_nonneg_right h5 (Nat.cast_nonneg d)

/-! ### `FIg (ν²)` and `FIg ([ν²,d])` -/

/-- For squarefree `ν`, `FIg (ν²) ≤ 3^{ω(ν)}/ν²`. -/
lemma FIg_sq_le_card_primeFactors (ν : ℕ) (hν : Squarefree ν) :
    FIg (ν ^ 2) ≤ (3 : ℝ) ^ (ν.primeFactors.card) / (ν : ℝ) ^ 2 := by
  have hν0 : ν ≠ 0 := hν.ne_zero
  have hv1 : ∀ p ∈ ν.primeFactors, ν.factorization p = 1 := by
    intro p hp
    have hle := (Nat.squarefree_iff_factorization_le_one hν0).mp hν p
    have hge : 1 ≤ ν.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization (Nat.prime_of_mem_primeFactors hp) hν0).mp
        (Nat.mem_primeFactors.mp hp).2.1
    omega
  have hfac : FIg (ν ^ 2) = ∏ p ∈ ν.primeFactors, FIg (p ^ 2) := by
    rw [FIg_eq_prod_primeFactors_pow (ν ^ 2) (by positivity),
      Nat.primeFactors_pow ν (by norm_num)]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have h2 : (ν ^ 2).factorization p = 2 * ν.factorization p := by
      rw [Nat.factorization_pow]; simp
    rw [h2, hv1 p hp, mul_one]
  rw [hfac]
  have hstep : (∏ p ∈ ν.primeFactors, FIg (p ^ 2))
      ≤ ∏ p ∈ ν.primeFactors, (3 : ℝ) / (p : ℝ) ^ 2 :=
    Finset.prod_le_prod₀ (fun p _ => FIg_nonneg _)
      (fun p hp => FIg_prime_sq_le p (Nat.prime_of_mem_primeFactors hp))
  refine le_trans hstep ?_
  rw [Finset.prod_div_distrib, Finset.prod_const]
  have hden : (∏ x ∈ ν.primeFactors, (x : ℝ) ^ 2) = (ν : ℝ) ^ 2 := by
    rw [Finset.prod_pow]
    congr 1
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hν]
  rw [hden]

/-- For squarefree `d` and `ν ≥ 1`,
`FIg ([ν²,d]) ≤ FIg (ν²)·(3^{ω(d)}·gcd(d,ν)/d)`. -/
lemma FIg_lcm_sq_le (ν d : ℕ) (hν1 : 1 ≤ ν) (hd : Squarefree d) (hd1 : 1 ≤ d) :
    FIg (Nat.lcm (ν ^ 2) d)
      ≤ FIg (ν ^ 2) * ((3 : ℝ) ^ (d.primeFactors.card) * (Nat.gcd d ν : ℝ) / (d : ℝ)) := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hν0 : ν ≠ 0 := by omega
  set m : ℕ := d / Nat.gcd d ν with hm
  have hgddd : Nat.gcd d ν ∣ d := Nat.gcd_dvd_left d ν
  have hgpos : 0 < Nat.gcd d ν := Nat.gcd_pos_of_pos_left ν (by omega)
  have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega) hgddd) hgpos
  have hdm : Nat.gcd d ν * m = d := by
    rw [hm]; exact Nat.mul_div_cancel' hgddd
  have hm_sf : Squarefree m := hd.squarefree_of_dvd (by rw [← hdm]; exact dvd_mul_left _ _)
  have hpf : m.primeFactors = d.primeFactors.filter (fun p => ¬ p ∣ ν) := by
    rw [hm, Nat.primeFactors_div_gcd hd hν0, Finset.sdiff_eq_filter]
    refine Finset.filter_congr (fun p hp => ?_)
    constructor
    · intro hpn hpv
      exact hpn (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hpv, hν0⟩)
    · intro hpv hpp
      exact hpv (Nat.mem_primeFactors.mp hpp).2.1
  have h1 := g_lcm_eq FIg (fun a b h => FI_gdens_mul h) FI_gdens_one hd ν
  rw [h1]
  have hpf2 : (∏ p ∈ d.primeFactors, (if p ∣ ν then 1 else FIg p))
      = ∏ p ∈ d.primeFactors.filter (fun p => ¬ p ∣ ν), FIg p := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    by_cases h : p ∣ ν <;> simp [h]
  rw [hpf2, ← hpf]
  have hm_eq : FIg m = ∏ p ∈ m.primeFactors, FIg p := by
    rw [FIg_eq_prod_primeFactors_pow m hmpos]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hle := (Nat.squarefree_iff_factorization_le_one hm_sf.ne_zero).mp hm_sf p
    have hge : 1 ≤ m.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization (Nat.prime_of_mem_primeFactors hp)
        hm_sf.ne_zero).mp (Nat.mem_primeFactors.mp hp).2.1
    have hf1 : m.factorization p = 1 := by omega
    rw [hf1, pow_one]
  rw [← hm_eq]
  have hstep : FIg m ≤ ∏ p ∈ m.primeFactors, (3 : ℝ) / (p : ℝ) := by
    rw [hm_eq]
    exact Finset.prod_le_prod₀ (fun p _ => FIg_nonneg _)
      (fun p hp => by
        simpa using FIg_prime_pow_le p 1 (Nat.prime_of_mem_primeFactors hp) le_rfl)
  have hcard : m.primeFactors.card ≤ d.primeFactors.card := by
    rw [hpf]; exact Finset.card_filter_le _ _
  have hden : (∏ p ∈ m.primeFactors, (p : ℝ)) = (m : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hm_sf]
  have h3 : (3 : ℝ) ^ (m.primeFactors.card) ≤ (3 : ℝ) ^ (d.primeFactors.card) :=
    pow_le_pow_right₀ (by norm_num) hcard
  have hmv : (m : ℝ) = (d : ℝ) / (Nat.gcd d ν : ℝ) := by
    have hd_eq : (d : ℝ) = (Nat.gcd d ν : ℝ) * (m : ℝ) := by
      have h := congrArg (fun x : ℕ => (x : ℝ)) hdm
      push_cast at h
      exact h.symm
    rw [hd_eq]
    have hg0 : (Nat.gcd d ν : ℝ) ≠ 0 := by positivity
    field_simp
  have hgnn : (0 : ℝ) < (Nat.gcd d ν : ℝ) := by exact_mod_cast hgpos
  have hrest : (∏ p ∈ m.primeFactors, (3 : ℝ) / (p : ℝ))
      ≤ (3 : ℝ) ^ (d.primeFactors.card) * (Nat.gcd d ν : ℝ) / (d : ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hden, hmv, div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hgnn.le)
      (Nat.cast_nonneg d)
  exact mul_le_mul_of_nonneg_left (le_trans hstep hrest) (FIg_nonneg _)

/-! ### The `gcd`-weighted sum -/

/-- `∑♭_{d ≤ D} 3^{ω(d)}·gcd(d,ν)/d ≤ C(log(D+2))^4·6^{ω(ν)}`. -/
lemma sum_three_pow_gcd_div_le :
    ∃ C : ℝ, 0 < C ∧ ∀ ν D : ℕ, Squarefree ν → 1 ≤ D →
      (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          (3 : ℝ) ^ (d.primeFactors.card) * (Nat.gcd d ν : ℝ) / (d : ℝ))
        ≤ C * (Real.log ((D : ℝ) + 2)) ^ 4 * (6 : ℝ) ^ (ν.primeFactors.card) := by
  obtain ⟨C4, hC4, h4⟩ := sum_three_pow_omega_div_le
  refine ⟨C4, hC4, fun ν D hν hD => ?_⟩
  have hν0 : ν ≠ 0 := hν.ne_zero
  have hνpos : 0 < ν := Nat.pos_of_ne_zero hν0
  -- the totient identity `gcd(d,ν) = ∑_{e | gcd(d,ν)} φ(e)`
  have hφ : ∀ d : ℕ, (Nat.gcd d ν : ℝ)
      = ∑ e ∈ (ν.divisors.filter (fun e => e ∣ d)), (Nat.totient e : ℝ) := by
    intro d
    have hset : (Nat.gcd d ν).divisors = ν.divisors.filter (fun e => e ∣ d) := by
      ext e
      rw [Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hed, -⟩
        exact ⟨⟨dvd_trans hed (Nat.gcd_dvd_right d ν), hν0⟩,
          dvd_trans hed (Nat.gcd_dvd_left d ν)⟩
      · rintro ⟨⟨hev, -⟩, hed⟩
        have hg0 : Nat.gcd d ν ≠ 0 := fun h => hν0 (Nat.gcd_eq_zero_iff.mp h).2
        exact ⟨Nat.dvd_gcd hed hev, hg0⟩
    have h := Nat.sum_totient (Nat.gcd d ν)
    rw [hset] at h
    rw [← h, Nat.cast_sum]
  -- the double sum
  have hswap : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        (3 : ℝ) ^ (d.primeFactors.card) * (Nat.gcd d ν : ℝ) / (d : ℝ))
      = ∑ e ∈ ν.divisors, (Nat.totient e : ℝ)
          * ∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d ∧ e ∣ d),
              (3 : ℝ) ^ (d.primeFactors.card) / (d : ℝ) := by
    have e1 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          (3 : ℝ) ^ (d.primeFactors.card) * (Nat.gcd d ν : ℝ) / (d : ℝ))
        = ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            (3 : ℝ) ^ (d.primeFactors.card) / (d : ℝ) * (Nat.gcd d ν : ℝ) :=
      Finset.sum_congr rfl (fun d _ => by ring)
    rw [e1]
    have e2 : ∀ d : ℕ,
        (3 : ℝ) ^ (d.primeFactors.card) / (d : ℝ) * (Nat.gcd d ν : ℝ)
          = ∑ e ∈ ν.divisors,
              (if e ∣ d then (3 : ℝ) ^ (d.primeFactors.card) / (d : ℝ)
                * (Nat.totient e : ℝ) else 0) := by
      intro d
      rw [hφ d, Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_congr rfl (fun d _ => e2 d), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    have hff : (Finset.Icc 1 D).filter (fun d => Squarefree d ∧ e ∣ d)
        = ((Finset.Icc 1 D).filter Squarefree).filter (fun d => e ∣ d) := by
      ext d; simp only [Finset.mem_filter]; tauto
    rw [hff, Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases h : e ∣ d <;> simp [h, mul_comm]
  rw [hswap]
  -- bound the inner sums
  have hinner : ∀ e ∈ ν.divisors,
      (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d ∧ e ∣ d),
          (3 : ℝ) ^ (d.primeFactors.card) / (d : ℝ))
        ≤ (3 : ℝ) ^ (e.primeFactors.card) / (e : ℝ)
            * (C4 * (Real.log ((D : ℝ) + 2)) ^ 4) := by
    intro e he
    have heν : e ∣ ν := Nat.dvd_of_mem_divisors he
    have he0 : e ≠ 0 := by
      rintro rfl
      exact hν0 (Nat.eq_zero_of_zero_dvd heν)
    have hepos : 0 < e := Nat.pos_of_ne_zero he0
    have hinj : Set.InjOn (fun d : ℕ => d / e)
        ↑((Finset.Icc 1 D).filter (fun d => Squarefree d ∧ e ∣ d)) := by
      intro a ha b hb hab
      have hae : e ∣ a := (Finset.mem_filter.mp ha).2.2
      have hbe : e ∣ b := (Finset.mem_filter.mp hb).2.2
      calc a = e * (a / e) := (Nat.mul_div_cancel' hae).symm
        _ = e * (b / e) := congrArg (fun x => e * x) hab
        _ = b := Nat.mul_div_cancel' hbe
    have hkey : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d ∧ e ∣ d),
          (3 : ℝ) ^ (d.primeFactors.card) / (d : ℝ))
        = ∑ m ∈ ((Finset.Icc 1 D).filter (fun d => Squarefree d ∧ e ∣ d)).image
            (fun d : ℕ => d / e),
            (3 : ℝ) ^ ((e * m).primeFactors.card) / ((e * m) : ℝ) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun d hd => ?_)
      have hde : e ∣ d := (Finset.mem_filter.mp hd).2.2
      have hterm : (3 : ℝ) ^ ((e * (d / e)).primeFactors.card) / ((e : ℝ) * ((d / e : ℕ) : ℝ))
          = (3 : ℝ) ^ (d.primeFactors.card) / (d : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hde]
      exact hterm.symm
    rw [hkey]
    have himg : ((Finset.Icc 1 D).filter (fun d => Squarefree d ∧ e ∣ d)).image
          (fun d : ℕ => d / e) ⊆ (Finset.Icc 1 D).filter Squarefree := by
      intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨d, hd, rfl⟩ := hm
      obtain ⟨hdI, hdsf, hde⟩ := Finset.mem_filter.mp hd
      have hd0 : 0 < d := (Finset.mem_Icc.mp hdI).1.trans_lt' (by omega)
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, hdsf.squarefree_of_dvd (Nat.div_dvd_of_dvd hde)⟩
      · exact Nat.div_pos (Nat.le_of_dvd hd0 hde) hepos
      · exact le_trans (Nat.div_le_self d e) (Finset.mem_Icc.mp hdI).2
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg himg
      (fun m _ _ => by positivity)) ?_
    have hpt : ∀ m ∈ (Finset.Icc 1 D).filter Squarefree,
        (3 : ℝ) ^ ((e * m).primeFactors.card) / ((e * m) : ℝ)
          ≤ (3 : ℝ) ^ (e.primeFactors.card) / (e : ℝ)
            * ((3 : ℝ) ^ (m.primeFactors.card) / (m : ℝ)) := by
      intro m hm
      obtain ⟨hmI, -⟩ := Finset.mem_filter.mp hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
      have hm0 : m ≠ 0 := by omega
      have hsub : (e * m).primeFactors ⊆ e.primeFactors ∪ m.primeFactors := by
        intro p hp
        have hp' := Nat.mem_primeFactors.mp hp
        rcases (hp'.1.dvd_mul).mp hp'.2.1 with h | h
        · exact Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp'.1, h, he0⟩)
        · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp'.1, h, hm0⟩)
      have hcard : (e * m).primeFactors.card ≤ e.primeFactors.card + m.primeFactors.card :=
        le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
      have h3 : (3 : ℝ) ^ ((e * m).primeFactors.card)
          ≤ (3 : ℝ) ^ (e.primeFactors.card) * (3 : ℝ) ^ (m.primeFactors.card) := by
        calc (3 : ℝ) ^ ((e * m).primeFactors.card)
            ≤ (3 : ℝ) ^ (e.primeFactors.card + m.primeFactors.card) :=
              pow_le_pow_right₀ (by norm_num) hcard
          _ = (3 : ℝ) ^ (e.primeFactors.card) * (3 : ℝ) ^ (m.primeFactors.card) :=
              pow_add _ _ _
      rw [div_mul_div_comm]
      exact div_le_div_of_nonneg_right h3 (by positivity)
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [← Finset.mul_sum]
    have hsmall : (∑ m ∈ (Finset.Icc 1 D).filter Squarefree,
        (3 : ℝ) ^ (m.primeFactors.card) / (m : ℝ))
        ≤ C4 * (Real.log ((D : ℝ) + 2)) ^ 4 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun m _ _ => by positivity)) (h4 D hD)
    exact mul_le_mul_of_nonneg_left hsmall (by positivity)
  refine le_trans (Finset.sum_le_sum (fun e he =>
    mul_le_mul_of_nonneg_left (hinner e he) (by positivity))) ?_
  have hprod : ∀ e ∈ ν.divisors,
      (Nat.totient e : ℝ) * ((3 : ℝ) ^ (e.primeFactors.card) / (e : ℝ))
      ≤ (3 : ℝ) ^ (ν.primeFactors.card) * ((Nat.totient e : ℝ) / (e : ℝ)) := by
    intro e he
    have heν : e ∣ ν := Nat.dvd_of_mem_divisors he
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos heν hνpos
    have hsub : e.primeFactors ⊆ ν.primeFactors := by
      intro p hp
      have hp' := Nat.mem_primeFactors.mp hp
      exact Nat.mem_primeFactors.mpr ⟨hp'.1, dvd_trans hp'.2.1 heν, hν0⟩
    have h3 : (3 : ℝ) ^ (e.primeFactors.card) ≤ (3 : ℝ) ^ (ν.primeFactors.card) :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_card hsub)
    have hφφ : (Nat.totient e : ℝ) * ((3 : ℝ) ^ (e.primeFactors.card) / (e : ℝ))
        = (3 : ℝ) ^ (e.primeFactors.card) * ((Nat.totient e : ℝ) / (e : ℝ)) := by ring
    rw [hφφ]
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  have htot : (∑ e ∈ ν.divisors, (Nat.totient e : ℝ) / (e : ℝ))
      ≤ (2 : ℝ) ^ (ν.primeFactors.card) :=
    Commons.NumberTheory.ArithmeticFunction.sum_totient_div_divisors_le_two_pow_omega hν
  have hmid : (∑ e ∈ ν.divisors,
        (Nat.totient e : ℝ) * ((3 : ℝ) ^ (e.primeFactors.card) / (e : ℝ)))
      ≤ (6 : ℝ) ^ (ν.primeFactors.card) := by
    refine le_trans (Finset.sum_le_sum hprod) ?_
    rw [← Finset.mul_sum]
    refine le_trans (mul_le_mul_of_nonneg_left htot (by positivity)) (le_of_eq ?_)
    rw [← mul_pow]
    norm_num
  calc (∑ e ∈ ν.divisors,
        (Nat.totient e : ℝ) * ((3 : ℝ) ^ (e.primeFactors.card) / (e : ℝ)
          * (C4 * (Real.log ((D : ℝ) + 2)) ^ 4)))
      = C4 * (Real.log ((D : ℝ) + 2)) ^ 4 * ∑ e ∈ ν.divisors,
          (Nat.totient e : ℝ) * ((3 : ℝ) ^ (e.primeFactors.card) / (e : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        ring
    _ ≤ C4 * (Real.log ((D : ℝ) + 2)) ^ 4 * (6 : ℝ) ^ (ν.primeFactors.card) :=
        mul_le_mul_of_nonneg_left hmid (by positivity)

/-! ### The `g`-part of (9.12) -/

/-- **Companion §9, the `g`-part of `E₂`**: `∑♭_{ν>L}∑♭_{d≤D}g([ν²,d])A(x) ≪ A(x)(log x)L^{-1}(log L)^B`
— here with the explicit power `(log L)^{32}` and the loss `(log x)^5`. -/
theorem EtwoG_FIa_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x t D L : ℕ, 1 ≤ t → t ≤ x → 1 ≤ D → D ≤ x → 1 ≤ L →
      EtwoG FIa FIg t D (L + 1) t
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 5
            * (Real.log ((L : ℝ) + 2)) ^ 32 / (L : ℝ) := by
  obtain ⟨C6, hC6, h6⟩ := sum_three_pow_gcd_div_le
  obtain ⟨C5, hC5, h5⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_sq_tail_le 5
  refine ⟨C6 * C5, by positivity, fun x t D L ht htx hD1 hDx hL1 => ?_⟩
  have hlogx : (1 : ℝ) ≤ Real.log ((x : ℝ) + 2) := by
    have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_trans ht htx)
    have he : Real.exp 1 ≤ (x : ℝ) + 2 := by
      linarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by
    have : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) (le_trans ht htx))
    exact this.le
  have hL0 : (0 : ℝ) < (L : ℝ) := by
    have : (0 : ℕ) < L := by omega
    exact_mod_cast this
  have hDlog : (0 : ℝ) < Real.log ((D : ℝ) + 2) := by
    have : (1 : ℝ) < (D : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
      linarith
    exact Real.log_pos this
  have hRD : Real.log ((D : ℝ) + 2) ^ 4 ≤ Real.log ((x : ℝ) + 2) ^ 5 := by
    have h1 : Real.log ((D : ℝ) + 2) ≤ Real.log ((x : ℝ) + 2) := by
      refine Real.log_le_log (by positivity) ?_
      have : (D : ℝ) ≤ (x : ℝ) := by exact_mod_cast hDx
      linarith
    have h2 : Real.log ((D : ℝ) + 2) ^ 4 ≤ Real.log ((x : ℝ) + 2) ^ 4 :=
      pow_le_pow_left₀ hDlog.le h1 4
    have h3 : Real.log ((x : ℝ) + 2) ^ 4 ≤ Real.log ((x : ℝ) + 2) ^ 5 :=
      pow_le_pow_right₀ hlogx (by norm_num)
    exact le_trans h2 h3
  -- the main double sum
  have hmain : (∑ ν ∈ ((Finset.Icc (L + 1) t).filter Squarefree),
        ∑ d ∈ ((Finset.Icc 1 D).filter Squarefree), FIg (Nat.lcm (ν ^ 2) d))
      ≤ C6 * (Real.log ((x : ℝ) + 2)) ^ 5
          * (C5 * (Real.log ((L : ℝ) + 2)) ^ 32 / (L : ℝ)) := by
    have hstep1 : (∑ ν ∈ ((Finset.Icc (L + 1) t).filter Squarefree),
          ∑ d ∈ ((Finset.Icc 1 D).filter Squarefree), FIg (Nat.lcm (ν ^ 2) d))
        ≤ ∑ ν ∈ ((Finset.Icc (L + 1) t).filter Squarefree),
            FIg (ν ^ 2) * (C6 * (Real.log ((D : ℝ) + 2)) ^ 4
              * (6 : ℝ) ^ (ν.primeFactors.card)) := by
      refine Finset.sum_le_sum (fun ν hν => ?_)
      have hνsf : Squarefree ν := (Finset.mem_filter.mp hν).2
      have hν1 : 1 ≤ ν := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hν).1).1
        omega
      have hstep : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, FIg (Nat.lcm (ν ^ 2) d))
          ≤ ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
              FIg (ν ^ 2) * ((3 : ℝ) ^ (d.primeFactors.card) * (Nat.gcd d ν : ℝ) / (d : ℝ)) :=
        Finset.sum_le_sum (fun d hd => FIg_lcm_sq_le ν d hν1 (Finset.mem_filter.mp hd).2
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1)
      refine le_trans hstep ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (h6 ν D hνsf hD1) (FIg_nonneg _)
    refine le_trans hstep1 ?_
    have hconst : (∑ ν ∈ ((Finset.Icc (L + 1) t).filter Squarefree),
          FIg (ν ^ 2) * (C6 * (Real.log ((D : ℝ) + 2)) ^ 4 * (6 : ℝ) ^ (ν.primeFactors.card)))
        = C6 * (Real.log ((D : ℝ) + 2)) ^ 4
            * ∑ ν ∈ ((Finset.Icc (L + 1) t).filter Squarefree),
                FIg (ν ^ 2) * (6 : ℝ) ^ (ν.primeFactors.card) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ν _ => by ring)
    rw [hconst]
    have hnu : (∑ ν ∈ ((Finset.Icc (L + 1) t).filter Squarefree),
          FIg (ν ^ 2) * (6 : ℝ) ^ (ν.primeFactors.card))
        ≤ C5 * (Real.log ((L : ℝ) + 2)) ^ 32 / (L : ℝ) := by
      have hpt : ∀ ν ∈ ((Finset.Icc (L + 1) t).filter Squarefree),
          FIg (ν ^ 2) * (6 : ℝ) ^ (ν.primeFactors.card)
            ≤ ((ν.divisors.card : ℝ)) ^ 5 / (ν : ℝ) ^ 2 := by
        intro ν hν
        have hνsf : Squarefree ν := (Finset.mem_filter.mp hν).2
        have hν1 : 1 ≤ ν := by
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hν).1).1
          omega
        have hτ1 : (2 : ℝ) ^ (ν.primeFactors.card) ≤ (ν.divisors.card : ℝ) := by
          have h := Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
            (by omega : 0 < ν)
          have h' : ((2 ^ ν.primeFactors.card : ℕ) : ℝ) ≤ ((ν.divisors.card : ℕ) : ℝ) :=
            Nat.cast_le.mpr h
          simpa using h'
        have h18 : (3 : ℝ) ^ (ν.primeFactors.card) * (6 : ℝ) ^ (ν.primeFactors.card) ≤ ((ν.divisors.card : ℝ)) ^ 5 := by
          have hmul : (3 : ℝ) ^ (ν.primeFactors.card) * (6 : ℝ) ^ (ν.primeFactors.card) = (18 : ℝ) ^ (ν.primeFactors.card) := by
            rw [← mul_pow]; norm_num
          rw [hmul]
          have h32 : (18 : ℝ) ^ (ν.primeFactors.card) ≤ (32 : ℝ) ^ (ν.primeFactors.card) :=
            pow_le_pow_left₀ (by norm_num) (by norm_num) _
          have hpow : (32 : ℝ) ^ (ν.primeFactors.card) = ((2 : ℝ) ^ (ν.primeFactors.card)) ^ 5 := by
            rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, ← pow_mul, ← pow_mul]
            congr 1
            omega
          calc (18 : ℝ) ^ (ν.primeFactors.card) ≤ (32 : ℝ) ^ (ν.primeFactors.card) := h32
            _ = ((2 : ℝ) ^ (ν.primeFactors.card)) ^ 5 := hpow
            _ ≤ ((ν.divisors.card : ℝ)) ^ 5 := pow_le_pow_left₀ (by positivity) hτ1 5
        have hsq := FIg_sq_le_card_primeFactors ν hνsf
        calc FIg (ν ^ 2) * (6 : ℝ) ^ (ν.primeFactors.card)
            ≤ (3 : ℝ) ^ (ν.primeFactors.card) / (ν : ℝ) ^ 2
                * (6 : ℝ) ^ (ν.primeFactors.card) :=
              mul_le_mul_of_nonneg_right hsq (by positivity)
          _ = ((3 : ℝ) ^ (ν.primeFactors.card) * (6 : ℝ) ^ (ν.primeFactors.card))
                / (ν : ℝ) ^ 2 := by ring
          _ ≤ ((ν.divisors.card : ℝ)) ^ 5 / (ν : ℝ) ^ 2 :=
              div_le_div_of_nonneg_right h18 (by positivity)
      refine le_trans (Finset.sum_le_sum hpt) ?_
      have hsub : ((Finset.Icc (L + 1) t).filter Squarefree)
          ⊆ (Finset.Icc 1 t).filter (fun n => L < n) := by
        intro ν hν
        obtain ⟨hνI, _⟩ := Finset.mem_filter.mp hν
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hνI
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, h2⟩, by omega⟩
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => by positivity)) ?_
      have h := h5 L t hL1
      simpa only [show ((2 : ℝ) ^ 5) = ((32 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using h
    refine le_trans (mul_le_mul_of_nonneg_left hnu (by positivity)) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRD hC6.le) (by positivity)
  -- conclude
  have hA : Acount FIa (t : ℝ) ≤ (Submission.Aseq x : ℝ) := by
    have h1 : Acount FIa (t : ℝ) ≤ Submission.Aseq t := by
      rw [FI_Acount_eq]; linarith [show (0:ℝ) ≤ 1 from by norm_num]
    exact le_trans h1 (by exact_mod_cast Aseq_mono htx)
  have hA0 : (0 : ℝ) ≤ Acount FIa (t : ℝ) := Finset.sum_nonneg (fun n _ => FIa_nonneg n)
  rw [EtwoG]
  have hfac : (∑ ν ∈ ((Finset.Icc (L + 1) t).filter Squarefree),
        ∑ d ∈ ((Finset.Icc 1 D).filter Squarefree), FIg (Nat.lcm (ν ^ 2) d) * Acount FIa (t : ℝ))
      = Acount FIa (t : ℝ) * ∑ ν ∈ ((Finset.Icc (L + 1) t).filter Squarefree),
          ∑ d ∈ ((Finset.Icc 1 D).filter Squarefree), FIg (Nat.lcm (ν ^ 2) d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  rw [hfac]
  refine le_trans (mul_le_mul hA hmain ?_ ?_) (le_of_eq ?_)
  · exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => FIg_nonneg _))
  · exact Nat.cast_nonneg (Submission.Aseq x)
  · ring

/-! ### The `S₁` bound of §9 -/

/-- The logarithmic exponent used for the `ν > L` splitting of §9. -/
def E2logB : ℝ := (2 : ℝ) ^ 63 + 100

/-- The logarithmic saving exponent of the `S₁` bound. -/
def E2lam : ℝ := (2 : ℝ) ^ 60



set_option maxHeartbeats 1000000 in
/-- **Companion §9, the `S₁` bound**: `∑♭_{L < ν ≤ √t} A_{ν²}(t) ≪ A(x)(log x)^{−2^60}`.
The `ν`-range is split at `ν₀`: below `ν₀` we use `(R₃)` (`FIr_sq_small_le_generic'`), above it
the Cauchy–Schwarz bound `FIr_sq_large_le_B2`, and the `g`-part contributes the convergent tail
`∑♭_{ν>L} g(ν²) ≤ K/√L`. -/
theorem FI_Ad_sqrt_le (β : ℝ) (hβ : 71 ≤ β) :
    ∃ X₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x → ∀ t L ν₀ : ℕ,
      2 ≤ t → t ≤ x → Submission.Rcut x ≤ t → 1 ≤ L → L ≤ ν₀ → ν₀ ≤ t.sqrt →
      ν₀ ^ 2 < Submission.X2Y4R3.R3cut x →
      (t : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((t : ℝ) + 2)) ^ β ≤ (ν₀ : ℝ) →
      (Real.log x) ^ ((β - 71) / 4) ≤ Real.sqrt (L : ℝ) →
      (∑ ν ∈ ((Finset.Icc (L + 1) t.sqrt).filter Squarefree), Ad FIa (ν ^ 2) t)
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((β - 71) / 4)) := by
  obtain ⟨X1, hsmall⟩ := FIr_sq_small_le_generic' β
  obtain ⟨K, hKpos, hTail⟩ := FI_sq_rates.2
  obtain ⟨X2, K3, hK3pos, hlarge⟩ := FIr_sq_large_le_B2 (K := K) (B := β) hKpos hTail
  obtain ⟨Y2, hY2pos, hY2⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := 2 * (X2 : ℝ)) (by positivity) (n := 0) (r := (11 : ℝ) / 16) (by norm_num)

  refine ⟨max (max (max X1 X2) Y2) 64 + 1,
    4 + K3 + 3 * (K3 + K), by positivity,
    fun x hx t L ν₀ ht htx hDt hL1 hLν₀ hν₀s hν₀sq hν₀b hLb => ?_⟩
  have hLν₀' : L ≤ ν₀ := hLν₀
  have hle : max (max (max X1 X2) Y2) 64 ≤ x := by omega
  have hxY2 : Y2 ≤ x := le_trans (le_trans (le_max_right (max X1 X2) Y2) (le_max_left _ _)) hle
  have hAX : max X1 X2 ≤ max (max (max X1 X2) Y2) 64 :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hxX1 : X1 ≤ x := le_trans (le_trans (le_max_left X1 X2) hAX) hle
  have hxX2 : X2 ≤ x := le_trans (le_trans (le_max_right X1 X2) hAX) hle
  have hx64 : 64 ≤ x := le_trans (le_max_right _ _) hle
  have hX2t : X2 ≤ t := by
    have hY := hY2 x hxY2
    simp only [pow_zero, mul_one] at hY
    have h2 : (x : ℝ) ^ ((11 : ℝ) / 16) / 2 ≤ (t : ℝ) :=
      le_trans (half_rpow_le_Rcut hx64) (by exact_mod_cast hDt)
    have h3 : (X2 : ℝ) ≤ (t : ℝ) := by
      have : (X2 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) / 2 := by linarith
      linarith
    exact_mod_cast h3
  have ht1 : 1 ≤ t := by omega
  have hν₀1 : 1 ≤ ν₀ := by omega
  have hRt : 4 ≤ Submission.Rcut x := four_le_Rcut hx64
  have ht4 : 4 ≤ t := le_trans hRt hDt
  -- the logarithm lower bound `1 ≤ log x`
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 3 ≤ x by omega)
    have he : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlogx0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlogx1
  have htxR : (t : ℝ) ≤ (x : ℝ) := by exact_mod_cast htx
  have htR0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hlogt : Real.log ((t : ℝ) + 2) ≤ Real.log ((x : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogx2 : Real.log x ≤ Real.log ((x : ℝ) + 2) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < x)) (by linarith)
  have hlogtp : (0 : ℝ) < Real.log ((t : ℝ) + 2) := by
    have : (1 : ℝ) < (t : ℝ) + 2 := by linarith
    exact Real.log_pos this
  have hAc0 : (0 : ℝ) ≤ Acount FIa (t : ℝ) := Finset.sum_nonneg (fun n _ => FIa_nonneg n)
  -- pointwise splitting
  have hpt : ∀ ν : ℕ, Ad FIa (ν ^ 2) t
      ≤ |FIr (ν ^ 2) t| + Acount FIa (t : ℝ) * FIg (ν ^ 2) := by
    intro ν
    have h : FIr (ν ^ 2) t = Ad FIa (ν ^ 2) t - FIg (ν ^ 2) * Acount FIa (t : ℝ) := rfl
    have h2 : Ad FIa (ν ^ 2) t = FIr (ν ^ 2) t + FIg (ν ^ 2) * Acount FIa (t : ℝ) := by
      rw [h]; ring
    rw [h2, mul_comm (Acount FIa (t : ℝ)) (FIg (ν ^ 2))]
    linarith [le_abs_self (FIr (ν ^ 2) t), mul_nonneg (FIg_nonneg (ν ^ 2)) hAc0]
  -- the two halves
  have hsplit : (∑ ν ∈ ((Finset.Icc (L + 1) t.sqrt).filter Squarefree), Ad FIa (ν ^ 2) t)
      = (∑ ν ∈ ((Finset.Icc (L + 1) ν₀).filter Squarefree), Ad FIa (ν ^ 2) t)
        + (∑ ν ∈ ((Finset.Icc (ν₀ + 1) t.sqrt).filter Squarefree), Ad FIa (ν ^ 2) t) := by
    have h1 : ((Finset.Icc (L + 1) t.sqrt).filter Squarefree)
        = ((Finset.Icc (L + 1) ν₀).filter Squarefree)
          ∪ ((Finset.Icc (ν₀ + 1) t.sqrt).filter Squarefree) := by
      ext ν
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        by_cases h : ν ≤ ν₀
        · exact Or.inl ⟨⟨h1, h⟩, h3⟩
        · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
      · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨⟨h1, le_trans h2 hν₀s⟩, h3⟩
        · exact ⟨⟨by omega, h2⟩, h3⟩
    rw [h1, Finset.sum_union]
    refine Finset.disjoint_left.mpr (fun ν h1 h2 => ?_)
    simp only [Finset.mem_filter, Finset.mem_Icc] at h1 h2
    omega
  rw [hsplit]
  -- the first half
  have h1 : (∑ ν ∈ ((Finset.Icc (L + 1) ν₀).filter Squarefree), Ad FIa (ν ^ 2) t)
      ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((β - 71) / 4))
        + Acount FIa (t : ℝ) * (K / Real.sqrt (L : ℝ)) := by
    have h2 : (∑ ν ∈ ((Finset.Icc (L + 1) ν₀).filter Squarefree), Ad FIa (ν ^ 2) t)
        ≤ (∑ ν ∈ ((Finset.Icc (L + 1) ν₀).filter Squarefree), |FIr (ν ^ 2) t|)
          + Acount FIa (t : ℝ) * (∑ ν ∈ ((Finset.Icc (L + 1) ν₀).filter Squarefree),
              FIg (ν ^ 2)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun ν _ => hpt ν)
    have h3 : (∑ ν ∈ ((Finset.Icc (L + 1) ν₀).filter Squarefree), |FIr (ν ^ 2) t|)
        ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((β - 71) / 4)) := by
      have hsub : ((Finset.Icc (L + 1) ν₀).filter Squarefree)
          ⊆ (Finset.Icc 1 ν₀).filter Squarefree := by
        intro ν hν
        obtain ⟨hνI, hνsf⟩ := Finset.mem_filter.mp hν
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hνI
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, h2⟩, hνsf⟩
      have hsm := hsmall x hxX1 t (by omega) htx ν₀ hν₀1 (by simpa using hν₀sq)
      exact le_trans (le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ => abs_nonneg _)) hsm)
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith)) (by positivity))
    have h4 : (∑ ν ∈ ((Finset.Icc (L + 1) ν₀).filter Squarefree), FIg (ν ^ 2))
        ≤ K / Real.sqrt (L : ℝ) := by
      have heq : (∑ ν ∈ ((Finset.Icc (L + 1) ν₀).filter Squarefree), FIg (ν ^ 2))
          = ∑ ν ∈ ((Finset.Icc (L + 1) ν₀).filter Squarefree), |FIg (ν ^ 2)| :=
        Finset.sum_congr rfl (fun ν _ => (abs_of_nonneg (FIg_nonneg (ν ^ 2))).symm)
      rw [heq]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => abs_nonneg _))
        (hTail t L hL1)
      intro ν hν
      obtain ⟨hνI, hνsf⟩ := Finset.mem_filter.mp hν
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hνI
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨by omega, le_trans h2 (le_trans hν₀s (Nat.sqrt_le_self t))⟩, by omega⟩
    exact le_trans h2 (add_le_add h3 (mul_le_mul_of_nonneg_left h4 hAc0))
  -- the second half
  have h2 : (∑ ν ∈ ((Finset.Icc (ν₀ + 1) t.sqrt).filter Squarefree), Ad FIa (ν ^ 2) t)
      ≤ (Acount FIa (t : ℝ) * K3 * (Real.log ((t : ℝ) + 2)) ^ ((71 - β) / 2)
          + Acount FIa (t : ℝ) * K3 / Real.sqrt (ν₀ : ℝ))
        + Acount FIa (t : ℝ) * (K / Real.sqrt (L : ℝ)) := by
    have h3 : (∑ ν ∈ ((Finset.Icc (ν₀ + 1) t.sqrt).filter Squarefree), Ad FIa (ν ^ 2) t)
        ≤ (∑ ν ∈ ((Finset.Icc (ν₀ + 1) t.sqrt).filter Squarefree), |FIr (ν ^ 2) t|)
          + Acount FIa (t : ℝ) * (∑ ν ∈ ((Finset.Icc (ν₀ + 1) t.sqrt).filter Squarefree),
              FIg (ν ^ 2)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun ν _ => hpt ν)
    have h4 : (∑ ν ∈ ((Finset.Icc (ν₀ + 1) t.sqrt).filter Squarefree), |FIr (ν ^ 2) t|)
        ≤ Acount FIa (t : ℝ) * K3 * (Real.log ((t : ℝ) + 2)) ^ ((71 - β) / 2)
          + Acount FIa (t : ℝ) * K3 / Real.sqrt (ν₀ : ℝ) := by
      exact hlarge x hxX2 t hX2t htx ν₀ hν₀1 hν₀s hν₀b
    have h5 : (∑ ν ∈ ((Finset.Icc (ν₀ + 1) t.sqrt).filter Squarefree), FIg (ν ^ 2))
        ≤ K / Real.sqrt (L : ℝ) := by
      have heq : (∑ ν ∈ ((Finset.Icc (ν₀ + 1) t.sqrt).filter Squarefree), FIg (ν ^ 2))
          = ∑ ν ∈ ((Finset.Icc (ν₀ + 1) t.sqrt).filter Squarefree), |FIg (ν ^ 2)| :=
        Finset.sum_congr rfl (fun ν _ => (abs_of_nonneg (FIg_nonneg (ν ^ 2))).symm)
      rw [heq]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => abs_nonneg _))
        (hTail t L hL1)
      intro ν hν
      obtain ⟨hνI, hνsf⟩ := Finset.mem_filter.mp hν
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hνI
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨by omega, le_trans h2 (Nat.sqrt_le_self t)⟩, by omega⟩
    exact le_trans h3 (add_le_add h4 (mul_le_mul_of_nonneg_left h5 hAc0))
  refine le_trans (add_le_add h1 h2) ?_
  -- each piece is `≤ Aseq x·(log x)^{−2^60}` (up to the constant `2^{2^62}`)
  have hAseq : (Submission.Aseq x : ℝ) = Acount FIa (x : ℝ) + 1 := by
    rw [FI_Acount_eq]; ring
  have hAt : Acount FIa (t : ℝ) ≤ (Submission.Aseq x : ℝ) := by
    have h1 : Acount FIa (t : ℝ) ≤ Submission.Aseq t := by
      rw [FI_Acount_eq]; linarith
    exact le_trans h1 (by exact_mod_cast Aseq_mono htx)
  have hlogx4 : (4 : ℝ) ≤ Real.log x := by
    have h1 : Real.exp 4 = ((Real.exp 1) ^ 2) ^ 2 := by
      rw [show (4 : ℝ) = (1 + 1) + (1 + 1) from by norm_num, Real.exp_add, Real.exp_add]
      ring
    have h2 : Real.exp 4 < 64 := by
      rw [h1]
      have h3 : (Real.exp 1) ^ 2 < (2.7182818286 : ℝ) ^ 2 := by
        nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
      nlinarith [h3, Real.exp_pos 1]
    have he : Real.exp 4 ≤ (x : ℝ) := by
      have hx64' : (64 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx64
      linarith
    have h := Real.log_le_log (Real.exp_pos 4) he
    rwa [Real.log_exp] at h
  have hlogt2 : Real.log x / 2 ≤ Real.log ((t : ℝ) + 2) := by
    have ht_ge : (x : ℝ) ^ ((11 : ℝ) / 16) / 2 ≤ (t : ℝ) :=
      le_trans (half_rpow_le_Rcut hx64) (by exact_mod_cast hDt)
    have h1 : Real.log ((x : ℝ) ^ ((11 : ℝ) / 16) / 2) ≤ Real.log ((t : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div (by positivity) (by norm_num),
      Real.log_rpow (by exact_mod_cast (by omega : 0 < x))] at h1
    have h3 : Real.log 2 ≤ (3 / 16 : ℝ) * Real.log x := by
      have h4 := Real.log_two_lt_d9
      nlinarith [hlogx4]
    linarith
  have hP0 : (0 : ℝ) ≤ (Real.log x) ^ (-((β - 71) / 4)) :=
    Real.rpow_nonneg hlogx0.le _
  have hsL : (0 : ℝ) < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < L))
  have hAs0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
  -- the `1/√L` and `1/√ν₀` comparisons
  have hbexp : (β - 71) / 4 + -((β - 71) / 4) = 0 := by ring
  have hcmpL : K / Real.sqrt (L : ℝ) ≤ K * (Real.log x) ^ (-((β - 71) / 4)) := by
    rw [div_le_iff₀ hsL]
    have h1 : (1 : ℝ) ≤ (Real.log x) ^ (-((β - 71) / 4)) * Real.sqrt (L : ℝ) := by
      calc (1 : ℝ) = (Real.log x) ^ ((β - 71) / 4) * (Real.log x) ^ (-((β - 71) / 4)) := by
            rw [← Real.rpow_add hlogx0, hbexp, Real.rpow_zero]
        _ ≤ Real.sqrt (L : ℝ) * (Real.log x) ^ (-((β - 71) / 4)) :=
            mul_le_mul_of_nonneg_right hLb hP0
        _ = (Real.log x) ^ (-((β - 71) / 4)) * Real.sqrt (L : ℝ) := by ring
    calc K = K * 1 := by ring
      _ ≤ K * ((Real.log x) ^ (-((β - 71) / 4)) * Real.sqrt (L : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hKpos.le
      _ = K * (Real.log x) ^ (-((β - 71) / 4)) * Real.sqrt (L : ℝ) := by ring
  -- piece 2
  have hp2 : Acount FIa (t : ℝ) * (K / Real.sqrt (L : ℝ))
      ≤ (Submission.Aseq x : ℝ) * (K * (Real.log x) ^ (-((β - 71) / 4))) :=
    le_trans (mul_le_mul_of_nonneg_right hAt (by positivity))
      (mul_le_mul_of_nonneg_left hcmpL hAs0)
  -- piece 3
  have hp3 : Acount FIa (t : ℝ) * K3 * (Real.log ((t : ℝ) + 2)) ^ ((71 - β) / 2)
      ≤ (Submission.Aseq x : ℝ) * (K3 * (Real.log x) ^ (-((β - 71) / 4))) := by
    have hbase : (1 : ℝ) ≤ Real.log ((t : ℝ) + 2) := by
      have h5 : (3 : ℝ) ≤ (t : ℝ) + 2 := by
        have h6 : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 3 ≤ t by omega)
        linarith
      have he : Real.exp 1 ≤ (t : ℝ) + 2 := by linarith [Real.exp_one_lt_three]
      have h := Real.log_le_log (Real.exp_pos 1) he
      rwa [Real.log_exp] at h
    have h2 : (Real.log ((t : ℝ) + 2)) ^ ((71 - β) / 2)
        ≤ (Real.log x) ^ (-((β - 71) / 4)) := by
      have h4 : (2 : ℝ) ≤ Real.log ((t : ℝ) + 2) := by linarith [hlogt2, hlogx4]
      have hsq : Real.log x ≤ (Real.log ((t : ℝ) + 2)) ^ 2 := by
        nlinarith [hlogt2, h4, hbase]
      have h5 : ((Real.log ((t : ℝ) + 2)) ^ 2) ^ (-((β - 71) / 4))
          ≤ (Real.log x) ^ (-((β - 71) / 4)) :=
        Commons.Analysis.RealPow.rpow_le_rpow_of_one_le_of_exponent_nonpos hlogx1 hsq
          (by linarith)
      have h6 : ((Real.log ((t : ℝ) + 2)) ^ 2) ^ (-((β - 71) / 4))
          = (Real.log ((t : ℝ) + 2)) ^ ((71 - β) / 2) := by
        rw [← Real.rpow_natCast (Real.log ((t : ℝ) + 2)) 2,
          ← Real.rpow_mul (le_trans zero_le_one hbase)]
        congr 1
        ring
      rw [h6] at h5
      exact h5
    have hstep : Acount FIa (t : ℝ) * (K3 * (Real.log ((t : ℝ) + 2)) ^ ((71 - β) / 2))
        ≤ Acount FIa (t : ℝ) * (K3 * (Real.log x) ^ (-((β - 71) / 4))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hK3pos.le) hAc0
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hAt (by positivity))
    simpa only [mul_assoc] using hstep
  -- piece 4
  have hν₀le : L ≤ ν₀ := hLν₀'
  have hν₀big : (Real.log x) ^ ((β - 71) / 4) ≤ Real.sqrt (ν₀ : ℝ) :=
    le_trans hLb (Real.sqrt_le_sqrt (by exact_mod_cast hν₀le))
  have hp4 : Acount FIa (t : ℝ) * K3 / Real.sqrt (ν₀ : ℝ)
      ≤ (Submission.Aseq x : ℝ) * (K3 * (Real.log x) ^ (-((β - 71) / 4))) := by
    have hsν : (0 : ℝ) < Real.sqrt (ν₀ : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < ν₀))
    have hcmpν : K3 / Real.sqrt (ν₀ : ℝ) ≤ K3 * (Real.log x) ^ (-((β - 71) / 4)) := by
      rw [div_le_iff₀ hsν]
      have h1 : (1 : ℝ) ≤ (Real.log x) ^ (-((β - 71) / 4)) * Real.sqrt (ν₀ : ℝ) := by
        calc (1 : ℝ) = (Real.log x) ^ ((β - 71) / 4) * (Real.log x) ^ (-((β - 71) / 4)) := by
              rw [← Real.rpow_add hlogx0, hbexp, Real.rpow_zero]
          _ ≤ Real.sqrt (ν₀ : ℝ) * (Real.log x) ^ (-((β - 71) / 4)) :=
              mul_le_mul_of_nonneg_right hν₀big hP0
          _ = (Real.log x) ^ (-((β - 71) / 4)) * Real.sqrt (ν₀ : ℝ) := by ring
      calc K3 = K3 * 1 := by ring
        _ ≤ K3 * ((Real.log x) ^ (-((β - 71) / 4)) * Real.sqrt (ν₀ : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 hK3pos.le
        _ = K3 * (Real.log x) ^ (-((β - 71) / 4)) * Real.sqrt (ν₀ : ℝ) := by ring
    rw [show Acount FIa (t : ℝ) * K3 / Real.sqrt (ν₀ : ℝ)
          = Acount FIa (t : ℝ) * (K3 / Real.sqrt (ν₀ : ℝ)) from by ring]
    exact le_trans (mul_le_mul_of_nonneg_right hAt (by positivity))
      (mul_le_mul_of_nonneg_left hcmpν hAs0)
  -- assembly
  have hp1' : 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((β - 71) / 4))
      ≤ (Submission.Aseq x : ℝ) * (4 * (Real.log x) ^ (-((β - 71) / 4))) :=
    le_of_eq (by ring)
  have hsum := add_le_add (add_le_add hp1' hp2) (add_le_add (add_le_add hp3 hp4) hp2)
  refine le_trans hsum ?_
  nlinarith [hKpos.le, hK3pos.le, mul_nonneg hAs0 hP0, hP0]
/-- For `1 ≤ y` and `v ≥ 0` with `v² ≤ A/4`, the ceiling `⌈v⌉₊` satisfies `(⌈v⌉₊)² ≤ A`
whenever `4 ≤ A`. -/
lemma ceil_sq_le {A : ℝ} (hA : 4 ≤ A) {v : ℝ} (hv : 0 ≤ v) (h : v ^ 2 ≤ A / 4) :
    ((⌈v⌉₊ : ℕ) : ℝ) ^ 2 ≤ A := by
  have h1 : (⌈v⌉₊ : ℝ) < v + 1 := Nat.ceil_lt_add_one hv
  have h2 : ((⌈v⌉₊ : ℕ) : ℝ) ^ 2 ≤ (v + 1) ^ 2 := by
    have h3 : (0 : ℝ) ≤ ((⌈v⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  nlinarith [h2, h1, hv, h]

/-- Strict version of `ceil_sq_le`. -/
lemma ceil_sq_lt {A : ℝ} (hA : 8 ≤ A) {v : ℝ} (hv : 0 ≤ v) (h : v ^ 2 ≤ A / 8) :
    ((⌈v⌉₊ : ℕ) : ℝ) ^ 2 < A := by
  have h1 : (⌈v⌉₊ : ℝ) < v + 1 := Nat.ceil_lt_add_one hv
  have h2 : ((⌈v⌉₊ : ℕ) : ℝ) ^ 2 ≤ (v + 1) ^ 2 := by
    have h3 : (0 : ℝ) ≤ ((⌈v⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  nlinarith [h2, h1, hv, h]

set_option maxHeartbeats 4000000 in
/-- **Companion §9, the `E₂` estimate (9.12)**: the `ν > L` part of the §9 error term is
`≪ A(x)(log x)^{−λ}`, given the `τ³`-weighted `S₂ ≪ A(x)(log x)^{B₂}` with `B₂ ≤ 2λ` and that
`(log x)^{4λ+100} ≤ L`. -/
theorem FI_Etwo_le (B2 C2 lam : ℝ) (hC2 : 0 < C2) (hB2 : 0 ≤ B2) (hcomp : B2 ≤ 2 * lam)
    (X2 : ℕ)
    (hS2 : ∀ x : ℕ, X2 ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      (∑ n ∈ Finset.Icc 1 t, FIa n * ((n.divisors.card : ℝ)) ^ (3 : ℕ))
        ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2) :
    ∃ X₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x → ∀ t L : ℕ,
      2 ≤ t → t ≤ x → Submission.Rcut x ≤ t → 1 ≤ L → L < t.sqrt →
      (L + 1) ^ 2 < Submission.X2Y4R3.R3cut x →
      (Real.log x) ^ (8 * lam + 100) ≤ (L : ℝ) →
      Etwo FIa FIg t (Submission.Rcut x) L
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
  obtain ⟨Cg, hCg, hGle⟩ := EtwoG_FIa_le
  set lamm : ℝ := B2 + 2 * lam + 10 with hlammdef
  set β : ℝ := 71 + 4 * lamm with hβdef
  have hβ71 : (71 : ℝ) ≤ β := by rw [hβdef]; linarith
  have hlamm0 : (0 : ℝ) ≤ lamm := by rw [hlammdef]; linarith
  have hβ0 : (0 : ℝ) ≤ β := le_trans (by norm_num) hβ71
  obtain ⟨Xlim, Clim, hClim, hAd⟩ := FI_Ad_sqrt_le β hβ71
  -- thresholds
  obtain ⟨Y1, -, hY1⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := (1 : ℝ)) (by norm_num) (n := ⌈2 * β⌉₊) (r := (1 : ℝ) / 60) (by norm_num)
  obtain ⟨Y2, -, hY2⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := 2 * Real.sqrt 2) (by positivity) (n := 0) (r := (1 : ℝ) / 480) (by norm_num)
  obtain ⟨Y3, -, hY3⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := 16) (by norm_num) (n := 0) (r := (1 : ℝ) / 60) (by norm_num)
  obtain ⟨Y4, -, hY4⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := 2 ^ (45 : ℕ)) (by positivity) (n := 40) (r := (1 : ℝ) / 2) (by norm_num)
  obtain ⟨Y6, -, hY6⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := 9) (by norm_num) (n := 0) (r := (7 : ℝ) / 10) (by norm_num)
  obtain ⟨Y5, -, hY5⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_add_two_pow_le_rpow_threshold_nat
      (K := Real.exp ((2 : ℝ) ^ (45 : ℕ))) (by positivity) (n := 0) (r := 1) (by norm_num)
  have hlam3 : (3 * lam + 100) ≥ (46 : ℝ) := by
    have := hcomp
    nlinarith [hB2, hcomp]
  refine ⟨max (max (max Xlim (max Y1 Y2)) (max Y3 (max Y4 Y5))) (max (max Y6 129) X2),
    (1 + Real.sqrt (Clim * C2) + Cg * (2 : ℝ) ^ (37 : ℕ)) * 8, by positivity,
    fun x hx t L ht htx hDt hL1 hLt hLsq hLbig => ?_⟩
  have hle := hx
  have hAX : max Xlim (max Y1 Y2)
      ≤ max (max (max Xlim (max Y1 Y2)) (max Y3 (max Y4 Y5))) (max (max Y6 129) X2) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hBY : max Y3 (max Y4 Y5)
      ≤ max (max (max Xlim (max Y1 Y2)) (max Y3 (max Y4 Y5))) (max (max Y6 129) X2) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hxXlim : Xlim ≤ x := le_trans (le_trans (le_max_left _ _) hAX) hle
  have hxY1 : Y1 ≤ x :=
    le_trans (le_trans (le_trans (le_max_left Y1 Y2) (le_max_right Xlim _)) hAX) hle
  have hxY2 : Y2 ≤ x :=
    le_trans (le_trans (le_trans (le_max_right Y1 Y2) (le_max_right Xlim _)) hAX) hle
  have hxY3 : Y3 ≤ x := le_trans (le_trans (le_max_left _ _) hBY) hle
  have hxY4 : Y4 ≤ x :=
    le_trans (le_trans (le_trans (le_max_left Y4 Y5) (le_max_right Y3 _)) hBY) hle
  have hxY5 : Y5 ≤ x :=
    le_trans (le_trans (le_trans (le_max_right Y4 Y5) (le_max_right Y3 _)) hBY) hle
  have hx128 : 128 ≤ x :=
    le_trans (by norm_num : (128 : ℕ) ≤ 129)
      (le_trans (le_max_right Y6 129)
        (le_trans (le_max_left (max Y6 129) X2) (le_trans (le_max_right _ _) hle)))
  have hxY6 : Y6 ≤ x :=
    le_trans (le_max_left Y6 129)
      (le_trans (le_max_left (max Y6 129) X2) (le_trans (le_max_right _ _) hle))
  have hxX2 : X2 ≤ x :=
    le_trans (le_max_right (max Y6 129) X2) (le_trans (le_max_right _ _) hle)
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hx1)
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have htxR : (t : ℝ) ≤ (x : ℝ) := by exact_mod_cast htx
  have ht1 : 1 ≤ t := le_trans (by norm_num : 1 ≤ 2) ht
  have ht4' : 4 ≤ t := le_trans (four_le_Rcut (le_trans (by norm_num : 64 ≤ 128) hx128)) hDt
  have htR0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) ht1)
  have ht4 : (4 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht4'
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hL1)
  have hL1R : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hRt : 4 ≤ Submission.Rcut x := four_le_Rcut (le_trans (by norm_num : 64 ≤ 128) hx128)
  have hD1 : 1 ≤ Submission.Rcut x := le_trans (by norm_num : 1 ≤ 4) hRt
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_trans (by norm_num : 2 ≤ 128) hx128)
  have hDx : Submission.Rcut x ≤ x := by
    rw [Submission.Rcut]
    have h1 : ((⌊(x : ℝ) ^ ((11 : ℝ) / 16)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) :=
      le_trans (Nat.floor_le (Real.rpow_nonneg hx0.le _))
        (by simpa using Real.rpow_le_rpow_of_exponent_le hxR1 (show (11 : ℝ) / 16 ≤ 1 by norm_num))
    exact_mod_cast h1
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    have hx3 : (3 : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 3 ≤ 128) hx128)
    have he : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlogx0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlogx1
  have hlogadd1 : (1 : ℝ) ≤ Real.log ((x : ℝ) + 2) := by
    have h5 : Real.exp 1 ≤ (x : ℝ) + 2 := by linarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (Real.exp_pos 1) h5
    rwa [Real.log_exp] at h
  have hlogt1 : (1 : ℝ) ≤ Real.log ((t : ℝ) + 2) := by
    have h3 : (3 : ℝ) ≤ (t : ℝ) + 2 := by linarith [ht4]
    have he : Real.exp 1 ≤ (t : ℝ) + 2 := by linarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlogt_le : Real.log ((t : ℝ) + 2) ≤ Real.log ((x : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  -- threshold consequences
  have h2sqrt2 : 2 * Real.sqrt 2 ≤ (x : ℝ) ^ ((1 : ℝ) / 480) := by
    have h := hY2 x hxY2
    simpa using h
  have h4pow : (16 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 60) := by
    have h := hY3 x hxY3
    simpa using h
  have h45log : ((2 : ℝ) ^ (45 : ℕ)) ≤ Real.log x := by
    have h := hY5 x hxY5
    simp only [pow_zero, mul_one] at h
    have h2 : Real.log (Real.exp ((2 : ℝ) ^ (45 : ℕ))) ≤ Real.log x :=
      Real.log_le_log (Real.exp_pos _) (by simpa using h)
    rwa [Real.log_exp] at h2
  have hlog2le : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hxR2
  have hpow45 : ((2 : ℝ) ^ (45 : ℕ)) * (Real.log x) ^ (45 : ℕ) ≤ (Real.log x) ^ (46 : ℕ) := by
    have h1 : (2 : ℝ) ^ (45 : ℕ) ≤ Real.log x := h45log
    calc ((2 : ℝ) ^ (45 : ℕ)) * (Real.log x) ^ (45 : ℕ)
        ≤ (Real.log x) * (Real.log x) ^ (45 : ℕ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (Real.log x) ^ (46 : ℕ) := by ring
  -- `(log(x+2))^{2β} ≤ x^{1/60}`
  have hthr : (Real.log ((x : ℝ) + 2)) ^ (2 * β) ≤ (x : ℝ) ^ ((1 : ℝ) / 60) := by
    have h2 := hY1 x hxY1
    have h3 : (Real.log ((x : ℝ) + 2)) ^ (2 * β)
        ≤ (Real.log ((x : ℝ) + 2)) ^ (⌈2 * β⌉₊ : ℕ) := by
      have h4 := Real.rpow_le_rpow_of_exponent_le hlogadd1 (Nat.le_ceil (2 * β))
      rwa [Real.rpow_natCast] at h4
    linarith
  have hlogβx : (Real.log ((x : ℝ) + 2)) ^ β ≤ (x : ℝ) ^ ((1 : ℝ) / 120) := by
    have h2 : ((Real.log ((x : ℝ) + 2)) ^ β) ^ 2 = (Real.log ((x : ℝ) + 2)) ^ (2 * β) := by
      rw [← Real.rpow_natCast ((Real.log ((x : ℝ) + 2)) ^ β) 2,
        ← Real.rpow_mul (le_trans zero_le_one hlogadd1)]
      congr 1
      ring
    have h3 : ((Real.log ((x : ℝ) + 2)) ^ β) ^ 2 ≤ (x : ℝ) ^ ((1 : ℝ) / 60) := by
      rw [h2]; exact hthr
    have h4 : (x : ℝ) ^ ((1 : ℝ) / 60) = ((x : ℝ) ^ ((1 : ℝ) / 120)) ^ 2 := by
      rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 120)) 2, ← Real.rpow_mul hx0.le]
      congr 1
      norm_num
    rw [h4] at h3
    have hA0 : (0 : ℝ) ≤ (Real.log ((x : ℝ) + 2)) ^ β := Real.rpow_nonneg (by linarith) _
    have hB0 : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 120) := Real.rpow_nonneg hx0.le _
    nlinarith [h3, hA0, hB0]
  -- the split point
  set v : ℝ := (t : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((t : ℝ) + 2)) ^ β with hvdef
  set ν₀ : ℕ := ⌈v⌉₊ with hν₀def
  set ν₁ : ℕ := max L ν₀ with hν₁def
  have hv0 : 0 ≤ v := mul_nonneg (Real.rpow_nonneg htR0.le _) (Real.rpow_nonneg (by positivity) _)
  have hν₀low : v ≤ (ν₀ : ℝ) := Nat.le_ceil v
  have hLν₁ : L ≤ ν₁ := le_max_left _ _
  have hν₀ν₁ : ν₀ ≤ ν₁ := le_max_right _ _
  -- `v ≤ x^{41/120}` and `v² ≤ x^{41/60}`
  have hv_le : v ≤ (x : ℝ) ^ ((41 : ℝ) / 120) := by
    have h1 : (Real.log ((t : ℝ) + 2)) ^ β ≤ (x : ℝ) ^ ((1 : ℝ) / 120) :=
      le_trans (Real.rpow_le_rpow (le_trans zero_le_one hlogt1) hlogt_le hβ0) hlogβx
    have h2 : v ≤ (t : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 120) := by
      rw [hvdef]
      exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg htR0.le _)
    have h3 : (t : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 120)
        ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 120) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow htR0.le htxR (by norm_num))
        (Real.rpow_nonneg hx0.le _)
    have h4 : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 120) = (x : ℝ) ^ ((41 : ℝ) / 120) := by
      rw [← Real.rpow_add hx0]; congr 1; norm_num
    linarith
  have hv_sq_le : v ^ 2 ≤ (x : ℝ) ^ ((41 : ℝ) / 60) := by
    rw [hvdef]
    have h1 : ((t : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((t : ℝ) + 2)) ^ β) ^ 2
        = (t : ℝ) ^ ((2 : ℝ) / 3) * ((Real.log ((t : ℝ) + 2)) ^ β) ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast ((t : ℝ) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul htR0.le]
      congr 2
      norm_num
    rw [h1]
    have h2 : ((Real.log ((t : ℝ) + 2)) ^ β) ^ 2 ≤ ((x : ℝ) ^ ((1 : ℝ) / 120)) ^ 2 :=
      pow_le_pow_left₀ (by positivity)
        (le_trans (Real.rpow_le_rpow (le_trans zero_le_one hlogt1) hlogt_le hβ0) hlogβx) 2
    have h3 : ((x : ℝ) ^ ((1 : ℝ) / 120)) ^ 2 = (x : ℝ) ^ ((1 : ℝ) / 60) := by
      rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 120)) 2, ← Real.rpow_mul hx0.le]
      congr 1
      norm_num
    have h4 : (t : ℝ) ^ ((2 : ℝ) / 3) ≤ (x : ℝ) ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow htR0.le htxR (by norm_num)
    calc (t : ℝ) ^ ((2 : ℝ) / 3) * ((Real.log ((t : ℝ) + 2)) ^ β) ^ 2
        ≤ (x : ℝ) ^ ((2 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 60) :=
          mul_le_mul h4 (le_trans h2 (le_of_eq h3)) (by positivity)
            (Real.rpow_nonneg hx0.le _)
      _ = (x : ℝ) ^ ((41 : ℝ) / 60) := by
          rw [← Real.rpow_add hx0]; congr 1; norm_num
  -- `ν₀ ≤ t.sqrt`
  have hx64' : 64 ≤ x := le_trans (by norm_num : 64 ≤ 128) hx128
  have hν₀_sqrt : ν₀ ≤ t.sqrt := by
    -- `x^{41/120} ≤ t^{1/2}/2`
    have h4 : (x : ℝ) ^ ((11 : ℝ) / 16) / 2 ≤ (t : ℝ) :=
      le_trans (half_rpow_le_Rcut hx64') (by exact_mod_cast hDt)
    have h5 : ((x : ℝ) ^ ((11 : ℝ) / 16) / 2) ^ ((1 : ℝ) / 2) ≤ (t : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) h4 (by norm_num)
    have h6 : ((x : ℝ) ^ ((11 : ℝ) / 16) / 2) ^ ((1 : ℝ) / 2)
        = (x : ℝ) ^ ((11 : ℝ) / 32) / Real.sqrt 2 := by
      rw [Real.div_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hx0.le]
      congr 1
      norm_num
    rw [h6] at h5
    have h7 : (x : ℝ) ^ ((41 : ℝ) / 120) ≤ (x : ℝ) ^ ((11 : ℝ) / 32) / (2 * Real.sqrt 2) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)]
      have h8 : (x : ℝ) ^ ((11 : ℝ) / 32)
          = (x : ℝ) ^ ((41 : ℝ) / 120) * (x : ℝ) ^ ((1 : ℝ) / 480) := by
        rw [← Real.rpow_add hx0]; congr 1; norm_num
      rw [h8]
      exact mul_le_mul_of_nonneg_left h2sqrt2 (Real.rpow_nonneg hx0.le _)
    have h9 : (x : ℝ) ^ ((11 : ℝ) / 32) / (2 * Real.sqrt 2)
        ≤ (t : ℝ) ^ ((1 : ℝ) / 2) / 2 := by
      have h10 : (x : ℝ) ^ ((11 : ℝ) / 32) / (2 * Real.sqrt 2)
          = (x : ℝ) ^ ((11 : ℝ) / 32) / Real.sqrt 2 / 2 := by ring
      rw [h10]
      linarith [h5]
    have h11 : v ≤ (t : ℝ) ^ ((1 : ℝ) / 2) / 2 := le_trans hv_le (le_trans h7 h9)
    have h12 : (ν₀ : ℝ) < v + 1 := Nat.ceil_lt_add_one hv0
    have h13 : (ν₀ : ℝ) ^ 2 < (t : ℝ) := by
      have h14 : (t : ℝ) ^ ((1 : ℝ) / 2) / 2 + 1 ≤ (t : ℝ) ^ ((1 : ℝ) / 2) := by
        have h15 : (2 : ℝ) ≤ (t : ℝ) ^ ((1 : ℝ) / 2) := by
          have h16 : (4 : ℝ) ^ ((1 : ℝ) / 2) ≤ (t : ℝ) ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow (by norm_num) ht4 (by norm_num)
          have h17 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by norm_num
          linarith
        linarith
      have h18 : ((t : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (t : ℝ) := by
        rw [← Real.rpow_natCast ((t : ℝ) ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul htR0.le]
        norm_num
      nlinarith [h12, h11, h14, h18, sq_nonneg ((t : ℝ) ^ ((1 : ℝ) / 2) - 1)]
    rw [Nat.le_sqrt]
    have h19 : (ν₀ * ν₀ : ℕ) = ν₀ ^ 2 := by ring
    rw [h19]
    exact_mod_cast le_of_lt h13
  -- `ν₀² < R3cut x`
  have hν₀_sq : (ν₀ : ℝ) ^ 2 < (Submission.X2Y4R3.R3cut x : ℝ) := by
    have h1 : v ^ 2 ≤ (Submission.X2Y4R3.R3cut x : ℝ) / 8 := by
      have h3 : (x : ℝ) ^ ((7 : ℝ) / 10) - 1 < (Submission.X2Y4R3.R3cut x : ℝ) := by
        rw [Submission.X2Y4R3.R3cut]
        have h6 : (1 : ℝ) ≤ (Real.log x) ^ ((2 : ℝ) ^ 25) :=
          Real.one_le_rpow hlogx1 (by norm_num)
        have h7 : (x : ℝ) ^ ((7 : ℝ) / 10)
            ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) := by
          calc (x : ℝ) ^ ((7 : ℝ) / 10) = (x : ℝ) ^ ((7 : ℝ) / 10) * 1 := by ring
            _ ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) :=
                mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg hx0.le _)
        have h8 := Nat.lt_floor_add_one
          ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25))
        push_cast at h8
        linarith
      have h8 : (x : ℝ) ^ ((41 : ℝ) / 60) * 16 ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := by
        calc (x : ℝ) ^ ((41 : ℝ) / 60) * 16
            ≤ (x : ℝ) ^ ((41 : ℝ) / 60) * (x : ℝ) ^ ((1 : ℝ) / 60) :=
              mul_le_mul_of_nonneg_left h4pow (Real.rpow_nonneg hx0.le _)
          _ = (x : ℝ) ^ ((7 : ℝ) / 10) := by
              rw [← Real.rpow_add hx0]; congr 1; norm_num
      have h10 : (2 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := by
        have h11 : (2 : ℝ) ≤ (64 : ℝ) ^ ((7 : ℝ) / 10) := two_le_rpow_seven_tenths (by norm_num)
        exact le_trans h11 (Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx64') (by norm_num))
      have h9''' : (8 : ℝ) * (x : ℝ) ^ ((41 : ℝ) / 60) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) - 1 := by
        have h12 : (8 : ℝ) * (x : ℝ) ^ ((41 : ℝ) / 60)
            = ((x : ℝ) ^ ((41 : ℝ) / 60) * 16) / 2 := by ring
        rw [h12]
        linarith [h8, h10]
      have h9'' : (8 : ℝ) * (x : ℝ) ^ ((41 : ℝ) / 60)
          ≤ (Submission.X2Y4R3.R3cut x : ℝ) := le_trans h9''' (le_of_lt h3)
      have h9' : (x : ℝ) ^ ((41 : ℝ) / 60)
          ≤ (Submission.X2Y4R3.R3cut x : ℝ) / 8 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
        simpa [mul_comm] using h9''
      linarith [h9', hv_sq_le]
    have hA8 : (8 : ℝ) ≤ (Submission.X2Y4R3.R3cut x : ℝ) := by
      rw [Submission.X2Y4R3.R3cut]
      have h13 : (9 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := by
        have h14 := hY6 x hxY6
        simpa using h14
      have h15 : (1 : ℝ) ≤ (Real.log x) ^ ((2 : ℝ) ^ 25) :=
        Real.one_le_rpow hlogx1 (by norm_num)
      have h16 : (9 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25) :=
        le_trans h13 (le_mul_of_one_le_right (Real.rpow_nonneg hx0.le _) h15)
      have h17 := Nat.lt_floor_add_one ((x : ℝ) ^ ((7 : ℝ) / 10) * (Real.log x) ^ ((2 : ℝ) ^ 25))
      push_cast at h17
      have h18 : (8 : ℝ) ≤ ((⌊(x : ℝ) ^ ((7 : ℝ) / 10)
          * (Real.log x) ^ ((2 : ℝ) ^ 25)⌋₊ : ℕ) : ℝ) := by linarith
      exact_mod_cast h18
    exact ceil_sq_lt hA8 hv0 h1
  -- `ν₁` bounds
  have hν₁_sqrt : ν₁ ≤ t.sqrt := by
    rw [hν₁def]
    exact max_le (le_of_lt hLt) hν₀_sqrt
  have hν₁_sq : ν₁ ^ 2 < Submission.X2Y4R3.R3cut x := by
    rw [hν₁def]
    have hmax : max L ν₀ ^ 2 = max (L ^ 2) (ν₀ ^ 2) := by
      rcases le_total L ν₀ with h | h
      · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ (Nat.zero_le L) h 2)]
      · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ (Nat.zero_le ν₀) h 2)]
    rw [hmax]
    refine max_lt ?_ ?_
    · exact lt_of_lt_of_le (by nlinarith : L ^ 2 < (L + 1) ^ 2) (le_of_lt hLsq)
    · have h4 : ((ν₀ ^ 2 : ℕ) : ℝ) = (ν₀ : ℝ) ^ 2 := by push_cast; ring
      have h5 : ((ν₀ ^ 2 : ℕ) : ℝ) < (Submission.X2Y4R3.R3cut x : ℝ) := by
        rw [h4]; exact hν₀_sq
      exact_mod_cast h5
  -- the `(log x)^{(β-71)/4} ≤ √L` comparison
  have hexp_le : (β - 71) / 4 ≤ 4 * lam + 50 := by
    rw [hβdef, hlammdef]
    linarith [hcomp, hB2]
  have hLbsqrt : (Real.log x) ^ ((β - 71) / 4) ≤ Real.sqrt (L : ℝ) := by
    have h1 : (Real.log x) ^ (4 * lam + 50) ≤ Real.sqrt (L : ℝ) := by
      rw [Real.le_sqrt (Real.rpow_nonneg hlogx0.le _) (Nat.cast_nonneg L)]
      have h2 : ((Real.log x) ^ (4 * lam + 50)) ^ 2 = (Real.log x) ^ (8 * lam + 100) := by
        rw [← Real.rpow_natCast ((Real.log x) ^ (4 * lam + 50)) 2,
          ← Real.rpow_mul hlogx0.le]
        congr 1
        ring
      rw [h2]; exact hLbig
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hlogx1 hexp_le) h1
  -- apply `FI_Ad_sqrt_le`
  have hS1 : (∑ ν ∈ ((Finset.Icc (L + 1) t.sqrt).filter Squarefree), Ad FIa (ν ^ 2) t)
      ≤ Clim * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
    have h := hAd x hxXlim t L ν₁ ht htx hDt hL1 hLν₁ hν₁_sqrt hν₁_sq
      (le_trans hν₀low (by exact_mod_cast hν₀ν₁)) hLbsqrt
    rwa [show (β - 71) / 4 = lamm from by rw [hβdef]; ring] at h
  -- the `X`-term vanishes
  have hsq0 : ∀ n ∈ Finset.Icc 1 t, sqdvCount n (t.sqrt + 1) t = 0 := by
    intro n hn
    rw [sqdvCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ν hν hdvd
    rw [Finset.mem_filter] at hν
    obtain ⟨hν1, _⟩ := hν
    obtain ⟨hν1a, hν1b⟩ := Finset.mem_Icc.mp hν1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn2 : n ≤ t := (Finset.mem_Icc.mp hn).2
    have h2 : ν ^ 2 ≤ n := Nat.le_of_dvd (by omega) hdvd
    have h3 : t < (t.sqrt + 1) ^ 2 := by
      have h4 : t < t.sqrt.succ * t.sqrt.succ := Nat.lt_succ_sqrt t
      have h5 : t.sqrt.succ = t.sqrt + 1 := rfl
      rw [h5] at h4
      simpa [pow_two] using h4
    have h6 : (t.sqrt + 1) ^ 2 ≤ ν ^ 2 := Nat.pow_le_pow_left hν1a 2
    omega
  have hX0 : (∑ n ∈ Finset.Icc 1 t, ((n.divisors.card : ℝ)) ^ (3 : ℕ)
      * (sqdvCount n (t.sqrt + 1) t : ℝ)) ≤ 0 := by
    have hzero : (∑ n ∈ Finset.Icc 1 t, ((n.divisors.card : ℝ)) ^ (3 : ℕ)
        * (sqdvCount n (t.sqrt + 1) t : ℝ)) = 0 := by
      refine Finset.sum_eq_zero (fun n hn => ?_)
      rw [hsq0 n hn, Nat.cast_zero, mul_zero]
    rw [hzero]
  -- apply `Etwo_le`
  have hE := Etwo_le FIa FIg (fun n => FIa_nonneg n) t (Submission.Rcut x) L t.sqrt
    (by omega) hLt (Nat.sqrt_le_self t) hX0 hS1 (hS2 x hxX2 t (by omega) htx)
    (hGle x t (Submission.Rcut x) L (by omega) htx hD1 hDx hL1)
  -- the final assembly
  have hS1nn : (0 : ℝ) ≤ Clim * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by positivity
  have hS2nn : (0 : ℝ) ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2 := by positivity
  have hsqrt0 : Real.sqrt (0 : ℝ) = 0 := Real.sqrt_zero
  have hA2nn : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 t, FIa n ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hstep : Etwo FIa FIg t (Submission.Rcut x) L ≤ Real.sqrt (Clim * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)) * Real.sqrt (C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2) + Cg * (Submission.Aseq x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 5 * (Real.log ((L : ℝ) + 2)) ^ 32 / (L : ℝ) := by
    refine le_trans hE (le_of_eq ?_)
    rw [Real.sqrt_zero, mul_zero, add_zero]
  -- bound the two terms
  have hterm1 : Real.sqrt (Clim * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm))
        * Real.sqrt (C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2)
      ≤ Real.sqrt (Clim * C2) * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
    have hS1nn : (0 : ℝ) ≤ Clim * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by positivity
    have hS2nn : (0 : ℝ) ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2 := by positivity
    rw [(Real.sqrt_mul hS1nn (C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2)).symm]
    have hprod : Clim * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)
          * (C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2)
        = Clim * C2 * (Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (B2 - lamm) := by
      have h1 : (Real.log x) ^ (-lamm) * (Real.log x) ^ B2 = (Real.log x) ^ (B2 - lamm) := by
        rw [← Real.rpow_add hlogx0]; ring_nf
      rw [← h1]; ring
    rw [hprod]
    have hA0 : (0 : ℝ) ≤ Clim * C2 := by positivity
    have hB0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) ^ 2 := by positivity
    have hC0 : (0 : ℝ) ≤ (Real.log x) ^ (B2 - lamm) := by positivity
    rw [show Clim * C2 * (Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (B2 - lamm)
        = Clim * C2 * ((Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (B2 - lamm)) from by ring]
    rw [Real.sqrt_mul hA0 ((Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (B2 - lamm)),
      Real.sqrt_mul hB0 ((Real.log x) ^ (B2 - lamm)), Real.sqrt_sq (Nat.cast_nonneg _)]
    have hCsqrt : Real.sqrt ((Real.log x) ^ (B2 - lamm)) = (Real.log x) ^ ((B2 - lamm) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlogx0.le]
      congr 1
      ring
    rw [hCsqrt]
    have hexp : (B2 - lamm) / 2 ≤ -lam := by
      rw [hlammdef]
      ring_nf
      linarith
    have hgoal : (Real.log x) ^ ((B2 - lamm) / 2) ≤ (Real.log x) ^ (-lam) :=
      Real.rpow_le_rpow_of_exponent_le hlogx1 hexp
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hgoal (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)) (le_of_eq ?_)
    ring
  have hterm2 : Cg * (Submission.Aseq x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 5
        * (Real.log ((L : ℝ) + 2)) ^ 32 / (L : ℝ)
      ≤ Cg * (2 : ℝ) ^ (37 : ℕ) * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)) := by
    have hlog2 : Real.log ((x : ℝ) + 2) ≤ 2 * Real.log x := by
      have h13 : Real.log ((x : ℝ) + 2) ≤ Real.log (2 * (x : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      rw [Real.log_mul (by norm_num) hx0.ne'] at h13
      linarith [Real.log_two_lt_d9]
    have hlogL : Real.log ((L : ℝ) + 2) ≤ 2 * Real.log x := by
      have h14 : (L : ℝ) + 2 ≤ (x : ℝ) + 2 := by
        have h15 : (L : ℝ) ≤ (t : ℝ) :=
          le_trans (le_of_lt (by exact_mod_cast hLt)) (Nat.cast_le.mpr (Nat.sqrt_le_self t))
        have h16 : (t : ℝ) ≤ (x : ℝ) := by exact_mod_cast htx
        linarith
      exact le_trans (Real.log_le_log (by positivity) h14) hlog2
    have hL2 : (0 : ℝ) ≤ Real.log ((L : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hx2 : (0 : ℝ) ≤ Real.log ((x : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hxl : (0 : ℝ) ≤ 2 * Real.log x := by linarith
    have h5b : (Real.log ((x : ℝ) + 2)) ^ 5 ≤ (2 * Real.log x) ^ 5 :=
      pow_le_pow_left₀ hx2 hlog2 5
    have h32b : (Real.log ((L : ℝ) + 2)) ^ 32 ≤ (2 * Real.log x) ^ 32 :=
      pow_le_pow_left₀ hL2 hlogL 32
    have hprod : (Real.log ((x : ℝ) + 2)) ^ 5 * (Real.log ((L : ℝ) + 2)) ^ 32
        ≤ (2 * Real.log x) ^ 37 :=
      le_trans (mul_le_mul h5b h32b (pow_nonneg hL2 32) (pow_nonneg hxl 5))
        (le_of_eq (by rw [← pow_add]))
    have h2nn : (0 : ℝ) ≤ (2 * Real.log x) ^ 37 := pow_nonneg hxl 37
    have h2pow : (2 * Real.log x) ^ 37 = (2 : ℝ) ^ 37 * (Real.log x) ^ 37 := by rw [mul_pow]
    have hClog : (0 : ℝ) ≤ Cg * (Submission.Aseq x : ℝ) := by positivity
    have hLinv : (1 : ℝ) / (L : ℝ) ≤ (Real.log x) ^ (-(4 * lam + 100)) := by
      have h1 : (Real.log x) ^ (4 * lam + 100) ≤ (L : ℝ) :=
        le_trans (Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith [hB2, hcomp])) hLbig
      have h2 : (0 : ℝ) < (Real.log x) ^ (4 * lam + 100) := Real.rpow_pos_of_pos hlogx0 _
      rw [one_div, Real.rpow_neg hlogx0.le]
      exact (inv_le_inv₀ hL0 h2).mpr h1
    have hLpos' : (0 : ℝ) ≤ 1 / (L : ℝ) := by positivity
    have hstep1 : Cg * (Submission.Aseq x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 5
          * (Real.log ((L : ℝ) + 2)) ^ 32 / (L : ℝ)
        = Cg * (Submission.Aseq x : ℝ)
          * ((Real.log ((x : ℝ) + 2)) ^ 5 * (Real.log ((L : ℝ) + 2)) ^ 32) * (1 / (L : ℝ)) := by
      rw [div_eq_mul_one_div]; ring
    have hstep2 : Cg * (Submission.Aseq x : ℝ)
          * ((Real.log ((x : ℝ) + 2)) ^ 5 * (Real.log ((L : ℝ) + 2)) ^ 32) * (1 / (L : ℝ))
        ≤ Cg * (Submission.Aseq x : ℝ)
          * ((2 * Real.log x) ^ 37 * (Real.log x) ^ (-(4 * lam + 100))) := by
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left
        (mul_le_mul hprod hLinv hLpos' h2nn) hClog)
      ring
    have hstep3 : Cg * (Submission.Aseq x : ℝ)
          * ((2 * Real.log x) ^ 37 * (Real.log x) ^ (-(4 * lam + 100)))
        = Cg * (2 : ℝ) ^ 37 * (Submission.Aseq x : ℝ)
          * ((Real.log x) ^ (37 : ℕ) * (Real.log x) ^ (-(4 * lam + 100))) := by
      rw [h2pow]; ring
    have h37 : (Real.log x) ^ (37 : ℕ) * (Real.log x) ^ (-(4 * lam + 100))
        ≤ (Real.log x) ^ (-lam) := by
      rw [← Real.rpow_natCast (Real.log x) 37, ← Real.rpow_add hlogx0]
      refine Real.rpow_le_rpow_of_exponent_le hlogx1 ?_
      have hc := hcomp
      push_cast
      linarith [hB2, hc]
    have h17 : (0 : ℝ) ≤ Cg * (2 : ℝ) ^ 37 := by positivity
    have h17b : (0 : ℝ) ≤ Cg * (2 : ℝ) ^ 37 * (Submission.Aseq x : ℝ) := by positivity
    have hstep4 : Cg * (2 : ℝ) ^ 37 * (Submission.Aseq x : ℝ)
          * ((Real.log x) ^ (37 : ℕ) * (Real.log x) ^ (-(4 * lam + 100)))
        ≤ Cg * (2 : ℝ) ^ 37 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) :=
      mul_le_mul_of_nonneg_left h37 h17b
    have hstep5 : Cg * (2 : ℝ) ^ 37 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)
        = Cg * (2 : ℝ) ^ (37 : ℕ) * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)) := by ring
    exact le_trans (le_of_eq hstep1) (le_trans hstep2 (le_trans (le_of_eq hstep3)
      (le_trans hstep4 (le_of_eq hstep5))))
  refine le_trans hstep ?_
  refine le_trans (add_le_add hterm1 hterm2) ?_
  have hA0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
  have h20 : (0 : ℝ) ≤ (Real.log x) ^ (-lam) := by positivity
  have hQ : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := mul_nonneg hA0 h20
  have h21 : (0 : ℝ) ≤ Real.sqrt (Clim * C2) := Real.sqrt_nonneg _
  have h22 : (0 : ℝ) ≤ Cg * (2 : ℝ) ^ (37 : ℕ) := by positivity
  nlinarith [hQ, h21, h22]

end

end Submission.ASP
