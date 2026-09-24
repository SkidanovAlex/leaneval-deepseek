import Mathlib
import Submission.Chen.SwitchDefs
import Submission.Commons.NumberTheory.Chen.exists_three_primes_of_medium_mult_le_one

open Finset
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Submission

open Commons.NumberTheory.Chen
open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1600000

/-- local notation for the sifted indicator `ChenEight.Id`. -/
abbrev II (m M : ℕ) : ℝ := ChenEight.Id m M

/-! ## Elementary numerical and finiteness lemmas -/

lemma pow_length_le_prod {c : ℕ} : ∀ l : List ℕ, (∀ p ∈ l, c ≤ p) → c ^ l.length ≤ l.prod
  | [], _ => le_of_eq (by simp)
  | p :: l, h => by
      have h1 : c ^ l.length ≤ l.prod :=
        pow_length_le_prod l (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have h2 : c ≤ p := h p List.mem_cons_self
      calc c ^ (p :: l).length = c ^ l.length * c := by rw [List.length_cons, pow_succ]
        _ ≤ l.prod * p := Nat.mul_le_mul h1 h2
        _ = (p :: l).prod := by rw [List.prod_cons]; ring

/-- Every prime factor of `n` is at least `n.minFac`, so `n ≥ n.minFac ^ Ω n`. -/
lemma minFac_pow_cardFactors_le {n : ℕ} (hn : n ≠ 0) :
    n.minFac ^ ArithmeticFunction.cardFactors n ≤ n := by
  rw [ArithmeticFunction.cardFactors_apply]
  conv_rhs => rw [← Nat.prod_primeFactorsList hn]
  exact pow_length_le_prod _ (fun p hp => by
    obtain ⟨hpp, hpd⟩ := (Nat.mem_primeFactorsList hn).mp hp
    exact Nat.minFac_le_of_dvd hpp.two_le hpd)

lemma cardFactors_four : ArithmeticFunction.cardFactors 4 = 2 := by
  have h : (4:ℕ) = 2 ^ 2 := by norm_num
  rw [h, ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two]

/-! ## `Id`, `goodSum` and the rough shifted-prime set -/

lemma id_eq_zero_or_one (m M : ℕ) : II m M = 0 ∨ II m M = 1 := by
  unfold II ChenEight.Id; split <;> simp

lemma mul_id_eq_ite (f : ℝ) (m M : ℕ) : f * II m M = if II m M = 1 then f else 0 := by
  rcases id_eq_zero_or_one m M with h | h <;> simp [h]

lemma goodSum_eq_s0Set_sum (x M : ℕ) :
    goodSum x M = (s0Set x M).sum (fun p => Real.log (p : ℝ)) := by
  unfold goodSum s0Set
  conv_rhs => rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact mul_id_eq_ite (Real.log (p : ℝ)) (p + 2) M

lemma mem_s0Set {x M p : ℕ} :
    p ∈ s0Set x M ↔ p < x + 1 ∧ p.Prime ∧ II (p + 2) M = 1 := by
  unfold s0Set
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

lemma log_nonneg_of_mem_s0Set {x M p : ℕ} (hp : p ∈ s0Set x M) : 0 ≤ Real.log (p : ℝ) := by
  have hp2 : 2 ≤ p := (mem_s0Set.mp hp).2.1.two_le
  exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))

/-! ## The window count `rhoStar` -/

lemma rhoStar_nonneg (n M Y : ℕ) : 0 ≤ rhoStar n M Y := by
  unfold rhoStar
  refine Finset.sum_nonneg (fun q _ => ?_)
  by_cases h : q ∣ n <;> simp [h]

lemma rhoStar_eq_card (n M Y : ℕ) :
    rhoStar n M Y = (((winPrimes M Y).filter (fun q => q ∣ n)).card : ℝ) := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  unfold rhoStar
  exact Finset.sum_congr rfl (fun q _ => by by_cases h : q ∣ n <;> simp [h])

lemma rhoStar_pos_of_dvd {n M Y q : ℕ} (hq : q ∈ winPrimes M Y) (hd : q ∣ n) :
    1 ≤ rhoStar n M Y := by
  rw [rhoStar_eq_card]
  have hmem : q ∈ (winPrimes M Y).filter (fun q => q ∣ n) := Finset.mem_filter.mpr ⟨hq, hd⟩
  have hcard : 1 ≤ ((winPrimes M Y).filter (fun q => q ∣ n)).card :=
    Finset.card_pos.mpr ⟨q, hmem⟩
  exact_mod_cast hcard

lemma mem_winPrimes {M Y q : ℕ} :
    q ∈ winPrimes M Y ↔ q.Prime ∧ 3 ≤ q ∧ M ≤ q ∧ q < Y := by
  unfold winPrimes oddLt
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨h.1.2.1, h.1.2.2, h.2, h.1.1⟩,
         fun h => ⟨⟨h.2.2.2, h.1, h.2.1⟩, h.2.2.1⟩⟩

lemma mem_oddLt {M q : ℕ} : q ∈ oddLt M ↔ q.Prime ∧ 3 ≤ q ∧ q < M := by
  unfold oddLt
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨h.2.1, h.2.2, h.1⟩, fun h => ⟨h.2.2, h.1, h.2.1⟩⟩

/-- A prime `p` whose shift is `M`-rough and has `Ω (p+2) ≥ 3` has a prime factor in the
window `[M, Y)`, provided `x + 2 < Y ^ 3`. -/
lemma one_le_rhoStar_of_bad {x M Y p : ℕ} (hY : x + 2 < Y ^ 3)
    (hp : p ∈ s0Set x M) (hΩ : 3 ≤ ArithmeticFunction.cardFactors (p + 2)) :
    1 ≤ rhoStar (p + 2) M Y := by
  obtain ⟨hpx, hpp, hid⟩ := mem_s0Set.mp hp
  have hp2ne : p + 2 ≠ 0 := by omega
  have hp2ne1 : p + 2 ≠ 1 := by omega
  set q := (p + 2).minFac with hqdef
  have hqprime : q.Prime := Nat.minFac_prime hp2ne1
  have hqdvd : q ∣ p + 2 := Nat.minFac_dvd (p + 2)
  have hpne2 : p ≠ 2 := by
    intro hp2
    subst hp2
    rw [cardFactors_four] at hΩ
    omega
  have hpmod : p % 2 = 1 := by
    rcases hpp.eq_two_or_odd with h | h
    · exact absurd h hpne2
    · exact h
  have hp2mod : (p + 2) % 2 = 1 := by omega
  have hqmod : q % 2 = 1 := by
    by_contra h
    have h0 : q % 2 = 0 := by omega
    have h2dvd : 2 ∣ q := Nat.dvd_of_mod_eq_zero h0
    have : 2 ∣ p + 2 := dvd_trans h2dvd hqdvd
    omega
  have hq3 : 3 ≤ q := by
    have h2 : 2 ≤ q := hqprime.two_le
    omega
  have hqM : M ≤ q := by
    by_contra hcon
    push_neg at hcon
    have hmemodd : q ∈ oddLt M := mem_oddLt.mpr ⟨hqprime, hq3, hcon⟩
    have hdiv : q ∣ oddPrimLt M := by
      rw [oddPrimLt_eq_prod_oddLt]
      exact Finset.dvd_prod_of_mem (s := oddLt M) (f := fun q => q) hmemodd
    have hcop : (p + 2).Coprime (oddPrimLt M) := by
      by_contra hc
      unfold II ChenEight.Id at hid
      rw [if_neg hc] at hid
      exact absurd hid (by norm_num)
    exact absurd hcop (Nat.not_coprime_of_dvd_of_dvd hqprime.one_lt hqdvd hdiv)
  have hqY : q < Y := by
    have hpow : q ^ ArithmeticFunction.cardFactors (p + 2) ≤ p + 2 :=
      minFac_pow_cardFactors_le hp2ne
    have h3 : q ^ 3 ≤ q ^ ArithmeticFunction.cardFactors (p + 2) :=
      Nat.pow_le_pow_right (by omega) hΩ
    have hlt : q ^ 3 < Y ^ 3 := by
      calc q ^ 3 ≤ q ^ ArithmeticFunction.cardFactors (p + 2) := h3
        _ ≤ p + 2 := hpow
        _ < Y ^ 3 := by omega
    exact (Nat.pow_lt_pow_iff_left (by omega : (3:ℕ) ≠ 0)).mp hlt
  exact rhoStar_pos_of_dvd (mem_winPrimes.mpr ⟨hqprime, hq3, hqM, hqY⟩) hqdvd


/-! ## The structural dichotomy for bad shifts -/

lemma pow_factorization_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p ^ (n.factorization p) ∣ n := by
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) hn, Finsupp.le_def]
  intro q
  rw [Nat.factorization_pow, hp.factorization]
  by_cases hq : p = q
  · subst hq; simp
  · have h1 : (Finsupp.single p 1 : ℕ →₀ ℕ) q = 0 := Finsupp.single_eq_of_ne (Ne.symm hq)
    rw [Finsupp.smul_apply, h1, smul_zero]
    exact Nat.zero_le _

lemma Icc_filter_prime_eq_winPrimes {M Y : ℕ} (hM : 3 ≤ M) :
    ((Finset.Icc M (Y - 1)).filter (fun q => q.Prime)) = winPrimes M Y := by
  ext q
  unfold winPrimes oddLt
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by omega, h3, by omega⟩, h1⟩
  · rintro ⟨⟨h1, h3, h4⟩, h2⟩
    exact ⟨⟨h2, by omega⟩, h3⟩

/-- Every prime factor of an `M`-rough shift with `Ω ≥ 3` is at least `M`. -/
lemma primeFactors_ge_of_rough {x M p r : ℕ} (hΩ : 3 ≤ ArithmeticFunction.cardFactors (p + 2))
    (hp : p ∈ s0Set x M) (hr : r ∈ (p + 2).primeFactors) : M ≤ r := by
  obtain ⟨hpx, hpp, hid⟩ := mem_s0Set.mp hp
  obtain ⟨hrprime, hrdvd, hp2ne⟩ := Nat.mem_primeFactors.mp hr
  by_contra hcon
  push_neg at hcon
  have hrne2 : r ≠ 2 := by
    intro hr2
    subst hr2
    have h2dvd : (2:ℕ) ∣ p + 2 := hrdvd
    have hpe : (2:ℕ) ∣ p := by omega
    rcases (Nat.dvd_prime hpp).mp hpe with h | h
    · exact absurd h (by norm_num)
    · rw [← h] at hΩ
      rw [cardFactors_four] at hΩ
      omega
  have hr3 : 3 ≤ r := by have := hrprime.two_le; omega
  have hmemodd : r ∈ oddLt M := mem_oddLt.mpr ⟨hrprime, hr3, hcon⟩
  have hdiv : r ∣ oddPrimLt M := by
    rw [oddPrimLt_eq_prod_oddLt]
    exact Finset.dvd_prod_of_mem (s := oddLt M) (f := fun q => q) hmemodd
  have hcop : (p + 2).Coprime (oddPrimLt M) := by
    by_contra hc
    unfold II ChenEight.Id at hid
    rw [if_neg hc] at hid
    exact absurd hid (by norm_num)
  exact absurd hcop (Nat.not_coprime_of_dvd_of_dvd hrprime.one_lt hrdvd hdiv)

/-- **The structural dichotomy.**  A prime `p` with `M`-rough shift, `Ω (p+2) ≥ 3`, whose
shift has exactly one prime factor in the window `[M,Y)`, is either a `q²`-divisible case or
a `B`-term case (`p + 2` is a product of three primes, the first in the window). -/
lemma bad_structure {x M Y p : ℕ} (hM : 3 ≤ M) (hY : x + 2 < Y ^ 3)
    (hp : p ∈ s0Set x M) (hΩ : 3 ≤ ArithmeticFunction.cardFactors (p + 2))
    (hrho : rhoStar (p + 2) M Y = 1) :
    (∃ q : ℕ, q.Prime ∧ M ≤ q ∧ q < Y ∧ q ^ 2 ∣ p + 2) ∨
    (∃ q q₂ q₃ : ℕ, q.Prime ∧ q₂.Prime ∧ q₃.Prime ∧ M ≤ q ∧ q < Y ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧
      p + 2 = q * q₂ * q₃) := by
  obtain ⟨hpx, hpp, hid⟩ := mem_s0Set.mp hp
  have hp2ne : p + 2 ≠ 0 := by omega
  have hcard : ((winPrimes M Y).filter (fun q => q ∣ p + 2)).card = 1 := by
    have hthis := hrho
    rw [rhoStar_eq_card] at hthis
    exact_mod_cast hthis
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
  have hqmem : q ∈ (winPrimes M Y).filter (fun q => q ∣ p + 2) := by rw [hq]; simp
  obtain ⟨hqW, hqdvd⟩ := Finset.mem_filter.mp hqmem
  obtain ⟨hqprime, hq3, hqM, hqY⟩ := mem_winPrimes.mp hqW
  by_cases hsq : q ^ 2 ∣ p + 2
  · exact Or.inl ⟨q, hqprime, hqM, hqY, hsq⟩
  refine Or.inr ?_
  -- the medium multiplicity sum is exactly `1`
  have hfac_q : (p + 2).factorization q = 1 := by
    have h1 : 1 ≤ (p + 2).factorization q :=
      (hqprime.dvd_iff_one_le_factorization hp2ne).mp hqdvd
    have h2 : ¬ (2 ≤ (p + 2).factorization q) := by
      intro hcon
      have hpow : q ^ ((p + 2).factorization q) ∣ p + 2 := pow_factorization_dvd hqprime hp2ne
      have hqq : q ^ 2 ∣ q ^ ((p + 2).factorization q) :=
        pow_dvd_pow _ hcon
      exact hsq (dvd_trans hqq hpow)
    omega
  have hmed : ((Finset.Icc M (Y - 1)).filter (fun q => q.Prime)).sum
      (fun r => (p + 2).factorization r) = 1 := by
    rw [Icc_filter_prime_eq_winPrimes hM]
    have hsplit : ∀ r ∈ winPrimes M Y, r ≠ q → (p + 2).factorization r = 0 := by
      intro r hr hrne
      have hnotmem : r ∉ (winPrimes M Y).filter (fun r => r ∣ p + 2) := by
        rw [hq]; simp [hrne]
      have hnd : ¬ r ∣ p + 2 := fun hd => hnotmem (Finset.mem_filter.mpr ⟨hr, hd⟩)
      exact Nat.factorization_eq_zero_of_not_dvd hnd
    rw [Finset.sum_eq_single q (fun r hr hrne => hsplit r hr hrne) (fun h => absurd hqW h)]
    exact hfac_q
  obtain ⟨q', p₂, p₃, hq'prime, hp₂, hp₃, hz, hy, hy₂, hy₃, heq⟩ :=
    Commons.NumberTheory.Chen.exists_three_primes_of_medium_mult_le_one
      (n := p + 2) (z := M) (y := Y) hΩ
      (fun r hr => primeFactors_ge_of_rough hΩ hp hr)
      (le_of_eq hmed) (by omega)
  exact ⟨q', p₂, p₃, hq'prime, hp₂, hp₃, hz, hy, hy₂, hy₃, heq⟩


/-! ## The switch -/

/-- `p + 2` is a product of three primes, the smallest in the window. -/
def IsBT (M Y p : ℕ) : Prop :=
  ∃ q q₂ q₃ : ℕ, q.Prime ∧ q₂.Prime ∧ q₃.Prime ∧ M ≤ q ∧ q < Y ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧
    p + 2 = q * q₂ * q₃

/-- `p + 2` is divisible by the square of a window prime. -/
def IsSQ (M Y p : ℕ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ M ≤ q ∧ q < Y ∧ q ^ 2 ∣ p + 2

lemma bTermMass_eq (x M Y : ℕ) :
    bTermMass x M Y = ((s0Set x M).filter (IsBT M Y)).sum (fun p => Real.log (p : ℝ)) := rfl

lemma sqMass_eq (x M Y : ℕ) :
    sqMass x M Y = ((s0Set x M).filter (IsSQ M Y)).sum (fun p => Real.log (p : ℝ)) := rfl

/-- `Σ_{p ∈ s0Set} log p · ρ*(p) = Σ_{q ∈ W} apMass q`. -/
lemma sum_log_mul_rhoStar (x M Y : ℕ) :
    (s0Set x M).sum (fun p => Real.log (p : ℝ) * rhoStar (p + 2) M Y)
      = ∑ q ∈ winPrimes M Y, apMass x M q := by
  have h1 : ∀ p : ℕ, Real.log (p : ℝ) * rhoStar (p + 2) M Y
      = ∑ q ∈ winPrimes M Y, Real.log (p : ℝ) * (if q ∣ p + 2 then (1:ℝ) else 0) := by
    intro p
    rw [rhoStar, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun p _ => h1 p), Finset.sum_comm]
  unfold apMass
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : q ∣ p + 2 <;> simp [h]

/-- **Chen's switch.**  The θ-mass of the `M`-rough shifted primes is bounded by the good part
plus half of the switched AP sum plus half of the exceptional `B`-term and `q²`-term. -/
theorem goodSum_le_goodMass_add (x M Y : ℕ) (hM : 3 ≤ M) (hY : x + 2 < Y ^ 3) :
    goodSum x M ≤ goodMass x M
      + (1 / 2) * (∑ q ∈ winPrimes M Y, apMass x M q)
      + (1 / 2) * bTermMass x M Y
      + (1 / 2) * sqMass x M Y := by
  rw [goodSum_eq_s0Set_sum]
  have hterm : ∀ p ∈ s0Set x M, Real.log (p : ℝ) ≤
      (if ArithmeticFunction.cardFactors (p + 2) ≤ 2 then Real.log (p : ℝ) else 0)
      + (1 / 2) * (if IsBT M Y p then Real.log (p : ℝ) else 0)
      + (1 / 2) * (if IsSQ M Y p then Real.log (p : ℝ) else 0)
      + (1 / 2) * (Real.log (p : ℝ) * rhoStar (p + 2) M Y) := by
    intro p hp
    have hlog : 0 ≤ Real.log (p : ℝ) := log_nonneg_of_mem_s0Set hp
    have hBT : 0 ≤ (1 / 2) * (if IsBT M Y p then Real.log (p : ℝ) else 0) := by
      by_cases h : IsBT M Y p <;> simp [h] <;> linarith
    have hSQ : 0 ≤ (1 / 2) * (if IsSQ M Y p then Real.log (p : ℝ) else 0) := by
      by_cases h : IsSQ M Y p <;> simp [h] <;> linarith
    by_cases hgood : ArithmeticFunction.cardFactors (p + 2) ≤ 2
    · rw [if_pos hgood]
      have h5 : 0 ≤ (1 / 2) * (Real.log (p : ℝ) * rhoStar (p + 2) M Y) :=
        mul_nonneg (by norm_num) (mul_nonneg hlog (rhoStar_nonneg _ _ _))
      linarith
    · rw [if_neg hgood]
      have hΩ : 3 ≤ ArithmeticFunction.cardFactors (p + 2) := by omega
      have hpos := one_le_rhoStar_of_bad hY hp hΩ
      by_cases hone : rhoStar (p + 2) M Y = 1
      · rcases bad_structure hM hY hp hΩ hone with hsq | hbt
        · obtain ⟨q, hq1, hq2, hq3, hq4⟩ := hsq
          rw [if_pos (show IsSQ M Y p from ⟨q, hq1, hq2, hq3, hq4⟩), hone]
          linarith
        · obtain ⟨q, q2, q3, hq1, hq2, hq3, hq4, hq5, hq6, hq7⟩ := hbt
          rw [if_pos (show IsBT M Y p from ⟨q, q2, q3, hq1, hq2, hq3, hq4, hq5, hq6, hq7⟩), hone]
          linarith
      · have hcard1 : 1 ≤ ((winPrimes M Y).filter (fun q => q ∣ p + 2)).card := by
          have hh := hpos
          rw [rhoStar_eq_card] at hh
          exact_mod_cast hh
        have hcardne : ((winPrimes M Y).filter (fun q => q ∣ p + 2)).card ≠ 1 := by
          intro hc
          exact hone (by rw [rhoStar_eq_card, hc]; norm_num)
        have hcard2 : 2 ≤ ((winPrimes M Y).filter (fun q => q ∣ p + 2)).card := by omega
        have h2 : 2 ≤ rhoStar (p + 2) M Y := by
          rw [rhoStar_eq_card]; exact_mod_cast hcard2
        have hmul : 0 ≤ Real.log (p : ℝ) * (rhoStar (p + 2) M Y - 2) :=
          mul_nonneg hlog (by linarith)
        nlinarith [hBT, hSQ, hmul]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have e1 : (s0Set x M).sum (fun p => if ArithmeticFunction.cardFactors (p + 2) ≤ 2
      then Real.log (p : ℝ) else 0) = goodMass x M := by
    unfold goodMass
    rw [Finset.sum_filter]
  have e2 : (s0Set x M).sum (fun p => (1 / 2) * (if IsBT M Y p then Real.log (p : ℝ) else 0))
      = (1 / 2) * bTermMass x M Y := by
    rw [bTermMass_eq, Finset.sum_filter, Finset.mul_sum]
  have e3 : (s0Set x M).sum (fun p => (1 / 2) * (if IsSQ M Y p then Real.log (p : ℝ) else 0))
      = (1 / 2) * sqMass x M Y := by
    rw [sqMass_eq, Finset.sum_filter, Finset.mul_sum]
  have e4 : (s0Set x M).sum (fun p => (1 / 2) * (Real.log (p : ℝ) * rhoStar (p + 2) M Y))
      = (1 / 2) * (∑ q ∈ winPrimes M Y, apMass x M q) := by
    rw [← Finset.mul_sum, ← sum_log_mul_rhoStar]
  rw [e1, e2, e3, e4] at hsum
  linarith


/-! ## Crude bounds for the exceptional terms -/


lemma bTermMass_le_count (x M Y : ℕ) :
    bTermMass x M Y ≤ (bTermCount x M Y : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ) := by
  have hcard : ((((s0Set x M).filter (IsBT M Y)).card : ℝ)) = (bTermCount x M Y : ℝ) := rfl
  rw [bTermMass_eq, ← hcard]
  calc ((s0Set x M).filter (IsBT M Y)).sum (fun p => Real.log (p : ℝ))
      ≤ ((s0Set x M).filter (IsBT M Y)).sum (fun _ => Real.log (((x + 2 : ℕ)) : ℝ)) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hps := Finset.mem_of_mem_filter _ hp
        have hpx : p < x + 1 := (mem_s0Set.mp hps).1
        have hp2 : 2 ≤ p := (mem_s0Set.mp hps).2.1.two_le
        have h1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
        have h2 : (p:ℝ) ≤ ((x+2:ℕ):ℝ) := by
          have : p ≤ x + 2 := by omega
          exact_mod_cast this
        exact Real.log_le_log h1 h2
    _ = ((((s0Set x M).filter (IsBT M Y)).card : ℕ) : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (bTermCount x M Y : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ) := by rw [hcard]

lemma sqMass_le_sqMassAll (x M Y : ℕ) : sqMass x M Y ≤ sqMassAll x M := by
  rw [sqMass_eq]
  unfold sqMassAll
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    obtain ⟨h1, q, hq1, hq2, hq3, hq4⟩ := hp
    exact ⟨h1, ⟨q, hq1, hq2, hq4⟩⟩
  · intro p hp _
    exact log_nonneg_of_mem_s0Set (Finset.mem_of_mem_filter _ hp)

lemma goodMass_le_chenCount (x M : ℕ) :
    goodMass x M ≤ (chenCount x : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ) := by
  unfold goodMass
  have hsub : (s0Set x M).filter (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 2)
      ⊆ (Finset.range (x + 1)).filter (fun p => p ∈ chenSetOmega) := by
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    obtain ⟨hps, hcard⟩ := hp
    obtain ⟨hpx, hpr, -⟩ := mem_s0Set.mp hps
    exact ⟨Finset.mem_range.mpr hpx, hpr, hcard⟩
  have hcard : ((s0Set x M).filter (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 2)).card
      ≤ chenCount x := by
    unfold chenCount
    exact Finset.card_le_card hsub
  have hcast : ((((s0Set x M).filter (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 2)).card : ℕ) : ℝ)
      ≤ (chenCount x : ℝ) := by exact_mod_cast hcard
  calc ((s0Set x M).filter (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 2)).sum
        (fun p => Real.log (p : ℝ))
      ≤ ((s0Set x M).filter (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 2)).sum
        (fun _ => Real.log (((x + 2 : ℕ)) : ℝ)) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hps := Finset.mem_of_mem_filter _ hp
        have hpx : p < x + 1 := (mem_s0Set.mp hps).1
        have hp2 : 2 ≤ p := (mem_s0Set.mp hps).2.1.two_le
        have h1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
        have h2 : (p:ℝ) ≤ ((x+2:ℕ):ℝ) := by
          have : p ≤ x + 2 := by omega
          exact_mod_cast this
        exact Real.log_le_log h1 h2
    _ = ((((s0Set x M).filter (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 2)).card : ℕ) : ℝ)
        * Real.log (((x + 2 : ℕ)) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (chenCount x : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ) :=
        mul_le_mul_of_nonneg_right hcast (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x + 2)))


/-! ## The assembly: Chen's rate estimate from the three analytic inputs -/


/-! ## The assembly: Chen's rate estimate from the three analytic inputs -/


/-! ## The assembly: Chen's rate estimate from the three analytic inputs -/

/-- **The reduction.**  Given
* `h1` the sharp lower bound for the `M`-rough shifted-prime mass,
* `h2` the switched AP sum bound with constant `A`,
* `h3` the `B`-term count bound with constant `B` (in division-free form),
* `hV` a lower bound `D·x ≤ x·VsieveOdd M · log x` (Mertens, division-free form),
* `hsq` the crude bound for the `q²`-exceptional mass (division-free form),
* `hlog2` the harmless `log (x+2) ≤ (1+δ)·log x`,
and the numerical condition
`hfin : 0 < ((1-ε) - A/2)·D - (1+δ)·B/2 - D/64`,
the count of Chen primes is at least the corresponding positive multiple of `x/log²x`. -/
theorem chenCount_lower_of_inputs {x M Y : ℕ} {ε A B D E δ : ℝ}
    (hM : 3 ≤ M) (hY : x + 2 < Y ^ 3)
    (hD0 : 0 < D) (hB0 : 0 ≤ B) (hδ : 0 ≤ δ) (hE0 : 0 ≤ E)
    (hlog1 : 1 ≤ Real.log (x : ℝ))
    (hlog2 : Real.log (((x + 2 : ℕ)) : ℝ) ≤ (1 + δ) * Real.log (x : ℝ))
    (hV : D * (x : ℝ) ≤ (x : ℝ) * VsieveOdd M * Real.log (x : ℝ))
    (hsq : sqMassAll x M * Real.log (x : ℝ) ≤ E * (x : ℝ))
    (h1 : (1 - ε) * (x : ℝ) * VsieveOdd M ≤ ChenEight.goodSum x M)
    (h2 : (∑ q ∈ winPrimes M Y, apMass x M q) ≤ A * (x : ℝ) * VsieveOdd M)
    (h3 : (bTermCount x M Y : ℝ) * Real.log (x : ℝ) * Real.log (x : ℝ) ≤ B * (x : ℝ))
    (hfin : 0 < ((1 - ε) - A / 2) * D - (1 + δ) * B / 2 - E / 2) :
    ((((1 - ε) - A / 2) * D - (1 + δ) * B / 2 - E / 2) / (1 + δ)) * (x : ℝ)
        / (Real.log (x : ℝ)) ^ 2 ≤ (chenCount x : ℝ) := by
  have hlogpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hsqpos : 0 < Real.log (x : ℝ) ^ 2 := by positivity
  have h1δ : 0 < 1 + δ := by linarith
  have hswitch := goodSum_le_goodMass_add x M Y hM hY
  have hgm := goodMass_le_chenCount x M
  have hgm0 : 0 ≤ goodMass x M := by
    unfold goodMass
    refine Finset.sum_nonneg (fun p hp => log_nonneg_of_mem_s0Set (Finset.mem_of_mem_filter _ hp))
  have hcx : 0 ≤ (chenCount x : ℝ) := Nat.cast_nonneg _
  have hcoef : 0 ≤ (1 - ε) - A / 2 := by
    by_contra hc
    push_neg at hc
    have h1' : ((1 - ε) - A / 2) * D ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc.le hD0.le
    have h2' : 0 ≤ (1 + δ) * B / 2 := by positivity
    have h3' : 0 ≤ E / 2 := by linarith
    linarith [hfin]
  -- (1) the AP part
  have hAsum : (1 / 2) * (∑ q ∈ winPrimes M Y, apMass x M q)
      ≤ (A / 2) * ((x : ℝ) * VsieveOdd M) := by linarith [h2]
  -- (2) the B-term part
  have hcnt : (bTermCount x M Y : ℝ) ≤ B * (x : ℝ) / Real.log (x : ℝ) ^ 2 := by
    rw [le_div_iff₀ hsqpos]
    have heq : Real.log (x : ℝ) ^ 2 = Real.log (x : ℝ) * Real.log (x : ℝ) := by ring
    rw [heq]
    simpa only [mul_assoc] using h3
  have hbterm : (1 / 2) * bTermMass x M Y ≤ ((1 + δ) * B / 2) * (x : ℝ) / Real.log (x : ℝ) := by
    have hbm := bTermMass_le_count x M Y
    have hcntnn : (0:ℝ) ≤ (bTermCount x M Y : ℝ) := Nat.cast_nonneg _
    have hlog2nn : (0:ℝ) ≤ Real.log (((x + 2 : ℕ)) : ℝ) := by
      refine Real.log_nonneg ?_
      exact_mod_cast (by omega : 1 ≤ x + 2)
    have h2' : bTermMass x M Y
        ≤ (B * (x : ℝ) / Real.log (x : ℝ) ^ 2) * ((1 + δ) * Real.log (x : ℝ)) := by
      have e1 : bTermMass x M Y ≤ (bTermCount x M Y : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ) := hbm
      have e2 : (bTermCount x M Y : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ)
          ≤ (B * (x : ℝ) / Real.log (x : ℝ) ^ 2) * ((1 + δ) * Real.log (x : ℝ)) := by
        have hle1 : Real.log (((x + 2 : ℕ)) : ℝ) ≤ (1 + δ) * Real.log (x : ℝ) := hlog2
        have hle2 : (bTermCount x M Y : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ)
            ≤ (B * (x : ℝ) / Real.log (x : ℝ) ^ 2) * Real.log (((x + 2 : ℕ)) : ℝ) :=
          mul_le_mul_of_nonneg_right hcnt hlog2nn
        have hle3 : (B * (x : ℝ) / Real.log (x : ℝ) ^ 2) * Real.log (((x + 2 : ℕ)) : ℝ)
            ≤ (B * (x : ℝ) / Real.log (x : ℝ) ^ 2) * ((1 + δ) * Real.log (x : ℝ)) :=
          mul_le_mul_of_nonneg_left hle1 (by positivity)
        linarith [hle2, hle3]
      linarith [e1, e2]
    have hval : (1 / 2) * ((B * (x : ℝ) / Real.log (x : ℝ) ^ 2) * ((1 + δ) * Real.log (x : ℝ)))
        = ((1 + δ) * B / 2) * (x : ℝ) / Real.log (x : ℝ) := by
      field_simp
      try ring
    linarith [h2', hval.le, hval.ge]
  -- (3) the `q^2` part
  have hsqpart : (1 / 2) * sqMass x M Y ≤ (E / 2) * (x : ℝ) / Real.log (x : ℝ) := by
    have hsq' : sqMass x M Y * Real.log (x : ℝ) ≤ sqMassAll x M * Real.log (x : ℝ) :=
      mul_le_mul_of_nonneg_right (sqMass_le_sqMassAll x M Y) hlogpos.le
    have h2' : sqMass x M Y * Real.log (x : ℝ) ≤ E * (x : ℝ) := le_trans hsq' hsq
    rw [le_div_iff₀ hlogpos]
    linarith
  -- (4) the Mertens input
  have hV' : D * (x : ℝ) / Real.log (x : ℝ) ≤ (x : ℝ) * VsieveOdd M := by
    rw [div_le_iff₀ hlogpos]
    linarith [hV]
  -- (5) the lower bound on `goodMass`, multiplied through by `log x`
  have expand : (((1 - ε) - A / 2) * ((D * (x : ℝ)) / Real.log (x : ℝ))
      - ((1 + δ) * B / 2) * (x : ℝ) / Real.log (x : ℝ)
      - (E / 2) * (x : ℝ) / Real.log (x : ℝ)) * Real.log (x : ℝ)
      = (((1 - ε) - A / 2) * D - (1 + δ) * B / 2 - E / 2) * (x : ℝ) := by
    field_simp
    try ring
  have hbig : (((1 - ε) - A / 2) * D - (1 + δ) * B / 2 - E / 2) * (x : ℝ)
      ≤ goodMass x M * Real.log (x : ℝ) := by
    have h1' : (1 - ε) * ((x : ℝ) * VsieveOdd M) ≤ ChenEight.goodSum x M := by
      have h := h1; ring_nf at h ⊢; linarith
    have hcoefV : ((1 - ε) - A / 2) * ((D * (x : ℝ)) / Real.log (x : ℝ))
        ≤ ((1 - ε) - A / 2) * ((x : ℝ) * VsieveOdd M) :=
      mul_le_mul_of_nonneg_left hV' hcoef
    have hlow : ((1 - ε) - A / 2) * ((D * (x : ℝ)) / Real.log (x : ℝ))
        - ((1 + δ) * B / 2) * (x : ℝ) / Real.log (x : ℝ)
        - (E / 2) * (x : ℝ) / Real.log (x : ℝ) ≤ goodMass x M := by
      nlinarith [hswitch, hAsum, hbterm, hsqpart, hcoefV, h1', hlogpos]
    have hx := mul_le_mul_of_nonneg_right hlow hlogpos.le
    linarith [hx, expand.le, expand.ge]
  -- (6) convert to a count
  have step1 : (((1 - ε) - A / 2) * D - (1 + δ) * B / 2 - E / 2) * (x : ℝ)
      ≤ (chenCount x : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ) * Real.log (x : ℝ) := by
    have h1' : goodMass x M * Real.log (x : ℝ)
        ≤ ((chenCount x : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ)) * Real.log (x : ℝ) :=
      mul_le_mul_of_nonneg_right hgm hlogpos.le
    linarith [hbig, h1']
  have step2 : (chenCount x : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ) * Real.log (x : ℝ)
      ≤ (chenCount x : ℝ) * ((1 + δ) * Real.log (x : ℝ)) * Real.log (x : ℝ) := by
    have h' : (chenCount x : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ)
        ≤ (chenCount x : ℝ) * ((1 + δ) * Real.log (x : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog2 hcx
    exact mul_le_mul_of_nonneg_right h' hlogpos.le
  rw [div_le_iff₀ hsqpos]
  have hfin2 : (((1 - ε) - A / 2) * D - (1 + δ) * B / 2 - E / 2) * (x : ℝ)
      ≤ (1 + δ) * ((chenCount x : ℝ) * (Real.log (x : ℝ)) ^ 2) := by
    have h := le_trans step1 step2
    nlinarith [h, hlogpos, hcx]
  rw [div_mul_eq_mul_div, div_le_iff₀ h1δ]
  nlinarith [hfin2]

/-- **Eventual form of the reduction.** -/
theorem chen_rate_estimate_of_inputs {ε A B D E δ : ℝ}
    (hD0 : 0 < D) (hB0 : 0 ≤ B) (hδ : 0 ≤ δ) (hE0 : 0 ≤ E)
    (hfin : 0 < ((1 - ε) - A / 2) * D - (1 + δ) * B / 2 - E / 2)
    (hlog : ∀ᶠ x : ℕ in Filter.atTop,
      1 ≤ Real.log (x : ℝ) ∧ Real.log (((x + 2 : ℕ)) : ℝ) ≤ (1 + δ) * Real.log (x : ℝ))
    (hM : ∀ᶠ x : ℕ in Filter.atTop, 3 ≤ chenSiftLimit x)
    (hY : ∀ᶠ x : ℕ in Filter.atTop, x + 2 < (chenWindowTop x) ^ 3)
    (hV : ∀ᶠ x : ℕ in Filter.atTop,
      D * (x : ℝ) ≤ (x : ℝ) * VsieveOdd (chenSiftLimit x) * Real.log (x : ℝ))
    (hsq : ∀ᶠ x : ℕ in Filter.atTop,
      sqMassAll x (chenSiftLimit x) * Real.log (x : ℝ) ≤ E * (x : ℝ))
    (h1 : ∀ᶠ x : ℕ in Filter.atTop,
      (1 - ε) * (x : ℝ) * VsieveOdd (chenSiftLimit x) ≤ ChenEight.goodSum x (chenSiftLimit x))
    (h2 : ∀ᶠ x : ℕ in Filter.atTop,
      (∑ q ∈ winPrimes (chenSiftLimit x) (chenWindowTop x), apMass x (chenSiftLimit x) q)
        ≤ A * (x : ℝ) * VsieveOdd (chenSiftLimit x))
    (h3 : ∀ᶠ x : ℕ in Filter.atTop,
      (bTermCount x (chenSiftLimit x) (chenWindowTop x) : ℝ) * Real.log (x : ℝ)
        * Real.log (x : ℝ) ≤ B * (x : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 ≤ (chenCount x : ℝ) := by
  refine ⟨(((1 - ε) - A / 2) * D - (1 + δ) * B / 2 - E / 2) / (1 + δ), by positivity, ?_⟩
  filter_upwards [hlog, hM, hY, hV, hsq, h1, h2, h3] with x hlog' hM' hY' hV' hsq' h1' h2' h3'
  exact chenCount_lower_of_inputs hM' hY' hD0 hB0 hδ hE0 hlog'.1 hlog'.2 hV' hsq' h1' h2' h3' hfin



/-! ## Elementary facts about the two thresholds -/

lemma eventually_chenSiftLimit_ge : ∀ᶠ x : ℕ in Filter.atTop, 3 ≤ chenSiftLimit x := by
  have h1 : Filter.Tendsto (fun x : ℕ => Real.rpow (x : ℝ) (1 / 8)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/8)).comp tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun y : ℝ => cut y 1) Filter.atTop Filter.atTop := by
    have h3 : Filter.Tendsto (fun y : ℝ => y ^ sieveAlpha) Filter.atTop Filter.atTop :=
      tendsto_rpow_atTop (by norm_num [sieveAlpha] : (0:ℝ) < sieveAlpha)
    simpa only [cut_one] using h3
  have h4 : ∀ᶠ x : ℕ in Filter.atTop, (3:ℝ) ≤ cut (Real.rpow (x : ℝ) (1/8)) 1 :=
    (h2.comp h1).eventually (Filter.eventually_ge_atTop 3)
  filter_upwards [h4] with x hx
  unfold chenSiftLimit
  have hfl : (3:ℕ) ≤ ⌊cut (Real.rpow (x : ℝ) (1/8)) 1⌋₊ := Nat.le_floor hx
  omega

/-- `x + 2 < (chenWindowTop x) ^ 3` for every `x`. -/
lemma window_cube (x : ℕ) : x + 2 < (chenWindowTop x) ^ 3 := by
  set k : ℕ := ⌊Real.rpow (x : ℝ) (1/3)⌋₊ with hk
  have hkY : chenWindowTop x = k + 2 := by unfold chenWindowTop; rw [hk]
  rw [hkY]
  have hk1 : Real.rpow (x : ℝ) (1/3) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hxpos : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg x
  have h2 : (0:ℝ) ≤ Real.rpow (x : ℝ) (1/3) := Real.rpow_nonneg hxpos (1/3)
  have hxr : (Real.rpow (x:ℝ) (1/3)) ^ (3:ℝ) = (x:ℝ) := by
    have hthis := Real.rpow_mul hxpos (1/3) 3
    rw [show (1:ℝ)/3 * 3 = 1 by norm_num, Real.rpow_one] at hthis
    simpa [Real.rpow_natCast] using hthis.symm
  have h3r : ((k:ℝ)+1) ^ (3:ℝ) = ((k:ℝ)+1)^3 := Real.rpow_natCast _ 3
  have hxltR : (x:ℝ) < ((k:ℝ)+1)^3 := by
    have hlt : (Real.rpow (x:ℝ) (1/3)) ^ (3:ℝ) < ((k:ℝ)+1) ^ (3:ℝ) :=
      Real.rpow_lt_rpow h2 hk1 (by norm_num)
    rw [hxr, h3r] at hlt
    exact hlt
  have hxlt : x < (k+1)^3 := by
    have hcast : ((x:ℕ):ℝ) < ((((k+1)^3 : ℕ)):ℝ) := by push_cast; linarith
    exact_mod_cast hcast
  have hexp : (k + 2) ^ 3 = (k + 1) ^ 3 + 3 * (k + 1) ^ 2 + 3 * (k + 1) + 1 := by ring
  omega

lemma eventually_window_cube : ∀ᶠ x : ℕ in Filter.atTop, x + 2 < (chenWindowTop x) ^ 3 :=
  Filter.Eventually.of_forall window_cube


/-- `chenSiftLimit x ≤ ⌊x^{1/8}⌋ + 1` for `x ≥ 1`: the sift limit is below the `x^{1/8}`
threshold used by the (fundamental-lemma type) lower-bound statements. -/
lemma chenSiftLimit_le {x : ℕ} (hx1 : 1 ≤ x) :
    chenSiftLimit x ≤ ⌊Real.rpow (x : ℝ) (1/8)⌋₊ + 1 := by
  unfold chenSiftLimit
  have hx1' : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1
  have hy1 : (1:ℝ) ≤ Real.rpow (x : ℝ) (1/8) := Real.one_le_rpow hx1' (by norm_num)
  have hcut : cut (Real.rpow (x : ℝ) (1/8)) 1 ≤ Real.rpow (x : ℝ) (1/8) := by
    rw [cut_one]
    have h : (Real.rpow (x : ℝ) (1/8)) ^ sieveAlpha ≤ (Real.rpow (x : ℝ) (1/8)) ^ (1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num [sieveAlpha])
    rwa [Real.rpow_one] at h
  have := Nat.floor_mono hcut
  omega


/-- `log (x+2) ≤ (1 + δ)·log x` eventually, for every `δ > 0` (the harmless log-correction used
by the assembly). -/
lemma eventually_log_add_two_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in Filter.atTop,
      Real.log (((x + 2 : ℕ)) : ℝ) ≤ (1 + δ) * Real.log (x : ℝ) := by
  have h1 : ∀ᶠ x : ℕ in Filter.atTop, 2/δ ≤ (x:ℝ) * Real.log (x:ℝ) := by
    have h2 : ∀ᶠ x : ℕ in Filter.atTop, (1:ℝ) ≤ Real.log (x:ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_ge_atTop 1)
    have h3 : ∀ᶠ x : ℕ in Filter.atTop, 2/δ ≤ (x:ℝ) := by
      have h4 : 2/δ ≤ ((⌈2/δ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      filter_upwards [Filter.eventually_ge_atTop (⌈2/δ⌉₊)] with x hx
      exact le_trans h4 (by exact_mod_cast hx)
    filter_upwards [h2, h3] with x h2' h3'
    nlinarith [h2', h3', (by positivity : (0:ℝ) ≤ (x:ℝ))]
  filter_upwards [h1] with x hx
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · subst hx0
    have hc : 2/δ ≤ 0 := by simpa using hx
    have : (0:ℝ) < 2/δ := by positivity
    linarith
  have hx2 : 2 ≤ x := by
    by_contra h
    interval_cases x <;> simp at hx
    · have : (0:ℝ) < 2/δ := by positivity
      linarith
  have hx1 : (1:ℕ) < x := by omega
  have hxpos : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlogpos : 0 < Real.log (x:ℝ) := Real.log_pos (by exact_mod_cast hx1)
  have hsplit : Real.log (((x + 2 : ℕ)) : ℝ)
      = Real.log (x:ℝ) + Real.log (1 + 2/(x:ℝ)) := by
    have harg : (((x+2:ℕ)):ℝ) = (x:ℝ) * (1 + 2/(x:ℝ)) := by
      push_cast
      field_simp
      try ring
    rw [harg, Real.log_mul (by positivity) (by positivity)]
  have h2 : Real.log (1 + 2/(x:ℝ)) ≤ 2/(x:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 2/(x:ℝ) by positivity)
    linarith
  have h3 : 2/(x:ℝ) ≤ δ * Real.log (x:ℝ) := by
    rw [div_le_iff₀ hxpos]
    have := (div_le_iff₀ hδ).mp hx
    nlinarith [this, hlogpos]
  rw [hsplit]
  linarith


/-- **Eventual form of the reduction, with a free sift limit.**  Identical to
`chen_rate_estimate_of_inputs` except that the sift limit is an arbitrary function `M : ℕ → ℕ`
of `x` (the natural choice is `M x ≈ x^{1/10}`, see `Submission/Chen/NOTES.md`), so that the three
analytic inputs can be requested at whatever level is optimal. -/
theorem chen_rate_estimate_of_inputs_gen {ε A B D E δ : ℝ} (M : ℕ → ℕ)
    (hD0 : 0 < D) (hB0 : 0 ≤ B) (hδ : 0 ≤ δ) (hE0 : 0 ≤ E)
    (hfin : 0 < ((1 - ε) - A / 2) * D - (1 + δ) * B / 2 - E / 2)
    (hlog : ∀ᶠ x : ℕ in Filter.atTop,
      1 ≤ Real.log (x : ℝ) ∧ Real.log (((x + 2 : ℕ)) : ℝ) ≤ (1 + δ) * Real.log (x : ℝ))
    (hM : ∀ᶠ x : ℕ in Filter.atTop, 3 ≤ M x)
    (hY : ∀ᶠ x : ℕ in Filter.atTop, x + 2 < (chenWindowTop x) ^ 3)
    (hV : ∀ᶠ x : ℕ in Filter.atTop,
      D * (x : ℝ) ≤ (x : ℝ) * VsieveOdd (M x) * Real.log (x : ℝ))
    (hsq : ∀ᶠ x : ℕ in Filter.atTop,
      sqMassAll x (M x) * Real.log (x : ℝ) ≤ E * (x : ℝ))
    (h1 : ∀ᶠ x : ℕ in Filter.atTop,
      (1 - ε) * (x : ℝ) * VsieveOdd (M x) ≤ ChenEight.goodSum x (M x))
    (h2 : ∀ᶠ x : ℕ in Filter.atTop,
      (∑ q ∈ winPrimes (M x) (chenWindowTop x), apMass x (M x) q)
        ≤ A * (x : ℝ) * VsieveOdd (M x))
    (h3 : ∀ᶠ x : ℕ in Filter.atTop,
      (bTermCount x (M x) (chenWindowTop x) : ℝ) * Real.log (x : ℝ) * Real.log (x : ℝ)
        ≤ B * (x : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 ≤ (chenCount x : ℝ) := by
  refine ⟨(((1 - ε) - A / 2) * D - (1 + δ) * B / 2 - E / 2) / (1 + δ), by positivity, ?_⟩
  filter_upwards [hlog, hM, hY, hV, hsq, h1, h2, h3] with x hlog' hM' hY' hV' hsq' h1' h2' h3'
  exact chenCount_lower_of_inputs hM' hY' hD0 hB0 hδ hE0 hlog'.1 hlog'.2 hV' hsq' h1' h2' h3' hfin


lemma eventually_chenSiftLimitTenth_ge : ∀ᶠ x : ℕ in Filter.atTop, 3 ≤ chenSiftLimitTenth x := by
  have h1 : ∀ᶠ x : ℕ in Filter.atTop, (3:ℝ) ≤ Real.rpow (x : ℝ) (1 / 10) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/10)).comp
      tendsto_natCast_atTop_atTop |>.eventually (Filter.eventually_ge_atTop 3)
  filter_upwards [h1] with x hx
  unfold chenSiftLimitTenth
  have hfl : (3:ℕ) ≤ ⌊Real.rpow (x : ℝ) (1/10)⌋₊ := Nat.le_floor hx
  omega


/-- A larger sift limit sifts out more: `Id · M' = 1 ⟹ Id · M = 1` when `M ≤ M'`. -/
lemma id_eq_one_anti {m M M' : ℕ} (h : M ≤ M') (hid : ChenEight.Id m M' = 1) :
    ChenEight.Id m M = 1 := by
  have hcop : m.Coprime (oddPrimLt M') := by
    by_contra hc
    have h0 : ChenEight.Id m M' = 0 := by
      unfold ChenEight.Id
      rw [if_neg hc]
    rw [h0] at hid
    norm_num at hid
  have hdvd : oddPrimLt M ∣ oddPrimLt M' := by
    rw [oddPrimLt_eq_prod_oddLt, oddPrimLt_eq_prod_oddLt]
    refine Finset.prod_dvd_prod_of_subset (s := oddLt M) (t := oddLt M') (f := fun q => q) ?_
    intro q hq
    simp only [oddLt, Finset.mem_filter, Finset.mem_range] at hq ⊢
    exact ⟨by omega, hq.2⟩
  have hcop' : m.Coprime (oddPrimLt M) := Nat.Coprime.coprime_dvd_right hdvd hcop
  unfold ChenEight.Id
  rw [if_pos hcop']

lemma s0Set_anti {x M M' p : ℕ} (h : M ≤ M') (hp : p ∈ s0Set x M') : p ∈ s0Set x M := by
  unfold s0Set at hp ⊢
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, id_eq_one_anti h hp.2⟩

/-- `sqMassAll` is antitone in the sift limit. -/
lemma sqMassAll_antitone (x M M' : ℕ) (h : M ≤ M') : sqMassAll x M' ≤ sqMassAll x M := by
  unfold sqMassAll
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    obtain ⟨hps, q, hqp, hqM, hqdvd⟩ := hp
    exact ⟨s0Set_anti h hps, q, hqp, le_trans h hqM, hqdvd⟩
  · intro p hp _
    exact log_nonneg_of_mem_s0Set (Finset.mem_filter.mp hp).1

/-- `chenSiftLimit x ≤ chenSiftLimitTenth x` for `x ≥ 1`. -/
lemma chenSiftLimit_le_tenth {x : ℕ} (hx : 1 ≤ x) :
    chenSiftLimit x ≤ chenSiftLimitTenth x := by
  unfold chenSiftLimit chenSiftLimitTenth
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hy : cut (Real.rpow (x : ℝ) (1/8)) 1 ≤ Real.rpow (x : ℝ) (1/10) := by
    rw [cut_one]
    have heq : (Real.rpow (x : ℝ) (1/8)) ^ sieveAlpha
        = Real.rpow (x : ℝ) ((1:ℝ)/8 * sieveAlpha) := by
      have h := Real.rpow_mul (by positivity : (0:ℝ) ≤ (x:ℝ)) ((1:ℝ)/8) sieveAlpha
      exact h.symm
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num [sieveAlpha] : (1:ℝ)/8 * sieveAlpha ≤ 1/10)
  have := Nat.floor_mono hy
  omega

end Submission
