import Mathlib
import Submission.Commons.NumberTheory.Chen.rough_theta_lower_of_bv
import Submission.Commons.NumberTheory.Mertens.primeProduct_oneSubInv_ge_sharp
import Submission.Commons.NumberTheory.Mertens.eulerMascheroni_exp_neg_lower

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Chen

noncomputable section

/-!
# `vsieve_log_lower_sharp`: `Vsieve n · log n ≥ 7/10` for all large `n`

`Vsieve Y = ∏_{3 ≤ p < Y} (1 - 1/(p-1))` is the odd Mertens product of the linear
sieve.  By Mertens' third theorem together with the twin-prime product,

`Vsieve Y · log Y → 2 · e^{-γ} · c₂`,  `c₂ = ∏_{p odd} (1 - 1/(p-1)²) ≈ 0.6602`,

and `2 e^{-γ} c₂ ≈ 0.7412`.  The lemma `vsieve_log_lower` (already in the commons)
proves the round bound `Vsieve Y · log Y ≥ 1/2` eventually.  Here we push the
constant up to `7/10`, leaving only a small margin below the limit.

The proof is the same three-input computation, used at its exact tilt:

* Mertens' lower bound `∏_{p ≤ m}(1 - 1/p) ≥ e^{-γ} e^{-(3/2)/log m}/log m`
  (`primeProduct_oneSubInv_ge_sharp`),
* the numerical bound `e^{-γ} ≥ 0.56` (`eulerMascheroni_exp_neg_lower`),
* the twin-prime product lower bound `∏_{3 ≤ p ≤ m}(1 - 1/(p-1)²) ≥ 0.65`
  (`twinProduct_ge`, proved below from the finite product over the odd primes
  `≤ 100` and the tail estimate `∑_{p>100} (p-1)^{-2} ≤ 1/99`).

The product identity

`Vsieve Y = 2 · ∏_{p ≤ Y-1}(1 - 1/p) · ∏_{3 ≤ p ≤ Y-1}(1 - 1/(p-1)²)`

(`Vsieve_eq_two_mul`) then gives, with `m = Y - 1` and `Y ≥ 10^18` (so `log m ≥ 39`)

`Vsieve Y · log Y ≥ 2 · 0.65 · 0.56 · e^{-(3/2)/log m} · (log Y / log m)`
`                ≥ 1.3 · 0.56 · (1 - 1/26) = 7/10`,

using `e^{-t} ≥ 1 - t` and `(3/2)/log m ≤ 1/26` (i.e. `log m ≥ 39`).  The numerical
core of the chain is isolated in `vsieve_numeric_core`.
-/

/-! ## The twin-prime product over the odd primes `≤ n` -/

/-- the odd primes `≤ n` -/
private def sqOdd (n : ℕ) : Finset ℕ := (Nat.primesLE n).filter (fun p => p ≠ 2)

/-- the twin-prime singular factor `1 - 1/(p-1)²` -/
private def sqf (p : ℕ) : ℝ := 1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2

private lemma mem_sqOdd {n p : ℕ} (hp : p ∈ sqOdd n) :
    p ≤ n ∧ Nat.Prime p ∧ p ≠ 2 := by
  rw [sqOdd, Finset.mem_filter] at hp
  exact ⟨(Nat.mem_primesLE.mp hp.1).1, (Nat.mem_primesLE.mp hp.1).2, hp.2⟩

private lemma three_le_of_mem_sqOdd {n p : ℕ} (hp : p ∈ sqOdd n) : 3 ≤ p := by
  have h := mem_sqOdd hp
  have h2 := h.2.1.two_le
  omega

private lemma sqf_pos {p : ℕ} (hp : 3 ≤ p) : 0 < sqf p := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpos : 0 < ((p : ℝ) - 1) ^ 2 := by
    apply pow_pos
    linarith
  have hlt : (1 : ℝ) / ((p : ℝ) - 1) ^ 2 < 1 := by
    rw [div_lt_one hpos]
    nlinarith
  simp only [sqf]
  linarith

/-- the explicit form of `sqf p` for `p ≥ 3` -/
private lemma twinFactor_pos {p : ℕ} (hp : 3 ≤ p) :
    0 < 1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  simpa only [sqf] using sqf_pos hp

private lemma primesLE_factor_pos {n p : ℕ} (hp : p ∈ Nat.primesLE n) :
    0 < 1 - (p : ℝ)⁻¹ := by
  have hpp : Nat.Prime p := (Nat.mem_primesLE.mp hp).2
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hinv : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
  have h' : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [← one_div]; exact hinv
  linarith

/-- `∏ (1 - t_i) ≥ 1 - ∑ t_i` for nonnegative `t_i` with total sum at most one. -/
private lemma prod_one_sub_ge_one_sub_sum {ι : Type*} (s : Finset ι) (t : ι → ℝ) :
    (∀ i ∈ s, 0 ≤ t i) → (∑ i ∈ s, t i) ≤ 1 →
    (1 - (∑ i ∈ s, t i)) ≤ ∏ i ∈ s, (1 - t i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro h0 hsum
    simp
  · intro a s' ha ih h0 hsum
    have h0a : 0 ≤ t a := h0 a (by simp)
    have h0s' : ∀ i ∈ s', 0 ≤ t i := fun i hi => h0 i (by simp [hi])
    have hs'sum_nonneg : 0 ≤ ∑ i ∈ s', t i := Finset.sum_nonneg h0s'
    have hsuma : t a + (∑ i ∈ s', t i) ≤ 1 := by
      simpa [Finset.sum_insert ha] using hsum
    have hta1 : t a ≤ 1 := by linarith
    have hs'sum_le_one : (∑ i ∈ s', t i) ≤ 1 := by linarith
    have hprod : (1 - (∑ i ∈ s', t i)) ≤ ∏ i ∈ s', (1 - t i) := ih h0s' hs'sum_le_one
    have h1ma : 0 ≤ 1 - t a := by linarith
    calc
      1 - (∑ i ∈ insert a s', t i) = 1 - (t a + (∑ i ∈ s', t i)) := by
        rw [Finset.sum_insert ha]
      _ ≤ (1 - t a) * (1 - (∑ i ∈ s', t i)) := by
        nlinarith
      _ ≤ (1 - t a) * ∏ i ∈ s', (1 - t i) := by
        exact mul_le_mul_of_nonneg_left hprod h1ma
      _ = ∏ i ∈ insert a s', (1 - t i) := by
        rw [Finset.prod_insert ha]

/-- the odd primes `≤ 100` -/
private def smallOdd : Finset ℕ :=
  {3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97}

private lemma sqOdd_hundred : sqOdd 100 = smallOdd := by decide

/-- the finite product over the odd primes `≤ 100` is at least `0.6613`. -/
private lemma prod_hundred_ge : (6613 / 10000 : ℝ) ≤ ∏ p ∈ sqOdd 100, sqf p := by
  rw [sqOdd_hundred]
  norm_num [smallOdd, sqf]

/-- Tail estimate: the sum of `1/(p-1)²` over the odd primes `p > 100` up to `n`
is at most `1/99`. -/
private lemma sum_sqf_tail_le (n : ℕ) (hn : 100 ≤ n) :
    (∑ p ∈ (sqOdd n).filter (fun p => 100 < p), (1 : ℝ) / ((p : ℝ) - 1) ^ 2) ≤ 1 / 99 := by
  set T : Finset ℕ := (sqOdd n).filter (fun p => 100 < p) with hT
  have hinj : Set.InjOn (fun p : ℕ => p - 1) (T : Set ℕ) := by
    intro p hp q hq hpq
    have hpF : p ∈ T := Finset.mem_coe.mp hp
    have hqF : q ∈ T := Finset.mem_coe.mp hq
    rw [hT, Finset.mem_filter] at hpF hqF
    have hp' : 100 < p := hpF.2
    have hq' : 100 < q := hqF.2
    simp only at hpq
    omega
  -- each term rewrites as `1/(p-1)²` with `p - 1 : ℕ`
  have hpt : ∀ p ∈ T, (1 : ℝ) / ((p : ℝ) - 1) ^ 2 = (1 : ℝ) / (((p - 1 : ℕ) : ℝ)) ^ 2 := by
    intro p hp
    have hpF : p ∈ T := hp
    rw [hT, Finset.mem_filter] at hpF
    have h1le : 1 ≤ p := by
      have h := mem_sqOdd hpF.1
      have h2 := h.2.1.two_le
      omega
    rw [Nat.cast_sub h1le]
    norm_num
  have hstep : (∑ p ∈ T, (1 : ℝ) / ((p : ℝ) - 1) ^ 2)
      = ∑ p ∈ T, (1 : ℝ) / (((p - 1 : ℕ) : ℝ)) ^ 2 :=
    Finset.sum_congr rfl hpt
  have himage : (∑ p ∈ T, (1 : ℝ) / (((p - 1 : ℕ) : ℝ)) ^ 2)
      = ∑ m ∈ T.image (fun p : ℕ => p - 1), (1 : ℝ) / ((m : ℝ)) ^ 2 :=
    (Finset.sum_image (s := T) (f := fun m : ℕ => (1 : ℝ) / ((m : ℝ)) ^ 2)
      (g := fun p : ℕ => p - 1) hinj).symm
  have hsub : T.image (fun p : ℕ => p - 1) ⊆ Finset.Ioc (99 : ℕ) (n - 1) := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
    rw [hT, Finset.mem_filter] at hp
    have hp1 : p ≤ n := (mem_sqOdd hp.1).1
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hle : (∑ m ∈ T.image (fun p : ℕ => p - 1), (1 : ℝ) / ((m : ℝ)) ^ 2)
      ≤ ∑ m ∈ Finset.Ioc (99 : ℕ) (n - 1), (1 : ℝ) / ((m : ℝ)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
  have hub : (∑ m ∈ Finset.Ioc (99 : ℕ) (n - 1), (1 : ℝ) / ((m : ℝ)) ^ 2) ≤ 1 / 99 := by
    have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 99) (n := n - 1) (by norm_num) (by omega)
    have h' : (∑ m ∈ Finset.Ioc (99 : ℕ) (n - 1), (1 : ℝ) / ((m : ℝ)) ^ 2)
        = ∑ m ∈ Finset.Ioc (99 : ℕ) (n - 1), (((m : ℝ)) ^ 2)⁻¹ := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [one_div]
    rw [h']
    have h2 : (0 : ℝ) ≤ (((n - 1 : ℕ)) : ℝ)⁻¹ := by positivity
    linarith
  rw [hstep, himage]
  exact le_trans hle hub

/-- The twin-prime product over the odd primes `≤ n` is at least `0.65`. -/
private lemma prod_sqf_ge (n : ℕ) (hn : 100 ≤ n) :
    (0.65 : ℝ) ≤ ∏ p ∈ sqOdd n, sqf p := by
  have hsplit : (∏ p ∈ sqOdd n, sqf p)
      = (∏ p ∈ (sqOdd n).filter (fun p => 100 < p), sqf p)
        * (∏ p ∈ (sqOdd n).filter (fun p => ¬ 100 < p), sqf p) := by
    rw [Finset.prod_filter_mul_prod_filter_not]
  have hnot : (sqOdd n).filter (fun p => ¬ 100 < p) = sqOdd 100 := by
    ext p
    simp only [sqOdd, Finset.mem_filter]
    constructor
    · intro h
      obtain ⟨⟨hp1, hp2⟩, hp3⟩ := h
      exact ⟨Nat.mem_primesLE.mpr ⟨by omega, (Nat.mem_primesLE.mp hp1).2⟩, hp2⟩
    · intro h
      obtain ⟨hp1, hp2⟩ := h
      have hp1' : p ≤ 100 := (Nat.mem_primesLE.mp hp1).1
      exact ⟨⟨Nat.primesLE_mono hn hp1, hp2⟩, by omega⟩
  have hhead : (6613 / 10000 : ℝ) ≤ ∏ p ∈ sqOdd 100, sqf p := prod_hundred_ge
  have hsum : (∑ p ∈ (sqOdd n).filter (fun p => 100 < p),
      (1 : ℝ) / ((p : ℝ) - 1) ^ 2) ≤ 1 := by
    have := sum_sqf_tail_le n hn
    linarith
  have htail : (1 - 1 / 99 : ℝ) ≤ ∏ p ∈ (sqOdd n).filter (fun p => 100 < p), sqf p := by
    have h := prod_one_sub_ge_one_sub_sum ((sqOdd n).filter (fun p => 100 < p))
      (fun p => (1 : ℝ) / ((p : ℝ) - 1) ^ 2)
      (fun p hp => by positivity) hsum
    have h2 : (∏ q ∈ (sqOdd n).filter (fun p => 100 < p),
          (1 - (1 : ℝ) / ((q : ℝ) - 1) ^ 2))
        = ∏ q ∈ (sqOdd n).filter (fun p => 100 < p), sqf q :=
      Finset.prod_congr rfl (fun q hq => by simp only [sqf])
    have h1 : (1 - 1 / 99 : ℝ) ≤ 1 - (∑ p ∈ (sqOdd n).filter (fun p => 100 < p),
        (1 : ℝ) / ((p : ℝ) - 1) ^ 2) := by
      have := sum_sqf_tail_le n hn
      linarith
    rw [h2] at h
    linarith
  rw [hsplit, hnot]
  have htail0 : (0 : ℝ) ≤ ∏ p ∈ (sqOdd n).filter (fun p => 100 < p), sqf p :=
    Finset.prod_nonneg (fun p hp =>
      (sqf_pos (three_le_of_mem_sqOdd (Finset.mem_filter.mp hp).1)).le)
  have hhead0 : (0 : ℝ) ≤ (6613 / 10000 : ℝ) := by norm_num
  have hmul := mul_le_mul htail hhead hhead0 htail0
  have hconst : (0.65 : ℝ) ≤ (1 - 1 / 99) * (6613 / 10000) := by norm_num
  linarith

/-- **Twin-prime product lower bound.** `∏_{3 ≤ p ≤ n} (1 - 1/(p-1)²) ≥ 0.65`
for `n ≥ 100`. -/
theorem twinProduct_ge (n : ℕ) (hn : 100 ≤ n) :
    (0.65 : ℝ) ≤ ∏ p ∈ (Nat.primesLE n).filter (fun p => p ≠ 2),
      (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2) := by
  simpa only [sqOdd, sqf] using prod_sqf_ge n hn

/-! ## Factorization of `Vsieve` -/

/-- Splitting off the prime `2` from the Mertens product doubles it. -/
private lemma prod_odd_eq_two_mul (m : ℕ) (hm : 2 ≤ m) :
    (∏ p ∈ sqOdd m, (1 - (p : ℝ)⁻¹)) = 2 * (∏ p ∈ Nat.primesLE m, (1 - (p : ℝ)⁻¹)) := by
  have h2mem : 2 ∈ Nat.primesLE m := by
    rw [Nat.mem_primesLE]
    exact ⟨hm, Nat.prime_two⟩
  have hdiff : Nat.primesLE m \ {2} = sqOdd m := by
    ext p
    simp only [sqOdd, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_filter]
  have h := Finset.prod_sdiff (s₁ := ({2} : Finset ℕ)) (s₂ := Nat.primesLE m)
    (f := fun p => (1 - (p : ℝ)⁻¹)) (Finset.singleton_subset_iff.mpr h2mem)
  rw [hdiff, Finset.prod_singleton] at h
  have h2 : (1 - ((2 : ℕ) : ℝ)⁻¹) = 1 / 2 := by norm_num
  rw [h2] at h
  linarith

private theorem Vsieve_eq_two_mul_aux (Y : ℕ) (hY : 3 ≤ Y) :
    Vsieve Y = 2 * (∏ p ∈ Nat.primesLE (Y - 1), (1 - (p : ℝ)⁻¹))
      * (∏ p ∈ sqOdd (Y - 1), sqf p) := by
  have hm : 2 ≤ Y - 1 := by omega
  rw [Vsieve_eq_VLE]
  unfold VLE
  have hfilter : (Nat.primesLE (Y - 1)).filter (fun p => p ≠ 2) = sqOdd (Y - 1) := rfl
  rw [hfilter]
  have hfac : ∀ p ∈ sqOdd (Y - 1),
      (1 - (1 : ℝ) / ((p : ℝ) - 1)) = (1 - (p : ℝ)⁻¹) * sqf p := by
    intro p hp
    have h3 : 3 ≤ p := three_le_of_mem_sqOdd hp
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) ≠ 0 := by linarith
    simp only [sqf]
    field_simp
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib,
    prod_odd_eq_two_mul (Y - 1) hm]
  try ring

/-- **Factorization of the odd Mertens product.**  For `Y ≥ 2`,

`Vsieve Y = 2 · ∏_{p ≤ Y-1}(1 - 1/p) · ∏_{3 ≤ p ≤ Y-1}(1 - 1/(p-1)²)`. -/
theorem Vsieve_eq_two_mul (Y : ℕ) (hY : 3 ≤ Y) :
    Vsieve Y = 2 * (∏ p ∈ Nat.primesLE (Y - 1), (1 - (p : ℝ)⁻¹))
      * (∏ p ∈ (Nat.primesLE (Y - 1)).filter (fun p => p ≠ 2),
          (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)) := by
  simpa only [sqOdd, sqf] using Vsieve_eq_two_mul_aux Y hY

/-! ## The numerical core -/

/-- Numerical chain: if `A ≥ 0.56`, `B ≥ 25/26`, `M ≥ A·B/C`, `Q ≥ 0.65`, with
`0 < C ≤ D`, then `2·M·Q·D ≥ 7/10`. -/
private lemma vsieve_numeric_core (A B C D M Q : ℝ)
    (hA : (0.56 : ℝ) ≤ A) (hA0 : 0 ≤ A) (hB : (25 / 26 : ℝ) ≤ B) (hB0 : 0 ≤ B)
    (hC : 0 < C) (hD : 0 < D) (hCD : C ≤ D)
    (hM : A * B / C ≤ M) (hQ : (0.65 : ℝ) ≤ Q) :
    (7 / 10 : ℝ) ≤ 2 * M * Q * D := by
  have hQ0 : (0 : ℝ) ≤ Q := le_trans (by norm_num) hQ
  have hAB0 : 0 ≤ A * B := mul_nonneg hA0 hB0
  have hM' : A * B ≤ M * C := (div_le_iff₀ hC).mp hM
  have hDC : 0 ≤ D / C := div_nonneg (le_of_lt hD) (le_of_lt hC)
  have hstep : (A * B) * (D / C) ≤ M * D := by
    have h := mul_le_mul_of_nonneg_right hM' hDC
    have heq : (M * C) * (D / C) = M * D := by field_simp
    rwa [heq] at h
  have hAB : (0.56 : ℝ) * (25 / 26 : ℝ) ≤ A * B :=
    mul_le_mul hA hB (by norm_num) hA0
  have hratio : (1 : ℝ) ≤ D / C := (one_le_div hC).mpr hCD
  have hlow : (0.56 : ℝ) * (25 / 26 : ℝ) ≤ (A * B) * (D / C) := by
    have h := mul_le_mul hAB hratio (by norm_num) hAB0
    simpa using h
  have hMD : (0.56 : ℝ) * (25 / 26 : ℝ) ≤ M * D := le_trans hlow hstep
  have hkey : 2 * (0.65 : ℝ) * ((0.56 : ℝ) * (25 / 26 : ℝ)) ≤ 2 * M * Q * D := by
    have hrw : 2 * M * Q * D = 2 * Q * (M * D) := by ring
    rw [hrw]
    have h1 : 2 * (0.65 : ℝ) * ((0.56 : ℝ) * (25 / 26 : ℝ))
        ≤ 2 * Q * ((0.56 : ℝ) * (25 / 26 : ℝ)) := by
      have h2 : 2 * (0.65 : ℝ) ≤ 2 * Q := by linarith
      exact mul_le_mul_of_nonneg_right h2 (by norm_num)
    have h2 : 2 * Q * ((0.56 : ℝ) * (25 / 26 : ℝ)) ≤ 2 * Q * (M * D) :=
      mul_le_mul_of_nonneg_left hMD (by linarith)
    linarith
  have hnum : (7 / 10 : ℝ) ≤ 2 * (0.65 : ℝ) * ((0.56 : ℝ) * (25 / 26 : ℝ)) := by norm_num
  linarith

/-! ## The main theorem -/

theorem vsieve_log_lower_sharp : ∃ Y₀ : ℕ, ∀ n : ℕ, Y₀ ≤ n →
    (7/10 : ℝ) ≤ Commons.NumberTheory.Chen.Vsieve n * Real.log (n:ℝ) := by
  refine ⟨10^18, fun n hn => ?_⟩
  set m : ℕ := n - 1 with hmdef
  have hm2 : 2 ≤ m := by omega
  have hm100 : 100 ≤ m := by omega
  have hmn : m ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hmlog1 : 1 < m := by omega
  have hnlog1 : 1 < n := by omega
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hmlog1)
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hnlog1)
  have hlog_le : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hm_pos (by exact_mod_cast hmn)
  -- `exp 39 ≤ m`, hence `log m ≥ 39`
  have hexp39 : Real.exp 39 ≤ (m : ℝ) := by
    have h1 : Real.exp 39 ≤ (2.7182818286 : ℝ) ^ 39 := by
      have hh : Real.exp 39 = (Real.exp 1) ^ 39 := by
        have hh0 := Real.exp_nat_mul (1 : ℝ) 39
        rw [mul_one] at hh0
        exact hh0
      rw [hh]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt Real.exp_one_lt_d9) 39
    have h2 : (2.7182818286 : ℝ) ^ 39 ≤ ((10 : ℕ) ^ 17 : ℝ) := by norm_num
    have h3 : ((10 : ℕ) ^ 17 : ℝ) ≤ (m : ℝ) := by
      have : (10 : ℕ) ^ 17 ≤ m := by omega
      exact_mod_cast this
    exact le_trans h1 (le_trans h2 h3)
  have hlogm : (39 : ℝ) ≤ Real.log (m : ℝ) := (Real.le_log_iff_exp_le hm_pos).mpr hexp39
  have hx : (3 / 2 : ℝ) / Real.log (m : ℝ) ≤ 1 / 26 := by
    rw [div_le_iff₀ hlogm_pos]
    nlinarith
  have hB : (25 / 26 : ℝ) ≤ Real.exp (-(3 / 2) / Real.log (m : ℝ)) := by
    have h := Real.one_sub_le_exp_neg ((3 / 2 : ℝ) / Real.log (m : ℝ))
    have h2 : -((3 / 2 : ℝ) / Real.log (m : ℝ)) = -(3 / 2) / Real.log (m : ℝ) := by ring
    rw [h2] at h
    linarith
  have hA : (0.56 : ℝ) ≤ Real.exp (-Real.eulerMascheroniConstant) :=
    Commons.NumberTheory.Mertens.eulerMascheroni_exp_neg_lower
  have hM := Commons.NumberTheory.Mertens.primeProduct_oneSubInv_ge_sharp m hm100
  have hQ := twinProduct_ge m hm100
  have hA0 : (0 : ℝ) ≤ Real.exp (-Real.eulerMascheroniConstant) := (Real.exp_pos _).le
  have hB0 : (0 : ℝ) ≤ Real.exp (-(3 / 2) / Real.log (m : ℝ)) := (Real.exp_pos _).le
  have hM0 : (0 : ℝ) ≤ ∏ p ∈ Nat.primesLE m, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_nonneg (fun p hp => (primesLE_factor_pos hp).le)
  have hn3 : 3 ≤ n := by omega
  have hVs := Vsieve_eq_two_mul n hn3
  rw [show n - 1 = m from hmdef.symm] at hVs
  rw [hVs]
  exact vsieve_numeric_core _ _ _ _ _ _
    hA hA0 hB hB0 hlogm_pos hlogn_pos hlog_le hM hQ

end

end Commons.NumberTheory.Chen
