import Mathlib
import Submission.Commons.NumberTheory.Linnik.lemma5_3

/-!
# The principal-character `K`-sum: Heath-Brown (1992), equation (6.9)

Heath-Brown's Lemma 5.3 (`Commons.NumberTheory.Linnik.lemma5_3`) states that for a
`C²`-function `f` supported in `[0,x₀]`,

`∑_n Λ(n) χ₀(n) n^{-s} f(log n / L) = L · ∫₀^{x₀} e^{-(s-1)Lt} f(t) dt + O(ω(q) + (log L)²)`

for `|Re s - 1| ≤ √(log L)/L`, `|Im s| ≤ L`.  Specialising to the real point `s = β` and
using `|β - 1| ≤ √(log log q)/log q`, `ω(q) = o(log q)` (proved below) and
`(log log q)² = o(log q)`, the error term is absorbed by the slack `f(0)·ε·log q`, which is
the inequality (6.9) of the paper.

The main difficulty is not analytic: the summand of Lemma 5.3 is a *complex* number while
the target sum is its real part, so we must pass from `Re (∑ ...)` to `∑ (Re ...)` using
the finite support of the summands.
-/

open scoped BigOperators
open MeasureTheory Set Finset

namespace Commons.NumberTheory.Linnik

/-! ### The `o(log q)` bound for `ω(q)` -/

/-- For `b ≥ 2` and `q ≥ 1`: `ω(q) ≤ b + log_b q`. -/
private lemma card_primeFactors_le_add_log {b q : ℕ} (hb : 1 < b) (hq : q ≠ 0) :
    q.primeFactors.card ≤ b + Nat.log b q := by
  set s : Finset ℕ := q.primeFactors.filter (fun p => b ≤ p) with hs
  set s' : Finset ℕ := q.primeFactors.filter (fun p => p < b) with hs'
  have hsplit : s'.card + s.card = q.primeFactors.card := by
    rw [← Finset.card_filter_add_card_filter_not (p := fun p => p < b) (s := q.primeFactors)]
    have : q.primeFactors.filter (fun p => ¬ p < b) = s := by
      rw [hs]
      refine Finset.filter_congr ?_
      intro p _
      exact not_lt
    rw [this, hs']
  have h1 : s'.card ≤ b := by
    have hsub : s' ⊆ Finset.range b := by
      intro p hp
      rw [hs', Finset.mem_filter] at hp
      exact Finset.mem_range.mpr hp.2
    calc s'.card ≤ (Finset.range b).card := Finset.card_le_card hsub
      _ = b := Finset.card_range b
  have h2 : s.card ≤ Nat.log b q := by
    apply Nat.le_log_of_pow_le hb
    have hbpow : (b : ℕ) ^ s.card = ∏ x ∈ s, b := (Finset.prod_const b).symm
    rw [hbpow]
    have hle1 : ∏ x ∈ s, b ≤ ∏ x ∈ s, x := by
      refine Finset.prod_le_prod₀ (fun x _ => Nat.zero_le _) ?_
      intro x hx
      rw [hs, Finset.mem_filter] at hx
      exact hx.2
    have hle2 : ∏ x ∈ s, x ≤ q := by
      have hsub : s ⊆ q.primeFactors := by
        rw [hs]; exact Finset.filter_subset _ _
      have hsplit2 : ∏ x ∈ q.primeFactors, x
          = (∏ x ∈ s, x) * (∏ x ∈ q.primeFactors \ s, x) := by
        rw [← Finset.prod_sdiff hsub]; ring
      have hqeq : ∏ x ∈ q.primeFactors, x ≤ q :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
      have hone : 1 ≤ ∏ x ∈ q.primeFactors \ s, x := by
        refine Finset.one_le_prod₀ ?_
        intro x hx
        rw [Finset.mem_sdiff] at hx
        exact Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hx.1)
      nlinarith
    exact le_trans hle1 hle2
  omega

/-- `ω(q) = o(log q)`: for every `δ > 0` all sufficiently large `q` satisfy
`ω(q) ≤ δ log q`. -/
private theorem primeFactors_card_le_eps_log (δ : ℝ) (hδ : 0 < δ) :
    ∃ q₁ : ℕ, ∀ q : ℕ, q₁ ≤ q → (q.primeFactors.card : ℝ) ≤ δ * Real.log (q : ℝ) := by
  have h8 : (0:ℝ) < 8 / δ := by positivity
  set b : ℕ := ⌈Real.exp (8 / δ)⌉₊ + 2 with hbdef
  have hb1 : 1 < b := by omega
  have hlogb : 8 / δ ≤ Real.log b := by
    have hle : Real.exp (8/δ) ≤ (b : ℝ) := by
      have h1 : Real.exp (8/δ) ≤ ((⌈Real.exp (8/δ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((⌈Real.exp (8/δ)⌉₊ : ℕ) : ℝ) ≤ (b : ℝ) := by
        rw [hbdef]; push_cast; linarith
      linarith
    calc 8 / δ = Real.log (Real.exp (8/δ)) := (Real.log_exp _).symm
      _ ≤ Real.log b := Real.log_le_log (Real.exp_pos _) hle
  refine ⟨⌈Real.exp (4 * (b : ℝ) / δ)⌉₊ + 1, ?_⟩
  intro q hq
  have hceilq : ((⌈Real.exp (4 * (b:ℝ) / δ)⌉₊ : ℕ) : ℝ) < (q : ℝ) := by
    have : (⌈Real.exp (4 * (b:ℝ) / δ)⌉₊ : ℕ) < q := by omega
    exact_mod_cast this
  have hqpos : 0 < q := by
    have : (0:ℕ) < ⌈Real.exp (4 * (b:ℝ) / δ)⌉₊ + 1 := by omega
    omega
  have hlogq : 4 * (b:ℝ) / δ ≤ Real.log q := by
    have hle : Real.exp (4 * (b:ℝ) / δ) ≤ (q : ℝ) := by
      have h1 : Real.exp (4 * (b:ℝ) / δ) ≤ ((⌈Real.exp (4 * (b:ℝ) / δ)⌉₊ : ℕ) : ℝ) :=
        Nat.le_ceil _
      linarith
    calc 4 * (b:ℝ) / δ = Real.log (Real.exp (4 * (b:ℝ) / δ)) := (Real.log_exp _).symm
      _ ≤ Real.log q := Real.log_le_log (Real.exp_pos _) hle
  have hlogqnonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hcard := card_primeFactors_le_add_log hb1 hqpos.ne'
  have hcastcard : (q.primeFactors.card : ℝ) ≤ (b : ℝ) + (Nat.log b q : ℝ) := by
    exact_mod_cast hcard
  have hlogbq : (Nat.log b q : ℝ) ≤ Real.log (q:ℝ) / Real.log b := by
    have hpow : b ^ Nat.log b q ≤ q := Nat.pow_log_le_self b hqpos.ne'
    have hcast : ((b:ℝ)) ^ Nat.log b q ≤ (q:ℝ) := by exact_mod_cast hpow
    have h1 : Real.log ((b:ℝ) ^ Nat.log b q) ≤ Real.log q :=
      Real.log_le_log (by positivity) hcast
    rw [Real.log_pow] at h1
    rw [le_div_iff₀ (by linarith : (0:ℝ) < Real.log b)]
    linarith
  have hstep1 : Real.log (q:ℝ) / Real.log b ≤ (δ/8) * Real.log (q:ℝ) := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.log b)]
    have hprod : (δ/8) * (8/δ) = (1:ℝ) := by field_simp
    have h1 : (δ/8) * (8/δ) ≤ (δ/8) * Real.log b :=
      mul_le_mul_of_nonneg_left hlogb (by positivity)
    rw [hprod] at h1
    nlinarith
  have hstep2 : (b:ℝ) ≤ (δ/4) * Real.log (q:ℝ) := by
    have h1 : (δ/4) * (4 * (b:ℝ)/δ) ≤ (δ/4) * Real.log q :=
      mul_le_mul_of_nonneg_left hlogq (by positivity)
    have h2 : (δ/4) * (4 * (b:ℝ)/δ) = (b:ℝ) := by field_simp
    linarith
  nlinarith [hcastcard, hlogbq, hstep1, hstep2, hlogqnonneg]

/-- For real `a g` and complex `w v`: `ℜ(a·(w/v)·g) = a·ℜ(w/v)·g`. -/
private lemma re_mul_div_mul (a g : ℝ) (w v : ℂ) :
    (((a:ℂ) * w / v) * (g:ℂ)).re = a * (w/v).re * g := by
  have h1 : ((a:ℂ) * w / v) = (a:ℂ) * (w/v) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  rw [h1]
  have h2 : ((a:ℂ) * (w/v) * (g:ℂ)).re = a * ((w/v) * (g:ℂ)).re := by
    rw [mul_assoc, Complex.re_ofReal_mul]
  have h3 : ((w/v) * (g:ℂ)).re = (w/v).re * g := by
    rw [mul_comm (w/v) ((g:ℂ)), Complex.re_ofReal_mul]; ring
  rw [h2, h3]; ring

/-! ### The numerical error budget -/

/-- The error term of Lemma 5.3 is absorbed by the slack `f₀ε log q`. -/
private lemma exists_error_bound (C f₀ ε : ℝ) (hC : 0 < C) (hf₀ : 0 < f₀) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      C * ((q.primeFactors.card : ℝ) + (Real.log (Real.log (q : ℝ)))^2)
        ≤ f₀ * ε * Real.log (q : ℝ) := by
  set δ : ℝ := f₀ * ε / (4 * C) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨q₁, hq₁⟩ := primeFactors_card_le_eps_log δ hδpos
  set T : ℝ := 16 / δ with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  refine ⟨max q₁ (⌈Real.exp (T^2 + 1)⌉₊ + 1), ?_⟩
  intro q hq
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : ⌈Real.exp (T^2 + 1)⌉₊ + 1 ≤ q := le_trans (le_max_right _ _) hq
  have hω : (q.primeFactors.card : ℝ) ≤ δ * Real.log (q : ℝ) := hq₁ q hq1
  have hceil : Real.exp (T^2 + 1) ≤ (q : ℝ) := by
    have h1 : Real.exp (T^2+1) ≤ ((⌈Real.exp (T^2+1)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp (T^2+1)⌉₊ : ℕ) : ℝ) < (q:ℝ) := by
      have h3 : ⌈Real.exp (T^2+1)⌉₊ < q := by omega
      exact_mod_cast h3
    linarith
  have hlogq : T^2 + 1 ≤ Real.log (q:ℝ) := by
    calc T^2 + 1 = Real.log (Real.exp (T^2+1)) := (Real.log_exp _).symm
      _ ≤ Real.log q := Real.log_le_log (Real.exp_pos _) hceil
  have hlogq1 : 1 ≤ Real.log (q:ℝ) := by nlinarith [hlogq, sq_nonneg T]
  have hlogqpos : 0 < Real.log (q:ℝ) := by linarith
  have hTle : T ≤ Real.sqrt (Real.log (q:ℝ)) := by
    have h1 : Real.sqrt (T^2) ≤ Real.sqrt (Real.log q) :=
      Real.sqrt_le_sqrt (by nlinarith [hlogq])
    rwa [Real.sqrt_sq (le_of_lt hTpos)] at h1
  have h16 : 16 * Real.sqrt (Real.log (q:ℝ)) ≤ δ * Real.log (q:ℝ) := by
    have hδT : δ * T = 16 := by rw [hTdef]; field_simp
    have h2 : T * Real.sqrt (Real.log (q:ℝ))
        ≤ Real.sqrt (Real.log (q:ℝ)) * Real.sqrt (Real.log (q:ℝ)) :=
      mul_le_mul_of_nonneg_right hTle (Real.sqrt_nonneg _)
    calc 16 * Real.sqrt (Real.log (q:ℝ))
        = δ * (T * Real.sqrt (Real.log (q:ℝ))) := by rw [← hδT]; ring
      _ ≤ δ * (Real.sqrt (Real.log (q:ℝ)) * Real.sqrt (Real.log (q:ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hδpos)
      _ = δ * Real.log (q:ℝ) := by rw [Real.mul_self_sqrt (le_of_lt hlogqpos)]
  have hsq : (Real.log (Real.log (q:ℝ)))^2 ≤ δ * Real.log (q:ℝ) := by
    have hll : 0 ≤ Real.log (Real.log (q:ℝ)) := Real.log_nonneg hlogq1
    have hloglog : Real.log (Real.log (q:ℝ)) ≤ 4 * (Real.log (q:ℝ))^(1/4:ℝ) := by
      have h1 : Real.log (Real.log (q:ℝ)) ≤ (Real.log (q:ℝ))^(1/4:ℝ) / (1/4) :=
        Real.log_le_rpow_div (le_of_lt hlogqpos) (by norm_num)
      have h3 : (Real.log (q:ℝ))^(1/4:ℝ) / (1/4) = 4 * (Real.log (q:ℝ))^(1/4:ℝ) := by ring
      linarith [h1, h3]
    have hrpow : (Real.log (q:ℝ))^(1/4:ℝ) = Real.sqrt (Real.sqrt (Real.log (q:ℝ))) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hlogqpos)]
      norm_num
    have h4 : (4 * (Real.log (q:ℝ))^(1/4:ℝ))^2 = 16 * Real.sqrt (Real.log (q:ℝ)) := by
      rw [hrpow, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
      ring
    have h5 : (Real.log (Real.log (q:ℝ)))^2 ≤ (4 * (Real.log (q:ℝ))^(1/4:ℝ))^2 := by
      nlinarith [hloglog, hll, Real.rpow_nonneg (le_of_lt hlogqpos) (1/4:ℝ)]
    rw [h4] at h5
    linarith [h5, h16]
  have hsum : (q.primeFactors.card : ℝ) + (Real.log (Real.log (q:ℝ)))^2
      ≤ 2 * δ * Real.log (q:ℝ) := by linarith [hω, hsq]
  have hfinal : C * (2 * δ * Real.log (q:ℝ)) = (f₀ * ε / 2) * Real.log (q:ℝ) := by
    rw [hδdef]; field_simp; ring
  have hLnn : 0 ≤ Real.log (q:ℝ) := le_of_lt hlogqpos
  calc C * ((q.primeFactors.card : ℝ) + (Real.log (Real.log (q:ℝ)))^2)
      ≤ C * (2 * δ * Real.log (q:ℝ)) := mul_le_mul_of_nonneg_left hsum (le_of_lt hC)
    _ = (f₀ * ε / 2) * Real.log (q:ℝ) := hfinal
    _ ≤ f₀ * ε * Real.log (q:ℝ) := by nlinarith [hLnn, mul_pos hf₀ hε]

/-- **Heath-Brown (1992), equation (6.9)**: the principal-character term, deduced from
Lemma 5.3. -/
theorem Ksum_principal_le (x₀ B : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
      {ε : ℝ} (hε : 0 < ε) (hf0 : 0 < f 0),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q → ∀ {β lam : ℝ},
        lam = Real.log (q : ℝ) * (1 - β) →
        |β - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re
              * f (Real.log n / Real.log (q : ℝ)))
          ≤ Real.log (q : ℝ) * (∫ t in (0:ℝ)..x₀, Real.exp (lam * t) * f t)
              + f 0 * ε * Real.log (q : ℝ) := by
  intro f hcont hsupp hf2 hBnd ε hε hf0
  obtain ⟨C, hCpos, hCbd⟩ := lemma5_3 x₀ B hx₀ hB hcont hsupp hf2 hBnd
  obtain ⟨q₀, hq₀⟩ := exists_error_bound C (f 0) ε hCpos hf0 hε
  refine ⟨max q₀ 8, ?_⟩
  intro q hqNe hqq β lam hlam hβbd
  have hq₀q : q₀ ≤ q := le_trans (le_max_left _ _) hqq
  have hq8 : 8 ≤ q := le_trans (le_max_right _ _) hqq
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hL2 : 2 ≤ L := by
    rw [hLdef]
    have h1 : Real.log 8 ≤ Real.log (q:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hq8)
    have h3 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    rw [h3] at h1
    have h4 : (2:ℝ) < 3 * Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    linarith
  have hLpos : 0 < L := by linarith
  have herr : C * ((q.primeFactors.card : ℝ) + (Real.log L)^2) ≤ f 0 * ε * L :=
    hq₀ q hq₀q
  -- abbreviations
  let cterm : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ (β:ℂ) *
      ((f (Real.log n / L) : ℝ) : ℂ)
  let rterm : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β:ℂ)).re *
      f (Real.log n / L)
  let M : ℂ := ∫ t in (0:ℝ)..x₀,
      Complex.exp (-((((β:ℂ) - 1) * L) * (t:ℂ))) * ((f t : ℝ):ℂ)
  change (∑' n : ℕ, rterm n)
      ≤ L * (∫ t in (0:ℝ)..x₀, Real.exp (lam * t) * f t) + f 0 * ε * L
  -- Heath-Brown, Lemma 5.3 at `s = β`
  have hbound : ‖(∑' n : ℕ, cterm n) - ((L:ℝ):ℂ) * M‖
      ≤ C * ((q.primeFactors.card : ℝ) + (Real.log L)^2) := by
    have h := hCbd (q := q) (L := L) hL2 (β:ℂ) ?_ ?_
    · simpa only [cterm, M] using h
    · simpa using hβbd
    · rw [Complex.ofReal_im, abs_zero]; exact hLpos.le
  -- real summand = real part of complex summand
  have hsummand : ∀ n : ℕ, rterm n = (cterm n).re := by
    intro n
    simp only [rterm, cterm]
    exact (re_mul_div_mul (ArithmeticFunction.vonMangoldt n) (f (Real.log n / L))
      ((1 : DirichletCharacter ℂ q) (n : ZMod q)) ((n:ℂ)^(β:ℂ))).symm
  -- truncation
  set N : ℕ := ⌊Real.exp (L * x₀)⌋₊ + 1 with hNdef
  have hsupp_f : ∀ n : ℕ, N ≤ n → f (Real.log n / L) = 0 := by
    intro n hn
    have h2 : ⌊Real.exp (L*x₀)⌋₊ + 1 ≤ n := by omega
    have h1 : ((⌊Real.exp (L*x₀)⌋₊ : ℕ) : ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast h2
    have h3 := Nat.lt_floor_add_one (Real.exp (L*x₀))
    have hexp : Real.exp (L*x₀) < (n:ℝ) := by linarith
    have hnpos : (0:ℝ) < n := by linarith
    have h4 : L * x₀ < Real.log (n:ℝ) := by
      rw [← Real.log_exp (L*x₀)]
      exact Real.log_lt_log (Real.exp_pos _) hexp
    apply hsupp
    rw [le_div_iff₀ hLpos]
    linarith
  have hzero_r : ∀ n : ℕ, n ∉ Finset.Icc 1 N → rterm n = 0 := by
    intro n hn
    by_cases hn1 : n < 1
    · have hn0 : n = 0 := by omega
      subst hn0
      simp [rterm]
    · have hnN : N ≤ n := by
        by_contra h
        exact hn (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      simp only [rterm]
      rw [hsupp_f n hnN, mul_zero]
  have hzero_c : ∀ n : ℕ, n ∉ Finset.Icc 1 N → cterm n = 0 := by
    intro n hn
    by_cases hn1 : n < 1
    · have hn0 : n = 0 := by omega
      subst hn0
      simp [cterm]
    · have hnN : N ≤ n := by
        by_contra h
        exact hn (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      simp only [cterm]
      rw [hsupp_f n hnN]
      simp
  have hLHS : (∑' n : ℕ, rterm n) = (∑' n : ℕ, cterm n).re := by
    rw [tsum_eq_sum (s := Finset.Icc 1 N) hzero_r, tsum_eq_sum (s := Finset.Icc 1 N) hzero_c,
      Complex.re_sum]
    exact Finset.sum_congr rfl (fun n _ => hsummand n)
  -- the main term
  have hM : (((L:ℝ):ℂ) * M).re = L * (∫ t in (0:ℝ)..x₀, Real.exp (lam * t) * f t) := by
    have harg : ∀ t : ℝ, Complex.exp (-((((β:ℂ) - 1) * L) * (t:ℂ)))
        = ((Real.exp (lam * t) : ℝ) : ℂ) := by
      intro t
      have h1 : (((β:ℂ) - 1) * L) = (((β - 1) * L : ℝ) : ℂ) := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul]
      have h2 : -((((β:ℂ) - 1) * L) * (t:ℂ)) = ((lam * t : ℝ) : ℂ) := by
        rw [h1, ← Complex.ofReal_mul, ← Complex.ofReal_neg]
        congr 1
        rw [hlam]; ring
      rw [h2, Complex.ofReal_exp]
    have hpt : ∀ t ∈ Set.uIcc (0:ℝ) x₀,
        Complex.exp (-((((β:ℂ) - 1) * L) * (t:ℂ))) * ((f t : ℝ):ℂ)
          = ((Real.exp (lam * t) * f t : ℝ) : ℂ) := by
      intro t _
      rw [harg t, ← Complex.ofReal_mul]
    have hint : M = (((∫ t in (0:ℝ)..x₀, Real.exp (lam * t) * f t) : ℝ) : ℂ) := by
      show (∫ t in (0:ℝ)..x₀, Complex.exp (-((((β:ℂ) - 1) * L) * (t:ℂ))) * ((f t : ℝ):ℂ)) = _
      rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_ofReal]
    rw [hint, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hLHS]
  have hsplit : (∑' n : ℕ, cterm n).re
      = (((L:ℝ):ℂ) * M).re + ((∑' n : ℕ, cterm n) - ((L:ℝ):ℂ) * M).re := by
    rw [Complex.sub_re]; ring
  rw [hsplit, hM]
  have h2 : ((∑' n : ℕ, cterm n) - ((L:ℝ):ℂ) * M).re
      ≤ ‖(∑' n : ℕ, cterm n) - ((L:ℝ):ℂ) * M‖ := Complex.re_le_norm _
  linarith [h2, hbound, herr]

end Commons.NumberTheory.Linnik
