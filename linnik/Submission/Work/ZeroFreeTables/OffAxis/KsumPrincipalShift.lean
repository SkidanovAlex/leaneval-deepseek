import Mathlib
import Submission.Work.ZeroFreeTables.CertData
import Submission.Commons.NumberTheory.Linnik.lemma5_3

/-!
# The principal-character `K`-sum at a shifted point: Heath-Brown (1992), §6

Companion of `Commons.NumberTheory.Linnik.Ksum_principal_le` for a point `s = β + iτ` off
the real axis.  Heath-Brown's Lemma 5.3 (`Commons.NumberTheory.Linnik.lemma5_3`) gives

`∑_n Λ(n) χ₀(n) n^{-s} f(log n / L) = L · ∫₀^{x₀} e^{-(s-1)Lt} f(t) dt + O(ω(q) + (log L)²)`

for `|Re s - 1| ≤ √(log L)/L`, `|Im s| ≤ L`.  At `L = log q` and `s = β + iτ` the main term
is bounded using the decay hypothesis `hdec` applied at `z = (s-1)L`, whose real part is
`-L(1-β) ≥ -1` and whose imaginary part `τL` has modulus `≥ 1`: the integral is at most
`Cdec/|τL|`, so the main term is at most `L·Cdec/(|τ|L) = Cdec/|τ| ≤ Cdec`.  The error term
`C(ω(q) + (log L)²)` is absorbed into the slack `f(0)·ε·log q` for large `q`.
-/

set_option maxHeartbeats 1000000

open scoped BigOperators
open MeasureTheory Set Finset

namespace Work.ZeroFreeTables.OffAxis

/-! ### The `o(log q)` bound for `ω(q)` (copied from `Ksum_principal_le`) -/

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
      nlinarith only [hsplit2, hqeq, hone]
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
        rw [hbdef]; push_cast; linarith only []
      linarith only [h1, h2]
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
      linarith only [hceilq, h1]
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
    rw [le_div_iff₀ (by linarith only [h8, hlogb] : (0:ℝ) < Real.log b)]
    linarith only [h1]
  have hstep1 : Real.log (q:ℝ) / Real.log b ≤ (δ/8) * Real.log (q:ℝ) := by
    rw [div_le_iff₀ (by linarith only [h8, hlogb] : (0:ℝ) < Real.log b)]
    have hprod : (δ/8) * (8/δ) = (1:ℝ) := by field_simp
    have h1 : (δ/8) * (8/δ) ≤ (δ/8) * Real.log b :=
      mul_le_mul_of_nonneg_left hlogb (by positivity)
    rw [hprod] at h1
    nlinarith only [hlogqnonneg, h1]
  have hstep2 : (b:ℝ) ≤ (δ/4) * Real.log (q:ℝ) := by
    have h1 : (δ/4) * (4 * (b:ℝ)/δ) ≤ (δ/4) * Real.log q :=
      mul_le_mul_of_nonneg_left hlogq (by positivity)
    have h2 : (δ/4) * (4 * (b:ℝ)/δ) = (b:ℝ) := by field_simp
    linarith only [h1, h2]
  linarith only [hcastcard, hlogbq, hstep1, hstep2, hlogqnonneg]

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

/-! ### The numerical error budget (copied from `Ksum_principal_le`) -/

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
    linarith only [h1, h2]
  have hlogq : T^2 + 1 ≤ Real.log (q:ℝ) := by
    calc T^2 + 1 = Real.log (Real.exp (T^2+1)) := (Real.log_exp _).symm
      _ ≤ Real.log q := Real.log_le_log (Real.exp_pos _) hceil
  have hlogq1 : 1 ≤ Real.log (q:ℝ) := by linarith only [hlogq, sq_nonneg T]
  have hlogqpos : 0 < Real.log (q:ℝ) := by linarith only [hlogq1]
  have hTle : T ≤ Real.sqrt (Real.log (q:ℝ)) := by
    have h1 : Real.sqrt (T^2) ≤ Real.sqrt (Real.log q) :=
      Real.sqrt_le_sqrt (by linarith only [hlogq])
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
      linarith only [h1, h3]
    have hrpow : (Real.log (q:ℝ))^(1/4:ℝ) = Real.sqrt (Real.sqrt (Real.log (q:ℝ))) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hlogqpos)]
      norm_num
    have h4 : (4 * (Real.log (q:ℝ))^(1/4:ℝ))^2 = 16 * Real.sqrt (Real.log (q:ℝ)) := by
      rw [hrpow, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
      ring
    have h5 : (Real.log (Real.log (q:ℝ)))^2 ≤ (4 * (Real.log (q:ℝ))^(1/4:ℝ))^2 := by
      nlinarith only [hloglog, hll, Real.rpow_nonneg (le_of_lt hlogqpos) (1/4:ℝ)]
    rw [h4] at h5
    linarith only [h5, h16]
  have hsum : (q.primeFactors.card : ℝ) + (Real.log (Real.log (q:ℝ)))^2
      ≤ 2 * δ * Real.log (q:ℝ) := by linarith only [hω, hsq]
  have hfinal : C * (2 * δ * Real.log (q:ℝ)) = (f₀ * ε / 2) * Real.log (q:ℝ) := by
    rw [hδdef]; field_simp; ring
  have hLnn : 0 ≤ Real.log (q:ℝ) := le_of_lt hlogqpos
  calc C * ((q.primeFactors.card : ℝ) + (Real.log (Real.log (q:ℝ)))^2)
      ≤ C * (2 * δ * Real.log (q:ℝ)) := mul_le_mul_of_nonneg_left hsum (le_of_lt hC)
    _ = (f₀ * ε / 2) * Real.log (q:ℝ) := hfinal
    _ ≤ f₀ * ε * Real.log (q:ℝ) := by nlinarith only [hLnn, mul_pos hf₀ hε, hfinal, hC, hω]
/-- **The principal-character `K`-sum at a shifted point.**  For every `ε > 0` and all
sufficiently large moduli `q`, the principal `K`-sum at `s = β + iτ` is at most
`f(0)·ε·log q + Cdec`, provided `|Re s - 1| ≤ √(log log q)/log q`, `log q·(1-β) ≤ 1` and
`1 ≤ |τ| ≤ log q`, the last hypothesis feeding the decay estimate `hdec` for the
Laplace transform of `f`. -/
theorem KsumPrincipalShift (x₀ B Cdec : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) (hCdec : 0 ≤ Cdec) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hdec : ∀ z : ℂ, -(1:ℝ) ≤ z.re → 1 ≤ |z.im| →
        ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * ((f t : ℝ):ℂ)‖ ≤ Cdec / |z.im|)
      {ε : ℝ} (hε : 0 < ε),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q → ∀ {β τ : ℝ},
        |β - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) →
        Real.log (q:ℝ) * (1 - β) ≤ 1 →
        |τ| ≤ Real.log (q:ℝ) → 1 ≤ |τ| →
        Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ)) ((β:ℂ) + (τ:ℂ)*Complex.I)
            (1 : DirichletCharacter ℂ q)
          ≤ f 0 * ε * Real.log (q:ℝ) + Cdec := by
  intro f hcont hsupp hf2 hBnd hf0 hdec ε hε
  -- Lemma 5.3 with its error constant
  obtain ⟨C, hCpos, hCbd⟩ :=
    Commons.NumberTheory.Linnik.lemma5_3 x₀ B hx₀ hB hcont hsupp hf2 hBnd
  -- absorb the error term into the slack
  obtain ⟨q₁, hq₁⟩ := exists_error_bound C (f 0) ε hCpos hf0 hε
  refine ⟨max q₁ 8, ?_⟩
  intro q hqNe hqq β τ hβbd hβlam hτL hτ1
  have hq₁q : q₁ ≤ q := le_trans (le_max_left _ _) hqq
  have hq8 : 8 ≤ q := le_trans (le_max_right _ _) hqq
  set L : ℝ := Real.log (q:ℝ) with hLdef
  have hL2 : 2 ≤ L := by
    rw [hLdef]
    have h1 : Real.log 8 ≤ Real.log (q:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hq8)
    have h3 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    rw [h3] at h1
    have h4 : (2:ℝ) < 3 * Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith only [this]
    linarith only [h1, h4]
  have hLpos : 0 < L := by linarith only [hL2]
  have herr : C * ((q.primeFactors.card : ℝ) + (Real.log L)^2) ≤ f 0 * ε * L :=
    hq₁ q hq₁q
  -- the shifted point
  set s : ℂ := (β:ℂ) + (τ:ℂ)*Complex.I with hsdef
  let cterm : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (((1 : DirichletCharacter ℂ q) (n : ZMod q) : ℂ)) / (n : ℂ) ^ s *
      ((f (Real.log n / L) : ℝ) : ℂ)
  let rterm : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ s).re *
      f (Real.log n / L)
  let M : ℂ := ∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - 1) * L) * (t:ℂ))) * ((f t : ℝ):ℂ)
  change (∑' n : ℕ, rterm n) ≤ f 0 * ε * L + Cdec
  -- Heath-Brown, Lemma 5.3 at `s = β + iτ`
  have hbound : ‖(∑' n : ℕ, cterm n) - ((L:ℝ):ℂ) * M‖
      ≤ C * ((q.primeFactors.card : ℝ) + (Real.log L)^2) := by
    have h := hCbd (q := q) (L := L) hL2 s ?_ ?_
    · simpa only [cterm, M] using h
    · have hsre : s.re = β := by rw [hsdef]; simp
      rw [hsre]
      have heq : Real.sqrt (Real.log L) / L
          = Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by rw [hLdef]
      rw [heq]; exact hβbd
    · have hsim : s.im = τ := by rw [hsdef]; simp
      rw [hsim]; exact hτL
  -- real summand = real part of complex summand
  have hsummand : ∀ n : ℕ, rterm n = (cterm n).re := by
    intro n
    simp only [rterm, cterm]
    exact (re_mul_div_mul (ArithmeticFunction.vonMangoldt n) (f (Real.log n / L))
      ((1 : DirichletCharacter ℂ q) (n : ZMod q)) ((n:ℂ)^s)).symm
  -- truncation at `n > e^{L x₀}`
  set N : ℕ := ⌊Real.exp (L * x₀)⌋₊ + 1 with hNdef
  have hsupp_f : ∀ n : ℕ, N ≤ n → f (Real.log n / L) = 0 := by
    intro n hn
    have h2 : ⌊Real.exp (L*x₀)⌋₊ + 1 ≤ n := by omega
    have h1 : ((⌊Real.exp (L*x₀)⌋₊ : ℕ) : ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast h2
    have h3 := Nat.lt_floor_add_one (Real.exp (L*x₀))
    have hexp : Real.exp (L*x₀) < (n:ℝ) := by linarith only [h1, h3]
    have hnpos : (0:ℝ) < n := by linarith only [h1]
    have h4 : L * x₀ < Real.log (n:ℝ) := by
      rw [← Real.log_exp (L*x₀)]
      exact Real.log_lt_log (Real.exp_pos _) hexp
    apply hsupp
    rw [le_div_iff₀ hLpos]
    linarith only [h4]
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
    rw [tsum_eq_sum (s := Finset.Icc 1 N) hzero_r,
      tsum_eq_sum (s := Finset.Icc 1 N) hzero_c, Complex.re_sum]
    exact Finset.sum_congr rfl (fun n _ => hsummand n)
  -- `hdec` at `z = (s-1)L`
  have hz_re : (((s - 1) * L)).re = (β - 1) * L := by
    rw [hsdef]
    have h2 : (((β:ℂ) + (τ:ℂ)*Complex.I) - 1) * (L:ℂ)
        = (((β-1)*L : ℝ) : ℂ) + ((τ*L : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h2]; simp
  have hz_im : (((s - 1) * L)).im = τ * L := by
    rw [hsdef]
    have h2 : (((β:ℂ) + (τ:ℂ)*Complex.I) - 1) * (L:ℂ)
        = (((β-1)*L : ℝ) : ℂ) + ((τ*L : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h2]; simp
  have hz_im1 : 1 ≤ |(((s - 1) * L)).im| := by
    rw [hz_im, abs_mul, abs_of_pos hLpos]
    nlinarith only [hτ1, hL2, hτL]
  have hMnorm : ‖M‖ ≤ Cdec / |(((s - 1) * L)).im| := by
    have h := hdec ((s - 1) * L)
      (by rw [hz_re]
          have hb : L * (1 - β) ≤ 1 := by rw [hLdef]; exact hβlam
          linarith only [hb, hβlam]) hz_im1
    simpa only [M] using h
  -- the main term is at most `Cdec`
  have hmain : (((L:ℝ):ℂ) * M).re ≤ Cdec := by
    have h2 : (((L:ℝ):ℂ) * M).re ≤ ‖((L:ℝ):ℂ) * M‖ := Complex.re_le_norm _
    have h3 : ‖((L:ℝ):ℂ) * M‖ = L * ‖M‖ := by
      rw [norm_mul]
      congr 1
      simp [Real.norm_eq_abs, abs_of_pos hLpos]
    have h4 : L * ‖M‖ ≤ L * (Cdec / |(((s - 1) * L)).im|) :=
      mul_le_mul_of_nonneg_left hMnorm hLpos.le
    have h5 : L * (Cdec / |(((s - 1) * L)).im|) = Cdec / |τ| := by
      rw [hz_im, abs_mul, abs_of_pos hLpos]
      have ha : (|τ| : ℝ) ≠ 0 := ne_of_gt (by linarith only [hτ1] : (0:ℝ) < |τ|)
      field_simp
    have h6 : Cdec / |τ| ≤ Cdec := by
      rw [div_le_iff₀ (by linarith only [hτ1] : (0:ℝ) < |τ|)]
      nlinarith only [hτ1, hCdec]
    linarith only [h2, h3, h4, h5, h6]
  have herr_le : ((∑' n : ℕ, cterm n) - ((L:ℝ):ℂ) * M).re
      ≤ C * ((q.primeFactors.card : ℝ) + (Real.log L)^2) :=
    le_trans (Complex.re_le_norm _) hbound
  rw [hLHS]
  have hsplit : (∑' n : ℕ, cterm n).re
      = (((L:ℝ):ℂ) * M).re + ((∑' n : ℕ, cterm n) - ((L:ℝ):ℂ) * M).re := by
    rw [Complex.sub_re]; ring
  rw [hsplit]
  linarith only [hmain, herr_le, herr]

end Work.ZeroFreeTables.OffAxis
