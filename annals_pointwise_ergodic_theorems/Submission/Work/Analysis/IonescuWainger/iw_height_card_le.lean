/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.Pset

/-!
# Cardinality of the Ionescu–Wainger arithmetic frequency set

Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals of Math. 195 (2022), Appendix A (`mag-lem`(iii)): the set
`(ℚ/ℤ)_{≤l} = iwArithFreqs ρ l` of arithmetic frequencies of Ionescu–Wainger height at most
`2^l` has cardinality `≲_ρ 2^{2^{ρ l}}`.

The proof formalises the argument of Appendix A.  Writing `(ℚ/ℤ)_{≤l} = ⋃_{q ∈ P_{≤l}} (1/q)ℤ/ℤ`,
the cardinality is at most `Σ_{q ∈ P_{≤l}} q`, and every element of `P_{≤l}` is at most

`Q_0^{(l)} · (2^l)^{D_ρ²}`   with   `Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}`,  `N_0^{(l)} = ⌊2^{ρl/2}⌋ + 1`.

Since `P_{≤l}` is a set of natural numbers contained in `[1, B]` with `B = Q_0^{(l)}·(2^l)^{D_ρ²}`,
both its cardinality and its largest element are at most `B`, so
`# (ℚ/ℤ)_{≤l} ≤ B²`.  The estimate `log₂ B ≤ 2^{ρl}/2` for `l > C⁰_ρ` (which is where the
definition of `iwC0 ρ` is used: `ρ C⁰_ρ ≳ 4/ρ + 12 + 100ρ`) then gives `# (ℚ/ℤ)_{≤l} ≤ 2^{2^{ρl}}`,
while for `l ≤ C⁰_ρ` we simply have `#(ℚ/ℤ)_{≤l} ≤ (2^l)² ≤ 2^{2C⁰_ρ}`.

## Main result

* `Work.Analysis.IonescuWainger.iw_height_card_le`
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

/-! ## 1. Elementary real-analysis bounds

These are the "polynomial growth is beaten by exponential growth" estimates used to compare
`Q_0^{(l)} · (2^l)^{D²}` with `2^{2^{ρl}}`. -/

/-- `log 2 ≥ 1/2`, from `Real.exp_one_lt_three`. -/
private lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have hlt : Real.exp (1 / 2) < 2 := by
    by_contra h
    push_neg at h
    have hmul : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_three, Real.exp_pos (1 / 2)]
  have h := Real.log_lt_log (Real.exp_pos (1 / 2)) hlt
  rw [Real.log_exp] at h
  linarith

/-- `v² ≤ 2^v` for `v ≥ 4` (equality at `v = 4`). -/
private lemma sq_le_two_rpow {v : ℝ} (hv : 4 ≤ v) : v ^ 2 ≤ (2 : ℝ) ^ v := by
  set s : ℝ := v / 4 - 1 with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hveq : v = 4 * (1 + s) := by rw [hs]; ring
  have h1 : (1 + s) ^ 2 ≤ Real.exp (2 * s) := by
    have h := Real.add_one_le_exp s
    have h2 : (1 + s) ^ 2 ≤ (Real.exp s) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h3 : (Real.exp s) ^ 2 = Real.exp (2 * s) := by
      rw [show (2 : ℝ) * s = (2 : ℕ) * s by norm_num, Real.exp_nat_mul]
    rwa [h3] at h2
  have he2 : (Real.exp 1) ^ 2 ≤ 16 := by
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have h4 : Real.exp (2 * s) ≤ (2 : ℝ) ^ (4 * s) := by
    have hexp : Real.exp (2 * s) = ((Real.exp 1) ^ 2) ^ s := by
      rw [Real.exp_mul]
      have h2 : Real.exp 2 = (Real.exp 1) ^ 2 := by simpa using Real.exp_nat_mul 1 2
      rw [h2]
    rw [hexp]
    have h16 : (16 : ℝ) ^ s = (2 : ℝ) ^ (4 * s) := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [← h16]
    exact Real.rpow_le_rpow (by positivity) he2 hs0
  calc v ^ 2 = 16 * (1 + s) ^ 2 := by rw [hveq]; ring
    _ ≤ 16 * Real.exp (2 * s) := by linarith
    _ ≤ 16 * (2 : ℝ) ^ (4 * s) := by linarith
    _ = (2 : ℝ) ^ (4 * (1 + s)) := by
        rw [show (4 : ℝ) * (1 + s) = 4 + 4 * s by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
    _ = (2 : ℝ) ^ v := by rw [hveq]

/-- `2 log₂ v ≤ v` for `v ≥ 4`, in logarithmic form. -/
private lemma two_mul_logb_two_le {v : ℝ} (hv : 4 ≤ v) : 2 * Real.logb 2 v ≤ v := by
  have hv0 : 0 < v := by linarith
  have h := (Real.logb_le_iff_le_rpow (show (1 : ℝ) < 2 by norm_num)
    (by positivity : (0 : ℝ) < v ^ 2)).mpr (sq_le_two_rpow hv)
  rwa [Real.logb_pow] at h

/-- `log₂ s ≤ s/6` for `s ≥ 40` (a consequence of `v² ≤ 2^v`). -/
private lemma logb_two_le_sixth {s : ℝ} (hs : 40 ≤ s) : Real.logb 2 s ≤ s / 6 := by
  have hs0 : 0 < s := by linarith
  set u : ℝ := s / 6 with hu
  have hu6 : 6 ≤ u := by rw [hu]; linarith
  have hsu : s = 6 * u := by rw [hu]; ring
  have h1 : 6 * u ≤ u ^ 2 := by nlinarith
  have h2 : u ^ 2 ≤ (2 : ℝ) ^ u := sq_le_two_rpow (by linarith)
  have h3 : s ≤ (2 : ℝ) ^ (s / 6) := by
    rw [show s / 6 = u from hu.symm, hsu]
    exact le_trans h1 h2
  exact (Real.logb_le_iff_le_rpow (show (1 : ℝ) < 2 by norm_num) hs0).mpr h3

/-- `log₂ x ≤ 6 + x/6` for `x ≥ 1`. -/
private lemma logb_two_le_six_add {x : ℝ} (hx : 1 ≤ x) : Real.logb 2 x ≤ 6 + x / 6 := by
  by_cases h40 : 40 ≤ x
  · linarith [logb_two_le_sixth h40]
  · push_neg at h40
    have hx0 : 0 < x := by linarith
    have hle : Real.logb 2 x ≤ 6 := by
      refine (Real.logb_le_iff_le_rpow (show (1 : ℝ) < 2 by norm_num) hx0).mpr ?_
      have : (2 : ℝ) ^ (6 : ℝ) = 64 := by norm_num
      rw [this]; linarith
    linarith

/-! ## 2. Bounds on `D_ρ = iwD ρ` and the threshold `C⁰_ρ = iwC0 ρ` -/

private lemma iwD_le_two_div_add_one {ρ : ℝ} (hρ : 0 < ρ) : (iwD ρ : ℝ) ≤ 2 / ρ + 1 := by
  have h : ((⌊2 / ρ⌋₊ : ℕ) : ℝ) ≤ 2 / ρ := Nat.floor_le (by positivity)
  rw [iwD, Nat.cast_add, Nat.cast_one]
  linarith

private lemma rho_mul_iwD_le {ρ : ℝ} (hρ : 0 < ρ) : ρ * (iwD ρ : ℝ) ≤ 2 + ρ := by
  have h := iwD_le_two_div_add_one hρ
  have h2 : ρ * (2 / ρ) = 2 := by field_simp
  nlinarith [hρ, h]

private lemma lt_rho_mul_iwD {ρ : ℝ} (hρ : 0 < ρ) : 2 < ρ * (iwD ρ : ℝ) := by
  have h : 2 / ρ < ((⌊2 / ρ⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (2 / ρ)
  have h1 : 2 / ρ < (iwD ρ : ℝ) := by rw [iwD, Nat.cast_add, Nat.cast_one]; linarith
  have h2 : ρ * (2 / ρ) = 2 := by field_simp
  nlinarith [hρ, h1]

private lemma iwD_le_three_of_one_le {ρ : ℝ} (hρ : 1 ≤ ρ) : iwD ρ ≤ 3 := by
  rw [iwD]
  have hρpos : (0 : ℝ) < ρ := by linarith
  have h : ⌊(2 : ℝ) / ρ⌋₊ ≤ 2 := by
    calc ⌊(2 : ℝ) / ρ⌋₊ ≤ ⌊(2 : ℝ)⌋₊ := Nat.floor_mono (by
          rw [div_le_iff₀ hρpos]; linarith)
      _ = 2 := by norm_num
  omega

/-- The lower bound on the threshold: `ρ C⁰_ρ ≥ 4/ρ + 12 + 100ρ`. -/
private lemma iwC0_lower_bound {ρ : ℝ} (hρ : 0 < ρ) :
    4 / ρ + 12 + 100 * ρ ≤ ρ * (iwC0 ρ : ℝ) := by
  have hDpos : 0 < ρ * (iwD ρ : ℝ) := by linarith [hρ, lt_rho_mul_iwD hρ]
  have hεpos : 0 < iwEps ρ := by rw [iwEps]; linarith [lt_rho_mul_iwD hρ]
  have hεle : iwEps ρ ≤ ρ / 2 := by rw [iwEps]; linarith [rho_mul_iwD_le hρ]
  have hA := Nat.le_ceil ((2 / ρ) * ((1 + iwEps ρ) / iwEps ρ))
  have hB := Nat.le_ceil (10 / ρ)
  have hCast : (iwC0 ρ : ℝ) = ((⌈(2 / ρ) * ((1 + iwEps ρ) / iwEps ρ)⌉₊ : ℕ) : ℝ)
      + ((⌈10 / ρ⌉₊ : ℕ) : ℝ) + 100 := by
    rw [iwC0]; push_cast; ring
  have hρA : ρ * ((2 / ρ) * ((1 + iwEps ρ) / iwEps ρ)) = 2 * (1 + iwEps ρ) / iwEps ρ := by
    field_simp
  have htwo : 4 / ρ ≤ 2 / iwEps ρ := by
    rw [div_le_div_iff₀ hρ hεpos]
    linarith
  have hkey : 2 * (1 + iwEps ρ) / iwEps ρ = 2 / iwEps ρ + 2 := by
    field_simp
  calc 4 / ρ + 12 + 100 * ρ
      = 4 / ρ + (2 + 10) + 100 * ρ := by ring
    _ ≤ 2 / iwEps ρ + 2 + 10 + 100 * ρ := by linarith
    _ = ρ * ((2 / ρ) * ((1 + iwEps ρ) / iwEps ρ)) + ρ * (10 / ρ) + ρ * 100 := by
        rw [hρA, hkey]; field_simp
    _ ≤ ρ * (iwC0 ρ : ℝ) := by
        rw [hCast]
        have h1 : (2 / ρ) * ((1 + iwEps ρ) / iwEps ρ) ≤
            ((⌈(2 / ρ) * ((1 + iwEps ρ) / iwEps ρ)⌉₊ : ℕ) : ℝ) := hA
        have h2 : 10 / ρ ≤ ((⌈10 / ρ⌉₊ : ℕ) : ℝ) := hB
        have h3 : ρ * (10 / ρ) = 10 := by field_simp
        nlinarith [hρ, h1, h2, h3]

/-! ## 3. Element bound for `P_{≤l}` -/

private theorem prod_prime_pow_factorization {S : Finset ℕ} {e : ℕ → ℕ}
    (hp : ∀ p ∈ S, p.Prime) (q : ℕ) :
    (S.prod (fun p => p ^ e p)).factorization q = if q ∈ S then e q else 0 := by
  classical
  rw [Nat.factorization_prod_apply (fun x hx => pow_ne_zero _ (hp x hx).ne_zero)]
  have key : ∀ p ∈ S, ((p ^ e p).factorization q) = if p = q then e p else 0 := by
    intro p hp'
    rw [(hp p hp').factorization_pow, Finsupp.single_apply]
  rw [Finset.sum_congr rfl key]
  simp

private theorem iwW_factorization_le {ρ : ℝ} {l w q : ℕ} (hw : w ∈ iwW ρ l) :
    w.factorization q ≤ if q ∈ iwPrimeRange ρ l then iwD ρ else 0 := by
  obtain ⟨hdvd, -⟩ := mem_iwW.mp hw
  classical
  have hle : w.factorization q ≤ (iwProd ρ l).factorization q :=
    Nat.factorization_le_factorization_of_dvd_right hdvd
      (pos_of_mem_iwW hw).ne' (iwProd_ne_zero ρ l)
  have hprod : (iwProd ρ l).factorization q
      = if q ∈ iwPrimeRange ρ l then iwD ρ else 0 :=
    prod_prime_pow_factorization (fun p hp => (Finset.mem_filter.mp hp).2) q
  rw [hprod] at hle; exact hle

/-- An element of `W_{≤l}` is at most `(2^l)^{D_ρ · D_ρ}`. -/
private theorem iwW_le {ρ : ℝ} {l w : ℕ} (hw : w ∈ iwW ρ l) :
    w ≤ (2 ^ l) ^ (iwD ρ * iwD ρ) := by
  classical
  have hw0 : w ≠ 0 := (pos_of_mem_iwW hw).ne'
  have hfact : ∀ p, w.factorization p ≤ iwD ρ := by
    intro p
    have h := iwW_factorization_le hw (q := p)
    split_ifs at h with hmem
    · exact h
    · exact h.trans (Nat.zero_le _)
  have hple : ∀ p ∈ w.factorization.support, p ≤ 2 ^ l := by
    intro p hp
    have hne : w.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    by_cases hmem : p ∈ iwPrimeRange ρ l
    · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).2
    · have h := iwW_factorization_le hw (q := p)
      rw [if_neg hmem] at h
      exact absurd (le_antisymm h (Nat.zero_le _)) hne
  calc w = ∏ p ∈ w.factorization.support, p ^ w.factorization p :=
        (Nat.prod_factorization_pow_eq_self hw0).symm
    _ ≤ ∏ _p ∈ w.factorization.support, (2 ^ l) ^ iwD ρ := by
        refine Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) fun p hp => ?_
        calc p ^ w.factorization p ≤ (2 ^ l) ^ w.factorization p :=
              Nat.pow_le_pow_left (hple p hp) _
          _ ≤ (2 ^ l) ^ iwD ρ := Nat.pow_le_pow_right (by positivity) (hfact p)
    _ = ((2 ^ l) ^ iwD ρ) ^ (w.factorization.support.card) := Finset.prod_const _
    _ ≤ ((2 ^ l) ^ iwD ρ) ^ iwD ρ :=
        Nat.pow_le_pow_right (by positivity) (mem_iwW.mp hw).2
    _ = (2 ^ l) ^ (iwD ρ * iwD ρ) := by rw [pow_mul]

/-- Every element of `P_{≤l}` is at most `Q_0^{(l)} · (2^l)^{D_ρ²}`. -/
private theorem iwP_le_Q0_mul {ρ : ℝ} {l q : ℕ} (hq : q ∈ iwP ρ l) :
    q ≤ iwQ0 ρ l * (2 ^ l) ^ (iwD ρ * iwD ρ) := by
  rw [mem_iwP] at hq
  have hD1 : 1 ≤ iwD ρ * iwD ρ := by
    have : 1 ≤ iwD ρ := by rw [iwD]; exact Nat.le_add_left 1 _
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hQ0 : 1 ≤ iwQ0 ρ l := by
    rw [iwQ0]
    exact Nat.one_le_pow _ _ (Nat.factorial_pos _)
  have hpow : 2 ^ l ≤ (2 ^ l) ^ (iwD ρ * iwD ρ) := by
    simpa using pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 ^ l by exact Nat.one_le_two_pow) hD1
  rcases hq with ⟨-, -, hq2⟩ | ⟨-, hqP⟩
  · calc q ≤ 2 ^ l := hq2
      _ = 1 * 2 ^ l := (one_mul _).symm
      _ ≤ iwQ0 ρ l * (2 ^ l) ^ (iwD ρ * iwD ρ) := Nat.mul_le_mul hQ0 hpow
  · obtain ⟨Q, hQ, w, hw, rfl⟩ := mem_iwPconcrete.mp hqP
    exact Nat.mul_le_mul
      (Nat.le_of_dvd (Nat.pos_of_ne_zero (iwQ0_ne_zero ρ l)) (Nat.mem_divisors.mp hQ).1)
      (iwW_le hw)

/-! ## 4. Cardinality of `(ℚ/ℤ)_{≤l}` in terms of the sum over `P_{≤l}` -/

private theorem iwArithFreqs_card_le_sum (ρ : ℝ) (l : ℕ) :
    (iwArithFreqs ρ l).card ≤ ∑ q ∈ iwP ρ l, q := by
  unfold iwArithFreqs
  calc ((iwP ρ l).biUnion
          (fun q => (Finset.range q).image (fun a : ℕ => ((a : ℝ) / (q : ℝ) : Circle)))).card
      ≤ ∑ q ∈ iwP ρ l,
          ((Finset.range q).image (fun a : ℕ => ((a : ℝ) / (q : ℝ) : Circle))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ q ∈ iwP ρ l, q := by
        refine Finset.sum_le_sum fun q _ => ?_
        calc ((Finset.range q).image (fun a : ℕ => ((a : ℝ) / (q : ℝ) : Circle))).card
            ≤ (Finset.range q).card := Finset.card_image_le
          _ = q := Finset.card_range q

/-- `# (ℚ/ℤ)_{≤l} ≤ B²` where `B = Q_0^{(l)} (2^l)^{D_ρ²}`. -/
private theorem card_le_sq (ρ : ℝ) (l : ℕ) :
    (iwArithFreqs ρ l).card ≤ (iwQ0 ρ l * (2 ^ l) ^ (iwD ρ * iwD ρ)) ^ 2 := by
  set B : ℕ := iwQ0 ρ l * (2 ^ l) ^ (iwD ρ * iwD ρ) with hB
  have hsub : iwP ρ l ⊆ Finset.Icc 1 B := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨pos_of_mem_iwP hq, by rw [hB]; exact iwP_le_Q0_mul hq⟩
  have hcard : (iwP ρ l).card ≤ B := by
    calc (iwP ρ l).card ≤ (Finset.Icc 1 B).card := Finset.card_le_card hsub
      _ = B := by rw [Nat.card_Icc]; omega
  calc (iwArithFreqs ρ l).card ≤ ∑ q ∈ iwP ρ l, q := iwArithFreqs_card_le_sum ρ l
    _ ≤ ∑ q ∈ iwP ρ l, B := Finset.sum_le_sum fun q hq => by rw [hB]; exact iwP_le_Q0_mul hq
    _ = (iwP ρ l).card * B := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ B * B := Nat.mul_le_mul_right B hcard
    _ = B ^ 2 := (pow_two B).symm

/-! ## 5. The numerical comparison -/

/-- `log₂ Q_0^{(l)} ≤ 2 D_ρ 2^{ρl/2} (1 + ρl/2)`. -/
private lemma logb_Q0_le {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) :
    Real.logb 2 (iwQ0 ρ l : ℝ) ≤
      2 * (iwD ρ : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) * (1 + ρ * (l : ℝ) / 2) := by
  set s : ℝ := ρ * (l : ℝ) with hs
  set t : ℝ := (2 : ℝ) ^ (s / 2) with ht
  have ht1 : 1 ≤ t := by rw [ht]; exact Real.one_le_rpow (by norm_num) (by positivity)
  have hN0pos : (0 : ℝ) < (iwN0 ρ l : ℝ) := by
    have : 0 < iwN0 ρ l := by rw [iwN0]; exact Nat.succ_pos _
    exact_mod_cast this
  have hN0one : 1 ≤ iwN0 ρ l := by rw [iwN0]; exact Nat.le_add_left 1 _
  have hN0le : (iwN0 ρ l : ℝ) ≤ 2 * t := by
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le (by positivity)
    have heq : (iwN0 ρ l : ℝ) = ((⌊t⌋₊ : ℕ) : ℝ) + 1 := by
      rw [iwN0, ← ht, Nat.cast_add, Nat.cast_one]
    rw [heq]; linarith
  have hlogN0 : Real.logb 2 (iwN0 ρ l : ℝ) ≤ 1 + s / 2 := by
    refine (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hN0pos).mpr ?_
    have h2 : (2 : ℝ) ^ (1 + s / 2) = 2 * t := by
      rw [show (1 : ℝ) + s / 2 = 1 + s / 2 by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, ht]
    rw [h2]; exact hN0le
  have hfact : Real.logb 2 ((iwN0 ρ l).factorial : ℝ)
      ≤ (iwN0 ρ l : ℝ) * Real.logb 2 (iwN0 ρ l : ℝ) := by
    have hpos : (0 : ℝ) < ((iwN0 ρ l).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hle : ((iwN0 ρ l).factorial : ℝ) ≤ ((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l) := by
      have h := Nat.factorial_le_pow (iwN0 ρ l)
      have h2 : (((iwN0 ρ l).factorial : ℕ) : ℝ) ≤ (((iwN0 ρ l) ^ (iwN0 ρ l) : ℕ) : ℝ) := by
        exact_mod_cast h
      rwa [Nat.cast_pow] at h2
    calc Real.logb 2 ((iwN0 ρ l).factorial : ℝ)
        ≤ Real.logb 2 (((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l)) :=
          (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hpos (by positivity)).mpr hle
      _ = (iwN0 ρ l : ℝ) * Real.logb 2 (iwN0 ρ l : ℝ) := Real.logb_pow 2 _ _
  have hmain : Real.logb 2 (iwQ0 ρ l : ℝ)
      ≤ (iwD ρ : ℝ) * ((2 * t) * (1 + s / 2)) := by
    have hstep : Real.logb 2 (iwQ0 ρ l : ℝ)
        = (iwD ρ : ℝ) * Real.logb 2 ((iwN0 ρ l).factorial : ℝ) := by
      rw [iwQ0, Nat.cast_pow, Real.logb_pow]
    rw [hstep]
    have hnn : (0 : ℝ) ≤ Real.logb 2 (iwN0 ρ l : ℝ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast hN0one)
    have hstep2 : Real.logb 2 ((iwN0 ρ l).factorial : ℝ) ≤ (2 * t) * (1 + s / 2) :=
      calc Real.logb 2 ((iwN0 ρ l).factorial : ℝ)
          ≤ (iwN0 ρ l : ℝ) * Real.logb 2 (iwN0 ρ l : ℝ) := hfact
        _ ≤ (2 * t) * (1 + s / 2) := mul_le_mul hN0le hlogN0 hnn (by positivity)
    exact mul_le_mul_of_nonneg_left hstep2 (by positivity)
  calc Real.logb 2 (iwQ0 ρ l : ℝ) ≤ (iwD ρ : ℝ) * ((2 * t) * (1 + s / 2)) := hmain
    _ = 2 * (iwD ρ : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) * (1 + ρ * (l : ℝ) / 2) := by
        rw [ht, hs]; ring

/-- The case `l > C⁰_ρ` of the cardinality estimate: `(Q_0^{(l)}(2^l)^{D²})² ≤ 2^{2^{ρl}}`. -/
private lemma case2_le {ρ : ℝ} (hρ : 0 < ρ) {l : ℕ} (hl : iwC0 ρ < l) :
    ((iwQ0 ρ l : ℝ) * (2 : ℝ) ^ ((iwD ρ : ℝ) ^ 2 * (l : ℝ))) ^ 2
      ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) := by
  set s : ℝ := ρ * (l : ℝ) with hs
  set D : ℝ := (iwD ρ : ℝ) with hD
  set T : ℝ := (2 : ℝ) ^ (s / 2) with hT
  have hρne : ρ ≠ 0 := hρ.ne'
  -- lower bound on `s`
  have hs1 : 4 / ρ + 12 + 100 * ρ ≤ s := by
    have h1 := iwC0_lower_bound hρ
    have h2 : (l : ℝ) ≥ (iwC0 ρ : ℝ) := by exact_mod_cast (Nat.le_of_lt hl)
    rw [hs]; nlinarith [hρ, h1, h2]
  have hs40 : 40 ≤ s := by
    have h40 : 40 ≤ 4 / ρ + 12 + 100 * ρ := by
      have hkey : (4 : ℝ) / ρ - 40 + 100 * ρ = (2 - 10 * ρ) ^ 2 / ρ := by
        field_simp; ring
      have hnn : 0 ≤ (2 - 10 * ρ) ^ 2 / ρ := div_nonneg (sq_nonneg _) hρ.le
      linarith
    linarith
  have hs2 : 2 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  have hv1 : 1 / ρ ≤ s / 4 := by
    have h4ρ : 4 / ρ ≤ s := by linarith [hs1]
    have h4 : (4 : ℝ) ≤ s * ρ := (div_le_iff₀ hρ).mp h4ρ
    rw [div_le_div_iff₀ hρ (by norm_num : (0 : ℝ) < 4)]
    linarith
  -- `D` bounds
  have hDle : D ≤ 2 / ρ + 1 := by rw [hD]; exact iwD_le_two_div_add_one hρ
  have hD1 : (1 : ℝ) ≤ D := by rw [hD]; exact_mod_cast Nat.le_add_left 1 _
  have hDnn : (0 : ℝ) < D := by linarith
  -- the two exponential estimates
  have hα : 8 * D * (1 + s / 2) ≤ T := by
    rw [hT, ← (Real.logb_le_iff_le_rpow (show (1 : ℝ) < 2 by norm_num)
      (by positivity : (0 : ℝ) < 8 * D * (1 + s / 2)))]
    have hs2' : 1 + s / 2 ≤ s := by linarith
    by_cases hρ1 : ρ ≤ 1
    · have hDle' : D ≤ 3 / ρ := by
        have h2 : (1 : ℝ) ≤ 1 / ρ := by
          rw [le_div_iff₀ hρ]; linarith
        have h3 : (3 : ℝ) / ρ = 2 / ρ + 1 / ρ := by ring
        rw [h3]; linarith
      have h8D : 8 * D ≤ 6 * s := by
        have h4ρ : 4 / ρ ≤ s := by linarith [hs1]
        calc 8 * D ≤ 8 * (3 / ρ) := by linarith
          _ = 6 * (4 / ρ) := by ring
          _ ≤ 6 * s := mul_le_mul_of_nonneg_left h4ρ (by norm_num)
      have hmain : Real.logb 2 (8 * D * (1 + s / 2)) ≤ Real.logb 2 (6 * s ^ 2) := by
        refine (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity)
          (by positivity)).mpr ?_
        calc 8 * D * (1 + s / 2) = (8 * D) * (1 + s / 2) := by ring
          _ ≤ (6 * s) * s := mul_le_mul h8D hs2' (by linarith) (by positivity)
          _ = 6 * s ^ 2 := by ring
      have hsplit : Real.logb 2 (6 * s ^ 2) = Real.logb 2 6 + 2 * Real.logb 2 s := by
        rw [show (6 : ℝ) * s ^ 2 = 6 * s ^ 2 by ring,
          Real.logb_mul (by norm_num) (by positivity), Real.logb_pow]
        ring
      have h6 : Real.logb 2 6 ≤ 3 := by
        have h := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 6)
          (by norm_num : (0 : ℝ) < 8)).mpr (by norm_num : (6 : ℝ) ≤ 8)
        have h8 : Real.logb 2 (8 : ℝ) = 3 := by
          rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.logb_pow,
            Real.logb_self_eq_one (by norm_num)]
          norm_num
        rwa [h8] at h
      have h2s : 2 * Real.logb 2 s ≤ s / 3 := by
        have := logb_two_le_sixth hs40
        linarith
      linarith
    · have hρ1' : (1 : ℝ) ≤ ρ := le_of_lt (not_le.mp hρ1)
      have hD3 : D ≤ 3 := by
        rw [hD]; exact_mod_cast iwD_le_three_of_one_le hρ1'
      have hmain : Real.logb 2 (8 * D * (1 + s / 2)) ≤ Real.logb 2 (24 * s) := by
        refine (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity)
          (by positivity)).mpr ?_
        have : 8 * D ≤ 24 := by linarith
        exact mul_le_mul this hs2' (by linarith) (by positivity)
      have hsplit : Real.logb 2 ((24 : ℝ) * s) = Real.logb 2 24 + Real.logb 2 s :=
        Real.logb_mul (by norm_num) (by positivity)
      have h24 : Real.logb 2 24 ≤ 5 := by
        have h := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 24)
          (by norm_num : (0 : ℝ) < 32)).mpr (by norm_num : (24 : ℝ) ≤ 32)
        have h32 : Real.logb 2 (32 : ℝ) = 5 := by
          rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) by norm_num, Real.logb_pow,
            Real.logb_self_eq_one (by norm_num)]
          norm_num
        rwa [h32] at h
      have h2s : Real.logb 2 s ≤ s / 6 := logb_two_le_sixth hs40
      linarith
  have hβ : 2 * D ^ 2 * s / ρ ≤ (1 / 2) * (2 : ℝ) ^ s := by
    have hhalf : (1 / 2) * (2 : ℝ) ^ s = (2 : ℝ) ^ (s - 1) := by
      rw [show s = s - 1 + 1 by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring
    rw [hhalf, ← (Real.logb_le_iff_le_rpow (show (1 : ℝ) < 2 by norm_num)
      (by positivity : (0 : ℝ) < 2 * D ^ 2 * s / ρ))]
    rw [show 2 * D ^ 2 * s / ρ = (2 * D ^ 2 / ρ) * s from by ring,
      Real.logb_mul (by positivity) (by positivity)]
    by_cases hρ1 : ρ ≤ 1
    · have hDle' : D ≤ 3 / ρ := by
        have h2 : (1 : ℝ) ≤ 1 / ρ := by
          rw [le_div_iff₀ hρ]; linarith
        have h3 : (3 : ℝ) / ρ = 2 / ρ + 1 / ρ := by ring
        rw [h3]; linarith
      have hfac : 2 * D ^ 2 / ρ ≤ 18 / ρ ^ 3 := by
        have h3 : D ^ 2 * ρ ^ 2 ≤ 9 := by
          have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ D) hDle' 2
          have h4 : (3 / ρ : ℝ) ^ 2 = 9 / ρ ^ 2 := by rw [div_pow]; norm_num
          rw [h4, le_div_iff₀ (by positivity : (0 : ℝ) < ρ ^ 2)] at h
          exact h
        rw [div_le_div_iff₀ hρ (by positivity : (0 : ℝ) < ρ ^ 3)]
        nlinarith [h3]
      have hlog1 : Real.logb 2 (2 * D ^ 2 / ρ) ≤ 23 + s / 8 := by
        have h1 : Real.logb 2 (2 * D ^ 2 / ρ) ≤ Real.logb 2 (18 / ρ ^ 3) :=
          (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) (by positivity)).mpr hfac
        have hloginv : Real.logb 2 ρ = -Real.logb 2 (1 / ρ) := by
          have h : Real.logb 2 ρ + Real.logb 2 (1 / ρ) = 0 := by
            rw [← Real.logb_mul (ne_of_gt hρ) (by positivity : (1 / ρ : ℝ) ≠ 0)]
            have h1 : ρ * (1 / ρ) = 1 := by field_simp
            rw [h1, Real.logb_one]
          linarith
        have h2 : Real.logb 2 (18 / ρ ^ 3) = Real.logb 2 18 + 3 * Real.logb 2 (1 / ρ) := by
          rw [Real.logb_div (by norm_num) (by positivity), Real.logb_pow, hloginv]
          ring
        have h3 : Real.logb 2 (1 / ρ) ≤ 6 + 1 / (6 * ρ) := by
          have := logb_two_le_six_add (show (1 : ℝ) ≤ 1 / ρ by rw [le_div_iff₀ hρ]; linarith)
          rwa [show (1 : ℝ) / ρ / 6 = 1 / (6 * ρ) by ring] at this
        have h4 : Real.logb 2 18 ≤ 5 := by
          have h := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 18)
            (by norm_num : (0 : ℝ) < 32)).mpr (by norm_num : (18 : ℝ) ≤ 32)
          have h32 : Real.logb 2 (32 : ℝ) = 5 := by
            rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) by norm_num, Real.logb_pow,
              Real.logb_self_eq_one (by norm_num)]
            norm_num
          rwa [h32] at h
        have h5 : 3 * (6 + 1 / (6 * ρ)) ≤ 18 + s / 8 := by
          have h6 : 3 * (1 / (6 * ρ)) = 1 / (2 * ρ) := by ring_nf
          have h7 : 1 / (2 * ρ) ≤ s / 8 := by
            have h8 : (1 : ℝ) / (2 * ρ) = (1 / 2) * (1 / ρ) := by ring
            have h9 : s / 8 = (1 / 2) * (s / 4) := by ring
            rw [h8, h9]
            exact mul_le_mul_of_nonneg_left hv1 (by norm_num)
          linarith
        linarith
      have h2s : Real.logb 2 s ≤ s / 6 := logb_two_le_sixth hs40
      linarith
    · have hρ1' : (1 : ℝ) ≤ ρ := le_of_lt (not_le.mp hρ1)
      have hD3 : D ≤ 3 := by
        rw [hD]; exact_mod_cast iwD_le_three_of_one_le hρ1'
      have hlog1 : Real.logb 2 (2 * D ^ 2 / ρ) ≤ 5 := by
        have h1 : 2 * D ^ 2 / ρ ≤ 18 := by
          rw [div_le_iff₀ hρ]
          nlinarith [hρ1', hρ, hD3, hDnn]
        have h2 : Real.logb 2 (2 * D ^ 2 / ρ) ≤ Real.logb 2 18 :=
          (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) (by norm_num)).mpr h1
        have h4 : Real.logb 2 18 ≤ 5 := by
          have h := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 18)
            (by norm_num : (0 : ℝ) < 32)).mpr (by norm_num : (18 : ℝ) ≤ 32)
          have h32 : Real.logb 2 (32 : ℝ) = 5 := by
            rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) by norm_num, Real.logb_pow,
              Real.logb_self_eq_one (by norm_num)]
            norm_num
          rwa [h32] at h
        linarith
      have h2s : Real.logb 2 s ≤ s / 6 := logb_two_le_sixth hs40
      linarith
  -- put the pieces together
  have hTsq : T ^ 2 = (2 : ℝ) ^ s := by
    rw [hT, pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2) (s / 2) (s / 2)]
    congr 1
    ring
  have hkey : 2 * (Real.logb 2 (iwQ0 ρ l : ℝ) + (D ^ 2) * (l : ℝ)) ≤ (2 : ℝ) ^ s := by
    have h1 : Real.logb 2 (iwQ0 ρ l : ℝ) ≤ 2 * D * T * (1 + s / 2) := by
      rw [hD, hT, hs]
      exact logb_Q0_le hρ l
    have hD2l : 2 * D ^ 2 * (l : ℝ) = 2 * D ^ 2 * s / ρ := by
      rw [hs]; field_simp
    have hα' : 4 * D * T * (1 + s / 2) ≤ T ^ 2 / 2 := by
      have h := hα
      nlinarith [hT, Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (s / 2)]
    have hβ' : 2 * D ^ 2 * s / ρ ≤ T ^ 2 / 2 := by
      have h := hβ
      rw [← hTsq] at h
      linarith [h]
    linarith [h1, hD2l, hα', hβ']
  have hlogB : Real.logb 2 ((iwQ0 ρ l : ℝ) * (2 : ℝ) ^ (D ^ 2 * (l : ℝ)))
      = Real.logb 2 (iwQ0 ρ l : ℝ) + D ^ 2 * (l : ℝ) := by
    rw [Real.logb_mul (Nat.cast_ne_zero.mpr (iwQ0_ne_zero ρ l))
        (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)),
      Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
  have harg : (0 : ℝ) < ((iwQ0 ρ l : ℝ) * (2 : ℝ) ^ (D ^ 2 * (l : ℝ))) ^ 2 := by
    have h1 : (0 : ℝ) < (iwQ0 ρ l : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (iwQ0_ne_zero ρ l))
    exact pow_pos (mul_pos h1 (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)) 2
  rw [← (Real.logb_le_iff_le_rpow (show (1 : ℝ) < 2 by norm_num) harg)]
  rw [Real.logb_pow, hlogB]
  simpa using hkey

/-! ## 6. The cardinality bound -/

/-- **Ionescu–Wainger cardinality bound** (Krause–Mirek–Tao, Appendix A, `mag-lem`(iii)):
the number of arithmetic frequencies of height at most `2^l` is `≲_ρ 2^{2^{ρl}}`. -/
theorem iw_height_card_le {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ l,
      ((iwArithFreqs ρ l).card : ℝ) ≤ C * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) := by
  refine ⟨(2 : ℝ) ^ (2 * (iwC0 ρ : ℝ)), by positivity, fun l => ?_⟩
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hCnn : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * (iwC0 ρ : ℝ)) := by positivity
  have hC1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * (iwC0 ρ : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  by_cases hl : l ≤ iwC0 ρ
  · have hP : iwP ρ l = Finset.Icc 1 (2 ^ l) := by rw [iwP, if_pos hl]
    have hcard := iwArithFreqs_card_le_sum ρ l
    rw [hP] at hcard
    have hsum : (∑ q ∈ Finset.Icc 1 (2 ^ l), q) ≤ (2 ^ l) * (2 ^ l) := by
      calc (∑ q ∈ Finset.Icc 1 (2 ^ l), q) ≤ ∑ _q ∈ Finset.Icc 1 (2 ^ l), (2 ^ l : ℕ) :=
            Finset.sum_le_sum fun q hq => (Finset.mem_Icc.mp hq).2
        _ = (Finset.Icc 1 (2 ^ l)).card * (2 ^ l) := by rw [Finset.sum_const, smul_eq_mul]
        _ = (2 ^ l) * (2 ^ l) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
    have hcard' : (iwArithFreqs ρ l).card ≤ (2 ^ l) * (2 ^ l) := le_trans hcard hsum
    have hcast : ((iwArithFreqs ρ l).card : ℝ) ≤ (((2 ^ l) * (2 ^ l) : ℕ) : ℝ) := by
      exact_mod_cast hcard'
    have h2l : (((2 ^ l) * (2 ^ l) : ℕ) : ℝ) = (2 : ℝ) ^ (2 * (l : ℝ)) := by
      push_cast
      rw [← pow_add, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have hle : (2 : ℝ) ^ (2 * (l : ℝ)) ≤ (2 : ℝ) ^ (2 * (iwC0 ρ : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have hlR : (l : ℝ) ≤ (iwC0 ρ : ℝ) := by exact_mod_cast hl
        linarith)
    calc ((iwArithFreqs ρ l).card : ℝ) ≤ (((2 ^ l) * (2 ^ l) : ℕ) : ℝ) := hcast
      _ = (2 : ℝ) ^ (2 * (l : ℝ)) := h2l
      _ ≤ (2 : ℝ) ^ (2 * (iwC0 ρ : ℝ)) := hle
      _ ≤ (2 : ℝ) ^ (2 * (iwC0 ρ : ℝ)) * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) :=
          le_mul_of_one_le_right hCnn hone
  · have hl' : iwC0 ρ < l := Nat.lt_of_not_le hl
    have hbound := card_le_sq ρ l
    have hBcast : (((iwQ0 ρ l * (2 ^ l) ^ (iwD ρ * iwD ρ)) : ℕ) : ℝ)
        = (iwQ0 ρ l : ℝ) * (2 : ℝ) ^ ((iwD ρ : ℝ) ^ 2 * (l : ℝ)) := by
      push_cast
      congr 1
      rw [← Real.rpow_natCast (2 : ℝ) l,
        ← Real.rpow_natCast ((2 : ℝ) ^ ((l : ℕ) : ℝ)) (iwD ρ * iwD ρ),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    have hBn : (((iwQ0 ρ l * (2 ^ l) ^ (iwD ρ * iwD ρ)) ^ 2 : ℕ) : ℝ)
        = (((iwQ0 ρ l : ℝ) * (2 : ℝ) ^ ((iwD ρ : ℝ) ^ 2 * (l : ℝ))) ^ 2) := by
      rw [Nat.cast_pow, hBcast]
    have hcast : ((iwArithFreqs ρ l).card : ℝ)
        ≤ (((iwQ0 ρ l * (2 ^ l) ^ (iwD ρ * iwD ρ)) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hbound
    have hfin := case2_le hρ hl'
    calc ((iwArithFreqs ρ l).card : ℝ)
        ≤ (((iwQ0 ρ l * (2 ^ l) ^ (iwD ρ * iwD ρ)) ^ 2 : ℕ) : ℝ) := hcast
      _ = (((iwQ0 ρ l : ℝ) * (2 : ℝ) ^ ((iwD ρ : ℝ) ^ 2 * (l : ℝ))) ^ 2) := hBn
      _ ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) := hfin
      _ ≤ (2 : ℝ) ^ (2 * (iwC0 ρ : ℝ)) * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) :=
          le_mul_of_one_le_left (by positivity) hC1

end Work.Analysis.IonescuWainger
