import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.window_T3_strip_bound
import Submission.Work.FITop4.Red5.gauss_repr_card_le
import Submission.Work.FITop4.Red5.sqfree_divisors_card
import Submission.Work.FITop4.Red5.assembly_helpers

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Membership in `primAnn R`, unfolded. -/
lemma mem_primAnn_iff {R : ℕ} {z : GaussianInt} :
    z ∈ primAnn R ↔ z ∈ Work.FIPlan.gBox (R : ℤ) ∧ 1 ≤ Work.FIPlan.gnorm z ∧
      Work.FIPlan.gnorm z ≤ R ∧ Work.FIPlan.IsPrimary z := by
  simp only [primAnn, Finset.mem_filter]; tauto

/-- The `gnorm`-fibre of `primAnn (2N)` has at most `4 d(n)` elements. -/
lemma fiber_card_primAnn_le {N n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ 2 * N) :
    ((primAnn (2 * N)).filter (fun z => Work.FIPlan.gnorm z = n)).card ≤ 4 * n.divisors.card := by
  have hsub : (primAnn (2 * N)).filter (fun z => Work.FIPlan.gnorm z = n)
      ⊆ (Work.FIPlan.gBox (((2 * N : ℕ)) : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨(mem_primAnn_iff.mp hz.1).1, hz.2⟩
  have h2N1 : 1 ≤ 2 * N := by omega
  have hR : n ≤ (2 * N) ^ 2 := by
    calc n ≤ 2 * N := hn2
      _ ≤ (2 * N) * (2 * N) := by
          calc 2 * N = (2 * N) * 1 := (mul_one _).symm
            _ ≤ (2 * N) * (2 * N) := Nat.mul_le_mul_left _ h2N1
      _ = (2 * N) ^ 2 := (pow_two _).symm
  calc ((primAnn (2 * N)).filter (fun z => Work.FIPlan.gnorm z = n)).card
      ≤ ((Work.FIPlan.gBox ((2 * N : ℕ) : ℤ)).filter
          (fun z => Work.FIPlan.gnorm z = n)).card := Finset.card_le_card hsub
    _ = ((Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter
          (fun z => Work.FIPlan.gnorm z = n)).card := by
          rw [gBox_filter_gnorm_eq' hn1 hR]
    _ ≤ 4 * n.divisors.card := gauss_repr_card_le n hn1

/-- `|μ(n)| d(n)² ≤ 4^{ω(n)}`. -/
lemma abs_moebius_mul_card_sq_le (n : ℕ) :
    |(ArithmeticFunction.moebius n : ℝ)|
        * ((n.divisors.card : ℕ) : ℝ) * ((n.divisors.card : ℕ) : ℝ)
      ≤ (4 : ℝ) ^ n.primeFactors.card := by
  by_cases h : Squarefree n
  · have hmu : |(ArithmeticFunction.moebius n : ℝ)| = 1 := by
      rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree h]
      norm_num
    have hd : ((n.divisors.card : ℕ) : ℝ) = (2:ℝ) ^ n.primeFactors.card := by
      rw [sqfree_divisors_card n h, Nat.cast_pow, Nat.cast_ofNat]
    rw [hmu, hd, one_mul]
    rw [← pow_add,
      show n.primeFactors.card + n.primeFactors.card = 2 * n.primeFactors.card from by ring,
      pow_mul]
    norm_num
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    simp only [Int.cast_zero, abs_zero, zero_mul]
    positivity

/-- The termwise reduction of one strip's contribution to the two boundary strips. -/
lemma real_term_le_strips {M : ℝ} {θ u s w : ℝ}
    (hs0 : 0 ≤ s) (hw0 : 0 ≤ w)
    (hu2 : u ≤ 2 * M)
    (hmid : M + θ * M / 2 < u → u ≤ 2 * M - 2 * θ * M → s = 1) :
    (if M < u then (1:ℝ) else 0) * (1 - s) * w
      ≤ (if M < u ∧ u ≤ M + θ * M / 2 then w else 0)
        + (if 2 * M - 2 * θ * M < u ∧ u ≤ 2 * M then w else 0) := by
  have hL : (1:ℝ) * (1 - s) * w ≤ w := by
    have h1s : 1 - s ≤ 1 := by linarith
    calc (1:ℝ)*(1-s)*w = (1-s)*w := by ring
      _ ≤ 1*w := mul_le_mul_of_nonneg_right h1s hw0
      _ = w := by ring
  by_cases h1 : M < u
  · rw [if_pos h1]
    by_cases h2 : u ≤ M + θ * M / 2
    · have hc : (M < u ∧ u ≤ M + θ * M / 2) := ⟨h1, h2⟩
      have hf : (if M < u ∧ u ≤ M + θ * M / 2 then w else 0) = w := if_pos hc
      have hb : (0:ℝ) ≤ (if 2*M - 2*θ*M < u ∧ u ≤ 2*M then w else 0) := by
        by_cases hh : 2*M - 2*θ*M < u ∧ u ≤ 2*M <;> simp [hh, hw0]
      rw [hf]; linarith
    · by_cases h3 : 2*M - 2*θ*M < u
      · have hc : (2*M - 2*θ*M < u ∧ u ≤ 2*M) := ⟨h3, hu2⟩
        have hf : (if 2*M - 2*θ*M < u ∧ u ≤ 2*M then w else 0) = w := if_pos hc
        have hb : (0:ℝ) ≤ (if M < u ∧ u ≤ M + θ * M / 2 then w else 0) := by
          by_cases hh : M < u ∧ u ≤ M + θ * M / 2 <;> simp [hh, hw0]
        rw [hf]; linarith
      · have hle : u ≤ 2 * M - 2 * θ * M := not_lt.mp h3
        have hs1 : s = 1 := hmid (by linarith) hle
        rw [hs1]
        have hb : (0:ℝ) ≤ (if M < u ∧ u ≤ M + θ * M / 2 then w else 0) := by
          by_cases hh : M < u ∧ u ≤ M + θ * M / 2 <;> simp [hh, hw0]
        have hb2 : (0:ℝ) ≤ (if 2*M - 2*θ*M < u ∧ u ≤ 2*M then w else 0) := by
          by_cases hh : 2*M - 2*θ*M < u ∧ u ≤ 2*M <;> simp [hh, hw0]
        have : (1:ℝ) * (1 - 1) * w = 0 := by ring
        rw [this]; linarith
  · rw [if_neg h1]
    have hb : (0:ℝ) ≤ (if M < u ∧ u ≤ M + θ * M / 2 then w else 0) := by
      by_cases hh : M < u ∧ u ≤ M + θ * M / 2 <;> simp [hh, hw0]
    have hb2 : (0:ℝ) ≤ (if 2*M - 2*θ*M < u ∧ u ≤ 2*M then w else 0) := by
      by_cases hh : 2*M - 2*θ*M < u ∧ u ≤ 2*M <;> simp [hh, hw0]
    simp only [zero_mul]
    linarith

/-- One strip's weight sum, reduced to `∑ 4^{ω(n)}` over the corresponding integer interval. -/
lemma primAnn_weight_le (N X H : ℕ) (C0 Cb : ℝ)
    (hC0nn : 0 ≤ C0) (hCbnn : 0 ≤ Cb) (hH : (H : ℝ) ≤ Cb)
    (hlog : (X : ℝ) + (H : ℝ) + 2 ≤ 2 * (N : ℝ) + 2)
    (hC0 : (∑ n ∈ Finset.Icc (X + 1) (X + H), (4 : ℝ) ^ n.primeFactors.card)
        ≤ C0 * (H : ℝ) * (Real.log ((X : ℝ) + (H : ℝ) + 2)) ^ 100)
    (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ n : ℕ, P n → X + 1 ≤ n ∧ n ≤ X + H) :
    (∑ z ∈ primAnn (2 * N),
        (if P (Work.FIPlan.gnorm z) then
          |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) else 0))
      ≤ 4 * C0 * Cb * (Real.log (2 * (N : ℝ) + 2)) ^ 100 := by
  classical
  have hmaps : ∀ z ∈ primAnn (2 * N), Work.FIPlan.gnorm z ∈ Finset.Icc 1 (2 * N) := by
    intro z hz
    rw [mem_primAnn_iff] at hz
    exact Finset.mem_Icc.mpr ⟨hz.2.1, hz.2.2.1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun z => (if P (Work.FIPlan.gnorm z) then
          |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) else 0))]
  have hstep : ∀ n ∈ Finset.Icc 1 (2 * N),
      (∑ z ∈ (primAnn (2 * N)).filter (fun z => Work.FIPlan.gnorm z = n),
        (if P (Work.FIPlan.gnorm z) then
          |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) else 0))
      ≤ 4 * (if P n then (4 : ℝ) ^ n.primeFactors.card else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hconst : ∀ z ∈ (primAnn (2 * N)).filter (fun z => Work.FIPlan.gnorm z = n),
        (if P (Work.FIPlan.gnorm z) then
          |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) else 0)
        = (if P n then |(ArithmeticFunction.moebius n : ℝ)|
            * (((n.divisors.card : ℕ) : ℝ)) else 0) := by
      intro z hz
      rw [Finset.mem_filter] at hz
      rw [hz.2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hcard := fiber_card_primAnn_le hn.1 hn.2
    have hcardR : (((primAnn (2 * N)).filter (fun z => Work.FIPlan.gnorm z = n)).card : ℝ)
        ≤ 4 * ((n.divisors.card : ℕ) : ℝ) := by exact_mod_cast hcard
    have hA0 : 0 ≤ (if P n then |(ArithmeticFunction.moebius n : ℝ)|
        * (((n.divisors.card : ℕ) : ℝ)) else 0) := by
      by_cases hh : P n <;> simp [hh]; positivity
    calc (((primAnn (2 * N)).filter (fun z => Work.FIPlan.gnorm z = n)).card : ℝ)
            * (if P n then |(ArithmeticFunction.moebius n : ℝ)|
                * (((n.divisors.card : ℕ) : ℝ)) else 0)
        ≤ (4 * ((n.divisors.card : ℕ) : ℝ))
            * (if P n then |(ArithmeticFunction.moebius n : ℝ)|
                * (((n.divisors.card : ℕ) : ℝ)) else 0) :=
          mul_le_mul_of_nonneg_right hcardR hA0
      _ = 4 * (if P n then (|(ArithmeticFunction.moebius n : ℝ)|
                * (((n.divisors.card : ℕ) : ℝ))) * (((n.divisors.card : ℕ) : ℝ)) else 0) := by
          by_cases hh : P n <;> simp [hh]; ring
      _ ≤ 4 * (if P n then (4 : ℝ) ^ n.primeFactors.card else 0) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          by_cases hh : P n
          · simp only [if_pos hh]
            exact abs_moebius_mul_card_sq_le n
          · simp only [if_neg hh, le_refl]
  calc (∑ n ∈ Finset.Icc 1 (2 * N),
          (∑ z ∈ (primAnn (2 * N)).filter (fun z => Work.FIPlan.gnorm z = n),
            (if P (Work.FIPlan.gnorm z) then
              |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
                * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) else 0)))
      ≤ ∑ n ∈ Finset.Icc 1 (2 * N),
          4 * (if P n then (4 : ℝ) ^ n.primeFactors.card else 0) := Finset.sum_le_sum hstep
    _ = 4 * ∑ n ∈ Finset.Icc 1 (2 * N),
          (if P n then (4 : ℝ) ^ n.primeFactors.card else 0) := by rw [Finset.mul_sum]
    _ = 4 * ∑ n ∈ (Finset.Icc 1 (2 * N)).filter P, (4 : ℝ) ^ n.primeFactors.card := by
          rw [← Finset.sum_filter]
    _ ≤ 4 * ∑ n ∈ Finset.Icc (X + 1) (X + H), (4 : ℝ) ^ n.primeFactors.card := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => by positivity)
          rw [Finset.mem_filter] at hn
          exact Finset.mem_Icc.mpr (hP n hn.2)
    _ ≤ 4 * (C0 * (H : ℝ) * (Real.log ((X : ℝ) + (H : ℝ) + 2)) ^ 100) :=
          mul_le_mul_of_nonneg_left hC0 (by norm_num)
    _ ≤ 4 * C0 * Cb * (Real.log (2 * (N : ℝ) + 2)) ^ 100 := by
          have hLnn : 0 ≤ (Real.log ((X : ℝ) + (H : ℝ) + 2)) ^ 100 := by positivity
          have hLle : (Real.log ((X : ℝ) + (H : ℝ) + 2)) ^ 100
              ≤ (Real.log (2 * (N : ℝ) + 2)) ^ 100 := by
            apply pow_le_pow_left₀ (Real.log_nonneg (by linarith))
            exact Real.log_le_log (by positivity) hlog
          have h1 : 4 * C0 * (H : ℝ) ≤ 4 * C0 * Cb := by nlinarith [hH, hC0nn]
          calc 4 * (C0 * (H : ℝ) * (Real.log ((X : ℝ) + (H : ℝ) + 2)) ^ 100)
              = (4 * C0 * (H : ℝ)) * (Real.log ((X : ℝ) + (H : ℝ) + 2)) ^ 100 := by ring
            _ ≤ (4 * C0 * Cb) * (Real.log ((X : ℝ) + (H : ℝ) + 2)) ^ 100 :=
                mul_le_mul_of_nonneg_right h1 hLnn
            _ ≤ (4 * C0 * Cb) * (Real.log (2 * (N : ℝ) + 2)) ^ 100 :=
                mul_le_mul_of_nonneg_left hLle (by nlinarith [hC0nn, hCbnn])
            _ = 4 * C0 * Cb * (Real.log (2 * (N : ℝ) + 2)) ^ 100 := by ring

theorem window_T3_weight_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (θ : ℝ) (K : ℕ) (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ),
      (1 ≤ N) → (0 < θ) → (θ ≤ 1/4) → (1 ≤ θ * (N : ℝ) ^ ((1:ℝ)/2)) →
      (∀ i, (N : ℝ) ≤ a i) →
      (∀ i u, 0 ≤ p i u) →
      (∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) →
      (∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1) →
      (∀ u, (N : ℝ) + θ * (N : ℝ) / 2 < u → u ≤ 2 * (N : ℝ) - 2 * θ * (N : ℝ) →
          (∑ i, p i u) = 1) →
      (∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
          (if (N : ℝ) < (Work.FIPlan.gnorm z : ℝ) then (1:ℝ) else 0)
            * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
        ≤ C * θ * (N : ℝ) * (Real.log (2 * (N : ℝ) + 2)) ^ (100 : ℕ) := by
  obtain ⟨C0, hC0pos, hC0raw⟩ := window_T3_strip_bound
  refine ⟨20 * C0 + 1, by linarith, ?_⟩
  intro N θ K a p hN hθ hθ4 hθN hai hp0 hpsup hp1 hp2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hsqN : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqroot : (N : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (N : ℝ) := (Real.sqrt_eq_rpow N).symm
  have hθsqrt : 1 ≤ θ * Real.sqrt (N : ℝ) := by
    have h := hθN; rw [hsqroot] at h; exact h
  have hθNge : Real.sqrt (N : ℝ) ≤ θ * (N : ℝ) := by
    have hstep : θ * (N : ℝ) = (θ * Real.sqrt (N : ℝ)) * Real.sqrt (N : ℝ) := by
      conv_lhs => rw [← hsqN]
      ring
    rw [hstep]
    calc Real.sqrt (N : ℝ) = 1 * Real.sqrt (N : ℝ) := (one_mul _).symm
      _ ≤ (θ * Real.sqrt (N : ℝ)) * Real.sqrt (N : ℝ) :=
          mul_le_mul_of_nonneg_right hθsqrt (le_of_lt hsqrtN_pos)
  have hθN1 : 1 ≤ θ * (N : ℝ) :=
    le_trans (Real.one_le_sqrt.mpr hN1) hθNge
  have hN16 : (16 : ℝ) ≤ (N : ℝ) := by
    have h2 : (4 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      have h1 : (1 : ℝ) / θ ≤ Real.sqrt (N : ℝ) := (div_le_iff₀ hθ).mpr (by linarith [hθsqrt])
      have h3 : (4 : ℝ) ≤ 1 / θ := (le_div_iff₀ hθ).mpr (by nlinarith [hθ4])
      linarith
    nlinarith [h2, hsqN]
  -- ================= strip 1 =================
  set H1 : ℕ := ⌈θ * (N : ℝ) / 2⌉₊ with hH1def
  have hH1_le : θ * (N : ℝ) / 2 ≤ (H1 : ℝ) := Nat.le_ceil _
  have hH1_lt : (H1 : ℝ) < θ * (N : ℝ) / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hH1_le2 : (H1 : ℝ) ≤ 2 * (θ * (N : ℝ)) := by linarith [hH1_lt, hθN1]
  have hH1_leN : (H1 : ℝ) ≤ (N : ℝ) := by
    have h1 : θ * (N : ℝ) / 2 ≤ (N : ℝ) / 8 := by nlinarith [hθ4, hNpos]
    have h2 : (N : ℝ) / 8 + 1 ≤ (N : ℝ) := by nlinarith [hN16]
    linarith [hH1_lt, h1, h2]
  have hH1_ge_sqrt : Real.sqrt (N : ℝ) / 2 ≤ (H1 : ℝ) := by linarith [hH1_le, hθNge]
  have hXH1 : N ≤ 4 * H1 * H1 := by
    have hreal : (N : ℝ) ≤ ((4 * H1 * H1 : ℕ) : ℝ) := by
      have h0 : (N : ℝ) ≤ 4 * (H1 : ℝ) * (H1 : ℝ) := by
        have h1 : (Real.sqrt (N : ℝ) / 2) ^ 2 ≤ (H1 : ℝ) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hH1_ge_sqrt 2
        have h2 : (Real.sqrt (N : ℝ) / 2) ^ 2 = (N : ℝ) / 4 := by
          rw [div_pow, hsqN]; norm_num
        nlinarith [h1, h2]
      push_cast; linarith [h0]
    exact_mod_cast hreal
  have hlog1 : (N : ℝ) + (H1 : ℝ) + 2 ≤ 2 * (N : ℝ) + 2 := by linarith [hH1_leN]
  have hP1 : ∀ n : ℕ, ((N : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ) + θ * (N : ℝ) / 2) →
      N + 1 ≤ n ∧ n ≤ N + H1 := by
    intro n hn
    obtain ⟨h1, h2⟩ := hn
    constructor
    · have : N < n := by exact_mod_cast h1
      omega
    · have h2' : (n : ℝ) ≤ (N : ℝ) + (H1 : ℝ) := by linarith [h2, hH1_le]
      exact_mod_cast h2'
  -- ================= strip 2 =================
  set H2 : ℕ := ⌈2 * (θ * (N : ℝ))⌉₊ with hH2def
  set X2 : ℕ := 2 * N - H2 with hX2def
  have hH2_le : 2 * (θ * (N : ℝ)) ≤ (H2 : ℝ) := Nat.le_ceil _
  have hH2_lt : (H2 : ℝ) < 2 * (θ * (N : ℝ)) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hH2_le2N : H2 ≤ 2 * N := by
    have hlt : (H2 : ℝ) < (2 * N : ℝ) := by nlinarith [hH2_lt, hθ4, hN1]
    have hlt2 : H2 < 2 * N := by exact_mod_cast hlt
    omega
  have hH2_le3 : (H2 : ℝ) ≤ 3 * (θ * (N : ℝ)) := by linarith [hH2_lt, hθN1]
  have hX2_eq : X2 + H2 = 2 * N := by rw [hX2def]; exact Nat.sub_add_cancel hH2_le2N
  have hX2_cast : (X2 : ℝ) = 2 * (N : ℝ) - (H2 : ℝ) := by
    rw [hX2def, Nat.cast_sub (R := ℝ) hH2_le2N]; push_cast; ring
  have hlog2 : (X2 : ℝ) + (H2 : ℝ) + 2 ≤ 2 * (N : ℝ) + 2 := by linarith [hX2_cast]
  have hXH2 : X2 ≤ 4 * H2 * H2 := by
    have hreal : (X2 : ℝ) ≤ ((4 * H2 * H2 : ℕ) : ℝ) := by
      have h0 : (X2 : ℝ) ≤ 4 * (H2 : ℝ) * (H2 : ℝ) := by
        have hH2ge2 : (2 : ℝ) * Real.sqrt (N : ℝ) ≤ (H2 : ℝ) := by linarith [hH2_le, hθNge]
        have hge : (2 * Real.sqrt (N : ℝ)) ^ 2 ≤ (H2 : ℝ) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hH2ge2 2
        have h2sq : (2 * Real.sqrt (N : ℝ)) ^ 2 = 4 * (N : ℝ) := by
          rw [mul_pow, hsqN]; norm_num
        have hle2N : (X2 : ℝ) ≤ 2 * (N : ℝ) := by
          have : X2 ≤ 2 * N := by rw [hX2def]; exact Nat.sub_le _ _
          exact_mod_cast this
        nlinarith [hge, h2sq, hle2N]
      push_cast; linarith [h0]
    exact_mod_cast hreal
  have hP2 : ∀ n : ℕ, (2 * (N : ℝ) - 2 * θ * (N : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ 2 * (N : ℝ)) →
      X2 + 1 ≤ n ∧ n ≤ X2 + H2 := by
    intro n hn
    obtain ⟨h1, h2⟩ := hn
    constructor
    · have hX2le : (X2 : ℝ) ≤ 2 * (N : ℝ) - 2 * θ * (N : ℝ) := by
        rw [hX2_cast]; nlinarith [hH2_le]
      have : (X2 : ℝ) < (n : ℝ) := by linarith
      have hlt : X2 < n := by exact_mod_cast this
      omega
    · rw [hX2_eq]; exact_mod_cast h2
  -- ================= termwise =================
  have hpt : ∀ z ∈ primAnn (2 * N),
      (if (N : ℝ) < (Work.FIPlan.gnorm z : ℝ) then (1:ℝ) else 0)
          * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
          * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
        ≤ (if ((N : ℝ) < (Work.FIPlan.gnorm z : ℝ) ∧
              (Work.FIPlan.gnorm z : ℝ) ≤ (N : ℝ) + θ * (N : ℝ) / 2) then
              |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
                * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) else 0)
          + (if (2 * (N : ℝ) - 2 * θ * (N : ℝ) < (Work.FIPlan.gnorm z : ℝ) ∧
              (Work.FIPlan.gnorm z : ℝ) ≤ 2 * (N : ℝ)) then
              |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
                * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) else 0) := by
    intro z hz
    rw [mem_primAnn_iff] at hz
    have hz2 : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hz.2.2.1
    have hs : 0 ≤ ∑ i, p i (Work.FIPlan.gnorm z) := Finset.sum_nonneg (fun i _ => hp0 i _)
    have hw : 0 ≤ |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by positivity
    have hmid' : (N : ℝ) + θ * (N : ℝ) / 2 < (Work.FIPlan.gnorm z : ℝ) →
        (Work.FIPlan.gnorm z : ℝ) ≤ 2 * (N : ℝ) - 2 * θ * (N : ℝ) →
        (∑ i, p i (Work.FIPlan.gnorm z)) = 1 :=
      fun h1 h2 => hp2 (Work.FIPlan.gnorm z : ℝ) h1 h2
    have h := real_term_le_strips hs hw hz2 hmid'
    rw [mul_assoc]
    exact h
  -- ================= the two strip bounds =================
  have hA := primAnn_weight_le N N H1 C0 (2 * (θ * (N : ℝ))) hC0pos.le (by positivity)
      hH1_le2 hlog1 (hC0raw N H1 hXH1)
      (fun n : ℕ => (N : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ) + θ * (N : ℝ) / 2) hP1
  have hB := primAnn_weight_le N X2 H2 C0 (3 * (θ * (N : ℝ))) hC0pos.le (by positivity)
      hH2_le3 hlog2 (hC0raw X2 H2 hXH2)
      (fun n : ℕ => 2 * (N : ℝ) - 2 * θ * (N : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ 2 * (N : ℝ)) hP2
  have hLnn : 0 ≤ (Real.log (2 * (N : ℝ) + 2)) ^ (100 : ℕ) := by positivity
  have hmain : (∑ z ∈ primAnn (2 * N),
        (if (N : ℝ) < (Work.FIPlan.gnorm z : ℝ) then (1:ℝ) else 0)
          * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
          * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ 20 * C0 * θ * (N : ℝ) * (Real.log (2 * (N : ℝ) + 2)) ^ (100 : ℕ) := by
    have hle := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib] at hle
    have heq : 4 * C0 * (2 * (θ * (N : ℝ))) * (Real.log (2 * (N : ℝ) + 2)) ^ (100 : ℕ)
        + 4 * C0 * (3 * (θ * (N : ℝ))) * (Real.log (2 * (N : ℝ) + 2)) ^ (100 : ℕ)
        = 20 * C0 * θ * (N : ℝ) * (Real.log (2 * (N : ℝ) + 2)) ^ (100 : ℕ) := by ring
    exact le_trans hle (le_trans (add_le_add hA hB) heq.le)
  have hfin : 20 * C0 * θ * (N : ℝ) * (Real.log (2 * (N : ℝ) + 2)) ^ (100 : ℕ)
      ≤ (20 * C0 + 1) * θ * (N : ℝ) * (Real.log (2 * (N : ℝ) + 2)) ^ (100 : ℕ) := by
    have hprod : 0 ≤ θ * (N : ℝ) * (Real.log (2 * (N : ℝ) + 2)) ^ (100 : ℕ) := by positivity
    nlinarith [hprod]
  linarith [hmain, hfin]

end

end Work.FITop4.Red5
