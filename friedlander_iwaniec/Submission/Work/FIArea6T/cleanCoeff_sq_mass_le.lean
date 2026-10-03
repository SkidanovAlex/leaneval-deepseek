/-
# `Submission.Work.FIArea6T.cleanCoeff_sq_mass_le` — T3: the L²-mass of a clean coefficient

For a clean coefficient `β` of *FI* (5.13) with (5.7)+(5.8) (`Work.FITop4.IsCleanCoeff6`) the
second moment over the inner box `boxN Pa = FIPlan.gBox (radN Pa)` is `O(N log⁷(2+N))`.  This is
the `A`-factor of the τ-removal: with T2 (`TcutBil_le_polar`) and T4 (`cleanTau_mass_le`) it gives
the `L²` Schur bound of *FI* (10.4),

  `‖Tcut (tauCut β) − Tcut β‖ ≤ 3·Λ·‖β‖₂‖δ‖₂`.

The proof is the elementary fibre count: `‖β z‖ ≤ τ(|z|²)`
(`Work.FIArea6T.IsCleanCoeff6.norm_le_tau`), every `z ∈ boxN Pa` has `|z|² ≤ 18N`
(`Work.FIArea4.a6_mem_boxN_gnorm_le`), the fibre of `z ↦ |z|²` over `n` has at most `4τ(n)` points
(`Commons.NumberTheory.GaussianInt.elemF`), and `Σ_{n ≤ y} τ(n)³ ≤ y(1+log y)⁷`
(`Work.FIArea7.sum_tau_pow_le 3`).
-/
import Mathlib
import Submission.Work.FIArea6T.Defs
import Submission.Work.FIArea4.A6Crude
import Submission.Work.FIArea7.sum_tau_pow_le
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos

set_option autoImplicit false

namespace Work.FIArea6T

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The two-squares fibre bound.**  At most `4τ(n)` Gaussian integers of norm exactly `n`
inside any set (`r₂(n) ≤ 4 d(n)`). -/
private lemma fibre_gnorm_card_le (n : ℕ) (hn1 : 1 ≤ n) (S : Finset GaussianInt) :
    (S.filter (fun z => Work.FIPlan.gnorm z = n)).card ≤ 4 * n.divisors.card := by
  have hsub : S.filter (fun z => Work.FIPlan.gnorm z = n)
      ⊆ Commons.NumberTheory.GaussianInt.elemF n := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Commons.NumberTheory.GaussianInt.mem_elemF hn1 z]
    exact hz.2
  calc (S.filter (fun z => Work.FIPlan.gnorm z = n)).card
      ≤ (Commons.NumberTheory.GaussianInt.elemF n).card := Finset.card_le_card hsub
    _ = (Commons.NumberTheory.GaussianInt.targetF n).card :=
        (Commons.NumberTheory.GaussianInt.targetF_card_eq_elemF_card n).symm
    _ ≤ 4 * n.divisors.card := by
        have h := Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos n hn1
        exact_mod_cast h

/-- `τ(0) = 0`. -/
private lemma divisors_card_zero : Nat.divisors 0 = ∅ := by
  rw [Nat.divisors]
  simp

/-- **T3 — the L²-mass of a clean coefficient.** -/
theorem cleanCoeff_sq_mass_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt)
      (β : GaussianInt → ℂ), Work.FITop4.IsCleanCoeff6 Pa φ z0 β →
      ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2
        ≤ C * Pa.N * (Real.log (2 + Pa.N)) ^ 7 := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro Pa φ z0 β hβ
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
  set s : Finset GaussianInt := Work.FITop.boxN Pa with hs
  set M : ℕ := ⌊18 * Pa.N⌋₊ with hM
  -- (1) pointwise: `‖β z‖ ≤ τ(|z|²)`
  have hstep1 : ∑ z ∈ s, ‖β z‖ ^ 2
      ≤ ∑ z ∈ s, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro z _
    exact pow_le_pow_left₀ (norm_nonneg _)
      (Work.FIArea6T.IsCleanCoeff6.norm_le_tau hβ z) 2
  -- (2) the fibre grouping
  have hmem : ∀ z ∈ s, Work.FIPlan.gnorm z ∈ Finset.Icc 0 M := by
    intro z hz
    rw [Finset.mem_Icc]
    refine ⟨Nat.zero_le _, ?_⟩
    rw [hM]
    refine Nat.le_floor ?_
    exact Work.FIArea4.a6_mem_boxN_gnorm_le Pa hz
  have hinner : ∀ n : ℕ,
      ∑ z ∈ s.filter (fun z => Work.FIPlan.gnorm z = n),
          (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2
        = (((s.filter (fun z => Work.FIPlan.gnorm z = n)).card : ℕ) : ℝ)
            * (((n.divisors.card : ℕ) : ℝ) ^ 2) := by
    intro n
    rw [Finset.sum_congr rfl (fun z hz => by rw [(Finset.mem_filter.mp hz).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hstep2 : ∑ z ∈ s, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2
      = ∑ n ∈ Finset.Icc 0 M,
          (((s.filter (fun z => Work.FIPlan.gnorm z = n)).card : ℕ) : ℝ)
            * (((n.divisors.card : ℕ) : ℝ) ^ 2) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := Finset.Icc 0 M)
      (g := fun z : GaussianInt => Work.FIPlan.gnorm z) hmem
      (f := fun z : GaussianInt => (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2)]
    exact Finset.sum_congr rfl (fun n _ => hinner n)
  -- (3) the fibre bound, pointwise in `n`, and the τ³ moment
  have hstep3 : ∑ n ∈ Finset.Icc 0 M,
        (((s.filter (fun z => Work.FIPlan.gnorm z = n)).card : ℕ) : ℝ)
          * (((n.divisors.card : ℕ) : ℝ) ^ 2)
      ≤ 4 * ∑ n ∈ Finset.Icc 0 M, (((n.divisors.card : ℕ) : ℝ) ^ 3) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0, divisors_card_zero]
      simp
    · have hfib : (((s.filter (fun z => Work.FIPlan.gnorm z = n)).card : ℕ) : ℝ)
          ≤ 4 * ((n.divisors.card : ℕ) : ℝ) := by
        have := fibre_gnorm_card_le n hnpos s
        exact_mod_cast this
      have h2 : (0 : ℝ) ≤ (((n.divisors.card : ℕ) : ℝ)) ^ 2 := by positivity
      calc (((s.filter (fun z => Work.FIPlan.gnorm z = n)).card : ℕ) : ℝ)
            * (((n.divisors.card : ℕ) : ℝ) ^ 2)
          ≤ (4 * ((n.divisors.card : ℕ) : ℝ)) * (((n.divisors.card : ℕ) : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hfib h2
        _ = 4 * (((n.divisors.card : ℕ) : ℝ) ^ 3) := by ring
  -- (4) `τ(0) = 0` lets us start the Icc-sum at `1`, and the moment bound applies
  have hstep4 : ∑ n ∈ Finset.Icc 0 M, (((n.divisors.card : ℕ) : ℝ) ^ 3)
      ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7 := by
    have hf0 : ((((0 : ℕ)).divisors.card : ℕ) : ℝ) ^ 3 = 0 := by
      rw [divisors_card_zero]; simp
    have hsplit : ∑ n ∈ Finset.Icc 0 M, (((n.divisors.card : ℕ) : ℝ) ^ 3)
        = ((((0 : ℕ)).divisors.card : ℕ) : ℝ) ^ 3
          + ∑ n ∈ Finset.Icc 1 M, (((n.divisors.card : ℕ) : ℝ) ^ 3) := by
      rcases Nat.eq_zero_or_pos M with hM0 | hMpos
      · rw [hM0]; simp
      · have : Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
          ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [this, Finset.sum_insert (by simp)]
    rw [hsplit, hf0, zero_add]
    have h := Work.FIArea7.sum_tau_pow_le 3 M
    rw [show (2 : ℕ) ^ 3 - 1 = 7 from rfl] at h
    linarith [h]
  -- (5) the arithmetic
  have hlog2N1 : (1 : ℝ) ≤ Real.log (2 + Pa.N) := by
    have h3 : (3 : ℝ) ≤ 2 + Pa.N := by linarith
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) h3
    have h2 : (1 : ℝ) < Real.log 3 := by
      have hh := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at hh
    linarith
  have hMle : (M : ℝ) ≤ 18 * Pa.N := by
    rw [hM]
    exact Nat.floor_le (by positivity)
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hlogM : Real.log (M : ℝ) ≤ Real.log 18 + Real.log Pa.N := by
    rcases Nat.eq_zero_or_pos M with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      have : (0 : ℝ) ≤ Real.log 18 + Real.log Pa.N := by
        have h1 : (0 : ℝ) ≤ Real.log 18 := Real.log_nonneg (by norm_num)
        have h2 : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
        linarith
      exact this
    · have hpos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hpos
      calc Real.log (M : ℝ) ≤ Real.log (18 * Pa.N) := Real.log_le_log hpos' hMle
        _ = Real.log 18 + Real.log Pa.N :=
            Real.log_mul (by norm_num) (by linarith)
  have hkey : 1 + Real.log (M : ℝ) ≤ 20 * Real.log (2 + Pa.N) := by
    have hlogN : Real.log Pa.N ≤ Real.log (2 + Pa.N) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlog18 : Real.log 18 ≤ 18 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 18)
      linarith
    have h1 : 1 + Real.log (M : ℝ) ≤ (1 + 18) + Real.log (2 + Pa.N) := by linarith
    nlinarith [h1, hlog2N1]
  have hpow : (1 + Real.log (M : ℝ)) ^ 7 ≤ 20 ^ 7 * (Real.log (2 + Pa.N)) ^ 7 := by
    have h0 : (0 : ℝ) ≤ 1 + Real.log (M : ℝ) := by
      have hlogMn : (0 : ℝ) ≤ Real.log (M : ℝ) := by
        rcases Nat.eq_zero_or_pos M with h0 | hpos
        · rw [h0]; simp
        · exact Real.log_nonneg (by exact_mod_cast hpos)
      linarith
    calc (1 + Real.log (M : ℝ)) ^ 7 ≤ (20 * Real.log (2 + Pa.N)) ^ 7 :=
          pow_le_pow_left₀ h0 hkey 7
      _ = 20 ^ 7 * (Real.log (2 + Pa.N)) ^ 7 := by rw [mul_pow]
  have hfinal : (4 : ℝ) * ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7)
      ≤ 10 ^ 12 * Pa.N * (Real.log (2 + Pa.N)) ^ 7 := by
    have hlog0 : (0 : ℝ) ≤ (Real.log (2 + Pa.N)) ^ 7 := by positivity
    have hM0' : (0 : ℝ) ≤ (M : ℝ) := hM0
    calc (4 : ℝ) * ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7)
        ≤ 4 * ((18 * Pa.N) * (20 ^ 7 * (Real.log (2 + Pa.N)) ^ 7)) := by
          have h1 : (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7
              ≤ (18 * Pa.N) * (20 ^ 7 * (Real.log (2 + Pa.N)) ^ 7) :=
            mul_le_mul hMle hpow (by positivity) (by positivity)
          linarith [h1]
      _ = (4 * 18 * 20 ^ 7) * Pa.N * (Real.log (2 + Pa.N)) ^ 7 := by ring
      _ ≤ 10 ^ 12 * Pa.N * (Real.log (2 + Pa.N)) ^ 7 := by
          have h : (4 : ℝ) * 18 * 20 ^ 7 ≤ 10 ^ 12 := by norm_num
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hN0) hlog0
          linarith [this]
  calc ∑ z ∈ s, ‖β z‖ ^ 2
      ≤ ∑ z ∈ s, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2 := hstep1
    _ = ∑ n ∈ Finset.Icc 0 M,
          (((s.filter (fun z => Work.FIPlan.gnorm z = n)).card : ℕ) : ℝ)
            * (((n.divisors.card : ℕ) : ℝ) ^ 2) := hstep2
    _ ≤ 4 * ∑ n ∈ Finset.Icc 0 M, (((n.divisors.card : ℕ) : ℝ) ^ 3) := hstep3
    _ ≤ 4 * ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) := by
        have h := hstep4
        linarith [h]
    _ ≤ 10 ^ 12 * Pa.N * (Real.log (2 + Pa.N)) ^ 7 := hfinal

end

end Work.FIArea6T
