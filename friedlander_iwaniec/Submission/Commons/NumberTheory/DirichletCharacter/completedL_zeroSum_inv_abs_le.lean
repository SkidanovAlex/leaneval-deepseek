import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_zeroSum_count_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.LSeries.exists_lt_one_bound_zeros_LFunction_low_im

open Complex
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

/-!
# A uniform bound for `∑ m(ρ)/‖ρ‖` over the zeros of a completed `L`-function

For a primitive non-trivial Dirichlet character `χ` modulo `N` we bound
`∑_{ρ} m(ρ)/‖ρ‖`, where `ρ` runs over the non-trivial zeros of `Λ(χ,·)` with
`|Im ρ| ≤ T` and `m(ρ)` is the multiplicity, by `C · (log (N (T+3)) + 2)²`.

The proof is the usual dyadic decomposition: zeros with `2^k < |Im ρ| ≤ 2^{k+1}`
contribute at most `2^{-k}` times their total multiplicity, which is controlled
(uniformly in `χ` and `N`) by `completedL_zeroSum_count_uniform`.  The finitely
many zeros with `|Im ρ| ≤ 2` are absorbed into the constant `C`, which is
allowed to depend on `χ` and `N`.
-/

/-- Shorthand: the order of vanishing of the completed `L`-function of `χ` at `ρ`,
as a real number. -/
private def ordNat {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℝ :=
  ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℝ)

private lemma ordNat_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) :
    0 ≤ ordNat χ ρ :=
  Nat.cast_nonneg _

private lemma analyticOrderNatAt_eq_zero_of_ne_zero {f : ℂ → ℂ} {z : ℂ} (hz : f z ≠ 0) :
    analyticOrderNatAt f z = 0 := by
  have h : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hz)
  simp [analyticOrderNatAt, h]

private lemma eq_zero_of_analyticOrderNatAt_ne_zero {f : ℂ → ℂ} {z : ℂ}
    (hz : analyticOrderNatAt f z ≠ 0) : f z = 0 :=
  by_contra fun h => hz (analyticOrderNatAt_eq_zero_of_ne_zero h)

private lemma divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hu : u ∈ U) :
    MeromorphicOn.divisor f U u = (analyticOrderNatAt f u : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, (hf u hu).meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f u) ⊤ with h | h
  · rw [h]; simp [analyticOrderNatAt, h]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    have h2 : analyticOrderNatAt f u = n := by
      rw [analyticOrderNatAt, ← hn]; simp
    rw [h2, ← hn]; simp

private lemma completedL_two_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    DirichletCharacter.completedLFunction χ 2 ≠ 0 := by
  intro h
  have hs := zerosInStrip χ hχ hχprim (2 : ℂ) h
  norm_num at hs

/-- The zeros of `Λ(χ,·)` in the strip `0 < Re < 1` with `|Im| ≤ τ` are finite. -/
private lemma completedL_zeroSet_box_finite {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (τ : ℝ) :
    ({ρ : ℂ | DirichletCharacter.completedLFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1
      ∧ |ρ.im| ≤ τ}).Finite := by
  rcases lt_or_ge τ 0 with hτ | hτ
  · refine Set.Finite.subset Set.finite_empty ?_
    intro ρ hρ
    exact absurd (le_trans (abs_nonneg (ρ.im)) hρ.2.2.2) (not_le.mpr hτ)
  · refine (Commons.NumberTheory.LSeries.finite_zeroSet_of_isCompact
      (DirichletCharacter.differentiable_completedLFunction hχ) (completedL_two_ne_zero χ hχ hχprim)
      (isCompact_closedBall (0 : ℂ) (1 + τ))).subset ?_
    intro ρ hρ
    refine ⟨hρ.1, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := Complex.norm_le_abs_re_add_abs_im ρ
    have h2 : |ρ.re| ≤ 1 := by rw [abs_of_pos hρ.2.1]; linarith [hρ.2.2.1]
    linarith [hρ.2.2.2]

/-- A product of `ordNat χ ρ` with an indicator function of a strip condition has finite
support. -/
private lemma hasFiniteSupport_ordNat_indicator {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {τ : ℝ} {P : ℂ → Prop} [DecidablePred P] {w : ℂ → ℝ}
    (hP : ∀ ρ, P ρ → 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ τ) :
    Function.HasFiniteSupport (fun ρ : ℂ => ordNat χ ρ * (if P ρ then w ρ else 0)) := by
  refine (completedL_zeroSet_box_finite χ hχ hχprim τ).subset ?_
  intro ρ hρ
  rw [Function.mem_support] at hρ
  have hm : ordNat χ ρ ≠ 0 := fun h0 => hρ (by rw [h0, zero_mul])
  have hPρ : P ρ := by
    by_contra h
    exact hρ (by rw [if_neg h, mul_zero])
  have hΛ : DirichletCharacter.completedLFunction χ ρ = 0 := by
    apply eq_zero_of_analyticOrderNatAt_ne_zero
    intro h0
    exact hm (by rw [ordNat, h0]; norm_num)
  exact ⟨hΛ, (hP ρ hPρ).1, (hP ρ hPρ).2.1, (hP ρ hPρ).2.2⟩

/-- The multiplicity-weighted count of zeros with `|Im| ≤ τ` is the divisor of `Λ` on
the corresponding strip box. -/
private lemma count_summand_eq_divisor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (_hχprim : χ.IsPrimitive) {τ : ℝ} (_hτ : 0 ≤ τ) (ρ : ℂ) :
    ordNat χ ρ * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ τ then 1 else 0)
      = (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Complex.reProdIm (Set.Ioo (0 : ℝ) 1) (Set.Icc (-τ) τ))) ρ : ℤ) : ℝ) := by
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Complex.reProdIm (Set.Ioo (0 : ℝ) 1) (Set.Icc (-τ) τ)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  by_cases hmem : ρ ∈ Complex.reProdIm (Set.Ioo (0 : ℝ) 1) (Set.Icc (-τ) τ)
  · have hcond : 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ τ := by
      obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hmem
      exact ⟨hre.1, hre.2, by rw [abs_le]; exact him⟩
    rw [if_pos hcond, mul_one, divisor_eq_analyticOrderNatAt hΛan hmem, ordNat]
    simp
  · have hcond : ¬ (0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ τ) := by
      intro h
      apply hmem
      rw [Complex.mem_reProdIm]
      exact ⟨⟨h.1, h.2.1⟩, by rw [abs_le] at h; exact h.2.2⟩
    rw [if_neg hcond, mul_zero, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hmem]
    norm_num

/-- Dyadic bracketing: if `2 < a ≤ T ≤ 2^K` there is `1 ≤ k ≤ K` with
`2^k < a ≤ 2^{k+1}`. -/
private lemma exists_pow_two_bracket {a T : ℝ} {K : ℕ} (h2 : 2 < a) (haT : a ≤ T)
    (hK : T ≤ (2 : ℝ) ^ K) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ (2 : ℝ) ^ k < a ∧ a ≤ (2 : ℝ) ^ (k + 1) := by
  have hex : ∃ k : ℕ, a ≤ (2 : ℝ) ^ k := ⟨K, le_trans haT hK⟩
  have hspec : a ≤ (2 : ℝ) ^ Nat.find hex := Nat.find_spec hex
  have hle : Nat.find hex ≤ K := Nat.find_le (le_trans haT hK)
  have hge2 : 2 ≤ Nat.find hex := by
    rcases lt_or_ge (Nat.find hex) 2 with h | h
    · interval_cases Nat.find hex
      · norm_num at hspec; linarith
      · norm_num at hspec; linarith
    · exact h
  refine ⟨Nat.find hex - 1, by omega, by omega, ?_, ?_⟩
  · have hmin : ¬ (a ≤ (2 : ℝ) ^ (Nat.find hex - 1)) :=
      Nat.find_min hex (by omega)
    push Not at hmin
    exact hmin
  · have : Nat.find hex - 1 + 1 = Nat.find hex := Nat.sub_add_cancel (by omega)
    rw [this]
    exact hspec

/-- Pointwise dyadic bound: for `2 ≤ T ≤ 2^K` the summand with threshold `T` is bounded
by the low part (threshold `2`) plus a dyadic sum of multiplicity indicators. -/
private lemma pointwise_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {T : ℝ}
    (hT : 2 ≤ T) {K : ℕ} (hK : T ≤ (2 : ℝ) ^ K) (ρ : ℂ) :
    ordNat χ ρ * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (‖ρ‖)⁻¹ else 0)
      ≤ ordNat χ ρ * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 2 then (‖ρ‖)⁻¹ else 0)
        + ∑ k ∈ Finset.Icc 1 K, ordNat χ ρ
            * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ) ^ (k + 1)
                then (1 / 2 : ℝ) ^ k else 0) := by
  have hm0 : 0 ≤ ordNat χ ρ := ordNat_nonneg χ ρ
  have hsum0 : 0 ≤ ∑ k ∈ Finset.Icc 1 K, ordNat χ ρ
      * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ) ^ (k + 1)
          then (1 / 2 : ℝ) ^ k else 0) := by
    refine Finset.sum_nonneg (fun k _ => ?_)
    refine mul_nonneg hm0 ?_
    split_ifs <;> positivity
  by_cases hs : 0 < ρ.re ∧ ρ.re < 1
  · by_cases ha : |ρ.im| ≤ 2
    · have hT' : |ρ.im| ≤ T := le_trans ha hT
      rw [if_pos ⟨hs.1, hs.2, hT'⟩, if_pos ⟨hs.1, hs.2, ha⟩]
      linarith
    · push Not at ha
      by_cases hb : |ρ.im| ≤ T
      · obtain ⟨k, hk1, hkK, hklt, hkle⟩ := exists_pow_two_bracket ha hb hK
        rw [if_pos ⟨hs.1, hs.2, hb⟩, if_neg (fun h => (not_le.mpr ha) h.2.2)]
        have hmem : k ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hk1, hkK⟩
        have hsingle := Finset.single_le_sum
          (f := fun k' => ordNat χ ρ
            * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ) ^ (k' + 1)
                then (1 / 2 : ℝ) ^ k' else 0))
          (fun k' _ => by
            refine mul_nonneg hm0 ?_
            split_ifs <;> positivity) hmem
        have hfk : ordNat χ ρ * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ) ^ (k + 1)
            then (1 / 2 : ℝ) ^ k else 0) = ordNat χ ρ * (1 / 2 : ℝ) ^ k := by
          rw [if_pos ⟨hs.1, hs.2, hkle⟩]
        rw [hfk] at hsingle
        have hr : (‖ρ‖)⁻¹ ≤ (1 / 2 : ℝ) ^ k := by
          have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
          have hle2 : (2 : ℝ) ^ k ≤ ‖ρ‖ := le_trans (le_of_lt hklt) (Complex.abs_im_le_norm ρ)
          have h := inv_anti₀ hpos hle2
          have h2 : ((2 : ℝ) ^ k)⁻¹ = (1 / 2 : ℝ) ^ k := by
            rw [← inv_pow]
            congr 1
            norm_num
          rwa [h2] at h
        rw [mul_zero, zero_add]
        have h1 : ordNat χ ρ * (‖ρ‖)⁻¹ ≤ ordNat χ ρ * (1 / 2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left hr hm0
        linarith [h1, hsingle]
      · rw [if_neg (fun h => hb h.2.2), if_neg (fun h => (not_le.mpr ha) h.2.2), mul_zero]
        have h1 : 0 ≤ ordNat χ ρ * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 2
            then (‖ρ‖)⁻¹ else 0) := by
          refine mul_nonneg hm0 ?_
          split_ifs <;> positivity
        linarith [h1, hsum0]
  · rw [if_neg (fun h => hs ⟨h.1, h.2.1⟩), mul_zero]
    have h1 : 0 ≤ ordNat χ ρ * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 2
        then (‖ρ‖)⁻¹ else 0) := by
      refine mul_nonneg hm0 ?_
      split_ifs <;> positivity
    linarith [h1, hsum0]

/-- The dyadic shell sum. -/
private lemma dyadic_shell_sum_le {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 2 ≤ T) {K : ℕ}
    (hK2 : (2 : ℝ) ^ (K + 1) ≤ 16 * (T + 3))
    (hK3 : (K : ℝ) ≤ 2 * (Real.log ((N : ℝ) * (T + 3)) + 2)) :
    (∑ k ∈ Finset.Icc 1 K,
        (1 / 2 : ℝ) ^ k * (((2 : ℝ) ^ (k + 1) + 2)
          * (Real.log ((N : ℝ) * ((2 : ℝ) ^ (k + 1) + 2)) + 2)))
      ≤ 400 * (Real.log ((N : ℝ) * (T + 3)) + 2) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hTpos : (0 : ℝ) < T := by linarith
  have hL0 : 0 ≤ Real.log ((N : ℝ) * (T + 3)) := Real.log_nonneg (by nlinarith)
  have hlog18 : Real.log 18 ≤ 17 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 18 by norm_num)
    linarith
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      (1 / 2 : ℝ) ^ k * (((2 : ℝ) ^ (k + 1) + 2)
          * (Real.log ((N : ℝ) * ((2 : ℝ) ^ (k + 1) + 2)) + 2))
        ≤ 4 * (Real.log ((N : ℝ) * (T + 3)) + 19) := by
    intro k hk
    obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hk
    have hp1 : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (K + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hp2 : (2 : ℝ) ^ (k + 1) + 2 ≤ 18 * (T + 3) := by linarith
    have harg : 0 < (N : ℝ) * ((2 : ℝ) ^ (k + 1) + 2) := by positivity
    have hle : Real.log ((N : ℝ) * ((2 : ℝ) ^ (k + 1) + 2))
        ≤ Real.log (18 * ((N : ℝ) * (T + 3))) := by
      apply Real.log_le_log harg
      nlinarith [hp2, hN1, hp1]
    have hsplit : Real.log (18 * ((N : ℝ) * (T + 3)))
        = Real.log 18 + Real.log ((N : ℝ) * (T + 3)) :=
      Real.log_mul (by norm_num) (by positivity)
    have hlogbound : Real.log ((N : ℝ) * ((2 : ℝ) ^ (k + 1) + 2)) + 2
        ≤ Real.log ((N : ℝ) * (T + 3)) + 19 := by linarith
    have hfac : (1 / 2 : ℝ) ^ k * ((2 : ℝ) ^ (k + 1) + 2) ≤ 4 := by
      have h1 : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ (k + 1) = 2 := by
        rw [pow_succ, ← mul_assoc, ← mul_pow]
        norm_num
      have h2 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith [h1, h2]
    have h2k1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
    have harg2 : 0 ≤ Real.log ((N : ℝ) * ((2 : ℝ) ^ (k + 1) + 2)) + 2 := by
      have : (1 : ℝ) ≤ (N : ℝ) * ((2 : ℝ) ^ (k + 1) + 2) := by nlinarith [hN1, h2k1]
      have := Real.log_nonneg this
      linarith
    calc (1 / 2 : ℝ) ^ k * (((2 : ℝ) ^ (k + 1) + 2)
            * (Real.log ((N : ℝ) * ((2 : ℝ) ^ (k + 1) + 2)) + 2))
        = ((1 / 2 : ℝ) ^ k * ((2 : ℝ) ^ (k + 1) + 2))
            * (Real.log ((N : ℝ) * ((2 : ℝ) ^ (k + 1) + 2)) + 2) := by ring
      _ ≤ 4 * (Real.log ((N : ℝ) * (T + 3)) + 19) :=
          mul_le_mul hfac hlogbound harg2 (by norm_num)
  have hcard : ((Finset.Icc 1 K).card : ℝ) = (K : ℝ) := by
    rw [Nat.card_Icc]
    norm_num
  calc (∑ k ∈ Finset.Icc 1 K,
        (1 / 2 : ℝ) ^ k * (((2 : ℝ) ^ (k + 1) + 2)
          * (Real.log ((N : ℝ) * ((2 : ℝ) ^ (k + 1) + 2)) + 2)))
      ≤ ∑ _k ∈ Finset.Icc 1 K, 4 * (Real.log ((N : ℝ) * (T + 3)) + 19) :=
        Finset.sum_le_sum hterm
    _ = ((Finset.Icc 1 K).card : ℝ) * (4 * (Real.log ((N : ℝ) * (T + 3)) + 19)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (K : ℝ) * (4 * (Real.log ((N : ℝ) * (T + 3)) + 19)) := by rw [hcard]
    _ ≤ 400 * (Real.log ((N : ℝ) * (T + 3)) + 2) ^ 2 := by
        nlinarith [hK3, hL0]

/-- The main bound for a fixed `T`, relative to the count constant `c`. -/
private theorem bound_for_T {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {c : ℝ} (hc : 0 < c)
    (hcount : ∀ τ : ℝ, 2 ≤ τ →
      (∑ᶠ ρ : ℂ, ordNat χ ρ * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ τ then 1 else 0))
        ≤ c * (τ + 2) * (Real.log ((N : ℝ) * (τ + 2)) + 2))
    {T : ℝ} (hT : 2 ≤ T) :
    (∑ᶠ ρ : ℂ, ordNat χ ρ * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (‖ρ‖)⁻¹ else 0))
      ≤ ((∑ᶠ ρ : ℂ, ordNat χ ρ
            * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 2 then (‖ρ‖)⁻¹ else 0)) + 400 * c)
          * (Real.log ((N : ℝ) * (T + 3)) + 2) ^ 2 := by
  classical
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hT0 : (0 : ℝ) < T := by linarith
  have hL0 : 0 ≤ Real.log ((N : ℝ) * (T + 3)) := Real.log_nonneg (by nlinarith)
  -- the dyadic exponent
  set x : ℝ := Real.logb 2 T with hx
  set K : ℕ := Nat.ceil x + 2 with hKdef
  have hx0 : 0 ≤ x := by
    rw [hx]; exact Real.logb_nonneg (by norm_num) (by linarith)
  have h2x : (2 : ℝ) ^ x = T := by
    rw [hx]; exact Real.rpow_logb (by norm_num) (by norm_num) hT0
  have hK2 : T ≤ (2 : ℝ) ^ K := by
    have h2ceil : T ≤ (2 : ℝ) ^ (Nat.ceil x : ℝ) := by
      rw [← h2x]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil x)
    have h2nat : T ≤ (2 : ℝ) ^ (Nat.ceil x) := by
      rwa [Real.rpow_natCast] at h2ceil
    have hsplit : (2 : ℝ) ^ K = (2 : ℝ) ^ (Nat.ceil x) * 4 := by
      rw [hKdef, pow_add]; norm_num
    rw [hsplit]
    nlinarith [h2nat, pow_pos (by norm_num : (0 : ℝ) < 2) (Nat.ceil x)]
  have hK16 : (2 : ℝ) ^ (K + 1) ≤ 16 * (T + 3) := by
    have hceil_lt : (Nat.ceil x : ℝ) < x + 1 := by
      have := Nat.ceil_lt_add_one hx0
      simpa using this
    have h2ceil_lt : (2 : ℝ) ^ (Nat.ceil x) < 2 * T := by
      have h1 : (2 : ℝ) ^ ((Nat.ceil x : ℕ) : ℝ) < (2 : ℝ) ^ (x + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hceil_lt
      have h2 : (2 : ℝ) ^ (x + 1) = 2 * T := by
        rw [Real.rpow_add (by norm_num), h2x, Real.rpow_one]; ring
      rw [Real.rpow_natCast, h2] at h1
      exact h1
    have hsplit : (2 : ℝ) ^ (K + 1) = (2 : ℝ) ^ (Nat.ceil x) * 8 := by
      have hKs : K + 1 = Nat.ceil x + 3 := by rw [hKdef]
      rw [hKs, pow_add]
      norm_num
    rw [hsplit]
    nlinarith [h2ceil_lt, hT0]
  have hK3 : (K : ℝ) ≤ 2 * (Real.log ((N : ℝ) * (T + 3)) + 2) := by
    have hceil_lt : (Nat.ceil x : ℝ) < x + 1 := by
      have := Nat.ceil_lt_add_one hx0
      simpa using this
    have hKval : (K : ℝ) = (Nat.ceil x : ℝ) + 2 := by rw [hKdef]; push_cast; ring
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hxle : x ≤ 2 * Real.log T := by
      have h1 : Real.log T / Real.log 2 ≤ Real.log T / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left hlogT0 (by norm_num) hlog2
      have h2 : Real.log T / (1 / 2 : ℝ) = 2 * Real.log T := by ring
      have h3 : Real.log T / Real.log 2 = x := by rw [hx, Real.log_div_log]
      linarith [h1, h2, h3]
    have hlogTL : Real.log T ≤ Real.log ((N : ℝ) * (T + 3)) := by
      apply Real.log_le_log hT0
      nlinarith [hN1]
    rw [hKval]
    linarith
  -- the finsums
  let F : ℂ → ℝ := fun ρ => ordNat χ ρ
    * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (‖ρ‖)⁻¹ else 0)
  let Lf : ℂ → ℝ := fun ρ => ordNat χ ρ
    * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 2 then (‖ρ‖)⁻¹ else 0)
  let Tk : ℕ → ℂ → ℝ := fun k ρ => ordNat χ ρ
    * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ) ^ (k + 1)
        then (1 / 2 : ℝ) ^ k else 0)
  let Kf : ℂ → ℝ := fun ρ => ∑ k ∈ Finset.Icc 1 K, Tk k ρ
  let G : ℂ → ℝ := fun ρ => Lf ρ + Kf ρ
  have hFG : F ≤ G := fun ρ => pointwise_bound χ hT hK2 ρ
  have hfinL : Function.HasFiniteSupport Lf :=
    hasFiniteSupport_ordNat_indicator χ hχ hχprim (P := fun ρ => 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 2)
      (fun _ h => h)
  have hfinF : Function.HasFiniteSupport F :=
    hasFiniteSupport_ordNat_indicator χ hχ hχprim (P := fun ρ => 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T)
      (fun _ h => h)
  have hfinTk : ∀ k : ℕ, Function.HasFiniteSupport (Tk k) := by
    intro k
    exact hasFiniteSupport_ordNat_indicator χ hχ hχprim
      (P := fun ρ => 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ) ^ (k + 1))
      (w := fun _ => (1 / 2 : ℝ) ^ k)
      (fun _ h => h)
  have hfinK : Function.HasFiniteSupport Kf := by
    refine (completedL_zeroSet_box_finite χ hχ hχprim ((2 : ℝ) ^ (K + 1))).subset ?_
    intro ρ hρ
    rw [Function.mem_support] at hρ
    have hex : ∃ k ∈ Finset.Icc 1 K, Tk k ρ ≠ 0 := by
      by_contra h
      push Not at h
      exact hρ (Finset.sum_eq_zero h)
    obtain ⟨k, hk, hkne⟩ := hex
    obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hk
    have hm : ordNat χ ρ ≠ 0 := by
      intro h0
      exact hkne (by simp only [Tk, h0, zero_mul])
    have hcond : 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ) ^ (k + 1) := by
      by_contra h
      exact hkne (by simp only [Tk, if_neg h, mul_zero])
    have hΛ : DirichletCharacter.completedLFunction χ ρ = 0 := by
      apply eq_zero_of_analyticOrderNatAt_ne_zero
      intro h0
      exact hm (by rw [ordNat, h0]; norm_num)
    refine ⟨hΛ, hcond.1, hcond.2.1, ?_⟩
    exact le_trans hcond.2.2 (pow_le_pow_right₀ (by norm_num) (by omega))
  have hfinG : Function.HasFiniteSupport G := hfinL.add hfinK
  have step1 : (∑ᶠ ρ, F ρ) ≤ ∑ᶠ ρ, G ρ := finsum_le_finsum' hfinF hfinG hFG
  have step2 : (∑ᶠ ρ, G ρ) = (∑ᶠ ρ, Lf ρ) + ∑ᶠ ρ, Kf ρ := finsum_add_distrib hfinL hfinK
  have step3 : (∑ᶠ ρ, Kf ρ) = ∑ k ∈ Finset.Icc 1 K, ∑ᶠ ρ, Tk k ρ :=
    finsum_sum_comm (Finset.Icc 1 K) (fun ρ k => Tk k ρ) (fun k _ => hfinTk k)
  have step4 : ∀ k : ℕ, (∑ᶠ ρ, Tk k ρ) = (1 / 2 : ℝ) ^ k
      * (∑ᶠ ρ, ordNat χ ρ
          * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ) ^ (k + 1) then 1 else 0)) := by
    intro k
    have hcongr : (∑ᶠ ρ, Tk k ρ) = ∑ᶠ ρ,
        (ordNat χ ρ * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ) ^ (k + 1) then 1 else 0))
          * (1 / 2 : ℝ) ^ k := by
      refine finsum_congr (fun ρ => ?_)
      by_cases h : 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ) ^ (k + 1)
      · simp only [Tk, if_pos h]
        ring
      · simp only [Tk, if_neg h]
        ring
    rw [hcongr, ← finsum_mul, mul_comm]
  have step5 : ∀ k ∈ Finset.Icc 1 K, (∑ᶠ ρ, Tk k ρ) ≤ (1 / 2 : ℝ) ^ k
      * (c * ((2 : ℝ) ^ (k + 1) + 2)
          * (Real.log ((N : ℝ) * ((2 : ℝ) ^ (k + 1) + 2)) + 2)) := by
    intro k hk
    obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hk
    have h2k : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
        _ ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hb := hcount ((2 : ℝ) ^ (k + 1)) h2k
    have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := pow_nonneg (by norm_num) k
    rw [step4 k]
    exact mul_le_mul_of_nonneg_left hb hnn
  have step6 : (∑ᶠ ρ, Kf ρ) ≤ 400 * c * (Real.log ((N : ℝ) * (T + 3)) + 2) ^ 2 := by
    rw [step3]
    calc ∑ k ∈ Finset.Icc 1 K, ∑ᶠ ρ, Tk k ρ
        ≤ ∑ k ∈ Finset.Icc 1 K, (1 / 2 : ℝ) ^ k
            * (c * ((2 : ℝ) ^ (k + 1) + 2)
                * (Real.log ((N : ℝ) * ((2 : ℝ) ^ (k + 1) + 2)) + 2)) :=
          Finset.sum_le_sum step5
      _ = c * (∑ k ∈ Finset.Icc 1 K, (1 / 2 : ℝ) ^ k
            * (((2 : ℝ) ^ (k + 1) + 2)
                * (Real.log ((N : ℝ) * ((2 : ℝ) ^ (k + 1) + 2)) + 2))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring
      _ ≤ c * (400 * (Real.log ((N : ℝ) * (T + 3)) + 2) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (dyadic_shell_sum_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) hT hK16 hK3) hc.le
      _ = 400 * c * (Real.log ((N : ℝ) * (T + 3)) + 2) ^ 2 := by ring
  have hLow0 : 0 ≤ ∑ᶠ ρ, Lf ρ := by
    refine finsum_nonneg (fun ρ => ?_)
    exact mul_nonneg (ordNat_nonneg χ ρ) (by split_ifs <;> positivity)
  have hB1 : (1 : ℝ) ≤ (Real.log ((N : ℝ) * (T + 3)) + 2) ^ 2 := by
    have h2 : (1 : ℝ) ≤ Real.log ((N : ℝ) * (T + 3)) + 2 := by linarith
    nlinarith
  calc (∑ᶠ ρ, F ρ) ≤ ∑ᶠ ρ, G ρ := step1
    _ = (∑ᶠ ρ, Lf ρ) + ∑ᶠ ρ, Kf ρ := step2
    _ ≤ (∑ᶠ ρ, Lf ρ) + 400 * c * (Real.log ((N : ℝ) * (T + 3)) + 2) ^ 2 := by
        linarith [step6]
    _ ≤ ((∑ᶠ ρ, Lf ρ) + 400 * c) * (Real.log ((N : ℝ) * (T + 3)) + 2) ^ 2 := by
        nlinarith [hLow0, hB1, hc]

theorem completedL_zeroSum_inv_abs_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (∑ᶠ ρ : ℂ, ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℝ)
        * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (‖ρ‖)⁻¹ else 0))
      ≤ C * (Real.log (N * (T + 3)) + 2) ^ 2 := by
  classical
  obtain ⟨c, hc, hcountD⟩ := completedL_zeroSum_count_uniform
  have hcount : ∀ τ : ℝ, 2 ≤ τ →
      (∑ᶠ ρ : ℂ, ordNat χ ρ * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ τ then 1 else 0))
        ≤ c * (τ + 2) * (Real.log ((N : ℝ) * (τ + 2)) + 2) := by
    intro τ hτ
    rw [finsum_congr (fun ρ => count_summand_eq_divisor χ hχ hχprim (by linarith : (0 : ℝ) ≤ τ) ρ)]
    exact hcountD N χ hχ hχprim τ hτ
  refine ⟨(∑ᶠ ρ : ℂ, ordNat χ ρ
      * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 2 then (‖ρ‖)⁻¹ else 0)) + 400 * c, ?_, ?_⟩
  · have h0 : 0 ≤ (∑ᶠ ρ : ℂ, ordNat χ ρ
        * (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 2 then (‖ρ‖)⁻¹ else 0)) := by
      refine finsum_nonneg (fun ρ => ?_)
      exact mul_nonneg (ordNat_nonneg χ ρ) (by split_ifs <;> positivity)
    linarith
  · intro T hT
    exact bound_for_T χ hχ hχprim hc hcount hT

end

end Commons.NumberTheory.DirichletCharacter
