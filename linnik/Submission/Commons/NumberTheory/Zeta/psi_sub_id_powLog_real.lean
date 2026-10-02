import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_near_axis_bound
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
import Submission.Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le

open Complex Filter Metric Set MeasureTheory
open scoped Real Topology BigOperators Interval

namespace Commons.NumberTheory.Zeta

set_option maxHeartbeats 0

/-! Helpers (all proved; the analytic engine theorem below is the remaining core). -/

/-- `log u ≤ 4·u^(1/4)` for `1 ≤ u` (crude, elementary). -/
private lemma log_le_four_rpow (u : ℝ) (hu : 1 ≤ u) : Real.log u ≤ 4 * u ^ (1 / 4 : ℝ) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hv0 : 0 < u ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hu0 (1 / 4 : ℝ)
  have hlogv : Real.log (u ^ (1 / 4 : ℝ)) ≤ u ^ (1 / 4 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hv0
  have hlogu : Real.log u = 4 * Real.log (u ^ (1 / 4 : ℝ)) := by
    rw [Real.log_rpow hu0 (1 / 4 : ℝ)]
    ring
  calc
    Real.log u = 4 * Real.log (u ^ (1 / 4 : ℝ)) := hlogu
    _ ≤ 4 * (u ^ (1 / 4 : ℝ) - 1) := by
      exact mul_le_mul_of_nonneg_left hlogv (by norm_num)
    _ ≤ 4 * u ^ (1 / 4 : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by linarith only []) (by norm_num)

/-- `c·√u ≥ A·log u` eventually in `u`. -/
private lemma sqrt_log_domination (c : ℝ) (hc : 0 < c) (A : ℝ) (hA : 0 < A) :
    ∃ U₀ : ℝ, (1 : ℝ) ≤ U₀ ∧ ∀ u : ℝ, U₀ ≤ u → 0 ≤ c * Real.sqrt u - A * Real.log u := by
  let K : ℝ := 4 * A / c
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hK4 : 0 ≤ K ^ (4 : ℝ) := Real.rpow_nonneg hK0 (4 : ℝ)
  refine ⟨max 1 (K ^ (4 : ℝ)), le_max_left _ _, ?_⟩
  intro u hu
  have hu1 : (1 : ℝ) ≤ u := le_trans (le_max_left _ _) hu
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hU : K ^ (4 : ℝ) ≤ u := le_trans (le_max_right _ _) hu
  have hpow : K ≤ u ^ (1 / 4 : ℝ) := by
    have hle : (K ^ (4 : ℝ)) ^ (1 / 4 : ℝ) ≤ u ^ (1 / 4 : ℝ) := by
      exact Real.rpow_le_rpow hK4 hU (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ))
    have hcube : (K ^ (4 : ℝ)) ^ (1 / 4 : ℝ) = K := by
      calc (K ^ (4 : ℝ)) ^ (1 / 4 : ℝ) = K ^ ((4 : ℝ) * (1 / 4 : ℝ)) :=
        (Real.rpow_mul hK0 (4 : ℝ) (1 / 4 : ℝ)).symm
      _ = K ^ (1 : ℝ) := by norm_num
      _ = K := Real.rpow_one K
    rwa [hcube] at hle
  have hA1 : A * Real.log u ≤ A * (4 * u ^ (1 / 4 : ℝ)) := by
    exact mul_le_mul_of_nonneg_left (log_le_four_rpow u hu1) (le_of_lt hA)
  have hmain : A * (4 * u ^ (1 / 4 : ℝ)) ≤ c * u ^ (1 / 2 : ℝ) := by
    have h1 : c * u ^ (1 / 2 : ℝ) = (c * u ^ (1 / 4 : ℝ)) * u ^ (1 / 4 : ℝ) := by
      have hE : (1 / 4 : ℝ) + (1 / 4 : ℝ) = (1 / 2 : ℝ) := by norm_num
      calc
        c * u ^ (1 / 2 : ℝ) = c * u ^ ((1 / 4 : ℝ) + (1 / 4 : ℝ)) := by rw [← hE]
        _ = c * (u ^ (1 / 4 : ℝ) * u ^ (1 / 4 : ℝ)) := by
          rw [Real.rpow_add hu0 (1 / 4 : ℝ) (1 / 4 : ℝ)]
        _ = (c * u ^ (1 / 4 : ℝ)) * u ^ (1 / 4 : ℝ) := by ring
    have h2 : A * (4 * u ^ (1 / 4 : ℝ)) = K * (c * u ^ (1 / 4 : ℝ)) := by
      dsimp [K]
      field_simp [hc.ne']
    rw [h1, h2]
    have hm := mul_le_mul_of_nonneg_right hpow (by
      exact mul_nonneg (le_of_lt hc) (le_of_lt (Real.rpow_pos_of_pos hu0 (1 / 4 : ℝ))))
    simpa [mul_comm, mul_left_comm, mul_assoc] using hm
  have hfinal : A * Real.log u ≤ c * Real.sqrt u := by
    rw [Real.sqrt_eq_rpow u]
    calc
      A * Real.log u ≤ A * (4 * u ^ (1 / 4 : ℝ)) := hA1
      _ ≤ c * u ^ (1 / 2 : ℝ) := hmain
  linarith only [hfinal]

/-- If `|ψ(x)−x| ≤ x·exp(−c√(log x))` eventually, then for every `A > 0`,
`|ψ(x)−x| ≤ x/(log x)^A` eventually. -/
private lemma exp_sqrtLog_pow_le_one {c : ℝ} (hc : 0 < c) :
    ∀ A : ℝ, 0 < A → ∃ x₀ : ℝ, (1 : ℝ) ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      Real.exp (-c * Real.sqrt (Real.log x)) * (Real.log x) ^ A ≤ 1 := by
  intro A hA
  rcases sqrt_log_domination c hc A hA with ⟨U₀, hU₀, hdom⟩
  refine ⟨Real.exp U₀, ?_, ?_⟩
  · simpa using (Real.exp_le_exp.mpr (le_trans zero_le_one hU₀))
  · intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos U₀) hx
    have hlogU : U₀ ≤ Real.log x := by
      exact (Real.le_log_iff_exp_le hxpos).2 hx
    have hdomx := hdom (Real.log x) hlogU
    have hLpos : 0 < Real.log x := lt_of_lt_of_le (by exact lt_of_lt_of_le zero_lt_one hU₀) hlogU
    have hLge : A * Real.log (Real.log x) ≤ c * Real.sqrt (Real.log x) := by linarith only [hdomx]
    have hstep : Real.log ((Real.log x) ^ A) ≤ c * Real.sqrt (Real.log x) := by
      rw [Real.log_rpow hLpos]
      exact hLge
    have hfac : (Real.log x) ^ A ≤ Real.exp (c * Real.sqrt (Real.log x)) := by
      have hle' : Real.log ((Real.log x) ^ A) ≤ Real.log (Real.exp (c * Real.sqrt (Real.log x))) := by
        rw [Real.log_exp]
        exact hstep
      exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hLpos A) (Real.exp_pos (c * Real.sqrt (Real.log x)))).1 hle'
    have heq : Real.exp (-c * Real.sqrt (Real.log x)) * (Real.log x) ^ A
        ≤ Real.exp (-c * Real.sqrt (Real.log x)) * Real.exp (c * Real.sqrt (Real.log x)) := by
      exact mul_le_mul_of_nonneg_left hfac (le_of_lt (Real.exp_pos (-c * Real.sqrt (Real.log x))))
    have hid : Real.exp (-c * Real.sqrt (Real.log x)) * Real.exp (c * Real.sqrt (Real.log x)) = 1 := by
      rw [← Real.exp_add]
      have hsum : -c * Real.sqrt (Real.log x) + c * Real.sqrt (Real.log x) = 0 := by ring
      rw [hsum, Real.exp_zero]
    rwa [hid] at heq


/-- Per-term non-negativity in the 3-4-1 inequality. -/
private lemma mangoldt_three_four_one_term_nonneg (n : ℕ) (σ : ℝ) (hσ : 0 < σ) (t : ℝ) :
    0 ≤ ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      (3 + 4 * Real.cos (t * Real.log (((n + 1 : ℕ) : ℝ))) +
        Real.cos (((2 * t) : ℝ) * Real.log (((n + 1 : ℕ) : ℝ)))) /
          ((((n + 1 : ℕ) : ℝ) ^ σ))) := by
  have htrig : 0 ≤ 3 + 4 * Real.cos (t * Real.log (((n + 1 : ℕ) : ℝ))) +
      Real.cos (((2 * t) : ℝ) * Real.log (((n + 1 : ℕ) : ℝ))) := by
    have h2t : ((2 * t) : ℝ) * Real.log (((n + 1 : ℕ) : ℝ)) = 2 * (t * Real.log (((n + 1 : ℕ) : ℝ))) := by ring
    rw [h2t]
    have h : 3 + 4 * Real.cos (t * Real.log (((n + 1 : ℕ) : ℝ))) +
          Real.cos (2 * (t * Real.log (((n + 1 : ℕ) : ℝ)))) =
        2 * (1 + Real.cos (t * Real.log (((n + 1 : ℕ) : ℝ)))) ^ 2 := by
      rw [Real.cos_two_mul]
      ring
    rw [h]
    positivity
  have hL : 0 ≤ (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) := by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
  have hd : 0 < ((((n + 1 : ℕ) : ℝ) ^ σ)) := Real.rpow_pos_of_pos (by positivity) σ
  positivity

/-- `Σ Λ(n+1)(3 + 4cos + cos(2·)) / (n+1)^σ ≥ 0` (the three-four-one inequality). -/
private lemma mangoldt_three_four_one (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    0 ≤ ∑' n : ℕ, ((((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      (3 + 4 * Real.cos (t * Real.log (((n + 1 : ℕ) : ℝ))) +
        Real.cos (((2 * t) : ℝ) * Real.log (((n + 1 : ℕ) : ℝ)))))) /
          ((((n + 1 : ℕ) : ℝ) ^ σ))) := by
  apply tsum_nonneg
  intro n
  exact mangoldt_three_four_one_term_nonneg n σ (by linarith only [hσ]) t

private lemma norm_term_mangoldt (n : ℕ) (σ : ℝ) (t : ℝ) :
    ‖(((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) /
      (((n + 1 : ℕ) : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I))))‖ =
      ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ)) /
        (((n + 1 : ℕ) : ℝ) ^ σ) := by
  have hx0 : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hM0 : 0 ≤ (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) := by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
  have hs : (((σ : ℂ) + (t : ℂ) * Complex.I)).re = σ := by simp
  have hnormpow : ‖(((n + 1 : ℕ) : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I)))‖ =
      (((n + 1 : ℕ) : ℝ) ^ σ) := by
    simpa [hs] using Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 1) (((σ : ℂ) + (t : ℂ) * Complex.I))
  rw [norm_div]
  rw [hnormpow]
  rw [Complex.norm_real]
  rw [Real.norm_of_nonneg hM0]

private lemma mangoldt_series_norm_le (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    ‖deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
      riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      ∑' n : ℕ, (((ArithmeticFunction.vonMangoldt (n + 1) : ℝ)) /
          ((((n + 1 : ℕ) : ℝ) ^ σ))) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hS
  have hs1 : (1 : ℝ) < s.re := by
    rw [hS]
    simpa using hσ
  have hΛ0 : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply]
    split_ifs with h
    · exfalso
      exact not_isPrimePow_zero h
    · rfl
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  have hf0 : f 0 = 0 := by
    dsimp [f]
    exact_mod_cast hΛ0
  let a : ℕ → ℂ := fun n => f n / ((n : ℂ) ^ s)
  have ha0 : a 0 = 0 := by
    dsimp [a, f]
    rw [hΛ0]
    simp
  have hL : LSeries f s = (-deriv riemannZeta s / riemannZeta s) := by
    simpa [f] using
      (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs1)
  have hLSumm : Summable (LSeries.term f s) := by
    change Summable (LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s)
    simpa [LSeriesSummable] using
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) hs1)
  have hSummA : Summable a := by
    apply hLSumm.congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [a, hf0]
    · dsimp [a, f]
      rw [LSeries.term, if_neg hn]
  have hSummN : Summable (fun n : ℕ => ‖a n‖) := hSummA.norm
  have htail : (∑' n : ℕ, a (n + 1)) = ∑' n : ℕ, a n := by
    have hsumadd := hSummA.sum_add_tsum_nat_add 1
    simpa [ha0] using hsumadd
  have hnorm0 : ‖a 0‖ = 0 := by
    rw [ha0]
    simp
  have hnorm_add : ‖∑' n : ℕ, a (n + 1)‖ ≤ ∑' n : ℕ, ‖a (n + 1)‖ := by
    exact norm_tsum_le_tsum_norm ((summable_nat_add_iff 1).2 hSummN)
  calc
    ‖deriv riemannZeta s / riemannZeta s‖
        = ‖LSeries f s‖ := by
          rw [hL]
          rw [neg_div (riemannZeta s) (deriv riemannZeta s)]
          rw [norm_neg]
    _ = ‖∑' n : ℕ, a n‖ := by
          simpa [a] using congrArg norm (LSeries_def₀ hf0 s)
    _ = ‖∑' n : ℕ, a (n + 1)‖ := by
          rw [htail]
    _ ≤ ∑' n : ℕ, ‖a (n + 1)‖ := hnorm_add
    _ = ∑' n : ℕ, (((ArithmeticFunction.vonMangoldt (n + 1) : ℝ)) /
          ((((n + 1 : ℕ) : ℝ) ^ σ))) := by
          apply tsum_congr
          intro n
          dsimp [a, f]
          rw [hS]
          exact norm_term_mangoldt n σ t

/-
Generic (RH-free) rectangle-residue machinery: decomposition of the Perron
integrand into its polar part at s=1 and the analytic part hFunc (which is
analytic wherever zeta1 does not vanish), so that integration around a
zero-free rectangle picks up only the residue x at s=1. These are the
unconditional analogues of the RH-conditional lemmas in
`chebyshevPsi_sub_id_rh_bound`. Ported from that file; no `RiemannHypothesis`.
-/

lemma psiIntF_eq_polar_add_hFunc_of_zeta1_ne_zero {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hz1 : riemannZeta₁ s ≠ 0) :
    psiIntF x s = (x : ℂ) / (s - 1) + hFunc x s := by
  have hid : -(deriv riemannZeta s / riemannZeta s) = (s - 1)⁻¹ - zeta1LogDeriv s := by
    have h := deriv_zeta_div_zeta_eq s hs1 hz1
    rw [h]
    dsimp [zeta1LogDeriv]
    ring
  have hslope : dslope (fun w : ℂ => (x : ℂ) ^ w) 1 s = ((x : ℂ) ^ s - (x : ℂ)) / (s - 1) :=
    dslope_cpow_eq_div hs1
  calc
    psiIntF x s = (-(deriv riemannZeta s / riemannZeta s)) * (x : ℂ) ^ s / s := by
      dsimp [psiIntF]
      ring
    _ = ((s - 1)⁻¹ - zeta1LogDeriv s) * (x : ℂ) ^ s / s := by rw [hid]
    _ = (x : ℂ) ^ s / ((s - 1) * s) - zeta1LogDeriv s * ((x : ℂ) ^ s / s) := by
      field_simp [hs0, sub_ne_zero.mpr hs1] <;> ring
    _ = (x : ℂ) / (s - 1) + hFunc x s := by
      dsimp [hFunc, zeta1LogDeriv]
      rw [hslope]
      field_simp [hs0, sub_ne_zero.mpr hs1] <;> ring

lemma zeta1LogDeriv_differentiableOn_noZero :
    DifferentiableOn ℂ zeta1LogDeriv {s : ℂ | riemannZeta₁ s ≠ 0} := by
  refine DifferentiableOn.div (c := fun s : ℂ => deriv riemannZeta₁ s)
    (d := fun s : ℂ => riemannZeta₁ s) (s := {s : ℂ | riemannZeta₁ s ≠ 0}) ?_ ?_ ?_
  · have hd : Differentiable ℂ (fun s : ℂ => deriv riemannZeta₁ s) :=
      (Differentiable.deriv differentiable_riemannZeta₁)
    intro s hs
    exact (hd.differentiableAt (x := s)).differentiableWithinAt
  · intro s hs
    exact (differentiable_riemannZeta₁.differentiableAt (x := s)).differentiableWithinAt
  · intro s hs
    exact hs

/-- `hFunc x` is analytic on the region where `ζ₁` does not vanish and `re s > 0`
(in particular wherever `ζ` has no zero and `s ≠ 1`-neighbourhood away from `0`). -/
lemma hFunc_differentiableOn_noZero (x : ℝ) (hx : 0 < x) :
    DifferentiableOn ℂ (hFunc x) {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0} := by
  have h1 : DifferentiableOn ℂ (fun s : ℂ => dslope (fun w : ℂ => (x : ℂ) ^ w) 1 s)
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0} := by
    intro s hs
    exact ((cpow_dslope_differentiable hx).differentiableAt (x := s)).differentiableWithinAt
  have h2 : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s / s)
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0} := by
    intro s hs
    have hs0 : s ≠ 0 := by
      intro h
      have hre : s.re = 0 := by simpa using congrArg Complex.re h
      have hlt : (0 : ℝ) < (0 : ℝ) := by simpa [hre] using hs.1
      exact (lt_irrefl (0 : ℝ)) hlt
    exact ((cpow_div_self_differentiableOn (x := x) hx).differentiableAt (x := s)
      (isOpen_ne.mem_nhds hs0)).differentiableWithinAt
  have h3 : DifferentiableOn ℂ (fun s : ℂ => zeta1LogDeriv s * ((x : ℂ) ^ s / s))
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0} := by
    exact DifferentiableOn.mul (zeta1LogDeriv_differentiableOn_noZero.mono (by intro s hs; exact hs.2)) h2
  change DifferentiableOn ℂ (fun s : ℂ =>
      dslope (fun w : ℂ => (x : ℂ) ^ w) 1 s - (x : ℂ) ^ s / s - zeta1LogDeriv s * ((x : ℂ) ^ s / s))
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0}
  exact (h1.sub h2).sub h3

/-- The analytic part `hFunc x` integrates to zero around any rectangle on which `ζ₁ ≠ 0`. -/
lemma rectInt_hFunc_zero_noZero {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hrect : Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0}) :
    rectInt z w (hFunc x) = 0 := by
  have H : DifferentiableOn ℂ (hFunc x) (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    exact (hFunc_differentiableOn_noZero x hx).mono hrect
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (hFunc x) z w H
  simpa [rectInt] using hc

/-- The rectangle identity: integrating `ψIntF x = -ζ'/ζ(s)·x^s/s` around a rectangle
whose interior contains `s = 1` and on which `ζ₁ ≠ 0` yields `x·2πi`. -/
lemma psiIntF_rectInt_eq_noZero {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < (1 : ℂ).re ∧ (1 : ℂ).re < w.re ∧ z.im < (1 : ℂ).im ∧ (1 : ℂ).im < w.im)
    (hrect : (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) ⊆ {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0}) :
    rectInt z w (psiIntF x) = (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  have hzr : z.re < 1 := huin.1
  have hwr : 1 < w.re := huin.2.1
  have hzi : z.im < 0 := huin.2.2.1
  have hwi : 0 < w.im := huin.2.2.2
  have hn1a : ∀ u : ℝ, u ∈ Set.uIcc z.re w.re → (u : ℂ) + z.im * Complex.I ≠ 1 := by
    intro u hu
    apply ne_one_of_im_ne_zero
    have him : ((u : ℂ) + z.im * Complex.I).im = z.im := by simp
    rw [him]
    exact ne_of_lt hzi
  have hn1b : ∀ u : ℝ, u ∈ Set.uIcc z.re w.re → (u : ℂ) + w.im * Complex.I ≠ 1 := by
    intro u hu
    apply ne_one_of_im_ne_zero
    have him : ((u : ℂ) + w.im * Complex.I).im = w.im := by simp
    rw [him]
    exact ne_of_gt hwi
  have hn1c : ∀ v : ℝ, v ∈ Set.uIcc z.im w.im → (w.re : ℂ) + v * Complex.I ≠ 1 := by
    intro v hv
    apply ne_one_of_re_ne_one
    have hre : ((w.re : ℂ) + v * Complex.I).re = w.re := by simp
    rw [hre]
    exact ne_of_gt hwr
  have hn1d : ∀ v : ℝ, v ∈ Set.uIcc z.im w.im → (z.re : ℂ) + v * Complex.I ≠ 1 := by
    intro v hv
    apply ne_one_of_re_ne_one
    have hre : ((z.re : ℂ) + v * Complex.I).re = z.re := by simp
    rw [hre]
    exact ne_of_lt hzr
  let polar : ℂ → ℂ := fun s : ℂ => (x : ℂ) / (s - (1 : ℂ))
  have ipol1 : IntervalIntegrable (fun u : ℝ => polar ((u : ℂ) + z.im * Complex.I)) volume z.re w.re := by
    exact edge_integrable_horiz (f := polar) (U := {s : ℂ | s ≠ 1}) isOpen_compl_singleton
      (continuousOn_polar x) (by intro u hu; dsimp [polar]; exact hn1a u hu)
  have ipol2 : IntervalIntegrable (fun u : ℝ => polar ((u : ℂ) + w.im * Complex.I)) volume z.re w.re := by
    exact edge_integrable_horiz (f := polar) (U := {s : ℂ | s ≠ 1}) isOpen_compl_singleton
      (continuousOn_polar x) (by intro u hu; dsimp [polar]; exact hn1b u hu)
  have ipol3 : IntervalIntegrable (fun v : ℝ => polar ((w.re : ℂ) + v * Complex.I)) volume z.im w.im := by
    exact edge_integrable_vert (f := polar) (U := {s : ℂ | s ≠ 1}) isOpen_compl_singleton
      (continuousOn_polar x) (by intro v hv; dsimp [polar]; exact hn1c v hv)
  have ipol4 : IntervalIntegrable (fun v : ℝ => polar ((z.re : ℂ) + v * Complex.I)) volume z.im w.im := by
    exact edge_integrable_vert (f := polar) (U := {s : ℂ | s ≠ 1}) isOpen_compl_singleton
      (continuousOn_polar x) (by intro v hv; dsimp [polar]; exact hn1d v hv)
  let U0 : Set ℂ := {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0}
  have hU0o : IsOpen U0 := by
    have h1 : IsOpen {s : ℂ | (0 : ℝ) < s.re} := Complex.isOpen_re_gt 0
    have h2 : IsOpen {s : ℂ | riemannZeta₁ s ≠ 0} := by
      have hEq2 : {s : ℂ | riemannZeta₁ s ≠ 0} = riemannZeta₁ ⁻¹' ({0}ᶜ : Set ℂ) := by
        ext s
        simp
      rw [hEq2]
      exact (isOpen_compl_singleton.preimage differentiable_riemannZeta₁.continuous)
    have hEqU : U0 = {s : ℂ | (0 : ℝ) < s.re} ∩ {s : ℂ | riemannZeta₁ s ≠ 0} := by
      ext s
      simp [U0]
    rw [hEqU]
    exact h1.inter h2
  have hfuncC : ContinuousOn (hFunc x) U0 := by
    exact (hFunc_differentiableOn_noZero x hx).continuousOn
  have ih1 : IntervalIntegrable (fun u : ℝ => hFunc x ((u : ℂ) + z.im * Complex.I)) volume z.re w.re := by
    exact edge_integrable_horiz (f := hFunc x) (U := U0) hU0o hfuncC (by
      intro u hu
      have hs : (u : ℂ) + z.im * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
        exact Complex.mem_reProdIm.mpr ⟨by simpa using hu, by simp⟩
      exact hrect hs)
  have ih2 : IntervalIntegrable (fun u : ℝ => hFunc x ((u : ℂ) + w.im * Complex.I)) volume z.re w.re := by
    exact edge_integrable_horiz (f := hFunc x) (U := U0) hU0o hfuncC (by
      intro u hu
      have hs : (u : ℂ) + w.im * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
        exact Complex.mem_reProdIm.mpr ⟨by simpa using hu, by simp⟩
      exact hrect hs)
  have ih3 : IntervalIntegrable (fun v : ℝ => hFunc x ((w.re : ℂ) + v * Complex.I)) volume z.im w.im := by
    exact edge_integrable_vert (f := hFunc x) (U := U0) hU0o hfuncC (by
      intro v hv
      have hs : (w.re : ℂ) + v * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
        exact Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hv⟩
      exact hrect hs)
  have ih4 : IntervalIntegrable (fun v : ℝ => hFunc x ((z.re : ℂ) + v * Complex.I)) volume z.im w.im := by
    exact edge_integrable_vert (f := hFunc x) (U := U0) hU0o hfuncC (by
      intro v hv
      have hs : (z.re : ℂ) + v * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
        exact Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hv⟩
      exact hrect hs)
  have hdecomp : rectInt z w (psiIntF x) = rectInt z w (fun s : ℂ => polar s + hFunc x s) := by
    apply rectInt_congr_boundary
    · intro u hu
      have hpt : (u : ℂ) + z.im * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
        exact Complex.mem_reProdIm.mpr ⟨by simpa using hu, by simp⟩
      have hzf : riemannZeta₁ ((u : ℂ) + z.im * Complex.I) ≠ 0 := (hrect hpt).2
      have h0 : (0 : ℝ) < ((u : ℂ) + z.im * Complex.I).re := (hrect hpt).1
      have hne0 : (u : ℂ) + z.im * Complex.I ≠ 0 := by
        intro h
        have hval : ((u : ℂ) + z.im * Complex.I).re = 0 := congrArg Complex.re h
        have hval2 : ((u : ℂ) + z.im * Complex.I).re = u := by simp
        rw [hval2] at hval
        have hlt : (0 : ℝ) < 0 := by simpa [hval] using h0
        exact (lt_irrefl (0 : ℝ)) hlt
      have hde := psiIntF_eq_polar_add_hFunc_of_zeta1_ne_zero (x := x) hx (s := (u : ℂ) + z.im * Complex.I)
        (hs1 := hn1a u hu) (hs0 := hne0) hzf
      simpa [polar] using hde
    · intro u hu
      have hpt : (u : ℂ) + w.im * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
        exact Complex.mem_reProdIm.mpr ⟨by simpa using hu, by simp⟩
      have hzf : riemannZeta₁ ((u : ℂ) + w.im * Complex.I) ≠ 0 := (hrect hpt).2
      have h0 : (0 : ℝ) < ((u : ℂ) + w.im * Complex.I).re := (hrect hpt).1
      have hne0 : (u : ℂ) + w.im * Complex.I ≠ 0 := by
        intro h
        have hval : ((u : ℂ) + w.im * Complex.I).re = 0 := congrArg Complex.re h
        have hval2 : ((u : ℂ) + w.im * Complex.I).re = u := by simp
        rw [hval2] at hval
        have hlt : (0 : ℝ) < 0 := by simpa [hval] using h0
        exact (lt_irrefl (0 : ℝ)) hlt
      have hde := psiIntF_eq_polar_add_hFunc_of_zeta1_ne_zero (x := x) hx (s := (u : ℂ) + w.im * Complex.I)
        (hs1 := hn1b u hu) (hs0 := hne0) hzf
      simpa [polar] using hde
    · intro v hv
      have hpt : (w.re : ℂ) + v * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
        exact Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hv⟩
      have hzf : riemannZeta₁ ((w.re : ℂ) + v * Complex.I) ≠ 0 := (hrect hpt).2
      have h0 : (0 : ℝ) < ((w.re : ℂ) + v * Complex.I).re := (hrect hpt).1
      have hne0 : (w.re : ℂ) + v * Complex.I ≠ 0 := by
        intro h
        have hval : ((w.re : ℂ) + v * Complex.I).re = 0 := congrArg Complex.re h
        have hval2 : ((w.re : ℂ) + v * Complex.I).re = w.re := by simp
        rw [hval2] at hval
        have hlt : (0 : ℝ) < 0 := by simpa [hval] using h0
        exact (lt_irrefl (0 : ℝ)) hlt
      have hde := psiIntF_eq_polar_add_hFunc_of_zeta1_ne_zero (x := x) hx (s := (w.re : ℂ) + v * Complex.I)
        (hs1 := hn1c v hv) (hs0 := hne0) hzf
      simpa [polar] using hde
    · intro v hv
      have hpt : (z.re : ℂ) + v * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
        exact Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hv⟩
      have hzf : riemannZeta₁ ((z.re : ℂ) + v * Complex.I) ≠ 0 := (hrect hpt).2
      have h0 : (0 : ℝ) < ((z.re : ℂ) + v * Complex.I).re := (hrect hpt).1
      have hne0 : (z.re : ℂ) + v * Complex.I ≠ 0 := by
        intro h
        have hval : ((z.re : ℂ) + v * Complex.I).re = 0 := congrArg Complex.re h
        have hval2 : ((z.re : ℂ) + v * Complex.I).re = z.re := by simp
        rw [hval2] at hval
        have hlt : (0 : ℝ) < 0 := by simpa [hval] using h0
        exact (lt_irrefl (0 : ℝ)) hlt
      have hde := psiIntF_eq_polar_add_hFunc_of_zeta1_ne_zero (x := x) hx (s := (z.re : ℂ) + v * Complex.I)
        (hs1 := hn1d v hv) (hs0 := hne0) hzf
      simpa [polar] using hde
  have hsplit : rectInt z w (fun s : ℂ => polar s + hFunc x s) = rectInt z w polar + rectInt z w (hFunc x) := by
    exact rectInt_add (f := polar) (g := hFunc x) ipol1 ih1 ipol2 ih2 ipol3 ih3 ipol4 ih4
  have hzero : rectInt z w (hFunc x) = 0 := by
    exact rectInt_hFunc_zero_noZero hx hrect
  have hres : rectInt z w polar = (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    dsimp [polar]
    exact rectInt_polar_residue (x : ℂ) hzre hzim huin
  calc
    rectInt z w (psiIntF x) = rectInt z w (fun s : ℂ => polar s + hFunc x s) := hdecomp
    _ = rectInt z w polar + rectInt z w (hFunc x) := hsplit
    _ = (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by rw [hzero, hres, add_zero]

/-- Top horizontal edge at height `+T`, from real part `σ₁` to `perronRe x`. -/
noncomputable def topIntG (σ₁ : ℝ) (x T : ℝ) : ℂ :=
  (∫ (u : ℝ) in σ₁..perronRe x, psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I))

/-- Bottom horizontal edge at height `−T`, from real part `σ₁` to `perronRe x`. -/
noncomputable def botIntG (σ₁ : ℝ) (x T : ℝ) : ℂ :=
  (∫ (u : ℝ) in σ₁..perronRe x, psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I))

/-- Left vertical edge at real part `σ₁`. -/
noncomputable def leftIntG (σ₁ : ℝ) (x T : ℝ) : ℂ :=
  (∫ (t : ℝ) in -T..T, psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I))

/-- `perronZeta − x` equals the three edge integrals of the deformed rectangle with
left side at real part `σ₁ < 1` (unconditional; the rectangle must avoid zeros of `ζ₁`). -/
lemma perronZeta_sub_id_noZero {x : ℝ} (hx : 0 < x) {T σ₁ : ℝ}
    (hT : 0 < T) (hσ₁ : 0 < σ₁) (hσ₁lt : σ₁ < 1) (hper : 1 < perronRe x)
    (hrect : (Set.uIcc σ₁ (perronRe x) ×ℂ Set.uIcc (-T) T) ⊆
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0}) :
    perronZeta x T - (x : ℂ) =
      (((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) * (topIntG σ₁ x T - botIntG σ₁ x T)) +
        (((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ)))) * leftIntG σ₁ x T := by
  let z : ℂ := ((σ₁ : ℂ) - Complex.I * (T : ℂ))
  let w : ℂ := ((perronRe x : ℂ) + Complex.I * (T : ℂ))
  have hzre0 : z.re < w.re := by
    dsimp [z, w]
    simp
    have h : σ₁ < perronRe x := lt_trans hσ₁lt hper
    exact h
  have hzim0 : z.im < w.im := by
    dsimp [z, w]
    simp
    linarith only [hT]
  have huin : z.re < (1 : ℂ).re ∧ (1 : ℂ).re < w.re ∧ z.im < (1 : ℂ).im ∧ (1 : ℂ).im < w.im := by
    repeat' constructor
    · simpa [z] using hσ₁lt
    · simpa [w] using hper
    · simpa [z] using (neg_lt_zero.mpr hT)
    · simpa [w] using hT
  have hrectz : (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) ⊆
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0} := by
    intro s hs
    have hs1 := (Complex.mem_reProdIm.mp hs).1
    have hs2 := (Complex.mem_reProdIm.mp hs).2
    have hzr' : z.re = σ₁ := by dsimp [z]; simp
    have hwr' : w.re = perronRe x := by dsimp [w]; simp
    have hzim' : z.im = -T := by dsimp [z]; simp
    have hwim' : w.im = T := by dsimp [w]; simp
    rw [hzr', hwr'] at hs1
    rw [hzim', hwim'] at hs2
    have hmem : s ∈ (Set.uIcc σ₁ (perronRe x) ×ℂ Set.uIcc (-T) T) := Complex.mem_reProdIm.mpr ⟨hs1, hs2⟩
    exact hrect hmem
  have hz0 : rectInt z w (psiIntF x) = (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    exact psiIntF_rectInt_eq_noZero hx hzre0 hzim0 huin hrectz
  have hzr : z.re = σ₁ := by dsimp [z]; simp
  have hwr : w.re = perronRe x := by dsimp [w]; simp
  have hzi : z.im = -T := by dsimp [z]; simp
  have hwi : w.im = T := by dsimp [w]; simp
  have hz1 : botIntG σ₁ x T - topIntG σ₁ x T + Complex.I * perronRight x T - Complex.I * leftIntG σ₁ x T =
      (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    have hb : (∫ (u : ℝ) in z.re..w.re, psiIntF x ((u : ℂ) + (z.im : ℂ) * Complex.I)) = botIntG σ₁ x T := by
      dsimp [botIntG]
      rw [hzr, hzi]
      congr 1
      funext u
      congr 1
      have h : (u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I = (u : ℂ) - (T : ℂ) * Complex.I := by
        norm_num
        ring
      simpa using h
    have ht : (∫ (u : ℝ) in z.re..w.re, psiIntF x ((u : ℂ) + (w.im : ℂ) * Complex.I)) = topIntG σ₁ x T := by
      simpa [topIntG, hzr, hwr, hwi]
    have hr : (∫ (t : ℝ) in z.im..w.im, psiIntF x ((w.re : ℂ) + (t : ℂ) * Complex.I)) = perronRight x T := by
      simpa [perronRight, hwr, hzi, hwi]
    have hl : (∫ (t : ℝ) in z.im..w.im, psiIntF x ((z.re : ℂ) + (t : ℂ) * Complex.I)) = leftIntG σ₁ x T := by
      simpa [leftIntG, hzr, hzi, hwi]
    have hz0' : (∫ (u : ℝ) in z.re..w.re, psiIntF x ((u : ℂ) + (z.im : ℂ) * Complex.I)) -
          (∫ (u : ℝ) in z.re..w.re, psiIntF x ((u : ℂ) + (w.im : ℂ) * Complex.I)) +
          Complex.I * (∫ (t : ℝ) in z.im..w.im, psiIntF x ((w.re : ℂ) + (t : ℂ) * Complex.I)) -
          Complex.I * (∫ (t : ℝ) in z.im..w.im, psiIntF x ((z.re : ℂ) + (t : ℂ) * Complex.I)) =
          (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
        simpa [rectInt, smul_eq_mul] using hz0
    simpa [hb, ht, hr, hl] using hz0'
  let c : ℂ := (1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
  let r : ℂ := (1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ))
  have hP : perronZeta x T = r * perronRight x T := by
    rfl
  have hcI : c * Complex.I = r := by
    dsimp [c, r]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hI, hπ] <;> ring
  have hc2 : c * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) = 1 := by
    dsimp [c]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hI, hπ]
  have hIR : Complex.I * perronRight x T =
      (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) + (topIntG σ₁ x T - botIntG σ₁ x T) +
        Complex.I * leftIntG σ₁ x T := by
    linear_combination hz1
  have h1 : c * ((x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) = (x : ℂ) := by
    calc c * (x * ((2:ℂ)*(Real.pi:ℂ)*Complex.I)) = x * (c * ((2:ℂ)*(Real.pi:ℂ)*Complex.I)) := by ring
         _ = x := by rw [hc2, mul_one]
  have h2 : c * (Complex.I * leftIntG σ₁ x T) = r * leftIntG σ₁ x T := by
    calc c * (Complex.I * leftIntG σ₁ x T) = (c * Complex.I) * leftIntG σ₁ x T := by ring
         _ = r * leftIntG σ₁ x T := by rw [hcI]
  have h1n : c * (x : ℂ) * (Real.pi : ℂ) * Complex.I * 2 = (x : ℂ) := by
    calc c * (x:ℂ) * (Real.pi:ℂ) * Complex.I * 2 = c * ((x:ℂ) * ((2:ℂ)*(Real.pi:ℂ)*Complex.I)) := by ring
         _ = (x:ℂ) := h1
  have h2n : c * Complex.I * leftIntG σ₁ x T = r * leftIntG σ₁ x T := by
    calc c * Complex.I * leftIntG σ₁ x T = c * (Complex.I * leftIntG σ₁ x T) := by ring
         _ = r * leftIntG σ₁ x T := h2
  have hmain : c * (Complex.I * perronRight x T) = (x : ℂ) + c * (topIntG σ₁ x T - botIntG σ₁ x T) + r * leftIntG σ₁ x T := by
    rw [hIR]
    ring_nf
    rw [h1n, h2n]
    ring
  calc
    perronZeta x T - (x : ℂ) = r * perronRight x T - (x : ℂ) := by rw [hP]
    _ = c * (Complex.I * perronRight x T) - (x : ℂ) := by
      have hsub : r * perronRight x T = c * (Complex.I * perronRight x T) := by
        calc r * perronRight x T = (c * Complex.I) * perronRight x T := by rw [hcI]
             _ = c * (Complex.I * perronRight x T) := by ring
      rw [hsub]
    _ = ((x : ℂ) + c * (topIntG σ₁ x T - botIntG σ₁ x T) + r * leftIntG σ₁ x T) - (x : ℂ) := by rw [hmain]
    _ = c * (topIntG σ₁ x T - botIntG σ₁ x T) + r * leftIntG σ₁ x T := by
      rw [show c = (1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) by rfl]
      rw [show r = (1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ)) by rfl]
      ring


/-- Bound `‖perronZeta − x‖` by the norms of the three edge integrals (up to `1/2π`),
with the deformed rectangle left side at `σ₁` (mirror of `perronZeta_sub_id_norm_le`). -/
lemma perronZeta_sub_id_norm_le_noZero {x : ℝ} (hx : 0 < x) {T σ₁ : ℝ}
    (hT : 0 < T) (hσ₁ : 0 < σ₁) (hσ₁lt : σ₁ < 1) (hper : 1 < perronRe x)
    (hrect : (Set.uIcc σ₁ (perronRe x) ×ℂ Set.uIcc (-T) T) ⊆
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0}) :
    ‖perronZeta x T - (x : ℂ)‖ ≤
      (1 / (2 * Real.pi)) *
        ((∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) +
         (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) +
         (∫ (t : ℝ) in -T..T, ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖)) := by
  have hleA : σ₁ ≤ perronRe x := le_of_lt (lt_trans hσ₁lt hper)
  have hleT : -T ≤ T := by linarith only [hT]
  have hsub := perronZeta_sub_id_noZero hx hT hσ₁ hσ₁lt hper hrect
  have htopb : ‖topIntG σ₁ x T‖ ≤ (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) := by
    dsimp [topIntG]
    exact intervalIntegral.norm_integral_le_integral_norm hleA
  have hbotb : ‖botIntG σ₁ x T‖ ≤ (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) := by
    dsimp [botIntG]
    exact intervalIntegral.norm_integral_le_integral_norm hleA
  have hleftb : ‖leftIntG σ₁ x T‖ ≤ (∫ (t : ℝ) in -T..T, ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) := by
    dsimp [leftIntG]
    exact intervalIntegral.norm_integral_le_integral_norm hleT
  have hc : ‖((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div]
    simp [Real.pi_pos.le]
  have hr : ‖((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div]
    simp [Real.pi_pos.le]
  rw [hsub]
  have h1 : ‖((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) * (topIntG σ₁ x T - botIntG σ₁ x T)‖ ≤
      (1 / (2 * Real.pi)) * (‖topIntG σ₁ x T‖ + ‖botIntG σ₁ x T‖) := by
    have hnorm := norm_mul_le ((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) (topIntG σ₁ x T - botIntG σ₁ x T)
    have hsubn : ‖topIntG σ₁ x T - botIntG σ₁ x T‖ ≤ ‖topIntG σ₁ x T‖ + ‖botIntG σ₁ x T‖ := norm_sub_le _ _
    rw [hc] at hnorm
    have hcoef : 0 ≤ 1 / (2 * Real.pi) := by positivity
    calc
      ‖((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) * (topIntG σ₁ x T - botIntG σ₁ x T)‖
          ≤ (1 / (2 * Real.pi)) * ‖topIntG σ₁ x T - botIntG σ₁ x T‖ := hnorm
      _ ≤ (1 / (2 * Real.pi)) * (‖topIntG σ₁ x T‖ + ‖botIntG σ₁ x T‖) :=
          mul_le_mul_of_nonneg_left hsubn hcoef
  have h2 : ‖((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ))) * leftIntG σ₁ x T‖ ≤
      (1 / (2 * Real.pi)) * ‖leftIntG σ₁ x T‖ := by
    have hnorm := norm_mul_le ((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ))) (leftIntG σ₁ x T)
    rw [hr] at hnorm
    simpa using hnorm
  have htot : ‖((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) * (topIntG σ₁ x T - botIntG σ₁ x T) +
      ((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ))) * leftIntG σ₁ x T‖ ≤
      (1 / (2 * Real.pi)) * (‖topIntG σ₁ x T‖ + ‖botIntG σ₁ x T‖ + ‖leftIntG σ₁ x T‖) := by
    have hadd := norm_add_le (((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) * (topIntG σ₁ x T - botIntG σ₁ x T))
      (((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ))) * leftIntG σ₁ x T)
    linarith only [h1, h2, hadd]
  have hcoef : 0 ≤ 1 / (2 * Real.pi) := by positivity
  have hfin : (1 / (2 * Real.pi)) * (‖topIntG σ₁ x T‖ + ‖botIntG σ₁ x T‖ + ‖leftIntG σ₁ x T‖) ≤
      (1 / (2 * Real.pi)) *
        ((∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) +
         (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) +
         (∫ (t : ℝ) in -T..T, ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖)) := by
    have hsum : ‖topIntG σ₁ x T‖ + ‖botIntG σ₁ x T‖ + ‖leftIntG σ₁ x T‖ ≤
        (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) +
        (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) +
        (∫ (t : ℝ) in -T..T, ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) := by
      linarith only [htopb, hbotb, hleftb]
    exact mul_le_mul_of_nonneg_left hsum hcoef
  exact le_trans htot hfin

lemma psiIntF_norm_le_of_logDeriv_bound {x : ℝ} (hx : 0 < x) (s : ℂ) {B : ℝ}
    (hB : ‖deriv riemannZeta s / riemannZeta s‖ ≤ B) :
    ‖psiIntF x s‖ ≤ B * x ^ s.re / ‖s‖ := by
  calc
    ‖psiIntF x s‖ = ‖deriv riemannZeta s / riemannZeta s‖ * (x : ℝ) ^ s.re / ‖s‖ := psiIntF_norm hx s
    _ ≤ B * (x : ℝ) ^ s.re / ‖s‖ := by
      have hxrpow : 0 ≤ (x : ℝ) ^ s.re := Real.rpow_nonneg (le_of_lt hx) s.re
      have hm : ‖deriv riemannZeta s / riemannZeta s‖ * (x : ℝ) ^ s.re ≤ B * (x : ℝ) ^ s.re :=
        mul_le_mul_of_nonneg_right hB hxrpow
      exact div_le_div_of_nonneg_right hm (norm_nonneg s)

lemma psiIntF_horiz_le_noZero {x : ℝ} (hx : 0 < x) {u r T : ℝ} (hT : 0 < T) (hr : |r| = T)
    {B : ℝ} (hB : ‖deriv riemannZeta (((u : ℂ) + (r : ℂ) * Complex.I)) /
        riemannZeta (((u : ℂ) + (r : ℂ) * Complex.I))‖ ≤ B) :
    ‖psiIntF x ((u : ℂ) + (r : ℂ) * Complex.I)‖ ≤ B * (x : ℝ) ^ u / T := by
  let s : ℂ := (u : ℂ) + (r : ℂ) * Complex.I
  have hsre : s.re = u := by dsimp [s]; simp
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hB
  have hBnd := psiIntF_norm_le_of_logDeriv_bound hx s hB
  have hnorm : T ≤ ‖s‖ := by
    calc
      T = |r| := hr.symm
      _ ≤ ‖s‖ := by
        have himv : s.im = r := by dsimp [s]; simp
        calc |r| = |s.im| := by rw [himv]
             _ ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hfac : 0 ≤ B * (x : ℝ) ^ u := mul_nonneg hB0 (Real.rpow_nonneg (le_of_lt hx) u)
  calc
    ‖psiIntF x s‖ ≤ B * (x : ℝ) ^ s.re / ‖s‖ := hBnd
    _ = B * (x : ℝ) ^ u / ‖s‖ := by rw [hsre]
    _ ≤ B * (x : ℝ) ^ u / T := div_le_div_of_nonneg_left hfac hT hnorm

private lemma interval_integral_le_const_mul {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} {c : ℝ}
    (hf : IntervalIntegrable f volume a b) (hfc : ∀ u ∈ Set.Icc a b, f u ≤ c) :
    (∫ (u : ℝ) in a..b, f u) ≤ c * (b - a) := by
  let g : ℝ → ℝ := fun _ => c
  have hgC : ContinuousOn g (Set.uIcc a b) := by
    dsimp [g]
    fun_prop
  have hg : IntervalIntegrable g volume a b := ContinuousOn.intervalIntegrable hgC
  have hle := intervalIntegral.integral_mono_on hab hf hg (by
    intro u hu
    dsimp [g]
    exact hfc u hu)
  have hgval : (∫ (u : ℝ) in a..b, g u) = c * (b - a) := by
    dsimp [g]
    rw [intervalIntegral.integral_const]
    ring
  rwa [hgval] at hle

/-- Bound of the top horizontal integral `∫_{σ₁}^{perronRe x} ‖ψIntF x (u+iT)‖ du`
from a pointwise log-derivative bound `B` along the edge. -/
lemma topEdgeInt_le_noZero {x : ℝ} (hx : (1 : ℝ) ≤ x) {T σ₁ : ℝ} (hT : 0 < T)
    (hσ₁le : σ₁ ≤ perronRe x) {B : ℝ}
    (hB : ∀ u : ℝ, u ∈ Set.Icc σ₁ (perronRe x) →
      ‖deriv riemannZeta (((u : ℂ) + (T : ℂ) * Complex.I)) /
        riemannZeta (((u : ℂ) + (T : ℂ) * Complex.I))‖ ≤ B)
    (hInt : IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) volume σ₁ (perronRe x)) :
    (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) ≤
      B * (x : ℝ) ^ perronRe x * (perronRe x - σ₁) / T := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hc : ∀ u : ℝ, u ∈ Set.Icc σ₁ (perronRe x) →
      ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B * (x : ℝ) ^ perronRe x / T := by
    intro u hu
    have hb := hB u hu
    have hle := psiIntF_horiz_le_noZero hxpos (u := u) (r := T) hT (abs_of_pos hT) hb
    have hrpow : (x : ℝ) ^ u ≤ (x : ℝ) ^ perronRe x := by
      by_cases hx1 : x = 1
      · subst x
        simp
      · have hxgt : (1 : ℝ) < x := lt_of_le_of_ne hx (Ne.symm hx1)
        exact (Real.rpow_le_rpow_left_iff hxgt).2 hu.2
    have hc0 : 0 ≤ B / T := div_nonneg (by
      have : 0 ≤ ‖deriv riemannZeta ((((u : ℂ) + (T : ℂ) * Complex.I))) /
        riemannZeta (((u : ℂ) + (T : ℂ) * Complex.I))‖ := norm_nonneg _
      exact le_trans this hb) (le_of_lt hT)
    calc
      ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B * (x : ℝ) ^ u / T := hle
      _ = (B / T) * (x : ℝ) ^ u := by ring
      _ ≤ (B / T) * (x : ℝ) ^ perronRe x := mul_le_mul_of_nonneg_left hrpow hc0
      _ = B * (x : ℝ) ^ perronRe x / T := by ring
  have hfin := interval_integral_le_const_mul hσ₁le hInt (by intro u hu; exact hc u hu)
  have hval : (B * (x : ℝ) ^ perronRe x / T) * (perronRe x - σ₁) =
      B * (x : ℝ) ^ perronRe x * (perronRe x - σ₁) / T := by ring
  rwa [hval] at hfin

/-- Bound of the bottom horizontal integral `∫_{σ₁}^{perronRe x} ‖ψIntF x (u + (−T)·I)‖ du`
(the bottom edge of the rectangle at height `−T`; written with `−T` to match the
per-point horizontal bound directly). -/

lemma botEdgeInt_le_noZero {x : ℝ} (hx : (1 : ℝ) ≤ x) {T σ₁ : ℝ} (hT : 0 < T)
    (hσ₁le : σ₁ ≤ perronRe x) {B : ℝ}
    (hB : ∀ u : ℝ, u ∈ Set.Icc σ₁ (perronRe x) →
      ‖deriv riemannZeta (((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I)) /
        riemannZeta (((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I))‖ ≤ B)
    (hInt : IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I)‖) volume σ₁ (perronRe x)) :
    (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I)‖) ≤
      B * (x : ℝ) ^ perronRe x * (perronRe x - σ₁) / T := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hc : ∀ u : ℝ, u ∈ Set.Icc σ₁ (perronRe x) →
      ‖psiIntF x ((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I)‖ ≤ B * (x : ℝ) ^ perronRe x / T := by
    intro u hu
    have hb := hB u hu
    have hAbs : |-(T : ℝ)| = T := by rw [abs_neg, abs_of_pos hT]
    have hle := psiIntF_horiz_le_noZero hxpos (u := u) (r := -T) hT hAbs hb
    have hrpow : (x : ℝ) ^ u ≤ (x : ℝ) ^ perronRe x := by
      by_cases hx1 : x = 1
      · subst x
        simp
      · have hxgt : (1 : ℝ) < x := lt_of_le_of_ne hx (Ne.symm hx1)
        exact (Real.rpow_le_rpow_left_iff hxgt).2 hu.2
    have hc0 : 0 ≤ B / T := div_nonneg (le_trans (norm_nonneg _) hb) (le_of_lt hT)
    calc
      ‖psiIntF x ((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I)‖ ≤ B * (x : ℝ) ^ u / T := hle
      _ = (B / T) * (x : ℝ) ^ u := by ring
      _ ≤ (B / T) * (x : ℝ) ^ perronRe x := mul_le_mul_of_nonneg_left hrpow hc0
      _ = B * (x : ℝ) ^ perronRe x / T := by ring
  have hfin := interval_integral_le_const_mul hσ₁le hInt (by intro u hu; exact hc u hu)
  have hval : (B * (x : ℝ) ^ perronRe x / T) * (perronRe x - σ₁) =
      B * (x : ℝ) ^ perronRe x * (perronRe x - σ₁) / T := by ring
  rwa [hval] at hfin

/-- Near-axis slice of the left edge, `|t| ≤ 2`:
`∫_{−2}^{2} ‖ψIntF x (σ₁+it)‖ dt ≤ 4·(C₂ + 1/(1−σ₁))·x^{σ₁}/σ₁`,
given the pole-type log-derivative bound `‖ζ'/ζ(σ₁+it)‖ ≤ C₂ + 1/‖s−1‖` (M2). -/
lemma leftEdgeNearAxis_le_noZero {x σ₁ : ℝ} (hx : 0 < x) (hσ₁pos : 0 < σ₁)
    (hδ₁ : 0 < 1 - σ₁) {C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (hM2 : ∀ t : ℝ, |t| ≤ 2 →
      ‖deriv riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C₂ + 1 / ‖(((σ₁ : ℂ) + (t : ℂ) * Complex.I)) - 1‖)
    (hInt : IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) volume (-2) 2) :
    (∫ (t : ℝ) in -2..2, ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      4 * (C₂ + 1 / (1 - σ₁)) * (x : ℝ) ^ σ₁ / σ₁ := by
  have hc : ∀ t : ℝ, t ∈ Set.Icc (-2) 2 →
      ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (C₂ + 1 / (1 - σ₁)) * (x : ℝ) ^ σ₁ / σ₁ := by
    intro t ht
    have ht2 : |t| ≤ 2 := by
      have h1 : (-2 : ℝ) ≤ t := ht.1
      have h2 : t ≤ 2 := ht.2
      exact abs_le.mpr ⟨by linarith only [h1], by linarith only [h2]⟩
    have hb := hM2 t ht2
    have hden : (1 - σ₁) ≤ ‖(((σ₁ : ℂ) + (t : ℂ) * Complex.I)) - 1‖ := by
      have hre : ((((σ₁ : ℂ) + (t : ℂ) * Complex.I)) - 1).re = σ₁ - 1 := by simp
      have h1 : (1 - σ₁) ≤ |σ₁ - 1| := by
        rw [abs_of_nonpos (by linarith only [hδ₁] : σ₁ - 1 ≤ 0)]
        linarith only []
      calc
        (1 - σ₁) ≤ |σ₁ - 1| := h1
        _ = |((((σ₁ : ℂ) + (t : ℂ) * Complex.I)) - 1).re| := by rw [hre]
        _ ≤ ‖(((σ₁ : ℂ) + (t : ℂ) * Complex.I)) - 1‖ := Complex.abs_re_le_norm _
    have hδ₁le : 1 / ‖(((σ₁ : ℂ) + (t : ℂ) * Complex.I)) - 1‖ ≤ 1 / (1 - σ₁) :=
      one_div_le_one_div_of_le hδ₁ hden
    have hB : ‖deriv riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C₂ + 1 / (1 - σ₁) := by
      have h1 : C₂ + 1 / ‖(((σ₁ : ℂ) + (t : ℂ) * Complex.I)) - 1‖ ≤ C₂ + 1 / (1 - σ₁) := by
        linarith only [hδ₁le]
      exact le_trans hb h1
    have hBnd := psiIntF_norm_le_of_logDeriv_bound hx ((σ₁ : ℂ) + (t : ℂ) * Complex.I) hB
    have hsre : ((σ₁ : ℂ) + (t : ℂ) * Complex.I).re = σ₁ := by simp
    have hns : σ₁ ≤ ‖((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ := by
      have hre : ‖((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ ≥ |(((σ₁ : ℂ) + (t : ℂ) * Complex.I)).re| := Complex.abs_re_le_norm _
      calc σ₁ = |σ₁| := (abs_of_pos hσ₁pos).symm
           _ = |(((σ₁ : ℂ) + (t : ℂ) * Complex.I)).re| := by rw [hsre]
           _ ≤ ‖((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ := hre
    have hC0 : 0 ≤ C₂ + 1 / (1 - σ₁) := by
      have hpos : 0 < 1 / (1 - σ₁) := one_div_pos.mpr hδ₁
      linarith only [hC₂, hpos]
    have hfac : 0 ≤ (C₂ + 1 / (1 - σ₁)) * (x : ℝ) ^ σ₁ :=
      mul_nonneg hC0 (Real.rpow_nonneg (le_of_lt hx) σ₁)
    calc
      ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (C₂ + 1 / (1 - σ₁)) * (x : ℝ) ^ σ₁ / ‖((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [hsre] at hBnd
        exact hBnd
      _ ≤ (C₂ + 1 / (1 - σ₁)) * (x : ℝ) ^ σ₁ / σ₁ := div_le_div_of_nonneg_left hfac hσ₁pos hns
  have hInt2 : IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) volume (-2) 2 := hInt
  have hfin := interval_integral_le_const_mul (by norm_num) hInt2 (by intro t ht; exact hc t ht)
  have hval : ((C₂ + 1 / (1 - σ₁)) * (x : ℝ) ^ σ₁ / σ₁) * (2 - (-2)) =
      4 * (C₂ + 1 / (1 - σ₁)) * (x : ℝ) ^ σ₁ / σ₁ := by ring
  rwa [hval] at hfin

/-- Far (positive-height) slice of the left edge: `2 ≤ t ≤ T`.
`∫_{2}^{T} ‖ψIntF x (σ₁+it)‖ dt ≤ C·x^{σ₁}·(log(T+3)+1)^5·log(T/2)`
from the region log-derivative bound (M1-shape) `‖ζ'/ζ(σ₁+it)‖ ≤ C·(log(|t|+3)+1)^5`. -/
lemma leftEdgeFarPos_le_noZero {x σ₁ : ℝ} (hx : 0 < x) (hσ₁pos : 0 < σ₁) {T C : ℝ}
    (h2T : 2 ≤ T) (hC : 0 ≤ C)
    (hB : ∀ t : ℝ, t ∈ Set.Icc 2 T →
      ‖deriv riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C * (Real.log (|t| + 3) + 1) ^ 5)
    (hInt : IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) volume 2 T) :
    (∫ (t : ℝ) in 2..T, ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      C * (x : ℝ) ^ σ₁ * (Real.log (T + 3) + 1) ^ 5 * Real.log (T / 2) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) h2T
  have hT2 : 2 ≤ T := h2T
  have hlogT : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith only [h2T])
  have hM0 : 0 ≤ C * (Real.log (T + 3) + 1) ^ 5 := by positivity

  let M : ℝ := C * (Real.log (T + 3) + 1) ^ 5
  have hM0' : 0 ≤ M := by
    dsimp [M]
    have hb2 : (1 : ℝ) ≤ T + 3 := by linarith only [h2T]
    have hb3 : 0 ≤ Real.log (T + 3) + 1 := by have h1 := Real.log_nonneg hb2; linarith only [hlogT]
    positivity
  have hpt : ∀ t : ℝ, t ∈ Set.Icc 2 T →
      ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * (x : ℝ) ^ σ₁ * t⁻¹ := by
    intro t ht
    have ht2 : 2 ≤ t := ht.1
    have htT : t ≤ T := ht.2
    have ht0 : 0 ≤ t := by linarith only [ht2]
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht2
    have htabs : |t| = t := abs_of_nonneg ht0
    have hb := hB t ht
    have hle : |t| + 3 ≤ T + 3 := by linarith only [htT, htabs]
    have hlog : Real.log (|t| + 3) ≤ Real.log (T + 3) := Real.log_le_log (by linarith only [ht2, htabs]) hle
    have hb1 : (1 : ℝ) ≤ |t| + 3 := by linarith only [ht2, htabs]
    have hbase0 : 0 ≤ Real.log (|t| + 3) + 1 := by have h1 := Real.log_nonneg hb1; linarith only [h1]
    have hb2 : (1 : ℝ) ≤ T + 3 := by linarith only [h2T]
    have hb3 : 0 ≤ Real.log (T + 3) + 1 := by have h1 := Real.log_nonneg hb2; linarith only [hlogT]
    have hle5 : (Real.log (|t| + 3) + 1) ≤ Real.log (T + 3) + 1 := by linarith only [hlog]
    have hlogle : (Real.log (|t| + 3) + 1) ^ 5 ≤ (Real.log (T + 3) + 1) ^ 5 :=
      pow_le_pow_left₀ hbase0 hle5 5
    have hBle : ‖deriv riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ M := by
      have hc0 : 0 ≤ C * (Real.log (|t| + 3) + 1) ^ 5 :=
        mul_nonneg hC (pow_nonneg hbase0 5)
      have hmul : C * (Real.log (|t| + 3) + 1) ^ 5 ≤ M := by
        dsimp [M]
        exact mul_le_mul_of_nonneg_left hlogle hC
      exact le_trans hb hmul
    let s : ℂ := ((σ₁ : ℂ) + (t : ℂ) * Complex.I)
    have hBnd := psiIntF_norm_le_of_logDeriv_bound hx s hBle
    have hsre : s.re = σ₁ := by dsimp [s]; simp
    have hns : t ≤ ‖s‖ := by
      calc
        t = |t| := htabs.symm
        _ = |s.im| := by dsimp [s]; simp
        _ ≤ ‖s‖ := Complex.abs_im_le_norm s
    have hMxp : 0 ≤ M * (x : ℝ) ^ σ₁ := mul_nonneg hM0' (Real.rpow_nonneg (le_of_lt hx) σ₁)
    calc
      ‖psiIntF x s‖ ≤ M * (x : ℝ) ^ s.re / ‖s‖ := by simpa [M] using hBnd
      _ = M * (x : ℝ) ^ σ₁ / ‖s‖ := by rw [hsre]
      _ ≤ M * (x : ℝ) ^ σ₁ / t := div_le_div_of_nonneg_left hMxp htpos hns
      _ = M * (x : ℝ) ^ σ₁ * t⁻¹ := by
        rw [div_eq_mul_inv]
  let c : ℝ := M * (x : ℝ) ^ σ₁
  let g : ℝ → ℝ := fun t : ℝ => c * t⁻¹
  have hgInt : IntervalIntegrable g volume 2 T := by
    refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.mul continuousOn_const ?_
    -- (fun t => t⁻¹) continuous on the closed interval (points are ≠ 0)
    have hc : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc 2 T) := by
      intro u hu
      have hu2 : 2 ≤ u := by
        have hu' : u ∈ Set.Icc 2 T := by rw [Set.uIcc_of_le h2T] at hu; exact hu
        exact hu'.1
      have hu0 : u ≠ 0 := by linarith only [hu2]
      have hid : ContinuousAt (fun t : ℝ => t) u := continuousAt_id
      exact (hid.inv₀ hu0).continuousWithinAt
    intro u hu
    exact hc u hu
  have hle := intervalIntegral.integral_mono_on h2T hInt hgInt (by
    intro t ht
    dsimp [g, c]
    have h1 : M * (x : ℝ) ^ σ₁ * t⁻¹ = M * (x : ℝ) ^ σ₁ * t⁻¹ := rfl
    simpa [h1] using hpt t ht)
  have hgval : (∫ (t : ℝ) in 2..T, g t) = c * Real.log (T / 2) := by
    dsimp [g]
    rw [intervalIntegral.integral_const_mul (𝕜 := ℝ)]
    rw [integral_inv_of_pos (by norm_num : (0 : ℝ) < 2) hTpos]
  have hgval2 : (∫ (t : ℝ) in 2..T, g t) = M * (x : ℝ) ^ σ₁ * Real.log (T / 2) := by
    simpa [c] using hgval
  rw [hgval2] at hle
  simpa [M, c, mul_assoc, mul_comm, mul_left_comm] using hle

/-- Far (negative-height) slice of the left edge: `−T ≤ t ≤ −2`.
`∫_{−T}^{−2} ‖ψIntF x (σ₁+it)‖ dt ≤ C·x^{σ₁}·(log(T+3)+1)^5·log(T/2)`
from the region log-derivative bound (M1-shape) `‖ζ'/ζ(σ₁+it)‖ ≤ C·(log(|t|+3)+1)^5`
on the negative heights `t ∈ [−T,−2]`. -/
lemma leftEdgeFarNeg_le_noZero {x σ₁ : ℝ} (hx : 0 < x) {T C : ℝ}
    (h2T : 2 ≤ T) (hC : 0 ≤ C)
    (hB : ∀ t : ℝ, t ∈ Set.Icc (-T) (-2) →
      ‖deriv riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C * (Real.log (|t| + 3) + 1) ^ 5)
    (hInt : IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) volume (-T) (-2)) :
    (∫ (t : ℝ) in -T..-2, ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      C * (x : ℝ) ^ σ₁ * (Real.log (T + 3) + 1) ^ 5 * Real.log (T / 2) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) h2T
  let M : ℝ := C * (Real.log (T + 3) + 1) ^ 5
  have hM0 : 0 ≤ M := by
    dsimp [M]
    have hb2 : (1 : ℝ) ≤ T + 3 := by linarith only [h2T]
    have hb3 : 0 ≤ Real.log (T + 3) + 1 := by have h1 := Real.log_nonneg hb2; linarith only [h1]
    positivity
  let c : ℝ := M * (x : ℝ) ^ σ₁
  have hpt : ∀ t : ℝ, t ∈ Set.Icc (-T) (-2) →
      ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ c * (-t)⁻¹ := by
    intro t ht
    have htneg : t < 0 := by
      have h2 : t ≤ -2 := ht.2
      linarith only [h2]
    have htabs : |t| = -t := abs_of_neg htneg
    have hb := hB t ht
    have hle_abs : C * (Real.log (|t| + 3) + 1) ^ 5 ≤ M := by
      have ht1 : -T ≤ t := ht.1
      have hle : |t| + 3 ≤ T + 3 := by rw [htabs]; linarith only [ht1]
      have hlog : Real.log (|t| + 3) ≤ Real.log (T + 3) := Real.log_le_log (by linarith only [htneg, htabs]) hle
      have hb1 : (1 : ℝ) ≤ |t| + 3 := by linarith only [abs_nonneg t, htneg, htabs]
      have hbase0 : 0 ≤ Real.log (|t| + 3) + 1 := by have h1 := Real.log_nonneg hb1; linarith only [h1]
      have hb2 : (1 : ℝ) ≤ T + 3 := by linarith only [h2T]
      have hb3 : 0 ≤ Real.log (T + 3) + 1 := by have h1 := Real.log_nonneg hb2; linarith only [h1]
      have hle5 : (Real.log (|t| + 3) + 1) ≤ Real.log (T + 3) + 1 := by linarith only [hlog]
      have hlogle : (Real.log (|t| + 3) + 1) ^ 5 ≤ (Real.log (T + 3) + 1) ^ 5 :=
        pow_le_pow_left₀ hbase0 hle5 5
      dsimp [M]
      exact mul_le_mul_of_nonneg_left hlogle hC
    have hBle : ‖deriv riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ M := by
      exact le_trans hb hle_abs
    let s : ℂ := ((σ₁ : ℂ) + (t : ℂ) * Complex.I)
    have hBnd := psiIntF_norm_le_of_logDeriv_bound hx s hBle
    have hsre : s.re = σ₁ := by dsimp [s]; simp
    have hns : |t| ≤ ‖s‖ := by
      calc
        |t| = |s.im| := by dsimp [s]; simp
        _ ≤ ‖s‖ := Complex.abs_im_le_norm s
    have hMxp : 0 ≤ M * (x : ℝ) ^ σ₁ := mul_nonneg hM0 (Real.rpow_nonneg (le_of_lt hx) σ₁)
    have htp : 0 < -t := by linarith only [htneg]
    calc
      ‖psiIntF x s‖ ≤ M * (x : ℝ) ^ s.re / ‖s‖ := by simpa [M] using hBnd
      _ = M * (x : ℝ) ^ σ₁ / ‖s‖ := by rw [hsre]
      _ ≤ M * (x : ℝ) ^ σ₁ / (-t) := by
        have hns2 : -t ≤ ‖s‖ := by rw [htabs] at hns; exact hns
        exact div_le_div_of_nonneg_left hMxp htp hns2
      _ = c * (-t)⁻¹ := by
        dsimp [c]
        rw [div_eq_mul_inv]
  -- g(t) = c·(−t)⁻¹
  let g : ℝ → ℝ := fun t : ℝ => c * (-t)⁻¹
  have hgInt : IntervalIntegrable g volume (-T) (-2) := by
    refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.mul continuousOn_const ?_
    intro u hu
    have hu2 : u ≤ -2 := by
      have hu' : u ∈ Set.Icc (-T) (-2) := by rw [Set.uIcc_of_le (by linarith only [h2T])] at hu; exact hu
      exact hu'.2
    have hu0 : -u ≠ 0 := by linarith only [hu2]
    have hid : ContinuousAt (fun t : ℝ => -t) u := by fun_prop
    exact (hid.inv₀ hu0).continuousWithinAt
  have hle := intervalIntegral.integral_mono_on (by linarith only [h2T] : -T ≤ -2) hInt hgInt (by
    intro t ht
    dsimp [g]
    exact hpt t ht)
  -- compute ∫_{−T}^{−2} g = c·log(T/2) by change of variable u = −t
  have hg_eq : (fun t : ℝ => g t) = fun t : ℝ => (fun u : ℝ => c * u⁻¹) (-t) := by
    funext t
    dsimp [g]
  have hcomp : (∫ (t : ℝ) in -T..-2, g t) = (∫ (t : ℝ) in 2..T, (fun u : ℝ => c * u⁻¹) t) := by
    rw [hg_eq]
    have hc := intervalIntegral.integral_comp_neg (a := -T) (b := -2) (f := fun u : ℝ => c * u⁻¹)
    simpa using hc
  have hval : (∫ (t : ℝ) in 2..T, (fun u : ℝ => c * u⁻¹) t) = c * Real.log (T / 2) := by
    rw [intervalIntegral.integral_const_mul (𝕜 := ℝ)]
    rw [integral_inv_of_pos (by norm_num : (0 : ℝ) < 2) hTpos]
  have hgval : (∫ (t : ℝ) in -T..-2, g t) = c * Real.log (T / 2) := by
    rw [hcomp, hval]
  rw [hgval] at hle
  simpa [M, c, mul_assoc, mul_comm, mul_left_comm] using hle

/-- Whole left edge bound: `∫_{−T}^{T} ‖ψIntF x (σ₁+it)‖ dt` is at most the sum of the
near-axis, far-negative and far-positive bounds. -/
lemma leftEdgeTot_le_noZero {x σ₁ : ℝ} (hx : 0 < x) (hσ₁pos : 0 < σ₁)
    (hδ₁ : 0 < 1 - σ₁) {T C C₂ : ℝ} (h2T : 2 ≤ T) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂)
    (hNear : ∀ t : ℝ, |t| ≤ 2 →
      ‖deriv riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C₂ + 1 / ‖(((σ₁ : ℂ) + (t : ℂ) * Complex.I)) - 1‖)
    (hFarPos : ∀ t : ℝ, t ∈ Set.Icc 2 T →
      ‖deriv riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C * (Real.log (|t| + 3) + 1) ^ 5)
    (hFarNeg : ∀ t : ℝ, t ∈ Set.Icc (-T) (-2) →
      ‖deriv riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) /
        riemannZeta (((σ₁ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C * (Real.log (|t| + 3) + 1) ^ 5)
    (hIntT : IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) volume (-T) T) :
    (∫ (t : ℝ) in -T..T, ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      C * (x : ℝ) ^ σ₁ * (Real.log (T + 3) + 1) ^ 5 * Real.log (T / 2) +
      4 * (C₂ + 1 / (1 - σ₁)) * (x : ℝ) ^ σ₁ / σ₁ +
      C * (x : ℝ) ^ σ₁ * (Real.log (T + 3) + 1) ^ 5 * Real.log (T / 2) := by
  let F : ℝ → ℝ := fun t : ℝ => ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖
  have hsub1 : Set.uIcc (-T) (-2) ⊆ Set.uIcc (-T) T := by
    intro z hz
    have hz1 : z ∈ Set.Icc (-T) (-2) := by simpa [Set.uIcc_of_le (by linarith only [h2T] : -T ≤ -2)] using hz
    have hz2 : z ∈ Set.Icc (-T) T := ⟨hz1.1, le_trans hz1.2 (by linarith only [hσ₁pos, hδ₁, h2T] : -2 ≤ T)⟩
    simpa [Set.uIcc_of_le (by linarith only [hσ₁pos, hδ₁, h2T] : -T ≤ T)] using hz2
  have hsub2 : Set.uIcc (-2) 2 ⊆ Set.uIcc (-T) T := by
    intro z hz
    have hz1 : z ∈ Set.Icc (-2) 2 := by simpa [Set.uIcc_of_le (by norm_num : -2 ≤ 2)] using hz
    have hz2 : z ∈ Set.Icc (-T) T := ⟨le_trans (by linarith only [h2T] : -T ≤ -2) hz1.1, le_trans hz1.2 (by linarith only [h2T] : 2 ≤ T)⟩
    simpa [Set.uIcc_of_le (by linarith only [hσ₁pos, hδ₁, h2T] : -T ≤ T)] using hz2
  have hsub3 : Set.uIcc 2 T ⊆ Set.uIcc (-T) T := by
    intro z hz
    have hz1 : z ∈ Set.Icc 2 T := by simpa [Set.uIcc_of_le h2T] using hz
    have hz2 : z ∈ Set.Icc (-T) T := ⟨le_trans (by linarith only [hσ₁pos, hδ₁, h2T] : -T ≤ 2) hz1.1, hz1.2⟩
    simpa [Set.uIcc_of_le (by linarith only [hσ₁pos, hδ₁, h2T] : -T ≤ T)] using hz2
  have hIntM : IntervalIntegrable F volume (-T) (-2) := by
    dsimp [F]
    exact hIntT.mono_set hsub1
  have hIntN : IntervalIntegrable F volume (-2) 2 := by
    dsimp [F]
    exact hIntT.mono_set hsub2
  have hIntP : IntervalIntegrable F volume 2 T := by
    dsimp [F]
    exact hIntT.mono_set hsub3
  -- three slice bounds
  have hNearB := leftEdgeNearAxis_le_noZero (x := x) (σ₁ := σ₁) hx hσ₁pos hδ₁ hC₂ hNear hIntN
  have hFarPosB := leftEdgeFarPos_le_noZero (x := x) (σ₁ := σ₁) hx hσ₁pos h2T hC hFarPos hIntP
  have hFarNegB := leftEdgeFarNeg_le_noZero (x := x) (σ₁ := σ₁) hx h2T hC hFarNeg hIntM
  -- split the total integral
  have hEq1 : (∫ (t : ℝ) in -T..-2, F t) + (∫ (t : ℝ) in -2..2, F t) = (∫ (t : ℝ) in -T..2, F t) :=
    intervalIntegral.integral_add_adjacent_intervals hIntM hIntN
  have hEq2 : (∫ (t : ℝ) in -T..2, F t) + (∫ (t : ℝ) in 2..T, F t) = (∫ (t : ℝ) in -T..T, F t) :=
    intervalIntegral.integral_add_adjacent_intervals (hIntM.trans hIntN) hIntP
  have hEq : (∫ (t : ℝ) in -T..-2, F t) + (∫ (t : ℝ) in -2..2, F t) + (∫ (t : ℝ) in 2..T, F t) =
      (∫ (t : ℝ) in -T..T, F t) := by
    calc
      (∫ (t : ℝ) in -T..-2, F t) + (∫ (t : ℝ) in -2..2, F t) + (∫ (t : ℝ) in 2..T, F t)
          = (∫ (t : ℝ) in -T..2, F t) + (∫ (t : ℝ) in 2..T, F t) := by
              rw [← hEq1]
      _ = (∫ (t : ℝ) in -T..T, F t) := hEq2
  have hle1 : (∫ (t : ℝ) in -T..-2, F t) ≤ C * (x : ℝ) ^ σ₁ * (Real.log (T + 3) + 1) ^ 5 * Real.log (T / 2) := by
    dsimp [F]
    simpa using hFarNegB
  have hle2 : (∫ (t : ℝ) in -2..2, F t) ≤ 4 * (C₂ + 1 / (1 - σ₁)) * (x : ℝ) ^ σ₁ / σ₁ := by
    dsimp [F]
    simpa using hNearB
  have hle3 : (∫ (t : ℝ) in 2..T, F t) ≤ C * (x : ℝ) ^ σ₁ * (Real.log (T + 3) + 1) ^ 5 * Real.log (T / 2) := by
    dsimp [F]
    simpa using hFarPosB
  rw [← hEq]
  linarith only [hNearB, hFarPosB, hFarNegB]

/-- Bridge: the committed truncated-Perron identity (whose integral is written with the
von-Mangoldt L-series) is exactly `‖ψ(x) − perronZeta x T‖ ≤ C·(x log²x/T + log x)`. -/
lemma psi_sub_perronZeta_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ), 3 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖(Chebyshev.psi x : ℂ) - perronZeta x T‖ ≤ C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  rcases chebyshevPsi_truncatedPerron with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro x hx T hT
  have hxlog : 0 < Real.log x := Real.log_pos (by linarith only [hx] : (1 : ℝ) < x)
  let s₀ : ℝ → ℂ := fun t : ℝ => ((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)
  have hinteg : (1 / (2 * Real.pi)) *
      (∫ (t : ℝ) in -T..T,
        (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (s₀ t)) *
          (x : ℂ) ^ (s₀ t) / (s₀ t)) = perronZeta x T := by
    dsimp [perronZeta, perronRight, psiIntF, perronRe]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have hs1 : (1 : ℝ) < (s₀ t).re := by
      dsimp [s₀]
      have h : 0 < 1 / Real.log x := one_div_pos.mpr hxlog
      simp
      linarith only [hxlog]
    have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s₀ t) hs1
    have harg1 : (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) =
        ((perronRe x : ℂ) + (t : ℂ) * Complex.I) := by
      dsimp [perronRe]
      ring
    calc
      (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (s₀ t)) *
          (x : ℂ) ^ (s₀ t) / (s₀ t)
          = (-(deriv riemannZeta (s₀ t)) / riemannZeta (s₀ t)) * (x : ℂ) ^ (s₀ t) / (s₀ t) := by
              rw [hL]
      _ = (-(deriv riemannZeta (((perronRe x : ℂ) + (t : ℂ) * Complex.I))) /
            riemannZeta (((perronRe x : ℂ) + (t : ℂ) * Complex.I))) *
            (x : ℂ) ^ (((perronRe x : ℂ) + (t : ℂ) * Complex.I)) /
            (((perronRe x : ℂ) + (t : ℂ) * Complex.I)) := by
              rw [← harg1]
  -- chebyshevPsi_truncatedPerron's own integral coincides with perronZeta:
  have hCx := hC x hx T hT
  rwa [hinteg] at hCx

/-- The explicit bound obtained from the three edges of the deformed Perron rectangle. -/
noncomputable def perronEdgeSum (x T σ₁ C1 C2 : ℝ) : ℝ :=
  C1 * (Real.log (T + 3) + 1) ^ 5 * (x : ℝ) ^ perronRe x * (perronRe x - σ₁) / T +
  4 * (C2 + 1 / (1 - σ₁)) * (x : ℝ) ^ σ₁ / σ₁ +
  C1 * (x : ℝ) ^ σ₁ * (Real.log (T + 3) + 1) ^ 5 * Real.log (T / 2) +
  C1 * (x : ℝ) ^ σ₁ * (Real.log (T + 3) + 1) ^ 5 * Real.log (T / 2) +
  C1 * (Real.log (T + 3) + 1) ^ 5 * (x : ℝ) ^ perronRe x * (perronRe x - σ₁) / T

/-- **Step A (norm chain).** For `3 ≤ x`, `2 ≤ T`, `0 < σ₁ < 1 < perronRe x` and a
zero-free rectangle, `|ψ(x) − x|` is bounded by the truncation error plus `1/2π` times
the three edge integrals. -/
lemma psi_sub_id_le_trunc_add_edges {x T σ₁ : ℝ}
    (hx : 3 ≤ x) (hT : 2 ≤ T) (hσ₁pos : 0 < σ₁) (hδ₁ : 0 < 1 - σ₁)
    (hper1 : 1 < perronRe x)
    (hrect : (Set.uIcc σ₁ (perronRe x) ×ℂ Set.uIcc (-T) T) ⊆
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0})
    {Ctr : ℝ}
    (htr : ∀ (x' : ℝ), 3 ≤ x' → ∀ (T' : ℝ), 2 ≤ T' →
      ‖(Chebyshev.psi x' : ℂ) - perronZeta x' T'‖ ≤ Ctr * (x' * (Real.log x') ^ 2 / T' + Real.log x')) :
    |Chebyshev.psi x - x| ≤
      Ctr * (x * (Real.log x) ^ 2 / T + Real.log x) +
        (1 / (2 * Real.pi)) *
          ((∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) +
           (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) +
           (∫ (t : ℝ) in -T..T, ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖)) := by
  have hxpos : 0 < x := by linarith only [hx, hσ₁pos, hδ₁]
  have hTpos : 0 < T := by linarith only [hT, hσ₁pos, hδ₁]
  have htrunc := htr x hx T hT
  have hsub := perronZeta_sub_id_norm_le_noZero hxpos hTpos hσ₁pos (by linarith only [hδ₁] : σ₁ < 1) hper1 hrect
  have habs1 : |Chebyshev.psi x - x| = ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have htri1 : ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ ≤
      ‖(Chebyshev.psi x : ℂ) - perronZeta x T‖ + ‖perronZeta x T - (x : ℂ)‖ := by
    have h := norm_add_le ((Chebyshev.psi x : ℂ) - perronZeta x T) (perronZeta x T - (x : ℂ))
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have h1 : ‖(Chebyshev.psi x : ℂ) - perronZeta x T‖ ≤ Ctr * (x * (Real.log x) ^ 2 / T + Real.log x) := htrunc
  have h2 : ‖perronZeta x T - (x : ℂ)‖ ≤
      (1 / (2 * Real.pi)) *
        ((∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) +
         (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) +
         (∫ (t : ℝ) in -T..T, ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖)) := hsub
  calc
    |Chebyshev.psi x - x| = ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ := habs1
    _ ≤ ‖(Chebyshev.psi x : ℂ) - perronZeta x T‖ + ‖perronZeta x T - (x : ℂ)‖ := htri1
    _ ≤ Ctr * (x * (Real.log x) ^ 2 / T + Real.log x) + ‖perronZeta x T - (x : ℂ)‖ := by linarith only [htrunc]
    _ ≤ Ctr * (x * (Real.log x) ^ 2 / T + Real.log x) +
        (1 / (2 * Real.pi)) *
          ((∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) +
           (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) +
           (∫ (t : ℝ) in -T..T, ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖)) := by linarith only [hsub]

/-- `‖ζ'(s)/ζ(s)‖` (real). -/
noncomputable def logDerivZ (s : ℂ) : ℝ := ‖deriv riemannZeta s / riemannZeta s‖

/-- Top edge integral of `‖ψIntF‖` at height `T`. -/
noncomputable def edgeTopInt (x T σ₁ : ℝ) : ℝ :=
  ∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖

/-- Bottom edge integral at height `−T` (minus-form, matching the norm decomposition). -/
noncomputable def edgeBotInt (x T σ₁ : ℝ) : ℝ :=
  ∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖

/-- Left edge integral at real part `σ₁`. -/
noncomputable def edgeLeftInt (x T σ₁ : ℝ) : ℝ :=
  ∫ (t : ℝ) in -T..T, ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖

/-- **Step C (edge assembly).** The three edge integrals are bounded by `perronEdgeSum`. -/
lemma psi_sub_id_edges_le_perronEdgeSum {x T σ₁ : ℝ}
    (hx : (1 : ℝ) ≤ x) (hT : 2 ≤ T)
    (hσ₁pos : 0 < σ₁) (hδ₁ : 0 < 1 - σ₁) (hσ₁le : σ₁ ≤ perronRe x)
    {C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hTopB : ∀ u : ℝ, u ∈ Set.Icc σ₁ (perronRe x) →
      logDerivZ (((u : ℂ) + (T : ℂ) * Complex.I)) ≤ C1 * (Real.log (T + 3) + 1) ^ 5)
    (hBotB : ∀ u : ℝ, u ∈ Set.Icc σ₁ (perronRe x) →
      logDerivZ (((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I)) ≤ C1 * (Real.log (T + 3) + 1) ^ 5)
    (hNear : ∀ t : ℝ, |t| ≤ 2 →
      logDerivZ (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) ≤
        C2 + 1 / ‖(((σ₁ : ℂ) + (t : ℂ) * Complex.I)) - 1‖)
    (hFarPos : ∀ t : ℝ, t ∈ Set.Icc 2 T →
      logDerivZ (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) ≤ C1 * (Real.log (|t| + 3) + 1) ^ 5)
    (hFarNeg : ∀ t : ℝ, t ∈ Set.Icc (-T) (-2) →
      logDerivZ (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) ≤ C1 * (Real.log (|t| + 3) + 1) ^ 5)
    (hIntTop : IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) volume σ₁ (perronRe x))
    (hIntBot : IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I)‖) volume σ₁ (perronRe x))
    (hIntL : IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) volume (-T) T) :
    edgeTopInt x T σ₁ + edgeBotInt x T σ₁ + edgeLeftInt x T σ₁ ≤ perronEdgeSum x T σ₁ C1 C2 := by
  rw [edgeTopInt, edgeBotInt, edgeLeftInt]
  have hTpos : 0 < T := by linarith only [hT, hσ₁pos, hδ₁]
  have htopInt := topEdgeInt_le_noZero (x := x) (T := T) (σ₁ := σ₁) hx
      (hσ₁le := hσ₁le) hTpos
      (by intro u hu; simpa [logDerivZ] using hTopB u hu) hIntTop
  have hbotInt := botEdgeInt_le_noZero (x := x) (T := T) (σ₁ := σ₁) hx
      (hσ₁le := hσ₁le) hTpos
      (by intro u hu; simpa [logDerivZ] using hBotB u hu) hIntBot
  have hboteq : (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) =
      (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I)‖) := by
    congr 1
    funext u
    congr 1
    have harg : ((u : ℂ) - (T : ℂ) * Complex.I) = ((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I) := by
      push_cast
      ring
    rw [harg]
  have hbotIntM : (∫ (u : ℝ) in σ₁..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) ≤
      C1 * (Real.log (T + 3) + 1) ^ 5 * (x : ℝ) ^ perronRe x * (perronRe x - σ₁) / T := by
    rw [hboteq]
    exact hbotInt
  have hleftInt := leftEdgeTot_le_noZero (x := x) (σ₁ := σ₁) (by linarith only [hx, hσ₁pos, hδ₁] : 0 < x) hσ₁pos hδ₁
      (h2T := hT) (C := C1) (C₂ := C2) hC1 hC2
      (by intro t ht; simpa [logDerivZ] using hNear t ht)
      (by intro t ht; simpa [logDerivZ] using hFarPos t ht)
      (by intro t ht; simpa [logDerivZ] using hFarNeg t ht) hIntL
  dsimp [perronEdgeSum]
  linarith only [htopInt, hbotIntM, hleftInt, hbotInt, hboteq]

/-- **Parameterized engine bound.** Combining the norm chain (Step A) with the edge
assembly (Step C): under the (M1-shape) far log-derivative bounds, the (M2-shape)
near-axis pole bound, the truncation bound and the zero-free rectangle geometry,
`|ψ(x) − x| ≤ Ctr·(x log²x/T + log x) + (1/2π)·perronEdgeSum x T σ₁ C1 C2`. -/
lemma psi_sub_id_le_engine {x T σ₁ : ℝ}
    (hx : 3 ≤ x) (hT : 2 ≤ T) (hσ₁pos : 0 < σ₁) (hδ₁ : 0 < 1 - σ₁)
    (hper1 : 1 < perronRe x)
    (hrect : (Set.uIcc σ₁ (perronRe x) ×ℂ Set.uIcc (-T) T) ⊆
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0})
    {Ctr C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (htr : ∀ (x' : ℝ), 3 ≤ x' → ∀ (T' : ℝ), 2 ≤ T' →
      ‖(Chebyshev.psi x' : ℂ) - perronZeta x' T'‖ ≤ Ctr * (x' * (Real.log x') ^ 2 / T' + Real.log x'))
    (hTopB : ∀ u : ℝ, u ∈ Set.Icc σ₁ (perronRe x) →
      logDerivZ (((u : ℂ) + (T : ℂ) * Complex.I)) ≤ C1 * (Real.log (T + 3) + 1) ^ 5)
    (hBotB : ∀ u : ℝ, u ∈ Set.Icc σ₁ (perronRe x) →
      logDerivZ (((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I)) ≤ C1 * (Real.log (T + 3) + 1) ^ 5)
    (hNear : ∀ t : ℝ, |t| ≤ 2 →
      logDerivZ (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) ≤
        C2 + 1 / ‖(((σ₁ : ℂ) + (t : ℂ) * Complex.I)) - 1‖)
    (hFarPos : ∀ t : ℝ, t ∈ Set.Icc 2 T →
      logDerivZ (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) ≤ C1 * (Real.log (|t| + 3) + 1) ^ 5)
    (hFarNeg : ∀ t : ℝ, t ∈ Set.Icc (-T) (-2) →
      logDerivZ (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) ≤ C1 * (Real.log (|t| + 3) + 1) ^ 5)
    (hIntTop : IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) volume σ₁ (perronRe x))
    (hIntBot : IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I)‖) volume σ₁ (perronRe x))
    (hIntL : IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) volume (-T) T) :
    |Chebyshev.psi x - x| ≤
      Ctr * (x * (Real.log x) ^ 2 / T + Real.log x) +
        (1 / (2 * Real.pi)) * perronEdgeSum x T σ₁ C1 C2 := by
  have hA := psi_sub_id_le_trunc_add_edges (x := x) (T := T) (σ₁ := σ₁) hx hT hσ₁pos hδ₁ hper1 hrect htr
  have hC := psi_sub_id_edges_le_perronEdgeSum (x := x) (T := T) (σ₁ := σ₁)
      (by linarith only [hx, hσ₁pos, hδ₁] : (1 : ℝ) ≤ x) hT hσ₁pos hδ₁ (le_of_lt (lt_trans (by linarith only [hδ₁] : σ₁ < 1) hper1))
      hC1 hC2 hTopB hBotB hNear hFarPos hFarNeg hIntTop hIntBot hIntL
  rw [edgeTopInt, edgeBotInt, edgeLeftInt] at hC
  have hcoef : 0 ≤ 1 / (2 * Real.pi) := by positivity
  have hm := mul_le_mul_of_nonneg_left hC hcoef
  linarith only [hA, hm]

/-- **Engine bound with the truncation constant instantiated** from the committed
`psi_sub_perronZeta_bound`. -/
lemma psi_sub_id_le_engine_exists {x T σ₁ : ℝ}
    (hx : 3 ≤ x) (hT : 2 ≤ T) (hσ₁pos : 0 < σ₁) (hδ₁ : 0 < 1 - σ₁)
    (hper1 : 1 < perronRe x)
    (hrect : (Set.uIcc σ₁ (perronRe x) ×ℂ Set.uIcc (-T) T) ⊆
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0})
    {C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hTopB : ∀ u : ℝ, u ∈ Set.Icc σ₁ (perronRe x) →
      logDerivZ (((u : ℂ) + (T : ℂ) * Complex.I)) ≤ C1 * (Real.log (T + 3) + 1) ^ 5)
    (hBotB : ∀ u : ℝ, u ∈ Set.Icc σ₁ (perronRe x) →
      logDerivZ (((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I)) ≤ C1 * (Real.log (T + 3) + 1) ^ 5)
    (hNear : ∀ t : ℝ, |t| ≤ 2 →
      logDerivZ (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) ≤
        C2 + 1 / ‖(((σ₁ : ℂ) + (t : ℂ) * Complex.I)) - 1‖)
    (hFarPos : ∀ t : ℝ, t ∈ Set.Icc 2 T →
      logDerivZ (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) ≤ C1 * (Real.log (|t| + 3) + 1) ^ 5)
    (hFarNeg : ∀ t : ℝ, t ∈ Set.Icc (-T) (-2) →
      logDerivZ (((σ₁ : ℂ) + (t : ℂ) * Complex.I)) ≤ C1 * (Real.log (|t| + 3) + 1) ^ 5)
    (hIntTop : IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) volume σ₁ (perronRe x))
    (hIntBot : IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I)‖) volume σ₁ (perronRe x))
    (hIntL : IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) volume (-T) T) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      |Chebyshev.psi x - x| ≤
        Ctr * (x * (Real.log x) ^ 2 / T + Real.log x) +
          (1 / (2 * Real.pi)) * perronEdgeSum x T σ₁ C1 C2 := by
  obtain ⟨Ctr, hCtrpos, htr⟩ := psi_sub_perronZeta_bound
  exact ⟨Ctr, hCtrpos,
    psi_sub_id_le_engine (x := x) (T := T) (σ₁ := σ₁) hx hT hσ₁pos hδ₁ hper1 hrect
      hC1 hC2 htr hTopB hBotB hNear hFarPos hFarNeg hIntTop hIntBot hIntL⟩

/-- The height parameter `T = exp(√(log x))`. -/
noncomputable def engT (x : ℝ) : ℝ := Real.exp (Real.sqrt (Real.log x))

/-- The width parameter `δ = c/(2·(log(T+3)+1))`. -/
noncomputable def engDelta (x c : ℝ) : ℝ := c / (2 * (Real.log (engT x + 3) + 1))

/-- The left side of the deformed rectangle: `σ₁ = 1 − δ`. -/
noncomputable def engSigma (x c : ℝ) : ℝ := 1 - engDelta x c

theorem engT_pos (x : ℝ) : 0 < engT x := Real.exp_pos _

/-- The top-edge M1-shape hypothesis (at height `T = exp(√(log x))`) follows from the
region log-derivative bound `hM1` when `H ≤ T` and `perronRe x ≤ 2`. -/
lemma hTopB_engine {x c C H : ℝ} (hx : 3 ≤ x) (hper2 : perronRe x ≤ 2) (hc : 0 ≤ c) (hHT : H ≤ engT x)
    (hM1 : ∀ t : ℝ, H ≤ |t| → ∀ σ : ℝ,
      (1 - c / (Real.log (|t| + 3) + 1)) ≤ σ → σ ≤ 2 →
      logDerivZ (((σ : ℂ) + (t : ℂ) * Complex.I)) ≤ C * (Real.log (|t| + 3) + 1) ^ 5) :
    ∀ u : ℝ, u ∈ Set.Icc (engSigma x c) (perronRe x) →
      logDerivZ (((u : ℂ) + (engT x : ℂ) * Complex.I)) ≤
        C * (Real.log (engT x + 3) + 1) ^ 5 := by
  intro u hu
  have hTpos : 0 < engT x := engT_pos x
  have hu1 : engSigma x c ≤ u := hu.1
  have hu2 : u ≤ perronRe x := hu.2
  have hTm : H ≤ |engT x| := by rw [abs_of_pos hTpos]; exact hHT
  have hlogabs : Real.log (|engT x| + 3) = Real.log (engT x + 3) := by
    rw [abs_of_pos hTpos]
  have hreg : (1 - c / (Real.log (|engT x| + 3) + 1)) ≤ u := by
    rw [hlogabs]
    have hδ : engDelta x c ≤ c / (Real.log (engT x + 3) + 1) := by
      dsimp [engDelta]
      have hpos : 0 < Real.log (engT x + 3) + 1 := by
        have h2 : (1 : ℝ) < engT x + 3 := by linarith only [hTpos]
        have h3 : 0 < Real.log (engT x + 3) := Real.log_pos h2
        linarith only [h3]
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * (Real.log (engT x + 3) + 1)) hpos]
      nlinarith only [hc, hpos]
    have : engSigma x c = 1 - engDelta x c := rfl
    rw [this] at hu1
    linarith only [hu1, hδ]
  have hu2' : u ≤ 2 := le_trans hu2 hper2
  have h := hM1 (engT x) hTm u hreg hu2'
  rwa [hlogabs] at h

/-- The bottom-edge M1-shape hypothesis (at height `−T`) follows likewise. -/
lemma hBotB_engine {x c C H : ℝ} (hx : 3 ≤ x) (hper2 : perronRe x ≤ 2) (hc : 0 ≤ c) (hHT : H ≤ engT x)
    (hM1 : ∀ t : ℝ, H ≤ |t| → ∀ σ : ℝ,
      (1 - c / (Real.log (|t| + 3) + 1)) ≤ σ → σ ≤ 2 →
      logDerivZ (((σ : ℂ) + (t : ℂ) * Complex.I)) ≤ C * (Real.log (|t| + 3) + 1) ^ 5) :
    ∀ u : ℝ, u ∈ Set.Icc (engSigma x c) (perronRe x) →
      logDerivZ (((u : ℂ) + (((-engT x : ℝ) : ℂ)) * Complex.I)) ≤
        C * (Real.log (engT x + 3) + 1) ^ 5 := by
  intro u hu
  have hTpos : 0 < engT x := engT_pos x
  have hu1 : engSigma x c ≤ u := hu.1
  have hu2 : u ≤ perronRe x := hu.2
  have hTm : H ≤ |-engT x| := by rw [abs_neg, abs_of_pos hTpos]; exact hHT
  have hlogabs : Real.log (|-engT x| + 3) = Real.log (engT x + 3) := by
    rw [abs_neg, abs_of_pos hTpos]
  have hreg : (1 - c / (Real.log (|-engT x| + 3) + 1)) ≤ u := by
    rw [hlogabs]
    have hδ : engDelta x c ≤ c / (Real.log (engT x + 3) + 1) := by
      dsimp [engDelta]
      have hpos : 0 < Real.log (engT x + 3) + 1 := by
        have h2 : (1 : ℝ) < engT x + 3 := by linarith only [hTpos]
        have h3 : 0 < Real.log (engT x + 3) := Real.log_pos h2
        linarith only [h3]
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * (Real.log (engT x + 3) + 1)) hpos]
      nlinarith only [hc, hpos]
    have : engSigma x c = 1 - engDelta x c := rfl
    rw [this] at hu1
    linarith only [hu1, hδ]
  have hu2' : u ≤ 2 := le_trans hu2 hper2
  have h := hM1 (-engT x) hTm u hreg hu2'
  rwa [hlogabs] at h

/-- The positive far slice of the left edge (heights `2 ≤ t ≤ T = exp(√(log x))`),
discharged from the M1 region datum. -/
lemma hFarPos_engine {x c C H : ℝ} (hx : 3 ≤ x) (hc : 0 ≤ c) (hH2 : H ≤ 2)
    (hT2 : 2 ≤ engT x)
    (hM1 : ∀ t : ℝ, H ≤ |t| → ∀ σ : ℝ,
      (1 - c / (Real.log (|t| + 3) + 1)) ≤ σ → σ ≤ 2 →
      logDerivZ (((σ : ℂ) + (t : ℂ) * Complex.I)) ≤ C * (Real.log (|t| + 3) + 1) ^ 5) :
    ∀ t : ℝ, t ∈ Set.Icc 2 (engT x) →
      logDerivZ (((engSigma x c : ℂ) + (t : ℂ) * Complex.I)) ≤
        C * (Real.log (|t| + 3) + 1) ^ 5 := by
  intro t ht
  have ht2 : 2 ≤ t := ht.1
  have htT : t ≤ engT x := ht.2
  have htpos : 0 < t := by linarith only [ht2]
  have htabs : |t| = t := abs_of_nonneg (by linarith only [ht2])
  have hTm : H ≤ |t| := by rw [htabs]; linarith only [hH2, ht2]
  have hlogpos : 0 < Real.log (|t| + 3) + 1 := by
    have h1 : (1 : ℝ) < |t| + 3 := by linarith only [abs_nonneg t, ht2, htabs]
    have h2 : 0 < Real.log (|t| + 3) := Real.log_pos h1
    linarith only [h2]
  have hlogTpos : 0 < 2 * (Real.log (engT x + 3) + 1) := by
    have h1 : (1 : ℝ) < engT x + 3 := by linarith only [engT_pos x, hT2]
    have h2 : 0 < Real.log (engT x + 3) := Real.log_pos h1
    linarith only [h2]
  have hreg : (1 - c / (Real.log (|t| + 3) + 1)) ≤ engSigma x c := by
    have hd : c / (2 * (Real.log (engT x + 3) + 1)) ≤ c / (Real.log (|t| + 3) + 1) := by
      apply div_le_div_of_nonneg_left hc hlogpos
      have hlogtT : Real.log (|t| + 3) ≤ Real.log (engT x + 3) := by
        rw [htabs]
        exact Real.log_le_log (by linarith only [ht2]) (by linarith only [htT])
      linarith only [hlogpos, hlogtT]
    dsimp [engSigma, engDelta]
    linarith only [hd]
  have h2 : engSigma x c ≤ 2 := by
    dsimp [engSigma, engDelta]
    have h3 : 0 ≤ c / (2 * (Real.log (engT x + 3) + 1)) := div_nonneg hc (le_of_lt hlogTpos)
    linarith only [h3]
  exact hM1 t hTm (engSigma x c) hreg h2

/-- The negative far slice of the left edge (heights `−T ≤ t ≤ −2`), discharged from the
M1 region datum. -/
lemma hFarNeg_engine {x c C H : ℝ} (hx : 3 ≤ x) (hc : 0 ≤ c) (hH2 : H ≤ 2)
    (hT2 : 2 ≤ engT x)
    (hM1 : ∀ t : ℝ, H ≤ |t| → ∀ σ : ℝ,
      (1 - c / (Real.log (|t| + 3) + 1)) ≤ σ → σ ≤ 2 →
      logDerivZ (((σ : ℂ) + (t : ℂ) * Complex.I)) ≤ C * (Real.log (|t| + 3) + 1) ^ 5) :
    ∀ t : ℝ, t ∈ Set.Icc (-(engT x)) (-2) →
      logDerivZ (((engSigma x c : ℂ) + (t : ℂ) * Complex.I)) ≤
        C * (Real.log (|t| + 3) + 1) ^ 5 := by
  intro t ht
  have ht2 : t ≤ -2 := ht.2
  have htT : -(engT x) ≤ t := ht.1
  have htneg : t < 0 := by linarith only [ht2]
  have htabs : |t| = -t := abs_of_neg htneg
  have hTm : H ≤ |t| := by rw [htabs]; linarith only [hH2, ht2]
  have hlogpos : 0 < Real.log (|t| + 3) + 1 := by
    have h1 : (1 : ℝ) < |t| + 3 := by linarith only [abs_nonneg t, ht2, htabs]
    have h2 : 0 < Real.log (|t| + 3) := Real.log_pos h1
    linarith only [h2]
  have hlogTpos : 0 < 2 * (Real.log (engT x + 3) + 1) := by
    have h1 : (1 : ℝ) < engT x + 3 := by linarith only [engT_pos x, hT2]
    have h2 : 0 < Real.log (engT x + 3) := Real.log_pos h1
    linarith only [h2]
  have hreg : (1 - c / (Real.log (|t| + 3) + 1)) ≤ engSigma x c := by
    have hd : c / (2 * (Real.log (engT x + 3) + 1)) ≤ c / (Real.log (|t| + 3) + 1) := by
      apply div_le_div_of_nonneg_left hc hlogpos
      have hlogtT : Real.log (|t| + 3) ≤ Real.log (engT x + 3) := by
        rw [htabs]
        exact Real.log_le_log (by linarith only [ht2]) (by linarith only [htT])
      linarith only [hlogpos, hlogtT]
    dsimp [engSigma, engDelta]
    linarith only [hd]
  have h2 : engSigma x c ≤ 2 := by
    dsimp [engSigma, engDelta]
    have h3 : 0 ≤ c / (2 * (Real.log (engT x + 3) + 1)) := div_nonneg hc (le_of_lt hlogTpos)
    linarith only [h3]
  exact hM1 t hTm (engSigma x c) hreg h2

/-- The near-axis M2-shape hypothesis at `σ₁ = engSigma x c` follows from the committed
`zeta_logDeriv_near_axis_bound` datum when `engDelta x c ≤ δ₂`. -/
lemma hNear_engine {x c C₂ δ₂ : ℝ} (hc : 0 < c) (hδ : engDelta x c ≤ δ₂)
    (hM2 : ∀ (t σ : ℝ), |t| ≤ 2 → σ ≠ 1 → (1 - δ₂) ≤ σ → σ ≤ 2 →
      logDerivZ (((σ : ℂ) + (t : ℂ) * Complex.I)) ≤
        C₂ + 1 / ‖(((σ : ℂ) + (t : ℂ) * Complex.I)) - 1‖) :
    ∀ t : ℝ, |t| ≤ 2 →
      logDerivZ (((engSigma x c : ℂ) + (t : ℂ) * Complex.I)) ≤
        C₂ + 1 / ‖(((engSigma x c : ℂ) + (t : ℂ) * Complex.I)) - 1‖ := by
  intro t ht
  have hden : 0 < 2 * (Real.log (engT x + 3) + 1) := by
    have h1 : (1 : ℝ) < engT x + 3 := by linarith only [engT_pos x]
    have h2 : 0 < Real.log (engT x + 3) := Real.log_pos h1
    linarith only [h2]
  have hδpos : 0 < engDelta x c := by
    dsimp [engDelta]
    exact div_pos hc hden
  have hσne : engSigma x c ≠ 1 := by
    dsimp [engSigma]
    linarith only [hδpos]
  have hσlo : (1 - δ₂) ≤ engSigma x c := by
    dsimp [engSigma]
    linarith only [hδ]
  have hσhi : engSigma x c ≤ 2 := by
    dsimp [engSigma]
    linarith only [hδpos]
  exact hM2 t (engSigma x c) ht hσne hσlo hσhi


/-! ## Basic helpers -/

private lemma engM_pos (x : ℝ) : 0 < Real.log (engT x + 3) + 1 := by
  have h : (1 : ℝ) < engT x + 3 := by linarith only [engT_pos x]
  have := Real.log_pos h
  linarith only [this]

private lemma engDelta_nonneg {x c : ℝ} (hc : 0 < c) : 0 ≤ engDelta x c := by
  dsimp [engDelta]
  exact div_nonneg (le_of_lt hc) (by linarith only [engM_pos x])

private lemma engDelta_pos {x c : ℝ} (hc : 0 < c) : 0 < engDelta x c := by
  dsimp [engDelta]
  have h : 0 < Real.log (engT x + 3) + 1 := engM_pos x
  positivity

private lemma perronRe_gt_one {x : ℝ} (hx : 1 < x) : 1 < perronRe x := by
  dsimp [perronRe]
  have h : 0 < 1 / Real.log x := by
    have := Real.log_pos hx
    positivity
  linarith only [h]

private lemma perronRe_le_two_of_three {x : ℝ} (hx : 3 ≤ x) : perronRe x ≤ 2 := by
  dsimp [perronRe]
  have hx1 : 1 < x := by linarith only [hx]
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hlog : 1 ≤ Real.log x := by
    have h3 : (1 : ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)).2 (le_of_lt Real.exp_one_lt_three)
    exact le_trans h3 (Real.log_le_log (by norm_num) hx)
  have hd : 1 / Real.log x ≤ 1 := (div_le_one hlogpos).2 hlog
  linarith only [hd]

private lemma zeta1_eq_sub_mul_zeta {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta₁, riemannZeta_eq_inv_sub_add hs]
  field_simp

private lemma zeta_ne_zero_of_zeta1_ne_zero {s : ℂ} (h1 : riemannZeta₁ s ≠ 0)
    (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  rw [zeta1_eq_sub_mul_zeta hs1] at h1
  exact fun h => h1 (by rw [h, mul_zero])

private lemma zeta1_ne_zero_of_zeta_ne_zero {s : ℂ} (h : riemannZeta s ≠ 0)
    (hs1 : s ≠ 1) : riemannZeta₁ s ≠ 0 := by
  rw [zeta1_eq_sub_mul_zeta hs1]
  exact mul_ne_zero (sub_ne_zero.mpr hs1) h

private lemma psiIntF_continuousAt_of_zeta_ne_zero {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hsRe : 0 < s.re) (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    ContinuousAt (psiIntF x) s := by
  have hderAn : AnalyticOnNhd ℂ (deriv riemannZeta) ({1}ᶜ : Set ℂ) :=
    AnalyticOnNhd.deriv analyticOn_riemannZeta
  have hc1 : ContinuousAt (fun w : ℂ => -(deriv riemannZeta w) / riemannZeta w) s := by
    have hcd : ContinuousAt (fun w : ℂ => deriv riemannZeta w) s :=
      hderAn.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hs1)
    have hcz : ContinuousAt riemannZeta s :=
      analyticOn_riemannZeta.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hs1)
    exact (hcd.neg).div hcz hζ
  have hcp : ContinuousAt (fun w : ℂ => (x : ℂ) ^ w) s := by
    have heq : (fun w : ℂ => (x : ℂ) ^ w) = fun w : ℂ => Complex.exp ((Real.log x : ℂ) * w) := by
      funext w; exact cpow_eq_exp_log_mul hx w
    rw [heq]; fun_prop
  have hs0 : s ≠ 0 := by intro h; rw [h] at hsRe; simp at hsRe
  have hm : ContinuousAt (fun w : ℂ => (-(deriv riemannZeta w) / riemannZeta w) * (x : ℂ) ^ w) s :=
    hc1.mul hcp
  have htotal : ContinuousAt
      (fun w : ℂ => ((-(deriv riemannZeta w) / riemannZeta w) * (x : ℂ) ^ w) / w) s :=
    hm.div continuousAt_id hs0
  change ContinuousAt (fun w : ℂ => -(deriv riemannZeta w) / riemannZeta w * (x : ℂ) ^ w / w) s
  exact htotal

private lemma psiIntF_integrable_horiz {x r a b : ℝ} (hx : 0 < x) (hr : r ≠ 0)
    (hpos : ∀ u : ℝ, u ∈ Set.uIcc a b → 0 < u)
    (hζ : ∀ u : ℝ, u ∈ Set.uIcc a b → riemannZeta ((u : ℂ) + (r : ℂ) * Complex.I) ≠ 0) :
    IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (r : ℂ) * Complex.I)‖) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.norm
  intro u0 hu0
  have hcφ : ContinuousAt (fun u : ℝ => (u : ℂ) + (r : ℂ) * Complex.I) u0 := by fun_prop
  have hsRe : 0 < ((u0 : ℂ) + (r : ℂ) * Complex.I).re := by simpa using hpos u0 hu0
  have hs1 : (u0 : ℂ) + (r : ℂ) * Complex.I ≠ 1 := by
    intro h
    have him : ((u0 : ℂ) + (r : ℂ) * Complex.I).im = 0 := by rw [h]; simp
    simp at him
    exact hr him
  have hcont := psiIntF_continuousAt_of_zeta_ne_zero hx hsRe hs1 (hζ u0 hu0)
  exact (ContinuousAt.comp (g := psiIntF x)
    (f := fun u : ℝ => (u : ℂ) + (r : ℂ) * Complex.I) hcont hcφ).continuousWithinAt

private lemma psiIntF_integrable_vert {x σ₁ c d : ℝ} (hx : 0 < x) (hσ1pos : 0 < σ₁)
    (hσ1ne : σ₁ ≠ 1)
    (hζ : ∀ t : ℝ, t ∈ Set.uIcc c d → riemannZeta ((σ₁ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) volume c d := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.norm
  intro t0 ht0
  have hcφ : ContinuousAt (fun t : ℝ => (σ₁ : ℂ) + (t : ℂ) * Complex.I) t0 := by fun_prop
  have hsRe : 0 < ((σ₁ : ℂ) + (t0 : ℂ) * Complex.I).re := by simpa using hσ1pos
  have hs1 : (σ₁ : ℂ) + (t0 : ℂ) * Complex.I ≠ 1 := by
    intro h
    have hre : ((σ₁ : ℂ) + (t0 : ℂ) * Complex.I).re = 1 := by rw [h]; simp
    simp at hre
    exact hσ1ne hre
  have hcont := psiIntF_continuousAt_of_zeta_ne_zero hx hsRe hs1 (hζ t0 ht0)
  exact (ContinuousAt.comp (g := psiIntF x)
    (f := fun t : ℝ => (σ₁ : ℂ) + (t : ℂ) * Complex.I) hcont hcφ).continuousWithinAt

/-! ## The zero-free rectangle -/

private lemma rect_zeta1_ne_zero_engine {x c ε₀ : ℝ} (hx : 3 ≤ x) (hc : 0 < c)
    (hδ : engDelta x c ≤ 1 / 2) (hε : engDelta x c ≤ ε₀)
    (hZF : ∀ t : ℝ, 1 ≤ |t| → ∀ σ : ℝ, 1 - c / Real.log (|t| + 3) ≤ σ →
      riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0)
    (hNA : ∀ (t σ : ℝ), |t| ≤ 4 → 1 - ε₀ ≤ σ → σ ≤ 2 →
      riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0) :
    (Set.uIcc (engSigma x c) (perronRe x) ×ℂ Set.uIcc (-(engT x)) (engT x)) ⊆
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0} := by
  intro s hs
  rw [Complex.mem_reProdIm] at hs
  obtain ⟨hsre, hsim⟩ := hs
  have hper2 : perronRe x ≤ 2 := perronRe_le_two_of_three hx
  have hσle : engSigma x c ≤ perronRe x := by
    have h1 : engSigma x c ≤ 1 := by
      dsimp [engSigma]
      have hdn : 0 ≤ engDelta x c := engDelta_nonneg hc
      linarith only [hdn]
    have h2 : 1 < perronRe x := perronRe_gt_one (by linarith only [hx] : 1 < x)
    linarith only [h1, h2]
  rw [Set.uIcc_of_le hσle] at hsre
  dsimp [engSigma, engDelta] at hsre
  dsimp [engDelta] at hδ hε
  have hTm : -(engT x) ≤ engT x := by linarith only [engT_pos x]
  rw [Set.uIcc_of_le hTm] at hsim
  constructor
  · have := hsre.1
    linarith only [hδ, this]
  · by_cases hs1 : s = 1
    · rw [hs1, riemannZeta₁_one]; exact one_ne_zero
    · apply zeta1_ne_zero_of_zeta_ne_zero _ hs1
      have hdecomp : ((s.re : ℂ) + Complex.I * (s.im : ℂ)) = s := by
        rw [mul_comm]; exact Complex.re_add_im s
      have hre2 : s.re ≤ 2 := le_trans hsre.2 hper2
      by_cases hre1 : 1 ≤ s.re
      · rw [← hdecomp]
        exact riemannZeta_ne_zero_of_one_le_re (by simpa using hre1)
      · push Not at hre1
        by_cases him4 : |s.im| ≤ 4
        · rw [← hdecomp]
          exact hNA s.im s.re him4 (by linarith only [hsre.1, hε, hsre]) hre2
        · push Not at him4
          have him1 : 1 ≤ |s.im| := by linarith only [him4]
          have hre' : 1 - c / Real.log (|s.im| + 3) ≤ s.re := by
            have hlogT : 0 < Real.log (engT x + 3) := by
              have : (1 : ℝ) < engT x + 3 := by linarith only [engT_pos x, hTm]
              exact Real.log_pos this
            have hlogim_pos : 0 < Real.log (|s.im| + 3) := by
              have : (1 : ℝ) < |s.im| + 3 := by linarith only [abs_nonneg s.im, him4]
              exact Real.log_pos this
            have himle : |s.im| ≤ engT x := abs_le.mpr ⟨hsim.1, hsim.2⟩
            have hlogle : Real.log (|s.im| + 3) ≤ Real.log (engT x + 3) :=
              Real.log_le_log (by linarith only [abs_nonneg s.im, him4]) (by linarith only [himle])
            have h3 : c / (2 * (Real.log (engT x + 3) + 1)) ≤ c / Real.log (engT x + 3) := by
              rw [div_le_div_iff₀ (by linarith only [hlogT] : (0:ℝ) < 2 * (Real.log (engT x + 3) + 1)) hlogT]
              nlinarith only [hc, hlogT]
            have h4 : c / Real.log (engT x + 3) ≤ c / Real.log (|s.im| + 3) :=
              div_le_div_of_nonneg_left (le_of_lt hc) hlogim_pos hlogle
            linarith only [hsre.1, h3, h4, hsre]
          rw [← hdecomp]
          exact hZF s.im him1 s.re hre'

/-! ## Integrability of the edge integrals -/

private lemma engSigma_le_perronRe {x c : ℝ} (hx : 1 < x) (hc : 0 < c) :
    engSigma x c ≤ perronRe x := by
  have h1 : engSigma x c ≤ 1 := by
    dsimp [engSigma]
    linarith only [engDelta_nonneg (x := x) hc, hc]
  linarith only [perronRe_gt_one hx, h1, hx]

private lemma mem_rect_horiz {x c T u : ℝ} (hu : u ∈ Set.uIcc (engSigma x c) (perronRe x))
    (hT : T ∈ Set.uIcc (-(engT x)) (engT x)) :
    (u : ℂ) + (T : ℂ) * Complex.I ∈
      Set.uIcc (engSigma x c) (perronRe x) ×ℂ Set.uIcc (-(engT x)) (engT x) := by
  rw [Complex.mem_reProdIm]
  exact ⟨by simpa using hu, by simpa using hT⟩

private lemma mem_rect_vert {x c σ t : ℝ} (hσ : σ ∈ Set.uIcc (engSigma x c) (perronRe x))
    (ht : t ∈ Set.uIcc (-(engT x)) (engT x)) :
    (σ : ℂ) + (t : ℂ) * Complex.I ∈
      Set.uIcc (engSigma x c) (perronRe x) ×ℂ Set.uIcc (-(engT x)) (engT x) := by
  rw [Complex.mem_reProdIm]
  exact ⟨by simpa using hσ, by simpa using ht⟩

private lemma engT_mem_uIcc (x : ℝ) : engT x ∈ Set.uIcc (-(engT x)) (engT x) := by
  rw [Set.uIcc_of_le (by linarith only [engT_pos x])]
  exact ⟨by linarith only [engT_pos x], le_rfl⟩

private lemma neg_engT_mem_uIcc (x : ℝ) : -(engT x) ∈ Set.uIcc (-(engT x)) (engT x) := by
  rw [Set.uIcc_of_le (by linarith only [engT_pos x])]
  exact ⟨le_rfl, by linarith only [engT_pos x]⟩

private lemma engSigma_mem_uIcc {x c : ℝ} (hx : 1 < x) (hc : 0 < c) :
    engSigma x c ∈ Set.uIcc (engSigma x c) (perronRe x) := by
  rw [Set.uIcc_of_le (engSigma_le_perronRe hx hc)]
  exact ⟨le_rfl, engSigma_le_perronRe hx hc⟩

private lemma engine_edge_integrable {x c : ℝ} (hx : 3 ≤ x) (hc : 0 < c)
    (hδ : engDelta x c < 1)
    (hrect : (Set.uIcc (engSigma x c) (perronRe x) ×ℂ Set.uIcc (-(engT x)) (engT x)) ⊆
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0}) :
    IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (engT x : ℂ) * Complex.I)‖)
        volume (engSigma x c) (perronRe x) ∧
    IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (((-engT x : ℝ) : ℂ)) * Complex.I)‖)
        volume (engSigma x c) (perronRe x) ∧
    IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((engSigma x c : ℂ) + (t : ℂ) * Complex.I)‖)
        volume (-(engT x)) (engT x) := by
  have hxpos : 0 < x := by linarith only [hx]
  have hx1 : 1 < x := by linarith only [hx]
  have hσpos : 0 < engSigma x c := by
    dsimp [engSigma]; linarith only [hδ]
  have hσne : engSigma x c ≠ 1 := by
    dsimp [engSigma]; linarith only [engDelta_pos (x := x) hc, hc]
  have hTnz : engT x ≠ 0 := ne_of_gt (engT_pos x)
  have hneghTnz : -engT x ≠ 0 := neg_ne_zero.mpr hTnz
  -- zeta nonzero helper
  have hζ : ∀ (σ : ℝ) (t : ℝ), σ ∈ Set.uIcc (engSigma x c) (perronRe x) →
      t ∈ Set.uIcc (-(engT x)) (engT x) →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro σ t hσ ht
    have hmem := mem_rect_vert hσ ht
    have h1' : riemannZeta₁ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := (hrect hmem).2
    by_cases hs1 : ((σ : ℂ) + (t : ℂ) * Complex.I) = 1
    · rw [hs1]; exact riemannZeta_one_ne_zero
    · exact zeta_ne_zero_of_zeta1_ne_zero h1' hs1
  refine ⟨?_, ?_, ?_⟩
  · refine psiIntF_integrable_horiz hxpos hTnz ?_ ?_
    · intro u hu
      have hmem := mem_rect_horiz hu (engT_mem_uIcc x)
      have := (hrect hmem).1
      simpa using this
    · intro u hu
      exact hζ u (engT x) hu (engT_mem_uIcc x)
  · refine psiIntF_integrable_horiz hxpos hneghTnz ?_ ?_
    · intro u hu
      have hmem := mem_rect_horiz hu (neg_engT_mem_uIcc x)
      have := (hrect hmem).1
      simpa using this
    · intro u hu
      exact hζ u (-engT x) hu (neg_engT_mem_uIcc x)
  · refine psiIntF_integrable_vert hxpos hσpos hσne ?_
    intro t ht
    exact hζ (engSigma x c) t (engSigma_mem_uIcc hx1 hc) ht

/-! ## M1/M2 data in engine shape -/

private lemma hM2_datum {C₂ δ₂ : ℝ}
    (hM2 : ∀ (t σ : ℝ), |t| ≤ 2 → σ ≠ 1 → (1 - δ₂) ≤ σ → σ ≤ 2 →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)))) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        C₂ + 1 / ‖(((σ : ℂ) + Complex.I * (t : ℂ))) - 1‖) :
    ∀ (t σ : ℝ), |t| ≤ 2 → σ ≠ 1 → (1 - δ₂) ≤ σ → σ ≤ 2 →
      logDerivZ (((σ : ℂ) + (t : ℂ) * Complex.I)) ≤
        C₂ + 1 / ‖(((σ : ℂ) + (t : ℂ) * Complex.I)) - 1‖ := by
  intro t σ ht hs hlo hhi
  have h := hM2 t σ ht hs hlo hhi
  have harg : ((σ : ℂ) + (t : ℂ) * Complex.I) = ((σ : ℂ) + Complex.I * (t : ℂ)) := by ring
  rw [harg]
  simpa [logDerivZ] using h

private lemma hM1_datum {c₁ C₁ : ℝ} (hc₁ : 0 < c₁) (hC₁ : 0 ≤ C₁)
    (hLD : ∀ t : ℝ, 1 ≤ |t| → ∀ σ : ℝ, 1 - c₁ / Real.log (|t| + 3) ≤ σ → σ ≤ 2 →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)))) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        C₁ * (Real.log (|t| + 3) + 1) ^ 4) :
    ∀ t : ℝ, 1 ≤ |t| → ∀ σ : ℝ, 1 - c₁ / (Real.log (|t| + 3) + 1) ≤ σ → σ ≤ 2 →
      logDerivZ (((σ : ℂ) + (t : ℂ) * Complex.I)) ≤ C₁ * (Real.log (|t| + 3) + 1) ^ 5 := by
  intro t ht σ hσ hσ2
  have hLpos : 0 < Real.log (|t| + 3) := Real.log_pos (by linarith only [abs_nonneg t, ht])
  have hσ' : 1 - c₁ / Real.log (|t| + 3) ≤ σ := by
    have hle : c₁ / (Real.log (|t| + 3) + 1) ≤ c₁ / Real.log (|t| + 3) := by
      rw [div_le_div_iff₀ (by linarith only [hLpos] : (0:ℝ) < Real.log (|t| + 3) + 1) hLpos]
      linarith only [hc₁]
    linarith only [hσ, hle]
  have h := hLD t ht σ hσ' hσ2
  have hpow : (Real.log (|t| + 3) + 1) ^ 4 ≤ (Real.log (|t| + 3) + 1) ^ 5 := by
    have h1 : (1 : ℝ) ≤ Real.log (|t| + 3) + 1 := by linarith only [hLpos]
    calc (Real.log (|t| + 3) + 1) ^ 4 = (Real.log (|t| + 3) + 1) ^ 4 * 1 := by ring
      _ ≤ (Real.log (|t| + 3) + 1) ^ 4 * (Real.log (|t| + 3) + 1) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith only [hLpos]) 4)
      _ = (Real.log (|t| + 3) + 1) ^ 5 := by ring
  have harg : ((σ : ℂ) + (t : ℂ) * Complex.I) = ((σ : ℂ) + Complex.I * (t : ℂ)) := by ring
  rw [harg, logDerivZ]
  exact le_trans h (mul_le_mul_of_nonneg_left hpow hC₁)

/-! ## Elementary transcription lemmas for the exponential bound -/

private lemma rpow_perronRe_eq {x : ℝ} (hx : 0 < x) (hL : Real.log x ≠ 0) :
    x ^ perronRe x = x * Real.exp 1 := by
  rw [Real.rpow_def_of_pos hx]
  have h : Real.log x * perronRe x = Real.log x + 1 := by
    dsimp [perronRe]
    rw [mul_add, mul_one, mul_one_div, div_self hL]
  rw [h, Real.exp_add, Real.exp_log hx]

private lemma rpow_engSigma_eq {x c : ℝ} (hx : 0 < x) :
    x ^ (engSigma x c) = x * Real.exp (-(engDelta x c * Real.log x)) := by
  have he : engSigma x c = 1 - engDelta x c := rfl
  rw [he, Real.rpow_sub hx, Real.rpow_one, Real.rpow_def_of_pos hx]
  have harg : Real.log x * engDelta x c = engDelta x c * Real.log x := by ring
  rw [harg, div_eq_mul_inv, ← Real.exp_neg]

private lemma engM_pow5_le {x : ℝ} (hL1 : 1 ≤ Real.log x)
    (hM3 : Real.log (engT x + 3) + 1 ≤ 3 * Real.sqrt (Real.log x)) :
    (Real.log (engT x + 3) + 1) ^ 5 ≤ 243 * (Real.log x) ^ 3 := by
  have hLpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  have hMnn : 0 ≤ Real.log (engT x + 3) + 1 := le_of_lt (engM_pos x)
  have h1 : (Real.log (engT x + 3) + 1) ^ 5 ≤ (3 * Real.sqrt (Real.log x)) ^ 5 :=
    pow_le_pow_left₀ hMnn hM3 5
  have h2 : (3 * Real.sqrt (Real.log x)) ^ 5 = 243 * (Real.sqrt (Real.log x)) ^ 5 := by ring
  have hs := Real.sq_sqrt (le_of_lt hLpos)
  have hs1 : 1 ≤ Real.sqrt (Real.log x) := Real.one_le_sqrt.mpr hL1
  have hsle : Real.sqrt (Real.log x) ≤ Real.log x := by nlinarith only [hs, hM3, hs1, hMnn]
  have h3 : (Real.sqrt (Real.log x)) ^ 5 ≤ (Real.log x) ^ 3 := by
    have h4 : (Real.sqrt (Real.log x)) ^ 5
        = (Real.sqrt (Real.log x)) ^ 2 * ((Real.sqrt (Real.log x)) ^ 2 * Real.sqrt (Real.log x)) := by
      ring
    calc (Real.sqrt (Real.log x)) ^ 5
        = Real.log x * (Real.log x * Real.sqrt (Real.log x)) := by rw [h4, hs]
      _ ≤ Real.log x * (Real.log x * Real.log x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsle (le_of_lt hLpos)) (le_of_lt hLpos)
      _ = (Real.log x) ^ 3 := by ring
  calc (Real.log (engT x + 3) + 1) ^ 5 ≤ (3 * Real.sqrt (Real.log x)) ^ 5 := h1
    _ = 243 * (Real.sqrt (Real.log x)) ^ 5 := h2
    _ ≤ 243 * (Real.log x) ^ 3 := mul_le_mul_of_nonneg_left h3 (by norm_num)

private lemma engDelta_mul_log_ge {x c : ℝ} (hc : 0 < c) (hL1 : 1 ≤ Real.log x)
    (hM3 : Real.log (engT x + 3) + 1 ≤ 3 * Real.sqrt (Real.log x)) :
    (c / 6) * Real.sqrt (Real.log x) ≤ engDelta x c * Real.log x := by
  have hLpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  have hsqLpos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLpos
  have hMpos : 0 < Real.log (engT x + 3) + 1 := engM_pos x
  have hsqL2 : Real.sqrt (Real.log x) ^ 2 = Real.log x := Real.sq_sqrt (le_of_lt hLpos)
  have hδeq : engDelta x c = c / (2 * (Real.log (engT x + 3) + 1)) := rfl
  have hsqL2' : Real.log x = Real.sqrt (Real.log x) ^ 2 := hsqL2.symm
  rw [hδeq]
  conv_rhs => rw [hsqL2']
  rw [show c / (2 * (Real.log (engT x + 3) + 1)) * Real.sqrt (Real.log x) ^ 2
      = c * Real.sqrt (Real.log x) ^ 2 / (2 * (Real.log (engT x + 3) + 1)) by ring]
  rw [le_div_iff₀ (by linarith only [hMpos] : (0:ℝ) < 2 * (Real.log (engT x + 3) + 1))]
  have hnn : 0 ≤ (c / 3) * Real.sqrt (Real.log x) :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hprod : (c / 3) * Real.sqrt (Real.log x) * (Real.log (engT x + 3) + 1)
      ≤ (c / 3) * Real.sqrt (Real.log x) * (3 * Real.sqrt (Real.log x)) :=
    mul_le_mul_of_nonneg_left hM3 hnn
  linarith only [hprod, hsqLpos]

private lemma engDelta_inv_le {x c : ℝ} (hc : 0 < c)
    (hM3 : Real.log (engT x + 3) + 1 ≤ 3 * Real.sqrt (Real.log x)) :
    1 / (1 - engSigma x c) ≤ 6 * Real.sqrt (Real.log x) / c := by
  have h1 : 1 - engSigma x c = engDelta x c := by dsimp [engSigma]; ring
  rw [h1]
  have hδeq : engDelta x c = c / (2 * (Real.log (engT x + 3) + 1)) := rfl
  rw [hδeq, one_div, inv_div]
  apply div_le_div_of_nonneg_right _ (le_of_lt hc)
  linarith only [hM3]

private lemma log_engT_div_two_le (x : ℝ) :
    Real.log (engT x / 2) ≤ Real.sqrt (Real.log x) := by
  have hTpos : 0 < engT x := engT_pos x
  have h1 : Real.log (engT x / 2) ≤ Real.log (engT x) :=
    Real.log_le_log (by linarith only [hTpos]) (by linarith only [hTpos])
  rw [engT, Real.log_exp] at h1
  exact h1

private lemma engSigma_ge_half {x c : ℝ} (hδh : engDelta x c ≤ 1 / 2) :
    1 / 2 ≤ engSigma x c := by
  dsimp [engSigma]
  linarith only [hδh]

private lemma perronRe_sub_engSigma_le_two {x c : ℝ} (hL1 : 1 ≤ Real.log x)
    (hδh : engDelta x c ≤ 1 / 2) :
    perronRe x - engSigma x c ≤ 2 := by
  have hLpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  have hd : 1 / Real.log x ≤ 1 := (div_le_one hLpos).2 hL1
  dsimp [perronRe, engSigma]
  linarith only [hδh, hd]

/-! ## Eventual size facts -/

private lemma engT_tendsto_atTop : Tendsto (fun x : ℝ => engT x) atTop atTop :=
  Real.tendsto_exp_atTop.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)

private lemma engT_eventually_ge (B : ℝ) : ∀ᶠ x : ℝ in atTop, B ≤ engT x :=
  engT_tendsto_atTop.eventually (eventually_ge_atTop B)

private lemma engDelta_eventually_le {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop, engDelta x c ≤ d := by
  filter_upwards [engT_eventually_ge (Real.exp (c / (2 * d)) + 3)] with x hx
  have h1 : Real.exp (c / (2 * d)) ≤ engT x + 3 := by linarith only [hx]
  have h2 : c / (2 * d) ≤ Real.log (engT x + 3) :=
    (Real.le_log_iff_exp_le (by linarith only [engT_pos x])).2 h1
  have hM : 0 < Real.log (engT x + 3) + 1 := engM_pos x
  have h3 : c ≤ Real.log (engT x + 3) * (2 * d) := by
    have h4 := mul_le_mul_of_nonneg_right h2 (by linarith only [hd] : (0:ℝ) ≤ 2 * d)
    rwa [div_mul_cancel₀ _ (by positivity : (2:ℝ) * d ≠ 0)] at h4
  rw [engDelta]
  rw [div_le_iff₀ (by linarith only [hM] : (0:ℝ) < 2 * (Real.log (engT x + 3) + 1))]
  linarith only [h3, hM, hd]

private lemma engM_eventually_le :
    ∀ᶠ x : ℝ in atTop, Real.log (engT x + 3) + 1 ≤ 3 * Real.sqrt (Real.log x) := by
  filter_upwards [engT_eventually_ge 3, Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hT3 hL1
  have hsq1 : 1 ≤ Real.sqrt (Real.log x) := Real.one_le_sqrt.mpr hL1
  have hlog2 : Real.log 2 ≤ Real.sqrt (Real.log x) := by
    have h : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith only [this]
    linarith only [hsq1, h]
  have hTpos : 0 < engT x := engT_pos x
  have h1 : Real.log (engT x + 3) ≤ Real.log (engT x * 2) :=
    Real.log_le_log (by linarith only [hT3]) (by linarith only [hT3])
  rw [Real.log_mul (ne_of_gt hTpos) (by norm_num : (2:ℝ) ≠ 0)] at h1
  have h2 : Real.log (engT x) = Real.sqrt (Real.log x) := by rw [engT, Real.log_exp]
  rw [h2] at h1
  linarith only [hsq1, hlog2, h1]

/-! ## The perronEdgeSum bound -/

private lemma perronEdgeSum_eventually_le {c₁ C₁ C₂ cf : ℝ} (hc₁ : 0 < c₁) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hcf : 0 < cf) (hcf1 : cf ≤ c₁ / 12) (hcf2 : cf ≤ 1 / 2) :
    ∀ᶠ x : ℝ in atTop,
      perronEdgeSum x (engT x) (engSigma x c₁) C₁ C₂ ≤
        5 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
  have hx3 : ∀ᶠ x : ℝ in atTop, 3 ≤ x := eventually_ge_atTop 3
  have hL1 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hT2 : ∀ᶠ x : ℝ in atTop, 2 ≤ engT x := engT_eventually_ge 2
  have hδh : ∀ᶠ x : ℝ in atTop, engDelta x c₁ ≤ 1 / 2 :=
    engDelta_eventually_le hc₁ (by norm_num)
  have hP1 : ∀ᶠ x : ℝ in atTop,
      486 * Real.exp 1 * C₁ * (Real.log x) ^ 3 * Real.exp (-Real.sqrt (Real.log x)) ≤
        Real.exp (-(1 / 2) * Real.sqrt (Real.log x)) := by
    have h := Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le 1 one_pos 3
      (486 * Real.exp 1 * C₁) (by positivity)
    filter_upwards [h] with x hx
    simpa using hx
  have hP2 : ∀ᶠ x : ℝ in atTop,
      243 * C₁ * (Real.log x) ^ 4 * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)) ≤
        Real.exp (-(c₁ / 12) * Real.sqrt (Real.log x)) := by
    have h := Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le (c₁ / 6) (by positivity) 4
      (243 * C₁) (by positivity)
    filter_upwards [h] with x hx
    have hx' : 243 * C₁ * (Real.log x) ^ 4 * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)) ≤
        Real.exp (-((c₁ / 6) / 2) * Real.sqrt (Real.log x)) := by simpa using hx
    have heq : (c₁ / 6) / 2 = c₁ / 12 := by ring
    rw [heq] at hx'
    exact hx'
  have hP3 : ∀ᶠ x : ℝ in atTop,
      16 * (C₂ + 6 / c₁ + 1) * (Real.log x) * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)) ≤
        Real.exp (-(c₁ / 12) * Real.sqrt (Real.log x)) := by
    have h := Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le (c₁ / 6) (by positivity) 1
      (16 * (C₂ + 6 / c₁ + 1)) (by positivity)
    filter_upwards [h] with x hx
    have hx' : 16 * (C₂ + 6 / c₁ + 1) * (Real.log x) ^ 1 *
        Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)) ≤
        Real.exp (-((c₁ / 6) / 2) * Real.sqrt (Real.log x)) := by simpa using hx
    have heq : (c₁ / 6) / 2 = c₁ / 12 := by ring
    rw [heq] at hx'
    simpa using hx'
  filter_upwards [hx3, hL1, hT2, engM_eventually_le, hδh, hP1, hP2, hP3]
    with x hx3 hL1 hT2 hM3 hδh hP1 hP2 hP3
  have hxpos : 0 < x := by linarith only [hcf, hcf2, hx3]
  have hLpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  have hLnn : 0 ≤ Real.log x := le_of_lt hLpos
  have hsqLnn : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hTinv : (engT x)⁻¹ = Real.exp (-Real.sqrt (Real.log x)) := by rw [engT, ← Real.exp_neg]
  have hrpow1 : x ^ perronRe x = x * Real.exp 1 := rpow_perronRe_eq hxpos (ne_of_gt hLpos)
  have hrpowsig := rpow_engSigma_eq (x := x) (c := c₁) hxpos
  have hM5 := engM_pow5_le hL1 hM3
  have hδmul := engDelta_mul_log_ge hc₁ hL1 hM3
  have hδinv := engDelta_inv_le hc₁ hM3
  have hlogT2 := log_engT_div_two_le x
  have hσhalf := engSigma_ge_half (x := x) (c := c₁) hδh
  have hσpos : 0 < engSigma x c₁ := by linarith only [hcf, hcf2, hσhalf]
  have hdiff := perronRe_sub_engSigma_le_two hL1 hδh
  have hδle : Real.exp (-(engDelta x c₁ * Real.log x)) ≤
      Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)) :=
    Real.exp_le_exp.mpr (by linarith only [hδmul])
  have hexp12 : Real.exp (-(c₁ / 12) * Real.sqrt (Real.log x)) ≤
      Real.exp (-cf * Real.sqrt (Real.log x)) :=
    Real.exp_le_exp.mpr (by nlinarith only [hcf1, hsqLnn])
  have hexp2 : Real.exp (-(1 / 2) * Real.sqrt (Real.log x)) ≤
      Real.exp (-cf * Real.sqrt (Real.log x)) :=
    Real.exp_le_exp.mpr (by nlinarith only [hcf2, hsqLnn])
  have hMnn : 0 ≤ Real.log (engT x + 3) + 1 := le_of_lt (engM_pos x)
  have hxe : 0 ≤ x * Real.exp 1 := mul_nonneg (le_of_lt hxpos) (le_of_lt (Real.exp_pos 1))
  have hdiffnn : 0 ≤ perronRe x - engSigma x c₁ := by
    have h1 : engSigma x c₁ ≤ 1 := by dsimp [engSigma]; linarith only [engDelta_nonneg (x := x) hc₁, hc₁]
    linarith [perronRe_gt_one (by linarith : 1 < x)]
  have hK : C₂ + 6 * Real.sqrt (Real.log x) / c₁ ≤ 2 * (C₂ + 6 / c₁ + 1) * Real.log x := by
    have h1 : 6 * Real.sqrt (Real.log x) / c₁ = (6 / c₁) * Real.sqrt (Real.log x) := by ring
    rw [h1]
    have h4 : Real.sqrt (Real.log x) ≤ Real.log x := by
      nlinarith only [Real.sq_sqrt (le_of_lt hLpos), Real.one_le_sqrt.mpr hL1, hLpos, hcf, hcf2, hL1, hsqLnn]
    have hKnn : 0 ≤ C₂ + 6 / c₁ + 1 := by
      have h0 : 0 ≤ 6 / c₁ := div_nonneg (by norm_num) (le_of_lt hc₁)
      linarith only [hC₂, hcf, hcf2, h0]
    have h2 : (6 / c₁) * Real.sqrt (Real.log x) ≤ (C₂ + 6 / c₁ + 1) * Real.log x := by
      have h3 : 6 / c₁ ≤ C₂ + 6 / c₁ + 1 := by linarith only [hC₂, hcf, hcf2]
      calc (6 / c₁) * Real.sqrt (Real.log x) ≤ (C₂ + 6 / c₁ + 1) * Real.sqrt (Real.log x) :=
            mul_le_mul_of_nonneg_right h3 hsqLnn
        _ ≤ (C₂ + 6 / c₁ + 1) * Real.log x := mul_le_mul_of_nonneg_left h4 hKnn
    have h5 : C₂ ≤ (C₂ + 6 / c₁ + 1) * Real.log x := by
      have h6 : C₂ ≤ C₂ + 6 / c₁ + 1 := by
        have h0 : 0 ≤ 6 / c₁ := div_nonneg (by norm_num) (le_of_lt hc₁)
        linarith only [hcf, hcf2, h0]
      calc C₂ = C₂ * 1 := by ring
        _ ≤ (C₂ + 6 / c₁ + 1) * 1 := mul_le_mul_of_nonneg_right h6 (by norm_num)
        _ ≤ (C₂ + 6 / c₁ + 1) * Real.log x := mul_le_mul_of_nonneg_left hL1 hKnn
    linarith only [h2, h5]
  have hA : C₁ * (Real.log (engT x + 3) + 1) ^ 5 * x ^ perronRe x *
        (perronRe x - engSigma x c₁) / engT x
      ≤ x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
    have hnum : C₁ * (Real.log (engT x + 3) + 1) ^ 5 * x ^ perronRe x *
        (perronRe x - engSigma x c₁) ≤ C₁ * (243 * (Real.log x) ^ 3) * (x * Real.exp 1) * 2 := by
      rw [hrpow1]
      have hb1 : C₁ * (Real.log (engT x + 3) + 1) ^ 5 * (x * Real.exp 1) ≤
          C₁ * (243 * (Real.log x) ^ 3) * (x * Real.exp 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM5 hC₁) hxe
      exact mul_le_mul hb1 hdiff hdiffnn
        (mul_nonneg (mul_nonneg hC₁ (mul_nonneg (by norm_num) (pow_nonneg hLnn 3))) hxe)
    have h1 : C₁ * (Real.log (engT x + 3) + 1) ^ 5 * x ^ perronRe x *
        (perronRe x - engSigma x c₁) / engT x
        ≤ (C₁ * (243 * (Real.log x) ^ 3) * (x * Real.exp 1) * 2) / engT x :=
      div_le_div_of_nonneg_right hnum (le_of_lt (engT_pos x))
    have h2 : (C₁ * (243 * (Real.log x) ^ 3) * (x * Real.exp 1) * 2) / engT x
        = x * (486 * Real.exp 1 * C₁ * (Real.log x) ^ 3 *
            Real.exp (-Real.sqrt (Real.log x))) := by
      rw [div_eq_mul_inv, hTinv]; ring
    rw [h2] at h1
    have hP1' : 486 * Real.exp 1 * C₁ * (Real.log x) ^ 3 * Real.exp (-Real.sqrt (Real.log x))
        ≤ Real.exp (-cf * Real.sqrt (Real.log x)) := le_trans hP1 hexp2
    exact le_trans h1 (mul_le_mul_of_nonneg_left hP1' (le_of_lt hxpos))
  have hB : 4 * (C₂ + 1 / (1 - engSigma x c₁)) * x ^ (engSigma x c₁) / engSigma x c₁
      ≤ x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
    have hnum : 4 * (C₂ + 1 / (1 - engSigma x c₁)) * x ^ (engSigma x c₁)
        ≤ 4 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) := by
      rw [hrpowsig]
      have hsum : C₂ + 1 / (1 - engSigma x c₁) ≤ C₂ + 6 * Real.sqrt (Real.log x) / c₁ := by
        linarith only [hδinv]
      have h1 : 4 * (C₂ + 1 / (1 - engSigma x c₁)) ≤
          4 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      have h2 : x * Real.exp (-(engDelta x c₁ * Real.log x)) ≤
          x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)) :=
        mul_le_mul_of_nonneg_left hδle (le_of_lt hxpos)
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hdiv : 4 * (C₂ + 1 / (1 - engSigma x c₁)) * x ^ (engSigma x c₁) / engSigma x c₁
        ≤ 8 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) := by
      have h1 := div_le_div_of_nonneg_right hnum (le_of_lt hσpos)
      have h2 : 4 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) / engSigma x c₁
          = 4 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) * (1 / engSigma x c₁) := by
        rw [div_eq_mul_inv, one_div]
      rw [h2] at h1
      refine le_trans h1 ?_
      have hinv : 1 / engSigma x c₁ ≤ 2 := by rw [div_le_iff₀ hσpos]; linarith only [hσhalf]
      have h3 := mul_le_mul_of_nonneg_left hinv (by positivity : (0:ℝ) ≤ 4 *
        (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
        (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))))
      linarith only [h3]
    have h16 : 8 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) ≤
        16 * (C₂ + 6 / c₁ + 1) * (Real.log x) := by
      have hh := mul_le_mul_of_nonneg_left hK (by norm_num : (0:ℝ) ≤ 8)
      linarith only [hh, hK]
    have hfin : 8 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
          (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)))
        ≤ x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
      have h1 : 8 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)))
          ≤ 16 * (C₂ + 6 / c₁ + 1) * (Real.log x) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) :=
        mul_le_mul_of_nonneg_right h16 (by positivity)
      refine le_trans h1 ?_
      rw [show 16 * (C₂ + 6 / c₁ + 1) * (Real.log x) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)))
          = x * (16 * (C₂ + 6 / c₁ + 1) * (Real.log x) *
            Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) by ring]
      exact mul_le_mul_of_nonneg_left (le_trans hP3 hexp12) (le_of_lt hxpos)
    linarith only [hdiv, hfin]
  have hC : C₁ * x ^ (engSigma x c₁) * (Real.log (engT x + 3) + 1) ^ 5 *
        Real.log (engT x / 2)
      ≤ x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
    rw [hrpowsig]
    have hnum : C₁ * (x * Real.exp (-(engDelta x c₁ * Real.log x))) *
        (Real.log (engT x + 3) + 1) ^ 5 * Real.log (engT x / 2)
        ≤ C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) *
            (243 * (Real.log x) ^ 3) * Real.sqrt (Real.log x) := by
      have hY : C₁ * (x * Real.exp (-(engDelta x c₁ * Real.log x))) ≤
          C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδle (le_of_lt hxpos)) hC₁
      have hLognn : 0 ≤ Real.log (engT x / 2) := Real.log_nonneg (by linarith only [hT2] : (1:ℝ) ≤ engT x / 2)
      have hX'nn : 0 ≤ C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) :=
        mul_nonneg hC₁ (mul_nonneg (le_of_lt hxpos) (le_of_lt (Real.exp_pos _)))
      exact mul_le_mul (mul_le_mul hY hM5 (pow_nonneg hMnn 5) hX'nn) hlogT2 hLognn
        (mul_nonneg hX'nn (mul_nonneg (by norm_num) (pow_nonneg hLnn 3)))
    have h3 : Real.sqrt (Real.log x) ≤ Real.log x := by
      nlinarith only [Real.sq_sqrt (le_of_lt hLpos), Real.one_le_sqrt.mpr hL1, hLpos, hcf, hcf2, hL1, hsqLnn]
    have hmid : C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) *
        (243 * (Real.log x) ^ 3) * Real.sqrt (Real.log x)
        ≤ x * (243 * C₁ * (Real.log x) ^ 4 *
            Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) := by
      have h4 : (Real.log x) ^ 3 * Real.sqrt (Real.log x) ≤ (Real.log x) ^ 4 := by
        calc (Real.log x) ^ 3 * Real.sqrt (Real.log x) ≤ (Real.log x) ^ 3 * Real.log x :=
              mul_le_mul_of_nonneg_left h3 (pow_nonneg hLnn 3)
          _ = (Real.log x) ^ 4 := by ring
      have hnn : 0 ≤ C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) * 243 :=
        mul_nonneg (mul_nonneg hC₁ (mul_nonneg (le_of_lt hxpos) (le_of_lt (Real.exp_pos _))))
          (by norm_num)
      have h5 := mul_le_mul_of_nonneg_left h4 hnn
      calc C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) *
            (243 * (Real.log x) ^ 3) * Real.sqrt (Real.log x)
          = (C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) * 243) *
              ((Real.log x) ^ 3 * Real.sqrt (Real.log x)) := by ring
        _ ≤ (C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) * 243) *
              (Real.log x) ^ 4 := h5
        _ = x * (243 * C₁ * (Real.log x) ^ 4 *
              Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) := by ring
    have h6 : x * (243 * C₁ * (Real.log x) ^ 4 *
          Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)))
        ≤ x * Real.exp (-cf * Real.sqrt (Real.log x)) :=
      mul_le_mul_of_nonneg_left (le_trans hP2 hexp12) (le_of_lt hxpos)
    linarith only [hnum, hmid, h6]
  rw [perronEdgeSum]
  linarith only [hA, hB, hC]

/-! ## const_mul_log absorption -/

private lemma const_mul_log_le_mul_exp_neg_sqrtLog (a : ℝ) (ha : 0 < a) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop,
      C * Real.log x ≤ x * Real.exp (-a * Real.sqrt (Real.log x)) := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · rw [← hC0]
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    simp only [zero_mul]
    exact mul_nonneg (le_of_lt hxpos) (le_of_lt (Real.exp_pos _))
  · set b₀ : ℝ := max 1 (max (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))) with hb₀def
    have hb₀ge1 : 1 ≤ b₀ := by
      rw [hb₀def]; exact le_max_left 1 (max (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0))))
    have hb₀ge2a : 2 * a ≤ b₀ := by
      rw [hb₀def]
      exact le_trans (le_max_left (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0))))
        (le_max_right 1 (max (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))))
    have hb₀pos : 0 < b₀ := lt_of_lt_of_le zero_lt_one hb₀ge1
    refine Filter.eventually_atTop.2 ⟨Real.exp (b₀ ^ 2), ?_⟩
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
    have hLge : b₀ ^ 2 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).2 hx
    have hLnonneg : 0 ≤ Real.log x := le_trans (sq_nonneg b₀) hLge
    set b : ℝ := Real.sqrt (Real.log x) with hbdef
    have hbsq : b ^ 2 = Real.log x := Real.sq_sqrt hLnonneg
    have hbnonneg : 0 ≤ b := Real.sqrt_nonneg _
    have hbge : b₀ ≤ b := by
      rw [hbdef, ← Real.sqrt_sq (le_of_lt hb₀pos)]
      exact Real.sqrt_le_sqrt hLge
    have hbge1 : 1 ≤ b := le_trans hb₀ge1 hbge
    have hbge2a : 2 * a ≤ b := le_trans hb₀ge2a hbge
    have hbge8 : 8 ≤ b := by
      have h8 : 8 ≤ b₀ := by
        rw [hb₀def]
        exact le_trans (le_trans (le_max_left 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))
            (le_max_right (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))))
          (le_max_right 1 (max (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))))
      linarith only [hbge, h8]
    have hbgeT : 2 * Real.sqrt (2 * max (Real.log C) 0) ≤ b := by
      have h8 : 2 * Real.sqrt (2 * max (Real.log C) 0) ≤ b₀ := by
        rw [hb₀def]
        exact le_trans (le_trans (le_max_right 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))
            (le_max_right (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))))
          (le_max_right 1 (max (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))))
      linarith only [hbge, h8]
    have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hbge1
    have hlogC : Real.log C ≤ b ^ 2 / 8 := by
      have hs : Real.sqrt (2 * max (Real.log C) 0) ≤ b / 2 := by linarith only [hbgeT]
      have hTnn : (0:ℝ) ≤ 2 * max (Real.log C) 0 := by
        have : (0:ℝ) ≤ max (Real.log C) 0 := le_max_right _ _
        linarith only [this]
      have hsq : 2 * max (Real.log C) 0 ≤ (b / 2) ^ 2 := by
        have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
        rwa [Real.sq_sqrt hTnn] at h
      have hmax : max (Real.log C) 0 ≤ b ^ 2 / 8 := by linarith only [hsq]
      exact le_trans (le_max_left _ _) hmax
    have hlogb : 2 * Real.log b ≤ 3 * b ^ 2 / 8 := by
      have h1 : Real.log b ≤ b := Real.log_le_self (le_of_lt hbpos)
      have h2 : b ≤ 3 * b ^ 2 / 16 := by nlinarith only [hbge8, hbnonneg]
      linarith only [h1, h2]
    have hkey : C * b ^ 2 * Real.exp (a * b) ≤ Real.exp (b ^ 2) := by
      have hb2pos : 0 < b ^ 2 := pow_pos hbpos 2
      have expand : C * b ^ 2 ≤ Real.exp (b ^ 2 / 2) := by
        rw [← Real.log_le_log_iff (mul_pos hCpos hb2pos) (Real.exp_pos _), Real.log_exp,
          Real.log_mul (ne_of_gt hCpos) (ne_of_gt hb2pos), Real.log_pow]
        push_cast
        linarith only [hlogC, hlogb]
      have expab : Real.exp (a * b) ≤ Real.exp (b ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr; nlinarith only [hbge2a, hb₀ge2a, hbnonneg, hbge]
      calc C * b ^ 2 * Real.exp (a * b) = (C * b ^ 2) * Real.exp (a * b) := by ring
        _ ≤ Real.exp (b ^ 2 / 2) * Real.exp (b ^ 2 / 2) :=
            mul_le_mul expand expab (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
        _ = Real.exp (b ^ 2) := by rw [← Real.exp_add]; ring_nf
    have hfinal : C * Real.log x * Real.exp (a * Real.sqrt (Real.log x)) ≤ x := by
      calc C * Real.log x * Real.exp (a * Real.sqrt (Real.log x))
          = C * b ^ 2 * Real.exp (a * b) := by
            rw [show Real.sqrt (Real.log x) = b from hbdef.symm, ← hbsq]
        _ ≤ Real.exp (b ^ 2) := hkey
        _ = x := by rw [hbsq]; exact Real.exp_log hxpos
    have hexpneg : x * Real.exp (-a * Real.sqrt (Real.log x)) =
        x / Real.exp (a * Real.sqrt (Real.log x)) := by
      rw [show -a * Real.sqrt (Real.log x) = -(a * Real.sqrt (Real.log x)) by ring,
        Real.exp_neg, div_eq_mul_inv]
    rw [hexpneg, le_div_iff₀ (Real.exp_pos _)]
    exact hfinal

/-! ## Truncation absorption -/

private lemma trunc_eventually_le {Ctr cf : ℝ} (hCtr : 0 ≤ Ctr) (hcf : 0 < cf)
    (hcf2 : cf ≤ 1 / 2) :
    ∀ᶠ x : ℝ in atTop,
      Ctr * (x * (Real.log x) ^ 2 / engT x + Real.log x) ≤
        2 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
  have hP : ∀ᶠ x : ℝ in atTop,
      Ctr * (Real.log x) ^ 2 * Real.exp (-Real.sqrt (Real.log x)) ≤
        Real.exp (-(1 / 2) * Real.sqrt (Real.log x)) := by
    have h := Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le 1 one_pos 2 Ctr hCtr
    filter_upwards [h] with x hx
    simpa using hx
  have hC := const_mul_log_le_mul_exp_neg_sqrtLog cf hcf Ctr hCtr
  filter_upwards [hP, hC, eventually_ge_atTop (1 : ℝ)] with x hP hC hx1
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hsqLnn : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hTinv : (engT x)⁻¹ = Real.exp (-Real.sqrt (Real.log x)) := by rw [engT, ← Real.exp_neg]
  have h2 : Real.exp (-(1 / 2) * Real.sqrt (Real.log x)) ≤
      Real.exp (-cf * Real.sqrt (Real.log x)) :=
    Real.exp_le_exp.mpr (by nlinarith only [hcf2, hsqLnn])
  have hA : Ctr * (x * (Real.log x) ^ 2 / engT x)
      ≤ x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
    have heq : Ctr * (x * (Real.log x) ^ 2 / engT x)
        = (Ctr * (Real.log x) ^ 2 * Real.exp (-Real.sqrt (Real.log x))) * x := by
      rw [div_eq_mul_inv, hTinv]; ring
    rw [heq]
    calc (Ctr * (Real.log x) ^ 2 * Real.exp (-Real.sqrt (Real.log x))) * x
        ≤ Real.exp (-(1 / 2) * Real.sqrt (Real.log x)) * x :=
          mul_le_mul_of_nonneg_right hP (le_of_lt hxpos)
      _ ≤ Real.exp (-cf * Real.sqrt (Real.log x)) * x :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt hxpos)
      _ = x * Real.exp (-cf * Real.sqrt (Real.log x)) := by ring
  linarith only [hC, hA]

/-! ## The engine with exponential error -/

private lemma psi_sub_id_engine_exp :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      |Chebyshev.psi x - x| ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c₁, C₁, hc₁, hC₁pos, hZF1, hLD1⟩ := zeta_zeroFreeRegion_logDeriv_bound
  obtain ⟨C₂, δ₂, hC₂pos, hδ₂pos, hM2⟩ := zeta_logDeriv_near_axis_bound
  obtain ⟨ε₀, hε₀pos, hNA⟩ := zeta_zeroFree_near_axis
  obtain ⟨Ctr, hCtrpos, htrunc⟩ := psi_sub_perronZeta_bound
  set cf : ℝ := min c₁ 1 / 32 with hcfdef
  have hcfpos : 0 < cf := by rw [hcfdef]; positivity
  have hcf1 : cf ≤ c₁ / 12 := by
    rw [hcfdef]
    have h1 : min c₁ 1 ≤ c₁ := min_le_left _ _
    linarith only [hc₁, h1]
  have hcf2 : cf ≤ 1 / 2 := by
    rw [hcfdef]
    have h1 : min c₁ 1 ≤ 1 := min_le_right _ _
    linarith only [h1]
  have hC₁ : 0 ≤ C₁ := le_of_lt hC₁pos
  have hM1D := hM1_datum (c₁ := c₁) (C₁ := C₁) hc₁ hC₁ hLD1
  have hM2D := hM2_datum (C₂ := C₂) (δ₂ := δ₂) hM2
  have hx3 : ∀ᶠ x : ℝ in atTop, 3 ≤ x := eventually_ge_atTop 3
  have hL1 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hT2 : ∀ᶠ x : ℝ in atTop, 2 ≤ engT x := engT_eventually_ge 2
  have hδδ : ∀ᶠ x : ℝ in atTop, engDelta x c₁ ≤ δ₂ := engDelta_eventually_le hc₁ hδ₂pos
  have hδε : ∀ᶠ x : ℝ in atTop, engDelta x c₁ ≤ ε₀ := engDelta_eventually_le hc₁ hε₀pos
  have hδh : ∀ᶠ x : ℝ in atTop, engDelta x c₁ ≤ 1 / 2 :=
    engDelta_eventually_le hc₁ (by norm_num)
  have hrectEv : ∀ᶠ x : ℝ in atTop,
      (Set.uIcc (engSigma x c₁) (perronRe x) ×ℂ Set.uIcc (-(engT x)) (engT x)) ⊆
        {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0} := by
    filter_upwards [hx3, hδh, hδε] with x hx3 hδh hδε
    exact rect_zeta1_ne_zero_engine hx3 hc₁ hδh hδε hZF1 hNA
  have hintEv : ∀ᶠ x : ℝ in atTop,
      IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (engT x : ℂ) * Complex.I)‖)
          volume (engSigma x c₁) (perronRe x) ∧
      IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (((-engT x : ℝ) : ℂ)) * Complex.I)‖)
          volume (engSigma x c₁) (perronRe x) ∧
      IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((engSigma x c₁ : ℂ) + (t : ℂ) * Complex.I)‖)
          volume (-(engT x)) (engT x) := by
    filter_upwards [hx3, hδh, hrectEv] with x hx3 hδh hrect
    exact engine_edge_integrable hx3 hc₁ (by linarith only [hcfpos, hcf2, hδh]) hrect
  have htruncEv := trunc_eventually_le (Ctr := Ctr) (cf := cf) (le_of_lt hCtrpos) hcfpos hcf2
  have hpeS := perronEdgeSum_eventually_le (c₁ := c₁) (C₁ := C₁) (C₂ := C₂) (cf := cf)
    hc₁ hC₁ (le_of_lt hC₂pos) hcfpos hcf1 hcf2
  have h7 : ∀ᶠ x : ℝ in atTop,
      7 * Real.exp (-cf * Real.sqrt (Real.log x)) ≤ Real.exp (-(cf / 2) * Real.sqrt (Real.log x)) := by
    have h := Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le cf hcfpos 0 7 (by norm_num)
    filter_upwards [h] with x hx
    simpa using hx
  refine ⟨cf / 2, by positivity, ?_⟩
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (show ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤ x * Real.exp (-(cf / 2) * Real.sqrt (Real.log x)) from by
    filter_upwards [hx3, hL1, hT2, hδδ, hδε, hδh, hrectEv, hintEv, htruncEv, hpeS, h7]
      with x hx3 hL1 hT2 hδδ hδε hδh hrect hint htruncB hpeSB h7B
    obtain ⟨hIntTop, hIntBot, hIntL⟩ := hint
    have hper2 : perronRe x ≤ 2 := perronRe_le_two_of_three hx3
    have hper1 : 1 < perronRe x := perronRe_gt_one (by linarith only [hcfpos, hcf2, hx3] : 1 < x)
    have hxpos : 0 < x := by linarith only [hcfpos, hcf2, hx3]
    have hσpos : 0 < engSigma x c₁ := by dsimp [engSigma]; linarith only [engDelta_pos (x := x) hc₁, hcfpos, hcf2, hδh]
    have hδ1 : 0 < 1 - engSigma x c₁ := by dsimp [engSigma]; linarith only [engDelta_pos (x := x) hc₁, hc₁]
    have hHT : (1 : ℝ) ≤ engT x := le_trans (by norm_num) hT2
    have hTopB := hTopB_engine (x := x) (c := c₁) (C := C₁) (H := 1) hx3 hper2
      (le_of_lt hc₁) hHT hM1D
    have hBotB := hBotB_engine (x := x) (c := c₁) (C := C₁) (H := 1) hx3 hper2
      (le_of_lt hc₁) hHT hM1D
    have hNear := hNear_engine (x := x) (c := c₁) (C₂ := C₂) (δ₂ := δ₂) hc₁ hδδ hM2D
    have hFarPos := hFarPos_engine (x := x) (c := c₁) (C := C₁) (H := 1) hx3
      (le_of_lt hc₁) (by norm_num) hT2 hM1D
    have hFarNeg := hFarNeg_engine (x := x) (c := c₁) (C := C₁) (H := 1) hx3
      (le_of_lt hc₁) (by norm_num) hT2 hM1D
    have hE := psi_sub_id_le_engine (x := x) (T := engT x) (σ₁ := engSigma x c₁)
      hx3 hT2 hσpos hδ1 hper1 hrect hC₁ (le_of_lt hC₂pos) htrunc hTopB hBotB hNear hFarPos hFarNeg
      hIntTop hIntBot hIntL
    have hcoef : 0 ≤ 1 / (2 * Real.pi) := by positivity
    have h2' := mul_le_mul_of_nonneg_left hpeSB hcoef
    have hle1 : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity : (0:ℝ) < 2 * Real.pi)]
      linarith only [Real.pi_gt_three, hcfpos, hcf2]
    have h2'' : (1 / (2 * Real.pi)) * (5 * x * Real.exp (-cf * Real.sqrt (Real.log x)))
        ≤ 5 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
      have hnn : 0 ≤ 5 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by positivity
      have hh := mul_le_mul_of_nonneg_right hle1 hnn
      rwa [one_mul] at hh
    have hcomb : (1 / (2 * Real.pi)) * perronEdgeSum x (engT x) (engSigma x c₁) C₁ C₂
        ≤ 5 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := le_trans h2' h2''
    calc |Chebyshev.psi x - x|
        ≤ Ctr * (x * (Real.log x) ^ 2 / engT x + Real.log x) +
            (1 / (2 * Real.pi)) * perronEdgeSum x (engT x) (engSigma x c₁) C₁ C₂ := hE
      _ ≤ 2 * x * Real.exp (-cf * Real.sqrt (Real.log x)) +
            5 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by linarith only [htruncB, hcomb, h2', h2'']
      _ = (7 * Real.exp (-cf * Real.sqrt (Real.log x))) * x := by ring
      _ ≤ Real.exp (-(cf / 2) * Real.sqrt (Real.log x)) * x :=
          mul_le_mul_of_nonneg_right h7B (le_of_lt hxpos)
      _ = x * Real.exp (-(cf / 2) * Real.sqrt (Real.log x)) := by ring)
  exact ⟨x₀, hx₀⟩

theorem psi_sub_id_powLog_real :
    ∀ A : ℝ, 0 < A → ∃ x₀ : ℝ,
      ∀ x : ℝ, x₀ ≤ x →
        |Chebyshev.psi x - x| ≤ x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨c, hc, x₀₁, hx₀₁⟩ := psi_sub_id_engine_exp
  obtain ⟨x₀₂, -, hx₀₂⟩ := exp_sqrtLog_pow_le_one hc A hA
  refine ⟨max x₀₁ (max x₀₂ 3), ?_⟩
  intro x hx
  have hx1 : x₀₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : x₀₂ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : (3 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have h1 := hx₀₁ x hx1
  have h2 := hx₀₂ x hx2
  have hxpos : 0 < x := by linarith only [hx3]
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith only [hx3])
  have hLApos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogpos A
  have hexp : Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 / (Real.log x) ^ A := by
    rw [le_div_iff₀ hLApos]
    linarith only [h2]
  calc |Chebyshev.psi x - x| ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := h1
    _ ≤ x * (1 / (Real.log x) ^ A) := mul_le_mul_of_nonneg_left hexp (le_of_lt hxpos)
    _ = x / (Real.log x) ^ A := by rw [mul_one_div]

end Commons.NumberTheory.Zeta
