import Mathlib
import Submission.Work.LinnikAreas.ZetaPrincipalDefs

open Complex MeasureTheory
open scoped BigOperators

namespace Work.LinnikAreas

open Commons.NumberTheory.Linnik

/-- **The exact Perron identity for ζ with the tent kernel.**

With `L = 11/2`, `K = 3/10` (but here for arbitrary `0 < 2K < L`) and `𝓛 = log q`, the
Mellin/Perron inversion of the Laplace transform `tentK` of Heath-Brown's tent weight gives
the identity

`(log q)⁻¹ • Σ_{n ≤ X} Λ(n)/n · w(log n / log q)
   = (1/2π) ∫_ℝ (-ζ'/ζ)(2+it) · Φ(2+it) dt`,

where `Φ(u) = tentK L K ((1-u) log q)`.  The sum is really supported on the finite range
`q^{L-2K} < n ≤ q^L`, which lies below `X` by hypothesis. -/
theorem zeta_perron_tent {L K : ℝ} (hK : 0 < K) (h2K : 2 * K < L) {q : ℕ} (hq : 2 ≤ q)
    {X : ℕ} (hX : (q : ℝ) ^ L ≤ (X : ℝ)) :
    (((Real.log (q : ℝ) : ℝ)) : ℂ)⁻¹ *
        (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
          ((Commons.NumberTheory.Linnik.tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ))
      = (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
          (- logDeriv riemannZeta ((2 : ℂ) + (t : ℂ) * Complex.I)) *
            Commons.NumberTheory.Linnik.tentPhi L K q ((2 : ℂ) + (t : ℂ) * Complex.I) := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  set lq : ℂ := ((Real.log (q : ℝ) : ℝ) : ℂ) with hlq
  have hlqne : lq ≠ 0 := by
    intro h
    have h' : lq.re = 0 := by simpa only [Complex.zero_re] using congrArg Complex.re h
    rw [hlq, Complex.ofReal_re] at h'
    exact hlogq.ne' h'
  have hPhi : ∀ t : ℝ, Commons.NumberTheory.Linnik.tentPhi L K q ((2 : ℂ) + (t : ℂ) * Complex.I)
      = tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq) := by
    intro t
    rw [Commons.NumberTheory.Linnik.tentPhi, hlq]
  rw [show (fun t : ℝ => (- logDeriv riemannZeta ((2 : ℂ) + (t : ℂ) * Complex.I)) *
        Commons.NumberTheory.Linnik.tentPhi L K q ((2 : ℂ) + (t : ℂ) * Complex.I))
      = (fun t : ℝ => (- logDeriv riemannZeta ((2 : ℂ) + (t : ℂ) * Complex.I)) *
        tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq))
      from funext (fun t => by rw [hPhi t])]
  set Cb : ℝ := Real.exp ((L - 2 * K) * Real.log (q : ℝ)) *
      (1 + Real.exp (K * Real.log (q : ℝ))) ^ 2 * ((Real.log (q : ℝ)) ^ 2)⁻¹ with hCb
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  have hKbound : ∀ t : ℝ, ‖tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq)‖
      ≤ Cb * (1 + t ^ 2)⁻¹ := by
    intro t
    have h := norm_tentK_line_two hK h2K hq t
    rw [hlq]
    calc ‖tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * ((Real.log (q : ℝ) : ℝ) : ℂ))‖
        ≤ Real.exp ((L - 2 * K) * Real.log (q : ℝ)) *
            (1 + Real.exp (K * Real.log (q : ℝ))) ^ 2 *
            (((1 + t ^ 2) * (Real.log (q : ℝ)) ^ 2))⁻¹ := h
      _ = Cb * (1 + t ^ 2)⁻¹ := by
          rw [hCb, mul_inv]
          ring
  set G : ℕ → ℝ → ℂ := fun n t => (ArithmeticFunction.vonMangoldt n : ℂ) *
      ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
        tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq) with hG
  have hGb : ∀ (n : ℕ) (t : ℝ), ‖G n t‖ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((n : ℝ))⁻¹ ^ 2 * Cb * (1 + t ^ 2)⁻¹ := by
    intro n t
    rw [hG, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rcases eq_or_ne n 0 with rfl | hn0
    · rw [ArithmeticFunction.map_zero]; simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      rw [norm_nat_cpow n hn1 t]
      have h2 : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      have h3 : (0 : ℝ) ≤ ((n : ℝ))⁻¹ ^ 2 := by positivity
      calc (ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ))⁻¹ ^ 2 *
            ‖tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq)‖
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ))⁻¹ ^ 2 *
            (Cb * (1 + t ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left (hKbound t) (mul_nonneg h2 h3)
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ))⁻¹ ^ 2 * Cb *
            (1 + t ^ 2)⁻¹ := by ring
  have hInt : ∀ n : ℕ, Integrable (G n) volume := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · have hzero : G 0 = fun _ => 0 := by
        funext t
        simp [hG, ArithmeticFunction.map_zero]
      rw [hzero]
      exact integrable_zero _ _ _
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hmeas : AEStronglyMeasurable (G n) volume := by
        apply Continuous.aestronglyMeasurable
        rw [hG]
        refine Continuous.mul ?_ ?_
        · refine Continuous.mul ?_ ?_
          · exact continuous_const
          · refine Continuous.cpow continuous_const (by fun_prop) ?_
            intro t
            exact Or.inl (by rw [Complex.natCast_re]; exact_mod_cast hn1)
        · exact (tentK_diff L K).continuous.comp (by fun_prop)
      refine Integrable.mono' (g := fun t : ℝ => ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((n : ℝ))⁻¹ ^ 2 * Cb) * (1 + t ^ 2)⁻¹)
        (integrable_inv_one_add_sq.const_mul _) hmeas ?_
      exact Filter.Eventually.of_forall (fun t => hGb n t)
  have hSum : Summable (fun n : ℕ => ∫ t : ℝ, ‖G n t‖) := by
    have hIint : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) volume := integrable_inv_one_add_sq
    have hVsum : Summable (fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ))⁻¹ ^ 2) := by
      have hLsum := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (2 : ℂ)) (by norm_num)
      rw [LSeriesSummable] at hLsum
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (by
        simpa using hLsum.norm)
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        rw [LSeries.term_def, if_neg hn0, norm_div,
          show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn1 : (0 : ℝ) < n),
          Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have h2r : ((2 : ℂ)).re = 2 := by simp
        rw [h2r, show ((n : ℝ) ^ (2 : ℝ)) = (n : ℝ) ^ 2 by rw [Real.rpow_two],
          div_eq_mul_inv, inv_pow]
    have hIntb : ∀ n : ℕ, ∫ t : ℝ, ‖G n t‖ ≤ ((ArithmeticFunction.vonMangoldt n : ℝ) *
        ((n : ℝ))⁻¹ ^ 2 * Cb) * (∫ t : ℝ, (1 + t ^ 2)⁻¹) := by
      intro n
      have hmono : ∫ t : ℝ, ‖G n t‖ ≤ ∫ t : ℝ, ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((n : ℝ))⁻¹ ^ 2 * Cb) * (1 + t ^ 2)⁻¹ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
          (hIint.const_mul _) ?_
        exact Filter.Eventually.of_forall (fun t => hGb n t)
      rwa [integral_const_mul] at hmono
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _)) hIntb ?_
    simpa only [mul_assoc] using hVsum.mul_right (Cb * (∫ t : ℝ, (1 + t ^ 2)⁻¹))
  have hpt : ∀ t : ℝ, (- logDeriv riemannZeta ((2 : ℂ) + (t : ℂ) * Complex.I)) *
      tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq) = ∑' n : ℕ, G n t := by
    intro t
    have hre : (((2 : ℂ) + (t : ℂ) * Complex.I)).re = 2 := by simp
    have hld := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (s := ((2 : ℂ) + (t : ℂ) * Complex.I)) (by rw [hre]; norm_num)
    rw [hG,
      show (- logDeriv riemannZeta ((2 : ℂ) + (t : ℂ) * Complex.I))
        = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            ((2 : ℂ) + (t : ℂ) * Complex.I) by rw [hld]; simp [logDeriv, Pi.div_apply, div_eq_mul_inv],
      LSeries, ← tsum_mul_right]
    apply tsum_congr
    intro n
    rw [LSeries.term_def]
    by_cases hn0 : n = 0
    · simp [hn0]
    · rw [if_neg hn0]
      beta_reduce
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
  rw [funext hpt, ← integral_tsum_of_summable_integral_norm hInt hSum]
  have hterm : ∀ n : ℕ, (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, G n t
      = ((n : ℂ))⁻¹ * ((tentWeight L K (Real.log n / Real.log q) : ℝ) : ℂ) / lq *
          ((ArithmeticFunction.vonMangoldt n : ℂ)) := by
    intro n
    rw [hG]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [ArithmeticFunction.map_zero]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have h1 : (∫ t : ℝ, (ArithmeticFunction.vonMangoldt n : ℂ) *
            ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
              tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq))
          = ((ArithmeticFunction.vonMangoldt n : ℂ)) *
            ∫ t : ℝ, ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
              tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        ring
      rw [h1]
      have hs' : (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
            ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
              tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq)
          = ((n : ℂ))⁻¹ * ((tentWeight L K (Real.log n / Real.log q) : ℝ) : ℂ) / lq := by
        have hswap : (∫ t : ℝ, ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
              tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * ((Real.log (q : ℝ) : ℝ) : ℂ)))
            = ∫ t : ℝ, tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) *
                ((Real.log (q : ℝ) : ℝ) : ℂ)) *
              ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) := by
          apply integral_congr_ae
          filter_upwards with t
          ring
        rw [show lq = ((Real.log (q : ℝ) : ℝ) : ℂ) from hlq, hswap]
        exact single_inversion (L := L) (K := K) hK h2K hq hn1
      rw [show (1 / (2 * (Real.pi : ℂ))) *
            (((ArithmeticFunction.vonMangoldt n : ℂ)) *
              ∫ t : ℝ, ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
                tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq))
          = ((ArithmeticFunction.vonMangoldt n : ℂ)) *
            ((1 / (2 * (Real.pi : ℂ))) *
              ∫ t : ℝ, ((n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) *
                tentK L K ((1 - ((2 : ℂ) + (t : ℂ) * Complex.I)) * lq)) by ring,
        hs']
      ring
  rw [← tsum_mul_left,
    show (∑' n : ℕ, (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, G n t)
      = ∑' n : ℕ, ((n : ℂ)⁻¹ *
        ((tentWeight L K (Real.log n / Real.log q) : ℝ) : ℂ) / lq *
          ((ArithmeticFunction.vonMangoldt n : ℂ)))
      from tsum_congr (fun n => hterm n)]
  clear hterm hGb hKbound hInt hSum hpt
  have hzero : ∀ n : ℕ, X < n → ((n : ℂ))⁻¹ *
        ((tentWeight L K (Real.log n / Real.log q) : ℝ) : ℂ) / lq *
          ((ArithmeticFunction.vonMangoldt n : ℂ)) = 0 := by
    intro n hn
    have hnq : (q : ℝ) ^ L < (n : ℝ) := lt_of_le_of_lt hX (by exact_mod_cast hn)
    have hu : L < Real.log (n : ℝ) / Real.log (q : ℝ) := by
      rw [lt_div_iff₀ hlogq]
      calc L * Real.log (q : ℝ) = Real.log ((q : ℝ) ^ L) := by
            rw [Real.log_rpow (by positivity : (0 : ℝ) < (q : ℝ))]
        _ < Real.log (n : ℝ) := Real.log_lt_log (Real.rpow_pos_of_pos (by positivity) _) hnq
    have htw : tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) = 0 :=
      (tentWeight_bounds (le_of_lt hK) (le_of_lt h2K)).2.2.2 _ (le_of_lt hu)
    rw [htw]
    simp
  have hsupport : ∀ n ∉ Finset.Icc 1 X, ((n : ℂ))⁻¹ *
        ((tentWeight L K (Real.log n / Real.log q) : ℝ) : ℂ) / lq *
          ((ArithmeticFunction.vonMangoldt n : ℂ)) = 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    push Not at hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · exact hzero n (hn (by omega))
  rw [tsum_eq_sum hsupport, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  field_simp

end Work.LinnikAreas
