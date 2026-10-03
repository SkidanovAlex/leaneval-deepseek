import Mathlib
import Submission.Commons.Analysis.Fourier.poisson_summation_scaled
import Submission.Commons.Analysis.Integral.exists_dual_witness
import Submission.Commons.Analysis.Integral.holder_complex_finset
import Submission.Commons.Analysis.Probability.lepingle_variation_ls
import Submission.Commons.Analysis.Series.variation_shift_le
import Submission.Commons.MeasureTheory.Integral.lintegral_Ioi_rpow_eq

namespace Commons.Analysis.Fourier

open _root_.MeasureTheory _root_.Metric
open scoped ENNReal Topology BigOperators

/-- The `L¹`-normalised dilation `t⁻¹ • Ψ(·/t)` convolved with `f`, evaluated at `x`. -/
noncomputable def winConv (Ψ : ℝ → ℂ) (f : ℝ → ℂ) (x t : ℝ) : ℂ :=
  ∫ y, f y * (t⁻¹ • Ψ ((x - y) / t))

variable {K : ℕ}

/-- The curve of `L¹`-normalised windowed convolutions, as a function of the scale `t > 0`. -/
noncomputable def winCurve (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) :
    {t : ℝ // 0 < t} → (Fin K → ℂ) :=
  fun t k => winConv (Ψ : ℝ → ℂ) (f k) x (t : ℝ)

/-- The logarithmic reparametrisation of `winCurve`. -/
noncomputable def winCurveR (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) :
    ℝ → (Fin K → ℂ) :=
  fun u => winCurve Ψ f x ⟨Real.exp u, Real.exp_pos u⟩

/-- The entropy-number integrand of the windowed curve at `x`. -/
noncomputable def winM (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) (l : ℝ) : ENNReal :=
  (((Metric.coveringNumber l.toNNReal (Set.range (winCurve Ψ f x)) : ℕ∞) : ENNReal) - 1)

/-- The `ℝ≥0∞`-valued supremum of the windowed curve at `x`. -/
noncomputable def winF (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) : ENNReal :=
  ⨆ (t : {t : ℝ // 0 < t}), ‖winCurve Ψ f x t‖ₑ

/-- `‖z‖ₑ = ofReal ‖z‖`. -/
lemma enorm_eq_ofReal_norm' {E : Type*} [SeminormedAddCommGroup E] (z : E) :
    ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

/-- The range of the logarithmically reparametrised curve is the range of the curve. -/
lemma range_winCurveR (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) :
    Set.range (winCurveR Ψ f x) = Set.range (winCurve Ψ f x) := by
  have h1 : Set.range (winCurveR Ψ f x)
      = Set.range (winCurve Ψ f x ∘ fun u : ℝ =>
          (⟨Real.exp u, Real.exp_pos u⟩ : {t : ℝ // 0 < t})) := rfl
  have h2 : Set.range (fun u : ℝ => (⟨Real.exp u, Real.exp_pos u⟩ : {t : ℝ // 0 < t}))
      = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro t
    exact ⟨Real.log t.1, Subtype.ext (Real.exp_log t.2)⟩
  rw [h1, Set.range_comp, h2, Set.image_univ]

/-- The supremum norm is at most the Euclidean norm. -/
lemma pi_norm_le_sqrt_sum (v : Fin K → ℂ) : ‖v‖ ≤ Real.sqrt (∑ k : Fin K, ‖v k‖ ^ 2) := by
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro k
  rw [← Real.sqrt_sq (norm_nonneg (v k))]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ k))

/-- The `ℝ≥0∞`-valued version of `pi_norm_le_sqrt_sum`. -/
lemma enorm_le_sqrt_sum (v : Fin K → ℂ) :
    ‖v‖ₑ ≤ (∑ k : Fin K, ‖v k‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
  have h2 : (∑ k : Fin K, ‖v k‖ₑ ^ (2:ℝ)) = ENNReal.ofReal (∑ k : Fin K, ‖v k‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [enorm_eq_ofReal_norm',
      show ENNReal.ofReal ‖v k‖ ^ (2:ℝ) = ENNReal.ofReal (‖v k‖ ^ 2) by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
          ENNReal.ofReal_pow (norm_nonneg _)]]
  calc ‖v‖ₑ = ENNReal.ofReal ‖v‖ := enorm_eq_ofReal_norm' v
    _ ≤ ENNReal.ofReal (Real.sqrt (∑ k : Fin K, ‖v k‖ ^ 2)) :=
        ENNReal.ofReal_le_ofReal (pi_norm_le_sqrt_sum v)
    _ = (ENNReal.ofReal (∑ k : Fin K, ‖v k‖ ^ 2)) ^ ((1:ℝ)/2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)
          (by norm_num : (0:ℝ) ≤ 1/2), Real.sqrt_eq_rpow]
    _ = (∑ k : Fin K, ‖v k‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by rw [h2]

/-! ### Arithmetic bounds for the exponent choice -/

/-- `max 1 (log (K+2))` is bounded by `200 log (K+2)`. -/
lemma max_one_log_le (K : ℕ) :
    max 1 (Real.log ((K:ℝ) + 2)) ≤ 200 * Real.log ((K:ℝ) + 2) := by
  have hKnn : (0:ℝ) ≤ (K:ℝ) := by exact_mod_cast Nat.zero_le K
  have h2 : (2:ℝ) ≤ (K:ℝ) + 2 := by linarith
  have hlog2 : 0 < Real.log ((K:ℝ) + 2) :=
    lt_of_lt_of_le (by linarith [Real.log_two_gt_d9]) (Real.log_le_log (by norm_num) h2)
  have h1 : max 1 (Real.log ((K:ℝ) + 2)) ≤ 1 + Real.log ((K:ℝ) + 2) :=
    max_le (by linarith) (by linarith)
  refine h1.trans ?_
  have h3 : (1:ℝ)/199 ≤ Real.log ((K:ℝ) + 2) :=
    le_trans (by linarith [Real.log_two_gt_d9]) (Real.log_le_log (by norm_num) h2)
  linarith

/-- The power `K ^ (1/2 - 1/s)`, with `s = 2 + 1 / max 1 (log (K+2))`, is at most `2`. -/
lemma rpow_half_sub_inv_le_two (K : ℕ) :
    (K:ℝ) ^ ((1:ℝ)/2 - 1 / (2 + 1 / max 1 (Real.log ((K:ℝ) + 2)))) ≤ 2 := by
  rcases eq_or_ne K 0 with hK | hK
  · subst hK
    simp only [Nat.cast_zero, zero_add]
    have hLpos : 0 < max 1 (Real.log ((2:ℝ))) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hlt : 1/(2 + 1/max 1 (Real.log (2:ℝ))) < 1/2 :=
      one_div_lt_one_div_of_lt (by norm_num) (by
        have hh : 0 < 1 / max 1 (Real.log (2:ℝ)) := one_div_pos.mpr hLpos
        linarith)
    have hpos : 0 < (1:ℝ)/2 - 1/(2 + 1/max 1 (Real.log (2:ℝ))) := by linarith
    rw [Real.zero_rpow hpos.ne']
    norm_num
  · have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hK
    have hKnn : (0:ℝ) ≤ (K:ℝ) := by exact_mod_cast Nat.zero_le K
    have h2 : (2:ℝ) ≤ (K:ℝ) + 2 := by linarith
    set L : ℝ := max 1 (Real.log ((K:ℝ) + 2)) with hLdef
    have hL1 : 1 ≤ L := le_max_left _ _
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
    have hLge : Real.log ((K:ℝ) + 2) ≤ L := le_max_right _ _
    have hlogpos : 0 < Real.log ((K:ℝ) + 2) :=
      lt_of_lt_of_le (by linarith [Real.log_two_gt_d9]) (Real.log_le_log (by norm_num) h2)
    have hexp : (1:ℝ)/2 - 1 / (2 + 1/L) = 1/(4*L + 2) := by
      have hLne : L ≠ 0 := ne_of_gt hLpos
      field_simp
      ring
    rw [hexp]
    have step1 : (K:ℝ) ^ (1/(4*L+2)) ≤ ((K:ℝ)+2) ^ (1/(4*L+2)) :=
      Real.rpow_le_rpow hKnn (by linarith) (by positivity)
    have step2 : ((K:ℝ)+2) ^ (1/(4*L+2)) ≤ ((K:ℝ)+2) ^ (1/(4*Real.log ((K:ℝ)+2) + 2)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
      exact one_div_le_one_div_of_le (by linarith) (by linarith [hLge])
    have step3 : ((K:ℝ)+2) ^ (1/(4*Real.log ((K:ℝ)+2) + 2)) ≤ Real.exp (1/4) := by
      have hbase : (0:ℝ) < (K:ℝ)+2 := by linarith
      rw [Real.rpow_def_of_pos hbase]
      refine Real.exp_le_exp.mpr ?_
      have hden : 0 < 4 * Real.log ((K:ℝ)+2) + 2 := by linarith
      rw [mul_one_div, div_le_iff₀ hden]
      linarith
    have step4 : Real.exp (1/4) ≤ 2 := by
      have h := Real.exp_le_exp.mpr (show (1:ℝ)/4 ≤ Real.log 2 by
        linarith [Real.log_two_gt_d9])
      rwa [Real.exp_log (by norm_num)] at h
    linarith [step1, step2, step3, step4]


/-- The final numerical comparison for the exponent choice `s = 2 + 1/L`. -/
lemma final_const_bound (K : ℕ) {s L A B : ℝ} (hL1 : 1 ≤ L) (hs : s - 2 = 1/L)
    (hLle : L ≤ 200 * Real.log ((K:ℝ)+2))
    (hKpow : (K:ℝ)^((1:ℝ)/2 - 1/s) ≤ 2) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ((1 + 2/(s-2)) * (K:ℝ)^((1:ℝ)/2-1/s))^2 * 2 * (2*(A/(s-2))^2 + 8*B)
      ≤ 10 ^ 30 * (A^2 + B^2 + 1) * (Real.log ((K:ℝ)+2))^4 := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hlogpos : 0 < Real.log ((K:ℝ)+2) := by
    have h2 : (2:ℝ) ≤ (K:ℝ)+2 := by
      have : (0:ℝ) ≤ (K:ℝ) := by exact_mod_cast Nat.zero_le K
      linarith
    exact lt_of_lt_of_le (by linarith [Real.log_two_gt_d9]) (Real.log_le_log (by norm_num) h2)
  have hLs : 1/(s-2) = L := by rw [hs, one_div_one_div]
  have hinv : (s-2)⁻¹ = L := by rw [inv_eq_one_div]; exact hLs
  have hK0 : (0:ℝ) ≤ (K:ℝ) := by exact_mod_cast Nat.zero_le K
  have hKnsq : ((K:ℝ)^((1:ℝ)/2 - 1/s))^2 ≤ 4 := by
    have h1 : (0:ℝ) ≤ (K:ℝ)^((1:ℝ)/2-1/s) := Real.rpow_nonneg hK0 _
    nlinarith [hKpow, h1]
  have hbase1 : 1 + 2/(s-2) ≤ 3*L := by
    rw [show (2:ℝ)/(s-2) = 2*(1/(s-2)) by ring, hLs]
    linarith
  have hbase1pos : 0 ≤ 1 + 2/(s-2) := by
    rw [show (2:ℝ)/(s-2) = 2*(1/(s-2)) by ring, hLs]
    linarith
  have hbasesq : (1 + 2/(s-2))^2 ≤ (3*L)^2 := pow_le_pow_left₀ hbase1pos hbase1 2
  have hterm : ((1 + 2/(s-2)) * (K:ℝ)^((1:ℝ)/2-1/s))^2 ≤ 36*L^2 := by
    rw [mul_pow]
    nlinarith [hbasesq, hKnsq]
  have hAdiv : A/(s-2) = A*L := by rw [div_eq_mul_inv, hinv]
  have hLsq : (1:ℝ) ≤ L^2 := by nlinarith
  have hstep : 2*(A/(s-2))^2 + 8*B ≤ 8*(A^2 + B^2 + 1)*L^2 := by
    rw [hAdiv]
    have hA2 : 2*(A*L)^2 ≤ 4*(A^2+B^2+1)*L^2 := by
      have h1 : 2*A^2 ≤ 4*(A^2+B^2+1) := by nlinarith [hA, hB, sq_nonneg B]
      calc 2*(A*L)^2 = (2*A^2)*L^2 := by ring
        _ ≤ (4*(A^2+B^2+1))*L^2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg L)
        _ = 4*(A^2+B^2+1)*L^2 := by ring
    have hB2 : 8*B ≤ 4*(A^2+B^2+1)*L^2 := by
      have h1 : 8*B ≤ 4*(A^2+B^2+1) := by nlinarith [hA, hB, sq_nonneg (B-1)]
      have h2 : A^2+B^2+1 ≤ (A^2+B^2+1)*L^2 :=
        le_mul_of_one_le_right (by positivity) hLsq
      linarith
    linarith
  have hL4 : L^4 ≤ (200 * Real.log ((K:ℝ)+2))^4 :=
    pow_le_pow_left₀ hLpos.le hLle 4
  have hlog4 : (200 * Real.log ((K:ℝ)+2))^4
      = 200^4 * Real.log ((K:ℝ)+2)^4 := by rw [mul_pow]
  have hconst : (576 : ℝ) * 200^4 ≤ 10^30 := by norm_num
  calc ((1 + 2/(s-2)) * (K:ℝ)^((1:ℝ)/2-1/s))^2 * 2 * (2*(A/(s-2))^2 + 8*B)
      ≤ 36*L^2 * 2 * (8*(A^2 + B^2 + 1)*L^2) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hterm (by norm_num)
        · exact hstep
        · positivity
        · positivity
    _ = 576 * (A^2 + B^2 + 1) * L^4 := by ring
    _ ≤ 576 * (A^2 + B^2 + 1) * (200 * Real.log ((K:ℝ)+2))^4 := by
        apply mul_le_mul_of_nonneg_left hL4
        positivity
    _ = 576 * 200^4 * (A^2 + B^2 + 1) * Real.log ((K:ℝ)+2)^4 := by
        rw [hlog4]; ring
    _ ≤ 10^30 * (A^2 + B^2 + 1) * Real.log ((K:ℝ)+2)^4 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right hconst (by positivity)

/-! ### The main assembly -/

end Commons.Analysis.Fourier
