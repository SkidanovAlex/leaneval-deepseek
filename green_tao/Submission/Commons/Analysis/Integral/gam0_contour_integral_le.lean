import Mathlib
import Submission.Commons.Analysis.Integral.exp_neg_log_div_log_pow_integral_le
import Submission.Commons.Analysis.Complex.contour_shift_residue
import Submission.Commons.Analysis.Complex.norm_gam_le
import Submission.Commons.Analysis.Complex.norm_cpow_gam_eq

namespace Commons.Analysis.Integral

/-!
# The `Γ₀` contour integral bound (Green–Tao Lemma A.1, first bound)

For the curve `Commons.Analysis.Complex.gam β t = (-(β/log(|t|+2)) : ℝ) + t·I` (the left boundary of
the classical zero-free region) and its velocity `Commons.Analysis.Complex.gamDot β t`, one has

`∫_ℝ ‖(R : ℂ)^(gam β t)‖ / ‖gam β t‖^A · (log(‖gam β t‖ + 2))^B · ‖gamDot β t‖ dt`
`    ≤ C · exp(-δ √(log R))`     for all `R ≥ 8`,

for every `A > 1`, `B ≥ 0`, `β > 0`.

## Hints

* `‖(R : ℂ)^z‖ = R^{Re z} = exp(-(β/log(|t|+2))·log R)` for `R > 0`, i.e. exactly the exponential
  factor of `Commons.Analysis.Integral.exp_neg_log_div_log_pow_integral_le` with `L = log R ≥ 2`.
* The integrand is even in `t`, so `∫_ℝ = 2 ∫_{Ici 0}` (`phi β (-t) = phi β t` gives
  `gam β (-t) = -conj (gam β t)`).
* `‖gam β t‖ ≥ c·(|t| + β)` for an explicit `c > 0` depending on `β` (use `‖gam β t‖ ≥ |t|` and
  `‖gam β t‖ ≥ β/log(|t|+2)`, splitting on `|t| ≤ β` vs `|t| ≥ β`), and
  `log(‖gam β t‖ + 2) ≤ C·log(|t| + 2)`.
* `‖gamDot β t‖` is bounded by an explicit constant depending only on `β` (near `t = 0`,
  `Phi' β 0 = β/(2 (log 2)^2)`, and it decays for large `|t|`).
-/
open _root_.Complex MeasureTheory intervalIntegral Filter Set
open scoped Topology Interval BigOperators

open Commons.Analysis.Complex

lemma gam_norm_ge_abs (β t : ℝ) : |t| ≤ ‖gam β t‖ := by
  have h := Complex.abs_im_le_norm (gam β t)
  rwa [gam_im] at h

lemma gam_norm_ge_phi {β : ℝ} (hβ : 0 < β) (t : ℝ) : β / Real.log (|t| + 2) ≤ ‖gam β t‖ := by
  have h := Complex.abs_re_le_norm (gam β t)
  rw [Commons.Analysis.Complex.gam_re, abs_neg, abs_of_nonneg] at h
  · exact h
  · exact div_nonneg hβ.le (Real.log_nonneg (by have := abs_nonneg t; linarith))

/-- There is a positive constant `c` with `c * (|t| + β) ≤ ‖gam β t‖`. -/
lemma exists_gam_norm_ge {β : ℝ} (hβ : 0 < β) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * (|t| + β) ≤ ‖gam β t‖ := by
  have hlogβ : 0 < Real.log (β + 2) := Real.log_pos (by linarith)
  refine ⟨min (1/2) (1/(2 * Real.log (β + 2))), lt_min (by norm_num) (by positivity), ?_⟩
  intro t
  rcases le_or_gt β |t| with ht | ht
  · have h1 : |t| ≤ ‖gam β t‖ := gam_norm_ge_abs β t
    have h2 : min (1/2) (1/(2 * Real.log (β + 2))) ≤ 1/2 := min_le_left _ _
    have h3 : min (1/2) (1/(2 * Real.log (β + 2))) * (|t| + β)
        ≤ (1/2) * (|t| + β) := mul_le_mul_of_nonneg_right h2 (by positivity)
    have h4 : (1/2) * (|t| + β) ≤ |t| := by linarith
    linarith
  · have hle : β / Real.log (β + 2) ≤ ‖gam β t‖ := by
      have h1 := gam_norm_ge_phi hβ t
      have h2 : Real.log (|t| + 2) ≤ Real.log (β + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have h3 : β / Real.log (β + 2) ≤ β / Real.log (|t| + 2) :=
        div_le_div_of_nonneg_left hβ.le (Real.log_pos (by linarith [abs_nonneg t])) h2
      linarith
    have h2 : min (1/2) (1/(2 * Real.log (β + 2))) ≤ 1/(2 * Real.log (β + 2)) :=
      min_le_right _ _
    have h3 : min (1/2) (1/(2 * Real.log (β + 2))) * (|t| + β)
        ≤ (1/(2 * Real.log (β + 2))) * (|t| + β) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have h4 : (1/(2 * Real.log (β + 2))) * (|t| + β) ≤ β / Real.log (β + 2) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.log (β + 2))]
      have h5 : (β / Real.log (β + 2)) * (2 * Real.log (β + 2)) = 2 * β := by
        field_simp
      rw [h5]
      nlinarith
    linarith


/-! ## Bounds for `gamDot` -/

lemma phiDeriv_aux_le {β : ℝ} (hβ : 0 < β) {s : ℝ} (hs : 0 ≤ s) :
    β / ((s + 2) * (Real.log (s + 2)) ^ 2) ≤ β / (2 * (Real.log 2) ^ 2) := by
  have h2 : (2:ℝ) ≤ s + 2 := by linarith
  have hl2 : (Real.log 2) ^ 2 ≤ (Real.log (s + 2)) ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg (by norm_num)) (Real.log_le_log (by norm_num) h2) 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine div_le_div_of_nonneg_left hβ.le (by positivity) ?_
  have : (2:ℝ) * (Real.log 2) ^ 2 ≤ (s + 2) * (Real.log (s + 2)) ^ 2 := by nlinarith
  exact this

lemma PhiPos_nonneg {β : ℝ} (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ PhiPos β t := by
  rw [PhiPos]
  exact div_nonneg hβ.le (mul_nonneg (by linarith) (sq_nonneg _))

lemma abs_Phi'_le {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    |Phi' β t| ≤ β / (2 * (Real.log 2) ^ 2) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [Phi', if_pos ht, abs_of_nonneg (PhiPos_nonneg hβ ht)]
    exact phiDeriv_aux_le hβ ht
  · rw [Phi', if_neg (not_le.mpr ht), PhiNeg]
    rw [abs_neg, abs_of_nonneg]
    · exact phiDeriv_aux_le hβ (by linarith)
    · exact div_nonneg hβ.le (mul_nonneg (by linarith) (sq_nonneg _))

lemma gamDot_norm_le {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    ‖gamDot β t‖ ≤ β / (2 * (Real.log 2) ^ 2) + 1 := by
  have h1 : ‖gamDot β t‖ ≤ ‖(Phi' β t : ℂ)‖ + ‖(Complex.I : ℂ)‖ := by
    simpa only [gamDot] using norm_add_le ((Phi' β t : ℂ)) (Complex.I)
  rw [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs] at h1
  linarith [abs_Phi'_le hβ t, h1]

/-! ## Symmetry -/

lemma PhiNeg_neg (β t : ℝ) : PhiNeg β (-t) = - PhiPos β t := by
  rw [PhiNeg, PhiPos]; ring_nf

lemma PhiPos_neg (β t : ℝ) : PhiPos β (-t) = - PhiNeg β t := by
  rw [PhiNeg, PhiPos]; ring_nf

lemma Phi'_neg (β : ℝ) {t : ℝ} (ht : t ≠ 0) : Phi' β (-t) = - Phi' β t := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hnt : (0:ℝ) ≤ -t := by linarith
    simp only [Phi']
    rw [if_pos hnt, if_neg (not_le.mpr ht)]
    exact PhiPos_neg β t
  · have hnt : ¬ (0 ≤ -t) := by intro h; linarith
    simp only [Phi']
    rw [if_neg hnt, if_pos (le_of_lt ht)]
    exact PhiNeg_neg β t

lemma gamDot_neg_eq_neg_conj (β : ℝ) {t : ℝ} (ht : t ≠ 0) :
    gamDot β (-t) = -(starRingEnd ℂ) (gamDot β t) := by
  simp only [gamDot, Phi'_neg (β:=β) ht, map_add, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg]
  ring

lemma gamDot_norm_neg (β t : ℝ) : ‖gamDot β (-t)‖ = ‖gamDot β t‖ := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [gamDot_neg_eq_neg_conj β ht, norm_neg, Complex.norm_conj]

lemma gam_re_neg (β t : ℝ) : (gam β (-t)).re = (gam β t).re := by
  simp only [Commons.Analysis.Complex.gam_re, abs_neg]

lemma gam_norm_neg (β t : ℝ) : ‖gam β (-t)‖ = ‖gam β t‖ := by
  rw [gam_neg_eq_conj, Complex.norm_conj]

lemma norm_cpow_gam_neg (β R t : ℝ) (hR : 0 < R) :
    ‖(R : ℂ) ^ (gam β (-t))‖ = ‖(R : ℂ) ^ (gam β t)‖ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hR, Complex.norm_cpow_eq_rpow_re_of_pos hR, gam_re_neg]


/-! ## The pointwise integrand bound -/

lemma gam0_integrand_pointwise_le {β A B : ℝ} (hA : 1 < A) (hB : 0 ≤ B) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      (1 / ‖gam β t‖ ^ A) * (Real.log (‖gam β t‖ + 2)) ^ B * ‖gamDot β t‖
        ≤ C * (Real.log (t + 2)) ^ B / (t + β) ^ A := by
  obtain ⟨c, hcpos, hc⟩ := exists_gam_norm_ge hβ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Clog : ℝ := 1 + Real.log (1 + β / (2 * Real.log 2)) / Real.log 2 with hClogdef
  have hKnn2 : 0 ≤ β / (2 * Real.log 2) := le_of_lt (div_pos hβ (by positivity))
  have hClogpos : 0 < Clog := by
    have h : 0 < Real.log (1 + β / (2 * Real.log 2)) :=
      Real.log_pos (by have h' : 0 < β / (2 * Real.log 2) := div_pos hβ (by positivity); linarith)
    rw [hClogdef]
    exact add_pos_of_pos_of_nonneg one_pos (div_nonneg h.le hlog2pos.le)
  have hA0 : 0 ≤ A := le_of_lt (lt_trans zero_lt_one hA)
  refine ⟨c ^ (-A) * Clog ^ B * (β / (2 * (Real.log 2) ^ 2) + 1), ?_, ?_⟩
  · have h1 : 0 < c ^ (-A) := Real.rpow_pos_of_pos hcpos _
    have h2 : 0 < Clog ^ B := Real.rpow_pos_of_pos hClogpos B
    have h3 : 0 < β / (2 * (Real.log 2) ^ 2) + 1 := by positivity
    positivity
  · intro t ht0
    have hKnn : 0 ≤ β / Real.log 2 := le_of_lt (div_pos hβ hlog2pos)
    have hctb : 0 < c * (t + β) := mul_pos hcpos (by linarith)
    have hgam : c * (t + β) ≤ ‖gam β t‖ := by
      have := hc t
      rwa [abs_of_nonneg ht0] at this
    have hstep1 : (1:ℝ) / ‖gam β t‖ ^ A ≤ c ^ (-A) / (t + β) ^ A := by
      have h2 : (c * (t + β)) ^ A ≤ ‖gam β t‖ ^ A :=
        Real.rpow_le_rpow (le_of_lt hctb) hgam hA0
      have h3 : (c * (t + β)) ^ A = c ^ A * (t + β) ^ A :=
        Real.mul_rpow hcpos.le (by linarith)
      rw [h3] at h2
      have h4 : (0:ℝ) < c ^ A * (t + β) ^ A :=
        mul_pos (Real.rpow_pos_of_pos hcpos A) (Real.rpow_pos_of_pos (by linarith) A)
      have h5 : (1:ℝ) / ‖gam β t‖ ^ A ≤ 1 / (c ^ A * (t + β) ^ A) :=
        one_div_le_one_div_of_le h4 h2
      have h6 : (1:ℝ) / (c ^ A * (t + β) ^ A) = c ^ (-A) / (t + β) ^ A := by
        rw [Real.rpow_neg hcpos.le, one_div, mul_inv, div_eq_mul_inv]
      rwa [h6] at h5
    have hClog_bound : Real.log (‖gam β t‖ + 2) ≤ Clog * Real.log (t + 2) := by
      have hgle : ‖gam β t‖ ≤ t + β / Real.log 2 := by
        have := norm_gam_le hβ t
        rwa [abs_of_nonneg ht0] at this
      have hstep1' : Real.log (‖gam β t‖ + 2) ≤ Real.log (t + 2 + β / Real.log 2) :=
        Real.log_le_log (by linarith [norm_nonneg (gam β t)]) (by linarith)
      have hstep2 : t + 2 + β / Real.log 2 ≤ (t + 2) * (1 + β / (2 * Real.log 2)) := by
        have hK : β / (2 * Real.log 2) = (β / Real.log 2) / 2 := by ring
        rw [hK]
        nlinarith [hKnn, ht0]
      have hstep3 : Real.log (t + 2 + β / Real.log 2)
          ≤ Real.log ((t + 2) * (1 + β / (2 * Real.log 2))) :=
        Real.log_le_log (by linarith) hstep2
      rw [Real.log_mul (by linarith : (t:ℝ) + 2 ≠ 0)
        (by positivity : (1:ℝ) + β / (2 * Real.log 2) ≠ 0)] at hstep3
      have hClog1nn : 0 ≤ Clog - 1 := by
        have hnum : 0 ≤ Real.log (1 + β / (2 * Real.log 2)) :=
          Real.log_nonneg (by linarith)
        have hClog1 : Clog - 1 = Real.log (1 + β / (2 * Real.log 2)) / Real.log 2 := by
          rw [hClogdef]; ring
        rw [hClog1]; exact div_nonneg hnum hlog2pos.le
      have hlogt : Real.log 2 ≤ Real.log (t + 2) := Real.log_le_log (by norm_num) (by linarith)
      have hClog_eq : Real.log (1 + β / (2 * Real.log 2)) = (Clog - 1) * Real.log 2 := by
        have hClog1 : Clog - 1 = Real.log (1 + β / (2 * Real.log 2)) / Real.log 2 := by
          rw [hClogdef]; ring
        rw [hClog1]; field_simp
      calc Real.log (‖gam β t‖ + 2)
          ≤ Real.log (t + 2) + Real.log (1 + β / (2 * Real.log 2)) := le_trans hstep1' hstep3
        _ = Real.log (t + 2) + (Clog - 1) * Real.log 2 := by rw [hClog_eq]
        _ ≤ Real.log (t + 2) + (Clog - 1) * Real.log (t + 2) := by
              have := mul_le_mul_of_nonneg_left hlogt hClog1nn
              linarith
        _ = Clog * Real.log (t + 2) := by ring
    have hlog_pow : (Real.log (‖gam β t‖ + 2)) ^ B ≤ (Clog * Real.log (t + 2)) ^ B :=
      Real.rpow_le_rpow (Real.log_nonneg (by linarith [norm_nonneg (gam β t)])) hClog_bound hB
    have hlog_pow2 : (Clog * Real.log (t + 2)) ^ B = Clog ^ B * (Real.log (t + 2)) ^ B :=
      Real.mul_rpow hClogpos.le (Real.log_nonneg (by linarith))
    have hmiddle : (1 / ‖gam β t‖ ^ A) * (Real.log (‖gam β t‖ + 2)) ^ B * ‖gamDot β t‖
        ≤ (c ^ (-A) / (t + β) ^ A) * (Clog ^ B * (Real.log (t + 2)) ^ B)
            * (β / (2 * (Real.log 2) ^ 2) + 1) := by
      refine mul_le_mul ?_ (gamDot_norm_le hβ t) (norm_nonneg _) ?_
      · refine mul_le_mul hstep1 ?_ (Real.rpow_nonneg (Real.log_nonneg (by linarith [norm_nonneg (gam β t)])) B) ?_
        · exact hlog_pow.trans (le_of_eq hlog_pow2)
        · exact div_nonneg (Real.rpow_nonneg hcpos.le _) (Real.rpow_nonneg (by linarith) _)
      · exact mul_nonneg (div_nonneg (Real.rpow_nonneg hcpos.le _) (Real.rpow_nonneg (by linarith) _))
          (mul_nonneg (Real.rpow_nonneg hClogpos.le B) (Real.rpow_nonneg (Real.log_nonneg (by linarith)) B))
    calc (1 / ‖gam β t‖ ^ A) * (Real.log (‖gam β t‖ + 2)) ^ B * ‖gamDot β t‖
        ≤ (c ^ (-A) / (t + β) ^ A) * (Clog ^ B * (Real.log (t + 2)) ^ B)
            * (β / (2 * (Real.log 2) ^ 2) + 1) := hmiddle
      _ = (c ^ (-A) * Clog ^ B * (β / (2 * (Real.log 2) ^ 2) + 1))
            * (Real.log (t + 2)) ^ B / (t + β) ^ A := by ring


/-! ## Evenness of the integrand -/

lemma gam0_integrand_even (A B β R : ℝ) (hR : 0 < R) (t : ℝ) :
    ‖(R : ℂ) ^ (gam β (-t))‖ / ‖gam β (-t)‖ ^ A
        * (Real.log (‖gam β (-t)‖ + 2)) ^ B * ‖gamDot β (-t)‖
      = ‖(R : ℂ) ^ (gam β t)‖ / ‖gam β t‖ ^ A
        * (Real.log (‖gam β t‖ + 2)) ^ B * ‖gamDot β t‖ := by
  rw [norm_cpow_gam_neg β R t hR, gam_norm_neg, gamDot_norm_neg]

/-! ## Integrability of the model integrand -/

lemma gam0_log_pow_le_const_mul_rpow (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → (Real.log x) ^ B ≤ K * x ^ ε := by
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    rw [← hB0, Real.rpow_zero, one_mul]
    exact Real.one_le_rpow hx hε.le
  · have hεB : 0 < ε / B := div_pos hε hBpos
    refine ⟨(B / ε) ^ B, Real.rpow_pos_of_pos (div_pos hBpos hε) B, fun x hx => ?_⟩
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hlog : Real.log x ≤ x ^ (ε / B) / (ε / B) := Real.log_le_rpow_div hx0.le hεB
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
    have h1 : (Real.log x) ^ B ≤ (x ^ (ε / B) / (ε / B)) ^ B :=
      Real.rpow_le_rpow hlog0 hlog hBpos.le
    have h2 : (x ^ (ε / B) / (ε / B)) ^ B = x ^ ε * (B / ε) ^ B := by
      rw [Real.div_rpow (le_of_lt (Real.rpow_pos_of_pos hx0 _)) (le_of_lt hεB)]
      rw [← Real.rpow_mul (le_of_lt hx0)]
      rw [show ε / B * B = ε by field_simp]
      rw [show ε / B = (B / ε)⁻¹ by field_simp]
      rw [Real.inv_rpow (le_of_lt (div_pos hBpos hε))]
      rw [div_inv_eq_mul]
    rw [h2] at h1
    linarith [h1]

lemma gam0_integrableOn_rpow_shift (s : ℝ) (hs : 1 < s) :
    IntegrableOn (fun t : ℝ => (t + 2) ^ (-s)) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => (t + 2) ^ (-s)) (Set.Ioi 0) := by
    refine ContinuousOn.rpow ((continuous_id.add continuous_const).continuousOn) continuousOn_const ?_
    intro x hx
    exact Or.inl (by have := Set.mem_Ioi.mp hx; linarith : x + 2 ≠ 0)
  have h1 : IntegrableOn (fun t : ℝ => (t + 2) ^ (-s)) (Set.Icc 0 1) := by
    refine ContinuousOn.integrableOn_Icc ?_
    refine ContinuousOn.rpow ((continuous_id.add continuous_const).continuousOn) continuousOn_const ?_
    intro x hx
    exact Or.inl (by have := hx.1; linarith : x + 2 ≠ 0)
  have h2 : IntegrableOn (fun t : ℝ => (t + 2) ^ (-s)) (Set.Ioi 1) := by
    have hbase : IntegrableOn (fun t : ℝ => t ^ (-s)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
    refine Integrable.mono' hbase ?_ ?_
    · exact (hcont.mono (by intro x hx; exact lt_trans zero_lt_one (Set.mem_Ioi.mp hx))).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := ht
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith : -s ≤ 0)
  have hset : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext x; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h, _⟩ | h); exacts [h, lt_trans zero_lt_one h]
    · intro h
      by_cases h1 : x ≤ 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
  rw [← hset]
  exact IntegrableOn.union (h1.mono_set (by intro x hx; exact ⟨le_of_lt hx.1, hx.2⟩)) h2

lemma gam0_integrableOn_exp_neg_log_div_log_pow (A B β L : ℝ) (hA : 1 < A) (hB : 0 ≤ B)
    (hβ : 0 < β) (hL : 0 ≤ L) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-(β * L) / Real.log (t + 2)) * (Real.log (t + 2)) ^ B / (t + β) ^ A)
      (Set.Ioi 0) := by
  have hε : 0 < (A - 1) / 2 := by linarith
  obtain ⟨Klog, hKlogpos, hKlog⟩ := gam0_log_pow_le_const_mul_rpow B ((A - 1) / 2) hB hε
  have hA0 : 0 ≤ A := by linarith
  set Cp : ℝ := max 1 (2 / β) with hCp
  have hCppos : 0 < Cp := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hle_Cp : ∀ t : ℝ, 0 ≤ t → t + 2 ≤ Cp * (t + β) := by
    intro t ht
    have h1 : (1:ℝ) ≤ Cp := le_max_left _ _
    have h2 : 2 / β ≤ Cp := le_max_right _ _
    have h3 : 2 ≤ Cp * β := by
      have h4 := mul_le_mul_of_nonneg_right h2 hβ.le
      rwa [div_mul_cancel₀ 2 (ne_of_gt hβ)] at h4
    nlinarith
  have hbase : IntegrableOn (fun t : ℝ => (t + 2) ^ (-(A + 1) / 2)) (Set.Ioi 0) := by
    have h := gam0_integrableOn_rpow_shift ((A + 1) / 2) (by linarith)
    simpa only [neg_div] using h
  have hmaj : Integrable (fun t : ℝ => Klog * Cp ^ A * (t + 2) ^ (-(A + 1) / 2))
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    simpa [smul_eq_mul] using hbase.const_mul (Klog * Cp ^ A)
  refine Integrable.mono' hmaj ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hlin2 : ContinuousOn (fun t : ℝ => t + 2) (Set.Ioi 0) :=
      (continuous_id.add continuous_const).continuousOn
    have hlinβ : ContinuousOn (fun t : ℝ => t + β) (Set.Ioi 0) :=
      (continuous_id.add continuous_const).continuousOn
    have hlog : ContinuousOn (fun t : ℝ => Real.log (t + 2)) (Set.Ioi 0) :=
      hlin2.log (fun t ht => ne_of_gt (by have := Set.mem_Ioi.mp ht; linarith))
    have hlogpos : ∀ t ∈ Set.Ioi (0:ℝ), 0 < Real.log (t + 2) :=
      fun t ht => Real.log_pos (by have := Set.mem_Ioi.mp ht; linarith)
    have hexp : ContinuousOn (fun t : ℝ => Real.exp (-(β * L) / Real.log (t + 2))) (Set.Ioi 0) :=
      Real.continuous_exp.comp_continuousOn
        (continuousOn_const.div hlog (fun t ht => ne_of_gt (hlogpos t ht)))
    have hlogpow : ContinuousOn (fun t : ℝ => (Real.log (t + 2)) ^ B) (Set.Ioi 0) :=
      hlog.rpow continuousOn_const (fun t ht => Or.inl (ne_of_gt (hlogpos t ht)))
    have hden : ContinuousOn (fun t : ℝ => (t + β) ^ A) (Set.Ioi 0) :=
      hlinβ.rpow continuousOn_const
        (fun t ht => Or.inl (ne_of_gt (by have := Set.mem_Ioi.mp ht; linarith)))
    exact (hexp.mul hlogpow).div hden
      (fun t ht => ne_of_gt (Real.rpow_pos_of_pos (by have := Set.mem_Ioi.mp ht; linarith) A))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hlogpos : 0 < Real.log (t + 2) := Real.log_pos (by linarith)
    have hgnn : 0 ≤ Real.exp (-(β * L) / Real.log (t + 2)) * (Real.log (t + 2)) ^ B / (t + β) ^ A :=
      div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hlogpos.le B))
        (Real.rpow_nonneg (by linarith) A)
    rw [Real.norm_eq_abs, abs_of_nonneg hgnn]
    have hexp_le : Real.exp (-(β * L) / Real.log (t + 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      exact neg_nonpos.mpr (div_nonneg (mul_nonneg hβ.le hL) hlogpos.le)
    have hKl : (Real.log (t + 2)) ^ B ≤ Klog * (t + 2) ^ ((A - 1) / 2) :=
      hKlog (t + 2) (by linarith)
    have hden_le : 1 / (t + β) ^ A ≤ Cp ^ A * (t + 2) ^ (-A) := by
      have h1 : t + 2 ≤ Cp * (t + β) := hle_Cp t (le_of_lt ht0)
      have h2 : (t + 2) ^ A ≤ (Cp * (t + β)) ^ A :=
        Real.rpow_le_rpow (by linarith) h1 hA0
      rw [Real.mul_rpow hCppos.le (by linarith : (0:ℝ) ≤ t + β)] at h2
      have h3 : (t + 2) ^ A / Cp ^ A ≤ (t + β) ^ A := by
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hCppos A)]
        linarith
      calc 1 / (t + β) ^ A ≤ 1 / ((t + 2) ^ A / Cp ^ A) :=
            one_div_le_one_div_of_le (by positivity) h3
        _ = Cp ^ A * (t + 2) ^ (-A) := by
              rw [one_div_div, Real.rpow_neg (by linarith : (0:ℝ) ≤ t + 2), div_eq_mul_inv]
    have h2 : (Real.log (t + 2)) ^ B * (1 / (t + β) ^ A)
        ≤ (Klog * (t + 2) ^ ((A - 1) / 2)) * (Cp ^ A * (t + 2) ^ (-A)) :=
      mul_le_mul hKl hden_le (by positivity) (by positivity)
    have h3 : (Klog * (t + 2) ^ ((A - 1) / 2)) * (Cp ^ A * (t + 2) ^ (-A))
        = Klog * Cp ^ A * (t + 2) ^ (-(A + 1) / 2) := by
      have hXY : (t + 2) ^ ((A - 1) / 2) * (t + 2) ^ (-A) = (t + 2) ^ (-(A + 1) / 2) := by
        rw [← Real.rpow_add (by linarith)]
        congr 1
        ring
      rw [← hXY]
      ring
    calc Real.exp (-(β * L) / Real.log (t + 2)) * (Real.log (t + 2)) ^ B / (t + β) ^ A
        = Real.exp (-(β * L) / Real.log (t + 2)) * ((Real.log (t + 2)) ^ B * (1 / (t + β) ^ A)) := by
          ring
      _ ≤ 1 * ((Klog * (t + 2) ^ ((A - 1) / 2)) * (Cp ^ A * (t + 2) ^ (-A))) :=
          mul_le_mul hexp_le h2 (by positivity) (by norm_num)
      _ = Klog * Cp ^ A * (t + 2) ^ (-(A + 1) / 2) := by rw [one_mul]; exact h3



/-- The `Γ₀` contour integral bound. -/
theorem gam0_contour_integral_le (A B β : ℝ) (hA : 1 < A) (hB : 0 ≤ B) (hβ : 0 < β) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ R : ℝ, 8 ≤ R →
      (∫ t : ℝ, ‖(R : ℂ) ^ (Commons.Analysis.Complex.gam β t)‖
          / ‖Commons.Analysis.Complex.gam β t‖ ^ A
          * (Real.log (‖Commons.Analysis.Complex.gam β t‖ + 2)) ^ B
          * ‖Commons.Analysis.Complex.gamDot β t‖)
        ≤ C * Real.exp (-(δ * Real.sqrt (Real.log R))) := by
  obtain ⟨δ, C₁, hδpos, hC₁pos, hC₁⟩ :=
    exp_neg_log_div_log_pow_integral_le A B β hA hB hβ
  obtain ⟨C₀, hC₀pos, hC₀⟩ := gam0_integrand_pointwise_le hA hB hβ
  refine ⟨δ, 2 * C₀ * C₁, hδpos, by positivity, ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  have hlogR2 : 2 ≤ Real.log R := by
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have hle := Real.log_le_log (by norm_num : (0:ℝ) < 8) hR
    rw [h8] at hle
    nlinarith [Real.log_two_gt_d9]
  let f : ℝ → ℝ := fun t => ‖(R : ℂ) ^ (gam β t)‖ / ‖gam β t‖ ^ A
      * (Real.log (‖gam β t‖ + 2)) ^ B * ‖gamDot β t‖
  let g : ℝ → ℝ := fun t => Real.exp (-(β * Real.log R) / Real.log (t + 2))
      * (Real.log (t + 2)) ^ B / (t + β) ^ A
  change (∫ t : ℝ, f t) ≤ (2 * C₀ * C₁) * Real.exp (-(δ * Real.sqrt (Real.log R)))
  have hf_even : ∀ t, f (-t) = f t := fun t => gam0_integrand_even A B β R hRpos t
  have hstep1 : (∫ t : ℝ, f t) = 2 * ∫ t in Set.Ioi (0:ℝ), f t := by
    have hcongr : (∫ t : ℝ, f t) = ∫ t : ℝ, f |t| := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      show f t = f |t|
      rcases le_or_gt 0 t with ht | ht
      · rw [abs_of_nonneg ht]
      · rw [abs_of_neg ht, hf_even t]
    rw [hcongr, integral_comp_abs]
  have hpt : ∀ t ∈ Set.Ioi (0:ℝ), f t ≤ C₀ * g t := by
    intro t ht
    have ht0 : 0 < t := ht
    have hN : ‖(R : ℂ) ^ (gam β t)‖ = Real.exp (-(β * Real.log R) / Real.log (t + 2)) := by
      rw [norm_cpow_gam_eq hRpos t, abs_of_pos ht0]
    have hP := hC₀ t (le_of_lt ht0)
    have hf_eq : f t = Real.exp (-(β * Real.log R) / Real.log (t + 2))
        * ((1 / ‖gam β t‖ ^ A) * (Real.log (‖gam β t‖ + 2)) ^ B * ‖gamDot β t‖) := by
      show ‖(R : ℂ) ^ (gam β t)‖ / ‖gam β t‖ ^ A
          * (Real.log (‖gam β t‖ + 2)) ^ B * ‖gamDot β t‖ = _
      rw [hN]; ring
    have hg_eq : C₀ * g t = Real.exp (-(β * Real.log R) / Real.log (t + 2))
        * (C₀ * (Real.log (t + 2)) ^ B / (t + β) ^ A) := by
      show C₀ * (Real.exp (-(β * Real.log R) / Real.log (t + 2))
          * (Real.log (t + 2)) ^ B / (t + β) ^ A) = _
      ring
    rw [hf_eq, hg_eq]
    exact mul_le_mul_of_nonneg_left hP (Real.exp_nonneg _)
  have hf_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    show 0 ≤ ‖(R : ℂ) ^ (gam β t)‖ / ‖gam β t‖ ^ A
        * (Real.log (‖gam β t‖ + 2)) ^ B * ‖gamDot β t‖
    exact mul_nonneg (mul_nonneg (div_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) A))
      (Real.rpow_nonneg (Real.log_nonneg (by linarith [norm_nonneg (gam β t)])) B)) (norm_nonneg _)
  have hgint : Integrable g (volume.restrict (Set.Ioi (0:ℝ))) := by
    show Integrable (fun t : ℝ => Real.exp (-(β * Real.log R) / Real.log (t + 2))
      * (Real.log (t + 2)) ^ B / (t + β) ^ A) (volume.restrict (Set.Ioi 0))
    exact gam0_integrableOn_exp_neg_log_div_log_pow A B β (Real.log R) hA hB hβ (by linarith)
  have hgi : Integrable (fun t => C₀ * g t) (volume.restrict (Set.Ioi (0:ℝ))) :=
    hgint.const_mul C₀
  have hle_ae : f ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] (fun t => C₀ * g t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpt t ht
  have hstep2 : ∫ t in Set.Ioi (0:ℝ), f t ≤ C₀ * ∫ t in Set.Ioi (0:ℝ), g t := by
    have h := MeasureTheory.integral_mono_of_nonneg hf_nn hgi hle_ae
    rwa [MeasureTheory.integral_const_mul] at h
  have hstep3 : ∫ t in Set.Ioi (0:ℝ), g t ≤ C₁ * Real.exp (-(δ * Real.sqrt (Real.log R))) := by
    show ∫ t in Set.Ioi (0:ℝ), Real.exp (-(β * Real.log R) / Real.log (t + 2))
      * (Real.log (t + 2)) ^ B / (t + β) ^ A ≤ _
    rw [← integral_Ici_eq_integral_Ioi]
    exact hC₁ (Real.log R) hlogR2
  calc (∫ t : ℝ, f t) = 2 * ∫ t in Set.Ioi (0:ℝ), f t := hstep1
    _ ≤ 2 * (C₀ * ∫ t in Set.Ioi (0:ℝ), g t) := mul_le_mul_of_nonneg_left hstep2 (by norm_num)
    _ ≤ 2 * (C₀ * (C₁ * Real.exp (-(δ * Real.sqrt (Real.log R))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep3 hC₀pos.le) (by norm_num)
    _ = (2 * C₀ * C₁) * Real.exp (-(δ * Real.sqrt (Real.log R))) := by ring


end Commons.Analysis.Integral
