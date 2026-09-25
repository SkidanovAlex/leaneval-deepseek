import Mathlib
import Submission.Commons.Analysis.Fourier.entropy_integral_le_of_sup_bound
import Submission.Commons.Analysis.Metric.coveringNumber_le_of_variation
import Submission.Commons.Analysis.Metric.coveringNumber_ne_top_of_isBounded
import Submission.Commons.Analysis.Fourier.maximal_dilation_convolution_l2
import Submission.Commons.Analysis.Fourier.lintegral_iSup_band_sum_dilation_le
import Submission.Commons.Analysis.Fourier.lintegral_iSup_pi_window_le
import Submission.Commons.Analysis.Fourier.dilation_variation_l2_sup
import Submission.Commons.Analysis.Fourier.dilation_variation_scalar_l2
import Submission.Commons.Analysis.Maximal.lintegral_rpow_hlMax_le

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

/-- The tuple sums of the logarithmically reparametrised curve are bounded by `winVar`. -/
lemma winVarVec_tuple_bound (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) {s : ℝ}
    (J : ℕ) (u : Fin (J + 1) → ℝ) (hu : StrictMono u) :
    ENNReal.ofReal ((∑ j : Fin J, dist (winCurveR Ψ f x (u (Fin.castSucc j)))
        (winCurveR Ψ f x (u (Fin.succ j))) ^ s) ^ ((1:ℝ)/s)) ≤ winVarVec Ψ f x s := by
  simp only [winCurveR, dist_eq_norm]
  refine le_iSup_of_le J (le_iSup_of_le (fun j => (⟨Real.exp (u j), Real.exp_pos _⟩ :
    {t : ℝ // 0 < t})) ?_)
  refine le_iSup_of_le ?_ le_rfl
  intro i j hij
  show (Real.exp (u i) : ℝ) < Real.exp (u j)
  exact Real.exp_lt_exp.mpr (hu hij)

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

/-- **The pointwise entropy-versus-variation bound** (Bourgain's Lemma 3.30). -/
lemma winM_mul_rpow_le (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) {s : ℝ} (hs : 1 ≤ s)
    (hΛ : winVarVec Ψ f x s < ⊤) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ t : {t : ℝ // 0 < t}, ‖winCurve Ψ f x t‖ ≤ R) :
    ∀ l : ℝ, 0 < l → ENNReal.ofReal l * (winM Ψ f x l) ^ ((1:ℝ)/s)
      ≤ ENNReal.ofReal ((2:ℝ) ^ ((1:ℝ)/s) * ((winVarVec Ψ f x s).toReal + 2 * R)) := by
  intro l hl
  rcases le_total l (2 * R) with h | h
  · have hfin : Metric.coveringNumber l.toNNReal (Set.range (winCurveR Ψ f x)) ≠ ⊤ := by
      refine Commons.Analysis.Metric.coveringNumber_ne_top_of_isBounded ?_ ?_
      · rw [isBounded_iff_subset_closedBall (0 : Fin K → ℂ)]
        refine ⟨R, ?_⟩
        rintro y ⟨u, rfl⟩
        rw [mem_closedBall, dist_zero_right]
        exact hR ⟨Real.exp u, Real.exp_pos u⟩
      · exact Real.toNNReal_pos.mpr hl
    · have hVreal : ∀ (J : ℕ) (u : Fin (J + 1) → ℝ), StrictMono u →
          (∑ j : Fin J, dist (winCurveR Ψ f x (u (Fin.castSucc j)))
              (winCurveR Ψ f x (u (Fin.succ j))) ^ s) ^ ((1:ℝ)/s)
            ≤ (winVarVec Ψ f x s).toReal := by
        intro J u hu
        have h1 := winVarVec_tuple_bound Ψ f x (s := s) J u hu
        have h2 := ENNReal.toReal_mono hΛ.ne h1
        rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg
          (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg dist_nonneg _) _)] at h2
      have hkey := Metric.coveringNumber_le_of_variation (winCurveR Ψ f x) s hs
        ((winVarVec Ψ f x s).toReal) hVreal hl hfin
      have hM : winM Ψ f x l = (((Metric.coveringNumber l.toNNReal
            (Set.range (winCurveR Ψ f x)) : ℕ∞) : ENNReal) - 1) := by
        rw [winM, range_winCurveR]
      rw [hM]
      refine le_trans hkey ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have h3 : (0:ℝ) < (2:ℝ) ^ ((1:ℝ)/s) := Real.rpow_pos_of_pos (by norm_num) _
      nlinarith [h, h3, (winVarVec Ψ f x s).toReal_nonneg]
  · have hzero : winM Ψ f x l = 0 := by
      rw [winM, tsub_eq_zero_iff_le]
      have hcov : Metric.coveringNumber l.toNNReal (Set.range (winCurve Ψ f x)) ≤ 1 := by
        refine Metric.coveringNumber_le_one_of_ediam_le ?_
        rw [ediam_le_iff]
        rintro p ⟨tp, rfl⟩ q ⟨tq, rfl⟩
        have hp : ‖winCurve Ψ f x tp‖ₑ ≤ ENNReal.ofReal R := by
          rw [enorm_eq_ofReal_norm']; exact ENNReal.ofReal_le_ofReal (hR tp)
        have hq : ‖winCurve Ψ f x tq‖ₑ ≤ ENNReal.ofReal R := by
          rw [enorm_eq_ofReal_norm']; exact ENNReal.ofReal_le_ofReal (hR tq)
        have h2R : (2:ℝ) * R = R + R := two_mul R
        rw [edist_eq_enorm_sub]
        calc ‖winCurve Ψ f x tp - winCurve Ψ f x tq‖ₑ
            = ‖winCurve Ψ f x tp + (- winCurve Ψ f x tq)‖ₑ := by rw [sub_eq_add_neg]
          _ ≤ ‖winCurve Ψ f x tp‖ₑ + ‖- winCurve Ψ f x tq‖ₑ := enorm_add_le _ _
          _ = ‖winCurve Ψ f x tp‖ₑ + ‖winCurve Ψ f x tq‖ₑ := by rw [enorm_neg]
          _ ≤ ENNReal.ofReal (2 * R) := by
              rw [h2R, ENNReal.ofReal_add hR0 hR0]; exact add_le_add hp hq
          _ ≤ ENNReal.ofReal l := by
              rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
              exact h
          _ = (l.toNNReal : ℝ≥0∞) := by
              rw [ENNReal.ofReal_eq_coe_nnreal hl.le, Real.toNNReal_of_nonneg hl.le]
      exact_mod_cast hcov
    rw [hzero, ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1/s), mul_zero]
    exact bot_le

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

theorem bourgain_entropy_integral_l2_fixed (Ψ : SchwartzMap ℝ ℂ) (M : ℝ)
    (hM : ∀ x : ℝ, ‖(Ψ : ℝ → ℂ) x‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (f : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MemLp (f k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K, MemLp (f k) ⊤ (volume : Measure ℝ)) →
      ∫⁻ x : ℝ, (∫⁻ r in Set.Ioi (0:ℝ),
          min (((Metric.coveringNumber r.toNNReal
                  (Set.range (fun t : {t : ℝ // 0 < t} => fun k : Fin K =>
                    ∫ y : ℝ, f k y * ((t:ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / (t:ℝ))))) : ℝ≥0∞) - 1) ^ (1/2:ℝ))
              (ENNReal.ofReal (Real.sqrt K))) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ)+2))^2)^2) *
            ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2) := by
  obtain ⟨Cv, hCvpos, hCv⟩ := dilation_variation_l2_sup Ψ
  obtain ⟨Cvs, hCvspos, hCvs⟩ := dilation_variation_scalar_l2 Ψ
  obtain ⟨C₁, hC₁pos, hC₁⟩ := maximal_dilation_convolution_enorm_le_hlMax Ψ
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.Analysis.Maximal.real_maximal_strong_type 2 (by norm_num)
  set C : ℝ := Real.sqrt (10 ^ 30 * (Cv ^ 2 + Cvs ^ 2 + (C₀ ^ 2 * C₁ ^ 2) ^ 2 + C₁ ^ 2 + 1))
    with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCsq : C ^ 2 = 10 ^ 30 * (Cv ^ 2 + Cvs ^ 2 + (C₀ ^ 2 * C₁ ^ 2) ^ 2 + C₁ ^ 2 + 1) := by
    rw [hCdef, Real.sq_sqrt (by positivity)]
  refine ⟨C, hCpos, ?_⟩
  intro K f hf2 hfinf
  set A : ENNReal := ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖ ^ 2) with hAdef
  set L : ℝ := max 1 (Real.log ((K:ℝ) + 2)) with hLdef
  set s : ℝ := 2 + 1/L with hsdef
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hs2 : 2 < s := by
    rw [hsdef]; exact lt_add_of_pos_right _ (one_div_pos.mpr hLpos)
  have hs3 : s ≤ 3 := by
    rw [hsdef, show (2:ℝ) + 1/L ≤ 3 ↔ 1/L ≤ 1 by constructor <;> intro h <;> linarith]
    rw [div_le_one hLpos]; exact hL1
  have hs1 : 1 ≤ s := by linarith
  have hsne : s - 2 = 1/L := by rw [hsdef]; ring
  have hKpow : (K:ℝ) ^ ((1:ℝ)/2 - 1/s) ≤ 2 := by
    rw [hsdef, hLdef]
    exact rpow_half_sub_inv_le_two K
  -- the measurable majorant of the sup of the curve
  set hh : ℝ → ENNReal := fun x => (∑ k : Fin K,
      (ENNReal.ofReal C₁ * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ))
      ^ ((1:ℝ)/2) with hhdef
  have hFle : ∀ x, winF Ψ f x ≤ hh x := by
    intro x
    have h1 : winF Ψ f x ≤ (⨆ (t : {t : ℝ // 0 < t}),
        (∑ k : Fin K, ‖winCurve Ψ f x t k‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) :=
      iSup_le fun t => (enorm_le_sqrt_sum (winCurve Ψ f x t)).trans
        (le_iSup (fun t : {t : ℝ // 0 < t} =>
          (∑ k : Fin K, ‖winCurve Ψ f x t k‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) t)
    refine h1.trans ?_
    rw [hhdef]
    refine iSup_le fun t => ?_
    refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun k _ => ?_) (by norm_num)
    exact ENNReal.rpow_le_rpow ((le_iSup (fun t : {t : ℝ // 0 < t} =>
      ‖winCurve Ψ f x t k‖ₑ) t).trans (hC₁ (f k) (hf2 k) x)) (by norm_num)
  have hhmeas : Measurable hh := by
    rw [hhdef]
    exact (ENNReal.continuous_rpow_const.measurable).comp
      (Finset.measurable_sum _ fun k _ =>
        (measurable_const.mul (Commons.Analysis.Maximal.measurable_hlMax _)).pow_const 2)
  have hb : ∀ k : Fin K, AEMeasurable
      (fun x => (ENNReal.ofReal C₁ * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ))
      volume := fun k => ((measurable_const.mul
        (Commons.Analysis.Maximal.measurable_hlMax _)).pow_const 2).aemeasurable
  have hAfin : A < ⊤ := by
    rw [hAdef]
    have hcongr : (fun x : ℝ => ENNReal.ofReal (∑ k : Fin K, ‖f k x‖ ^ 2))
        = fun x => ∑ k : Fin K, ENNReal.ofReal (‖f k x‖ ^ 2) := by
      funext x
      exact ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)
    rw [hcongr, lintegral_finsetSum' (Finset.univ)
      (f := fun k : Fin K => fun x : ℝ => ENNReal.ofReal (‖f k x‖ ^ 2))
      (fun k _ => ((hf2 k).aemeasurable.norm.pow_const 2).ennreal_ofReal)]
    refine ENNReal.sum_lt_top.mpr fun k _ => ?_
    have h1 : Integrable (fun x : ℝ => ‖f k x‖ ^ 2) volume := by
      have := (hf2 k).integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
      simpa using this
    have h2 := h1.lintegral_lt_top
    simpa only [enorm_eq_ofReal_norm'] using h2
  have hhfin : ∫⁻ x, hh x ^ (2:ℝ) ≤ ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * A := by
    have hpow : ∀ x : ℝ, hh x ^ (2:ℝ)
        = ∑ k : Fin K, (ENNReal.ofReal C₁ * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ) := by
      intro x
      rw [hhdef, ← ENNReal.rpow_mul, show ((1:ℝ)/2) * 2 = 1 by norm_num, ENNReal.rpow_one]
    have hstep : ∀ k : Fin K, ∫⁻ x, (ENNReal.ofReal C₁ *
          Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ)
        ≤ ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖f k x‖ ^ 2) := by
      intro k
      have hfac : (fun x : ℝ => (ENNReal.ofReal C₁ *
            Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ))
          = fun x => (ENNReal.ofReal C₁) ^ (2:ℝ) *
              (Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ) := by
        funext x; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [hfac, lintegral_const_mul'' _
        (((Commons.Analysis.Maximal.measurable_hlMax _).pow_const 2).aemeasurable)]
      rw [show (ENNReal.ofReal C₁) ^ (2:ℝ) = ENNReal.ofReal (C₁ ^ 2) by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
          ENNReal.ofReal_pow hC₁pos.le]]
      have h32 : ∫⁻ x : ℝ, (Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ)
          ≤ ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖f k x‖ ^ 2) := by
        have h := hC₀ (fun y : ℝ => ‖f k y‖)
        have h1 : (fun y : ℝ => ‖(fun y : ℝ => ‖f k y‖) y‖ₑ) = fun y => ‖f k y‖ₑ := by
          funext y; exact enorm_norm_eq_enorm (f k y)
        rw [h1] at h
        have h2 : (fun x : ℝ => ‖‖f k x‖‖ₑ ^ (2:ℝ)) = fun x => ENNReal.ofReal (‖f k x‖ ^ 2) := by
          funext x
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, enorm_norm_eq_enorm,
            enorm_eq_ofReal_norm', ENNReal.ofReal_pow (norm_nonneg _)]
        rw [h2] at h
        have hC : (C₀ : ℝ) ^ (2:ℝ) = C₀ ^ 2 := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        rw [hC] at h
        simpa only [Commons.Analysis.Maximal.hlMax] using h
      calc ENNReal.ofReal (C₁ ^ 2) * ∫⁻ x, (Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ)
          ≤ ENNReal.ofReal (C₁ ^ 2) * (ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖f k x‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h32 bot_le
        _ = ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖f k x‖ ^ 2) := by
            rw [ENNReal.ofReal_mul (sq_nonneg C₀)]
            ring
    calc ∫⁻ x, hh x ^ (2:ℝ)
        = ∑ k : Fin K, ∫⁻ x, (ENNReal.ofReal C₁ *
            Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ) := by
          rw [lintegral_congr fun x => hpow x, lintegral_finsetSum' Finset.univ (fun k _ => hb k)]
      _ ≤ ∑ k : Fin K, ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖f k x‖ ^ 2) :=
          Finset.sum_le_sum fun k _ => hstep k
      _ = ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * A := by
          rw [← Finset.mul_sum, hAdef]
          congr 1
          rw [← lintegral_finsetSum' Finset.univ
            (f := fun k : Fin K => fun x : ℝ => ENNReal.ofReal (‖f k x‖ ^ 2))
            (fun k _ => ((hf2 k).aemeasurable.norm.pow_const 2).ennreal_ofReal)]
          exact lintegral_congr fun x =>
            (ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)).symm
  have hhh2 : ∀ᵐ x ∂(volume : Measure ℝ), hh x ^ (2:ℝ) < ⊤ :=
    ae_lt_top (hhmeas.pow_const 2) (by
      refine ne_of_lt (lt_of_le_of_lt hhfin ?_)
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hAfin)
  have hhh : ∀ᵐ x ∂(volume : Measure ℝ), hh x < ⊤ := by
    filter_upwards [hhh2] with x hx
    by_contra h
    rw [not_lt] at h
    rw [top_le_iff.mp h, ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 2)] at hx
    exact lt_irrefl _ hx
  have hVtop : ∀ᵐ x ∂(volume : Measure ℝ), winVarVec Ψ f x s < ⊤ := by
    have hmeas : ∀ k : Fin K, AEMeasurable (fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)) volume :=
      fun k => (dilation_variation_aemeasurable Ψ s (f k) (hf2 k).aemeasurable (hf2 k)).pow_const 2
    have hsumfin : ∫⁻ x, ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) < ⊤ := by
      rw [lintegral_finsetSum' Finset.univ (fun k _ => hmeas k)]
      refine ENNReal.sum_lt_top.mpr fun k _ => ?_
      refine lt_of_le_of_lt (hCvs s hs2 hs3 (f k) (hf2 k) (hfinf k)) ?_
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
        have h1 : Integrable (fun x : ℝ => ‖f k x‖ ^ 2) volume := by
          have := (hf2 k).integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
          simpa using this
        have h2 := h1.lintegral_lt_top
        simpa only [enorm_eq_ofReal_norm'] using h2)
    have hmeas2 : AEMeasurable (fun x : ℝ => ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ)) volume := by
      have hsa : (∑ k : Fin K, (fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)))
          = fun x : ℝ => ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) := by
        funext x; exact Finset.sum_apply x Finset.univ _
      rw [← hsa]
      exact Finset.aemeasurable_sum Finset.univ
        (f := fun k : Fin K => fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)) (fun k _ => hmeas k)
    have htop := ae_lt_top' hmeas2 hsumfin.ne
    filter_upwards [htop] with x hx
    have h3 : winVarVec Ψ f x s ^ (2:ℝ) < ⊤ :=
      lt_of_le_of_lt (winVarVec_sq_le_sum Ψ f x hs2.le) hx
    by_contra h
    rw [not_lt] at h
    rw [top_le_iff.mp h, ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 2)] at h3
    exact lt_irrefl _ h3
  -- the pointwise entropy bound
  set Gc : ℝ → ℝ := fun x => (2:ℝ) ^ ((1:ℝ)/s)
    * ((winVarVec Ψ f x s).toReal + 2 * (hh x).toReal) with hGcdef
  set Lc : ℝ := (1 + 2/(s - 2)) * (K:ℝ) ^ ((1:ℝ)/2 - 1/s) with hLcdef
  have hsL0 : 1 / (s - 2) = L := by rw [hsne, one_div_one_div]
  have hLcpos : 0 ≤ Lc := by
    rw [hLcdef]
    have h2 : (0:ℝ) ≤ 1 + 2/(s-2) := by
      rw [show (2:ℝ)/(s-2) = 2*(1/(s-2)) by ring, hsL0]
      linarith [hL1]
    exact mul_nonneg h2 (Real.rpow_nonneg (by positivity) _)
  have hGcpos : ∀ x, 0 ≤ Gc x := by
    intro x
    rw [hGcdef]
    refine mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le ?_
    have h1 := (winVarVec Ψ f x s).toReal_nonneg
    have h2 := (hh x).toReal_nonneg
    linarith
  have hpw : ∀ᵐ x ∂(volume : Measure ℝ),
      (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt K)) (winM Ψ f x r ^ ((1:ℝ)/2)))
        ≤ ENNReal.ofReal (Lc * Gc x) := by
    filter_upwards [hVtop, hhh] with x hxV hxH
    have hR : ∀ t : {t : ℝ // 0 < t}, ‖winCurve Ψ f x t‖ ≤ (hh x).toReal := by
      intro t
      have h1 : ‖winCurve Ψ f x t‖ₑ ≤ hh x :=
        (le_iSup (fun t : {t : ℝ // 0 < t} => ‖winCurve Ψ f x t‖ₑ) t).trans (hFle x)
      rw [enorm_eq_ofReal_norm'] at h1
      have h2 := ENNReal.toReal_mono hxH.ne h1
      rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h2
    have this := entropy_integral_le_of_sup_bound (M := fun r => winM Ψ f x r) (K := (K:ℝ))
      (r := s) (G := Gc x) (by positivity) hs2 (by positivity : (0:ℝ) ≤ Gc x)
      (winM_mul_rpow_le Ψ f x hs1 hxV ENNReal.toReal_nonneg hR)
    simpa only [hLcdef] using this
  -- the two integral bounds
  have hVsum : ∀ᵐ x ∂(volume : Measure ℝ),
      ENNReal.ofReal ((winVarVec Ψ f x s).toReal ^ 2)
        ≤ ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) := by
    filter_upwards [hVtop] with x hxV
    have h1 : winVarVec Ψ f x s ^ (2:ℝ) ≤ ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) :=
      winVarVec_sq_le_sum Ψ f x hs2.le
    have h2 : ENNReal.ofReal ((winVarVec Ψ f x s).toReal ^ 2)
        = (ENNReal.ofReal (winVarVec Ψ f x s).toReal) ^ (2:ℝ) := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
        ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    rw [h2, ENNReal.ofReal_toReal hxV.ne]
    exact h1
  have hVint : ∫⁻ x, ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ)
      ≤ ENNReal.ofReal ((Cvs / (s - 2)) ^ 2) * A := by
    have hmeas : ∀ k : Fin K, AEMeasurable (fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)) volume :=
      fun k => (dilation_variation_aemeasurable Ψ s (f k) (hf2 k).aemeasurable (hf2 k)).pow_const 2
    have hsplit : ∫⁻ x, ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ)
        = ∑ k : Fin K, ∫⁻ x, winVar Ψ (f k) x s ^ (2:ℝ) := by
      simpa only [Finset.sum_apply] using lintegral_finsetSum' Finset.univ
        (f := fun k : Fin K => fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)) (fun k _ => hmeas k)
    have hAeq : A = ∑ k : Fin K, ∫⁻ x : ℝ, ENNReal.ofReal (‖f k x‖ ^ 2) := by
      rw [hAdef]
      rw [lintegral_congr fun x => ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
      simpa only [Finset.sum_apply] using lintegral_finsetSum' Finset.univ
        (f := fun k : Fin K => fun x : ℝ => ENNReal.ofReal (‖f k x‖ ^ 2))
        (fun k _ => ((hf2 k).aemeasurable.norm.pow_const 2).ennreal_ofReal)
    rw [hsplit, hAeq, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hCvs s hs2 hs3 (f k) (hf2 k) (hfinf k)
  have hRint : ∫⁻ x, ENNReal.ofReal ((hh x).toReal ^ 2) ≤ ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * A := by
    refine le_trans (lintegral_mono fun x => ?_) hhfin
    have h1 : ENNReal.ofReal ((hh x).toReal ^ 2)
        = (ENNReal.ofReal (hh x).toReal) ^ (2:ℝ) := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
        ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    rw [h1]
    exact ENNReal.rpow_le_rpow ENNReal.ofReal_toReal_le (by norm_num)
  -- final assembly
  have hsL : 1 / (s - 2) = L := by rw [hsne, one_div_one_div]
  have hLle : L ≤ 200 * Real.log ((K:ℝ)+2) := by rw [hLdef]; exact max_one_log_le K
  have hRmeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal ((hh x).toReal ^ 2)) volume :=
    (((hhmeas.ennreal_toReal).pow_const 2).ennreal_ofReal).aemeasurable
  have hsumMeas : AEMeasurable (fun x : ℝ => ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ)) volume := by
    have hsa : (∑ k : Fin K, (fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)))
        = fun x : ℝ => ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) := by
      funext x; exact Finset.sum_apply x Finset.univ _
    rw [← hsa]
    exact Finset.aemeasurable_sum Finset.univ
      (f := fun k : Fin K => fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)) (fun k _ =>
        (dilation_variation_aemeasurable Ψ s (f k) (hf2 k).aemeasurable (hf2 k)).pow_const 2)

  have hIntMeas : AEMeasurable (fun x : ℝ => 2 * (∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
      + 8 * ENNReal.ofReal ((hh x).toReal ^ 2)) volume :=
    (hsumMeas.const_mul 2).add (hRmeas.const_mul 8)
  have hG2 : ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (Gc x ^ 2)
      ≤ ENNReal.ofReal 2 * (2 * (∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
          + 8 * ENNReal.ofReal ((hh x).toReal ^ 2)) := by
    filter_upwards [hVsum, hVtop] with x hx hxV
    have hreal : ENNReal.ofReal (Gc x ^ 2)
        ≤ ENNReal.ofReal 2 * (2 * ENNReal.ofReal ((winVarVec Ψ f x s).toReal ^ 2)
            + 8 * ENNReal.ofReal ((hh x).toReal ^ 2)) := by
      rw [hGcdef]
      have hexp2 : ((2:ℝ) ^ ((1:ℝ)/s)) ^ 2 ≤ 2 := by
        have h1 : (2:ℝ) ^ ((1:ℝ)/s) ≤ Real.sqrt 2 := by
          rw [Real.sqrt_eq_rpow]
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          rw [div_le_iff₀ (by linarith : (0:ℝ) < s)]
          linarith
        calc ((2:ℝ) ^ ((1:ℝ)/s)) ^ 2 ≤ (Real.sqrt 2) ^ 2 :=
              pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) h1 2
          _ = 2 := Real.sq_sqrt (by norm_num)
      have hquad : ((winVarVec Ψ f x s).toReal + 2 * (hh x).toReal) ^ 2
          ≤ 2 * ((winVarVec Ψ f x s).toReal) ^ 2 + 8 * ((hh x).toReal) ^ 2 := by
        nlinarith [sq_nonneg ((winVarVec Ψ f x s).toReal - 2 * (hh x).toReal)]
      have hAnn : (0:ℝ) ≤ ((2:ℝ) ^ ((1:ℝ)/s)) ^ 2 := by positivity
      calc ENNReal.ofReal (((2:ℝ) ^ ((1:ℝ)/s) * ((winVarVec Ψ f x s).toReal + 2 * (hh x).toReal)) ^ 2)
          = ENNReal.ofReal (((2:ℝ) ^ ((1:ℝ)/s)) ^ 2
              * ((winVarVec Ψ f x s).toReal + 2 * (hh x).toReal) ^ 2) := by
            rw [mul_pow]
        _ ≤ ENNReal.ofReal (2 * (2 * ((winVarVec Ψ f x s).toReal) ^ 2 + 8 * ((hh x).toReal) ^ 2)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            exact mul_le_mul hexp2 hquad (by positivity) (by norm_num)
        _ = ENNReal.ofReal 2 * (2 * ENNReal.ofReal ((winVarVec Ψ f x s).toReal ^ 2)
              + 8 * ENNReal.ofReal ((hh x).toReal ^ 2)) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
              ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
              ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8)]
            norm_num
    refine hreal.trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num)) le_rfl) bot_le
    exact hx
  rw [show (fun x : ℝ => (∫⁻ r in Set.Ioi (0:ℝ),
        min (((Metric.coveringNumber r.toNNReal (Set.range (fun t : {t : ℝ // 0 < t} =>
          fun k : Fin K => ∫ y : ℝ, f k y * ((t:ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / (t:ℝ))))) : ℝ≥0∞) - 1)
          ^ (1/2:ℝ)) (ENNReal.ofReal (Real.sqrt K))) ^ (2:ℝ))
      = fun x : ℝ => (∫⁻ r in Set.Ioi (0:ℝ),
          min (ENNReal.ofReal (Real.sqrt K)) (winM Ψ f x r ^ ((1:ℝ)/2))) ^ (2:ℝ) from by
    funext x
    congr 1
    refine lintegral_congr fun r => ?_
    exact min_comm _ _]
  -- the numerical collapse of the constants
  have hfinal_cmp : ENNReal.ofReal (Lc^2) * ENNReal.ofReal (2:ℝ)
      * (2 * ENNReal.ofReal ((Cvs/(s-2))^2) + 8 * ENNReal.ofReal (C₀^2*C₁^2))
      ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ)+2))^2)^2) := by
    have hEq : ENNReal.ofReal (Lc^2) * ENNReal.ofReal (2:ℝ)
        * (2 * ENNReal.ofReal ((Cvs/(s-2))^2) + 8 * ENNReal.ofReal (C₀^2*C₁^2))
        = ENNReal.ofReal (Lc^2 * 2 * (2*(Cvs/(s-2))^2 + 8*(C₀^2*C₁^2))) := by
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by simp]
      rw [show (8:ℝ≥0∞) = ENNReal.ofReal (8:ℝ) by simp]
      rw [← ENNReal.ofReal_mul (sq_nonneg Lc),
          ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num),
          ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 8 by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
    have hReal : Lc^2 * 2 * (2*(Cvs/(s-2))^2 + 8*(C₀^2*C₁^2))
        ≤ (C * (Real.log ((K:ℝ)+2))^2)^2 := by
      have hb := final_const_bound K (s := s) (L := L) (A := Cvs) (B := C₀^2*C₁^2)
        hL1 hsne hLle hKpow (le_of_lt hCvspos) (by positivity)
      have hLc2 : Lc^2 = ((1 + 2/(s-2)) * (K:ℝ)^((1:ℝ)/2-1/s))^2 := by rw [hLcdef]
      have hCsq' : (C * (Real.log ((K:ℝ)+2))^2)^2
          = 10^30 * (Cv^2 + Cvs^2 + (C₀^2*C₁^2)^2 + C₁^2 + 1)
              * (Real.log ((K:ℝ)+2))^4 := by
        rw [mul_pow, hCsq]
        ring
      rw [hLc2, hCsq']
      refine hb.trans ?_
      calc 10^30 * (Cvs^2 + (C₀^2*C₁^2)^2 + 1) * (Real.log ((K:ℝ)+2))^4
          = (10^30 * (Real.log ((K:ℝ)+2))^4) * (Cvs^2 + (C₀^2*C₁^2)^2 + 1) := by ring
        _ ≤ (10^30 * (Real.log ((K:ℝ)+2))^4)
              * (Cv^2 + Cvs^2 + (C₀^2*C₁^2)^2 + C₁^2 + 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith [sq_nonneg Cv, sq_nonneg C₁]
        _ = 10^30 * (Cv^2 + Cvs^2 + (C₀^2*C₁^2)^2 + C₁^2 + 1)
              * (Real.log ((K:ℝ)+2))^4 := by ring
    exact hEq.le.trans (ENNReal.ofReal_le_ofReal hReal)
  -- the chain of integral estimates
  have h1 : ∫⁻ x, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt K))
        (winM Ψ f x r ^ ((1:ℝ)/2))) ^ (2:ℝ)
      ≤ ∫⁻ x, (ENNReal.ofReal (Lc * Gc x)) ^ (2:ℝ) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hpw] with x hx
    exact ENNReal.rpow_le_rpow hx (by norm_num)
  have h2 : ∫⁻ x, (ENNReal.ofReal (Lc * Gc x)) ^ (2:ℝ)
      = ENNReal.ofReal (Lc^2) * ∫⁻ x, ENNReal.ofReal ((Gc x)^2) := by
    have hp : ∀ x : ℝ, (ENNReal.ofReal (Lc * Gc x)) ^ (2:ℝ)
        = ENNReal.ofReal (Lc^2) * ENNReal.ofReal ((Gc x)^2) := by
      intro x
      calc (ENNReal.ofReal (Lc * Gc x)) ^ (2:ℝ)
          = ENNReal.ofReal ((Lc * Gc x) ^ (2:ℝ)) :=
            ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hLcpos (hGcpos x))
              (by norm_num : (0:ℝ) ≤ 2)
        _ = ENNReal.ofReal ((Lc * Gc x) ^ 2) := by rw [Real.rpow_two]
        _ = ENNReal.ofReal (Lc^2 * (Gc x)^2) := by rw [mul_pow]
        _ = ENNReal.ofReal (Lc^2) * ENNReal.ofReal ((Gc x)^2) :=
            ENNReal.ofReal_mul (sq_nonneg Lc)
    rw [lintegral_congr hp, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h3 : ∫⁻ x, ENNReal.ofReal ((Gc x)^2)
      ≤ ENNReal.ofReal (2:ℝ) * (2 * (∫⁻ x, ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
          + 8 * (∫⁻ x, ENNReal.ofReal ((hh x).toReal ^ 2))) := by
    calc ∫⁻ x, ENNReal.ofReal ((Gc x)^2)
        ≤ ∫⁻ x, ENNReal.ofReal (2:ℝ) * (2 * (∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
            + 8 * ENNReal.ofReal ((hh x).toReal ^ 2)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hG2] with x hx
          exact hx
      _ = ENNReal.ofReal (2:ℝ) * ∫⁻ x, (2 * (∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
            + 8 * ENNReal.ofReal ((hh x).toReal ^ 2)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (2:ℝ) * (2 * (∫⁻ x, ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
            + 8 * (∫⁻ x, ENNReal.ofReal ((hh x).toReal ^ 2))) := by
          congr 1
          rw [lintegral_add_left' (hsumMeas.const_mul 2),
            lintegral_const_mul' (2:ℝ≥0∞) _ (by norm_num : (2:ℝ≥0∞) ≠ ⊤),
            lintegral_const_mul' (8:ℝ≥0∞) _ (by norm_num : (8:ℝ≥0∞) ≠ ⊤)]
  have h4 : ENNReal.ofReal (2:ℝ) * (2 * (∫⁻ x, ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
          + 8 * (∫⁻ x, ENNReal.ofReal ((hh x).toReal ^ 2)))
      ≤ ENNReal.ofReal (2:ℝ) * (2 * (ENNReal.ofReal ((Cvs / (s-2))^2) * A)
          + 8 * (ENNReal.ofReal (C₀^2 * C₁^2) * A)) := by
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    refine add_le_add (mul_le_mul_of_nonneg_left hVint (by norm_num))
      (mul_le_mul_of_nonneg_left hRint (by norm_num))
  have h5 : ENNReal.ofReal (Lc^2) * (ENNReal.ofReal (2:ℝ)
        * (2 * (ENNReal.ofReal ((Cvs / (s-2))^2) * A)
          + 8 * (ENNReal.ofReal (C₀^2 * C₁^2) * A)))
      ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ)+2))^2)^2) * A := by
    rw [show ENNReal.ofReal (Lc^2) * (ENNReal.ofReal (2:ℝ)
          * (2 * (ENNReal.ofReal ((Cvs / (s-2))^2) * A)
            + 8 * (ENNReal.ofReal (C₀^2 * C₁^2) * A)))
        = (ENNReal.ofReal (Lc^2) * ENNReal.ofReal (2:ℝ)
            * (2 * ENNReal.ofReal ((Cvs/(s-2))^2) + 8 * ENNReal.ofReal (C₀^2*C₁^2))) * A
        from by ring]
    exact mul_le_mul_of_nonneg_right hfinal_cmp bot_le
  refine h1.trans ?_
  rw [h2]
  exact (mul_le_mul_of_nonneg_left (h3.trans h4) bot_le).trans h5

end Commons.Analysis.Fourier
