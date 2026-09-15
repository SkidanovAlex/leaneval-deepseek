import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set

namespace Commons.Analysis.Integral

/-!
# Integrability of `g · P` when `‖g‖` grows logarithmically and `‖P‖` is dominated by a Lorentzian

If `‖g t‖ ≤ C * (log (2 + |t|) + 1)` and `‖P t‖ ≤ K / (a^2 + (t - b)^2)` with `a > 0`, `C, K ≥ 0`,
then `t ↦ g t * P t` is integrable: the logarithmic growth is beaten by the quadratic decay, and
the dominating function is a constant multiple of `(1 + (t-b)^2)^{-3/4}`.

The auxiliary lemmas `integrable_one_add_sq_rpow_neg` (integrability of `(1+t^2)^{-c}` for `c > 1/2`)
and `log_two_add_abs_le` (a global logarithmic bound) are general and reusable.
-/


lemma integrable_one_add_sq_rpow_neg (c : ℝ) (hc : (1:ℝ)/2 < c) :
    Integrable (fun s : ℝ => (1 + s ^ 2) ^ (-c)) volume := by
  set F : ℝ → ℝ := fun s => (1 + s ^ 2) ^ (-c) with hF
  have hcont : Continuous F := by
    rw [hF]
    refine Continuous.rpow_const (continuous_const.add (continuous_id.pow 2)) ?_
    intro x; left; positivity
  have hnonneg : ∀ x, 0 ≤ F x := fun x => Real.rpow_nonneg (by positivity) _
  have hIoi : IntegrableOn F (Ioi 1) volume := by
    have hg : IntegrableOn (fun s : ℝ => s ^ (-(2*c))) (Ioi 1) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine Integrable.mono' hg (hcont.aestronglyMeasurable.restrict) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Real.norm_of_nonneg (hnonneg x)]
    have hx1 : (0:ℝ) < x := lt_trans zero_lt_one hx
    have hle : (1 + x^2) ^ (-c) ≤ (x^2) ^ (-c) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg x]) (by linarith)
    calc (1 + x^2) ^ (-c) ≤ (x^2)^(-c) := hle
      _ = x ^ (-(2*c)) := by
            rw [← Real.rpow_natCast_mul hx1.le 2 (-c)]
            congr 1; ring
  have hIio : IntegrableOn F (Iio (-1)) volume := by
    have h := hIoi.comp_neg
    have hset : -Ioi (1:ℝ) = Iio (-1) := by ext x; simp
    rw [hset] at h
    refine h.congr_fun_ae ?_
    filter_upwards with x
    simp only [hF, neg_sq]
  have hmid : IntegrableOn F (Icc (-1) 1) volume := by
    refine IntegrableOn.of_bound ?_ (hcont.aestronglyMeasurable.restrict) 1 ?_
    · rw [Real.volume_Icc]; norm_num
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_of_nonneg (hnonneg x), hF]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg x]) (by linarith)
  have hcover : (Ioi 1 ∪ (Iio (-1) ∪ Icc (-1) 1) : Set ℝ) = univ := by
    ext x
    simp only [mem_union, mem_Ioi, mem_Iio, mem_Icc, mem_univ, iff_true]
    rcases lt_or_ge x (-1) with h | h
    · right; left; exact h
    · rcases lt_or_ge x 1 with h2 | h2
      · right; right; exact ⟨h, le_of_lt h2⟩
      · rcases lt_or_eq_of_le h2 with h3 | h3
        · left; exact h3
        · right; right; exact ⟨h, by linarith [h3]⟩
  have hall : IntegrableOn F ((Ioi 1) ∪ ((Iio (-1)) ∪ (Icc (-1) 1))) volume :=
    hIoi.union (hIio.union hmid)
  refine integrableOn_univ.mp ?_
  exact Eq.mp (congrArg (fun U : Set ℝ => IntegrableOn F U volume) hcover) hall

lemma log_two_add_abs_le (b t : ℝ) :
    Real.log (2 + |t|) + 1 ≤ (Real.log (3 + |b|) + 3) * (1 + (t - b) ^ 2) ^ ((1:ℝ)/4) := by
  set s := t - b with hs
  set u := (1 + s ^ 2) ^ ((1:ℝ)/4) with hu
  have hu1 : 1 ≤ u := by
    rw [hu]
    exact Real.one_le_rpow (by nlinarith [sq_nonneg s]) (by norm_num)
  have hupos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hu2 : u ^ 2 = Real.sqrt (1 + s ^ 2) := by
    rw [hu, ← Real.rpow_natCast ((1 + s^2) ^ ((1:ℝ)/4)) 2,
        ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1 + s^2)]
    rw [show ((1:ℝ)/4) * ((2:ℕ):ℝ) = 1/2 by norm_num, Real.sqrt_eq_rpow]
  have hsabs : |s| ≤ u ^ 2 := by
    rw [hu2, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg s])
  have ht_abs : |t| ≤ |b| + u ^ 2 := by
    have htb : t = b + s := by rw [hs]; ring
    rw [htb]
    calc |b + s| ≤ |b| + |s| := abs_add_le b s
      _ ≤ |b| + u ^ 2 := by linarith [hsabs]
  have hnum : (2:ℝ) + |t| ≤ (3 + |b|) * u ^ 2 := by
    have hu2ge1 : 1 ≤ u ^ 2 := by nlinarith [hu1]
    have key : 0 ≤ (2 + |b|) * (u ^ 2 - 1) := mul_nonneg (by positivity) (by linarith)
    nlinarith [ht_abs, key]
  have hlogbound : Real.log (2 + |t|) ≤ Real.log (3 + |b|) + 2 * Real.log u := by
    have h1 : Real.log (2 + |t|) ≤ Real.log ((3 + |b|) * u^2) :=
      Real.log_le_log (by positivity) hnum
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    rw [Real.log_pow] at h1
    simpa using h1
  have hlogu : Real.log u ≤ u := Real.log_le_self hupos.le
  have hfinal : Real.log (3 + |b|) + 2 * Real.log u + 1 ≤ (Real.log (3 + |b|) + 3) * u := by
    have hlog3 : 0 ≤ Real.log (3 + |b|) := Real.log_nonneg (by linarith [abs_nonneg b])
    have key2 : 0 ≤ (Real.log (3 + |b|) + 1) * (u - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hlogu, key2]
  calc Real.log (2 + |t|) + 1 ≤ Real.log (3 + |b|) + 2 * Real.log u + 1 := by linarith
    _ ≤ (Real.log (3 + |b|) + 3) * u := hfinal
    _ = (Real.log (3 + |b|) + 3) * (1 + (t - b) ^ 2) ^ ((1:ℝ)/4) := by rw [hu, hs]

theorem integrable_of_log_le_lorentz {g P : ℝ → ℂ} {a b C K : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => g t * P t) MeasureTheory.volume)
    (hb : ∀ t : ℝ, ‖g t‖ ≤ C * (Real.log (2 + |t|) + 1))
    (hP : ∀ t : ℝ, ‖P t‖ ≤ K / (a ^ 2 + (t - b) ^ 2)) :
    MeasureTheory.Integrable (fun t : ℝ => g t * P t) MeasureTheory.volume := by
  set M : ℝ := Real.log (3 + |b|) + 3 with hM
  set D : ℝ := C * K * M * (min (a^2) 1)⁻¹ with hD
  have hMnn : 0 ≤ M := by
    rw [hM]
    have : 0 ≤ Real.log (3 + |b|) := Real.log_nonneg (by linarith [abs_nonneg b])
    linarith
  have hminpos : 0 < min (a^2) 1 := lt_min (by positivity) one_pos
  have hCKnn : 0 ≤ C * K := mul_nonneg hC hK
  have hDnn : 0 ≤ D := by
    rw [hD]
    exact mul_nonneg (mul_nonneg hCKnn hMnn) (inv_nonneg.mpr hminpos.le)
  have hdom : Integrable (fun t : ℝ => D * (1 + (t - b) ^ 2) ^ (-((3:ℝ)/4))) volume := by
    have hbase : Integrable (fun t : ℝ => (1 + (t - b) ^ 2) ^ (-((3:ℝ)/4))) volume := by
      have h := (integrable_one_add_sq_rpow_neg ((3:ℝ)/4) (by norm_num)).comp_sub_right b
      simpa using h
    simpa using hbase.const_mul D
  refine Integrable.mono' hdom hmeas ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  have hinvnn : 0 ≤ (a^2 + (t-b)^2)⁻¹ := by positivity
  have hposD : 0 < a^2 + (t-b)^2 := by positivity
  -- log bound
  have hlogt : Real.log (2 + |t|) + 1 ≤ M * (1 + (t-b)^2) ^ ((1:ℝ)/4) := by
    rw [hM]
    exact log_two_add_abs_le b t
  have hlog0 : 0 ≤ Real.log (2 + |t|) + 1 := by
    have : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  -- basic product bound
  have hPt : ‖P t‖ ≤ K * (a^2 + (t-b)^2)⁻¹ := by
    have := hP t
    rw [div_eq_mul_inv] at this
    exact this
  have hstep1 : ‖g t‖ * ‖P t‖ ≤ (C*(Real.log (2+|t|)+1)) * (K*(a^2+(t-b)^2)⁻¹) :=
    mul_le_mul (hb t) hPt (norm_nonneg _) (mul_nonneg hC hlog0)
  -- logarithm factor
  have hprod : (Real.log (2+|t|)+1) * (a^2+(t-b)^2)⁻¹
      ≤ M * ((1+(t-b)^2)^((1:ℝ)/4) * (a^2+(t-b)^2)⁻¹) := by
    calc (Real.log (2+|t|)+1) * (a^2+(t-b)^2)⁻¹
        ≤ (M * (1+(t-b)^2)^((1:ℝ)/4)) * (a^2+(t-b)^2)⁻¹ :=
          mul_le_mul_of_nonneg_right hlogt hinvnn
      _ = M * ((1+(t-b)^2)^((1:ℝ)/4) * (a^2+(t-b)^2)⁻¹) := by ring
  have hbig : (C*(Real.log (2+|t|)+1)) * (K*(a^2+(t-b)^2)⁻¹)
      ≤ C*K*(M * ((1+(t-b)^2)^((1:ℝ)/4) * (a^2+(t-b)^2)⁻¹)) := by
    calc (C*(Real.log (2+|t|)+1)) * (K*(a^2+(t-b)^2)⁻¹)
        = C*K*((Real.log (2+|t|)+1) * (a^2+(t-b)^2)⁻¹) := by ring
      _ ≤ C*K*(M * ((1+(t-b)^2)^((1:ℝ)/4) * (a^2+(t-b)^2)⁻¹)) :=
          mul_le_mul_of_nonneg_left hprod hCKnn
  -- denominator bound
  have hge : min (a^2) 1 * (1 + (t-b)^2) ≤ a^2 + (t-b)^2 := by
    rcases le_total (a^2) 1 with ha1 | ha1
    · rw [min_eq_left ha1]
      nlinarith [sq_nonneg (t-b), mul_le_mul_of_nonneg_right ha1 (sq_nonneg (t-b))]
    · rw [min_eq_right ha1]
      nlinarith [sq_nonneg (t-b)]
  have hinv : (a^2+(t-b)^2)⁻¹ ≤ (min (a^2) 1)⁻¹ * (1+(t-b)^2)⁻¹ := by
    have hxpos : 0 < min (a^2) 1 * (1 + (t-b)^2) := mul_pos hminpos (by positivity)
    have h1 := one_div_le_one_div_of_le hxpos hge
    simpa only [one_div, mul_inv] using h1
  have hdiv : (1+(t-b)^2)^((1:ℝ)/4) * (a^2+(t-b)^2)⁻¹
      ≤ (min (a^2) 1)⁻¹ * (1+(t-b)^2)^(-((3:ℝ)/4)) := by
    calc (1+(t-b)^2)^((1:ℝ)/4) * (a^2+(t-b)^2)⁻¹
        ≤ (1+(t-b)^2)^((1:ℝ)/4) * ((min (a^2) 1)⁻¹ * (1+(t-b)^2)⁻¹) :=
          mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg (by positivity) _)
      _ = (min (a^2) 1)⁻¹ * ((1+(t-b)^2)^((1:ℝ)/4) * (1+(t-b)^2)⁻¹) := by ring
      _ = (min (a^2) 1)⁻¹ * (1+(t-b)^2)^(-((3:ℝ)/4)) := by
          rw [← Real.rpow_neg_one (1+(t-b)^2),
              ← Real.rpow_add (by positivity : (0:ℝ) < 1 + (t-b)^2)]
          congr 1; norm_num
  have hfinal : C*K*(M * ((1+(t-b)^2)^((1:ℝ)/4) * (a^2+(t-b)^2)⁻¹))
      ≤ D * (1+(t-b)^2)^(-((3:ℝ)/4)) := by
    have hCKM : 0 ≤ C*K*M := mul_nonneg hCKnn hMnn
    rw [hD]
    calc C*K*(M * ((1+(t-b)^2)^((1:ℝ)/4) * (a^2+(t-b)^2)⁻¹))
        = C*K*M*((1+(t-b)^2)^((1:ℝ)/4) * (a^2+(t-b)^2)⁻¹) := by ring
      _ ≤ C*K*M*((min (a^2) 1)⁻¹ * (1+(t-b)^2)^(-((3:ℝ)/4))) :=
          mul_le_mul_of_nonneg_left hdiv hCKM
      _ = (C*K*M*(min (a^2) 1)⁻¹) * (1+(t-b)^2)^(-((3:ℝ)/4)) := by ring
  rw [norm_mul]
  exact hstep1.trans (hbig.trans hfinal)

end Commons.Analysis.Integral