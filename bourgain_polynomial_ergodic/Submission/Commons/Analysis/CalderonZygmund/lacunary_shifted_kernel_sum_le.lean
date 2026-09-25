import Mathlib
import Submission.Commons.Analysis.Sum.lacunary_finset_card_le
import Submission.Commons.Analysis.Sum.lacunary_finset_sum_inv_le

/-!
# A lacunary sum bound for shifted kernels

We prove `Commons.Analysis.CalderonZygmund.lacunary_shifted_kernel_sum_le`: for a `Λ`-lacunary
finite set of scales `N`, a function `Φ` with `|Φ|` and `|Φ'|` both bounded by `C/(1+t^2)`, and
a shift `y` with `|y| ≤ L/2`, the sum of the integrals away from `{|x| ≥ 50 L}` of the shifted
differences is bounded by a constant multiple of `K`, where `|λ N| ≤ 2^K`.

The proof splits each summand according to the size of the scale `A N ^ d` and of `λ N`.
-/

namespace Commons.Analysis.CalderonZygmund

open MeasureTheory
open scoped BigOperators

/-! ## Elementary one-dimensional estimates -/

/-- `arctan x ≤ x` for `x ≥ 0`. -/
lemma arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h := integral_inv_one_add_sq (a := 0) (b := x)
  rw [Real.arctan_zero, sub_zero] at h
  rw [← h]
  calc ∫ u in (0:ℝ)..x, (1 + u ^ 2)⁻¹ ≤ ∫ u in (0:ℝ)..x, (1:ℝ) := by
        apply intervalIntegral.integral_mono_on hx
        · exact ((continuous_const.add (continuous_id.pow 2)).inv₀
            (fun u => ne_of_gt (by positivity : (0:ℝ) < 1 + u^2))).intervalIntegrable _ _
        · exact intervalIntegrable_const
        · intro t ht
          exact inv_le_one_of_one_le₀ (by nlinarith [ht.1, sq_nonneg t])
    _ = x := by simp

/-- `π / 2 - arctan ρ ≤ 1 / ρ` for `ρ > 0`. -/
lemma pi_div_two_sub_arctan_le (ρ : ℝ) (hρ : 0 < ρ) : Real.pi / 2 - Real.arctan ρ ≤ 1 / ρ := by
  rw [← Real.arctan_inv_of_pos hρ]
  calc Real.arctan ρ⁻¹ ≤ ρ⁻¹ := arctan_le_self (by positivity)
    _ = 1 / ρ := by rw [one_div]

/-- `∫_{ρ}^{∞} (1+t^2)^{-1} ≤ 1/ρ`. -/
lemma integral_Ioi_inv_one_add_sq_le (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ t in Set.Ioi ρ, (1 + t^2)⁻¹) ≤ 1 / ρ := by
  rw [integral_Ioi_inv_one_add_sq]
  exact pi_div_two_sub_arctan_le ρ hρ

/-- `∫_{-∞}^{-ρ} (1+t^2)^{-1} ≤ 1/ρ`. -/
lemma integral_Iic_inv_one_add_sq_le (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ t in Set.Iic (-ρ), (1 + t^2)⁻¹) ≤ 1 / ρ := by
  have e2 : (∫ t in Set.Iic (-ρ), (1 + t^2)⁻¹) = ∫ t in Set.Ioi ρ, (1 + t^2)⁻¹ := by
    have := integral_comp_neg_Iic (-ρ) (fun u : ℝ => (1+u^2)⁻¹)
    simp only [neg_sq, neg_neg] at this
    exact this
  rw [e2]
  exact integral_Ioi_inv_one_add_sq_le ρ hρ

/-- The two-sided tail bound `∫_{{ρ ≤ |t|}} (1+t^2)^{-1} ≤ 2/ρ`. -/
lemma tail_inv_one_add_sq_le (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ t in {t : ℝ | ρ ≤ |t|}, (1 + t^2)⁻¹) ≤ 2 / ρ := by
  have hset : {t : ℝ | ρ ≤ |t|} = Set.Iic (-ρ) ∪ Set.Ici ρ := by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
    constructor
    · intro h
      by_cases ht : t ≤ 0
      · left; rw [abs_of_nonpos ht] at h; linarith
      · right; push_neg at ht; rw [abs_of_pos ht] at h; linarith
    · rintro (h | h)
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  rw [hset]
  have hdisj : Disjoint (Set.Iic (-ρ)) (Set.Ici ρ) := by
    rw [Set.disjoint_left]; intro x hx1 hx2
    simp only [Set.mem_Iic] at hx1; simp only [Set.mem_Ici] at hx2; linarith
  rw [setIntegral_union hdisj measurableSet_Ici
      (integrable_inv_one_add_sq.integrableOn) (integrable_inv_one_add_sq.integrableOn),
    integral_Ici_eq_integral_Ioi]
  have h1 := integral_Ioi_inv_one_add_sq_le ρ hρ
  have h2 := integral_Iic_inv_one_add_sq_le ρ hρ
  have h3 : (1:ℝ)/ρ + 1/ρ = 2/ρ := by ring
  linarith

/-- `∫_ℝ (1+t^2)^{-1} ≤ 4`. -/
lemma integral_inv_one_add_sq_le_four : (∫ t : ℝ, (1 + t^2)⁻¹) ≤ 4 := by
  have hsplit : (∫ t : ℝ, (1 + t^2)⁻¹)
      = (∫ t in Set.Iic (0:ℝ), (1 + t^2)⁻¹) + ∫ t in Set.Ioi (0:ℝ), (1 + t^2)⁻¹ := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        (integrable_inv_one_add_sq.integrableOn) (integrable_inv_one_add_sq.integrableOn),
      Set.Iic_union_Ioi, Measure.restrict_univ]
  rw [hsplit]
  have hleft : (∫ t in Set.Iic (0:ℝ), (1 + t^2)⁻¹) = ∫ t in Set.Ioi (0:ℝ), (1 + t^2)⁻¹ := by
    have := integral_comp_neg_Iic (0:ℝ) (fun u : ℝ => (1+u^2)⁻¹)
    simp only [neg_sq, neg_zero] at this
    exact this
  rw [hleft, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]
  have := Real.pi_le_four
  linarith

/-! ## Substitution lemmas for scaling and translation -/

/-- Change of variables `x ↦ (x - d)/a` on the whole line. -/
lemma integral_comp_div_sub (f : ℝ → ℝ) (a d : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, f ((x - d)/a)) = a * ∫ t : ℝ, f t := by
  have h1 : (∫ x : ℝ, f ((x - d)/a)) = ∫ x : ℝ, (fun y => f (y - d/a)) (a⁻¹ * x) := by
    apply integral_congr_ae; filter_upwards with x; congr 1; field_simp
  rw [h1, Measure.integral_comp_inv_mul_left (fun y => f (y - d/a)) a]
  have h2 : (∫ y : ℝ, f (y - d/a)) = ∫ t : ℝ, f t := by
    have := MeasureTheory.MeasurePreserving.integral_comp
      (measurePreserving_add_right (volume : Measure ℝ) (-d/a))
      (measurableEmbedding_addRight (G := ℝ) (-d/a)) f
    simpa [sub_eq_add_neg, neg_div] using this
  rw [h2]
  simp [abs_of_pos ha]

/-- Change of variables `x ↦ (x - c)/a` for set integrals. -/
lemma setIntegral_comp_div_sub (g : ℝ → ℝ) (a c : ℝ) (ha : 0 < a) (S : Set ℝ)
    (hS : MeasurableSet S) :
    (∫ x in S, g ((x - c)/a)) = a * ∫ u in {u : ℝ | c + a * u ∈ S}, g u := by
  rw [← integral_indicator hS]
  have hmeasT : MeasurableSet {u : ℝ | c + a * u ∈ S} := hS.preimage (by fun_prop)
  rw [← integral_indicator hmeasT]
  have hcore : ∀ x : ℝ, c + a * ((x - c)/a) = x := by
    intro x; field_simp; ring
  have hpt : ∀ x : ℝ, S.indicator (fun x => g ((x - c)/a)) x
      = (Set.indicator {u : ℝ | c + a * u ∈ S} g) ((x - c)/a) := by
    intro x
    have hiff : ((x - c)/a ∈ {u : ℝ | c + a * u ∈ S}) ↔ (x ∈ S) := by
      simp only [Set.mem_setOf_eq, hcore x]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.mpr hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hiff.mp h))]
  rw [show (∫ x, S.indicator (fun x => g ((x - c)/a)) x)
        = ∫ x, (Set.indicator {u : ℝ | c + a * u ∈ S} g) ((x - c)/a)
      from integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_comp_div_sub (Set.indicator {u : ℝ | c + a * u ∈ S} g) a c ha


/-! ## Translation substitution -/

/-- Translation invariance of the integral on the whole line. -/
lemma integral_comp_sub_right (f : ℝ → ℝ) (d : ℝ) : (∫ x : ℝ, f (x - d)) = ∫ u : ℝ, f u := by
  have := MeasureTheory.MeasurePreserving.integral_comp
    (measurePreserving_add_right (volume : Measure ℝ) (-d))
    (measurableEmbedding_addRight (G := ℝ) (-d)) f
  simpa [sub_eq_add_neg] using this

/-- Translation substitution for set integrals. -/
lemma setIntegral_comp_sub (f : ℝ → ℝ) (d : ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ x in S, f (x - d)) = ∫ u in {u : ℝ | u + d ∈ S}, f u := by
  rw [← integral_indicator hS]
  have hmeasT : MeasurableSet {u : ℝ | u + d ∈ S} := hS.preimage (by fun_prop)
  rw [← integral_indicator hmeasT]
  have hpt : ∀ x : ℝ, S.indicator (fun x => f (x - d)) x
      = (Set.indicator {u : ℝ | u + d ∈ S} f) (x - d) := by
    intro x
    have hiff : (x - d ∈ {u : ℝ | u + d ∈ S}) ↔ (x ∈ S) := by
      simp only [Set.mem_setOf_eq]
      rw [show x - d + d = x by ring]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.mpr hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hiff.mp h))]
  rw [show (∫ x, S.indicator (fun x => f (x - d)) x)
        = ∫ x, (Set.indicator {u : ℝ | u + d ∈ S} f) (x - d)
      from integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_comp_sub_right (Set.indicator {u : ℝ | u + d ∈ S} f) d

/-! ## Integrability and integral bounds for functions decaying like `C/(1+t^2)` -/

/-- If `|f t| ≤ C/(1+t^2)` then `∫ |f| ≤ 4C`. -/
lemma integral_abs_le_of_bound {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ t, |f t| ≤ C / (1 + t^2)) :
    (∫ t : ℝ, |f t|) ≤ 4 * C := by
  have hmono : (∫ t : ℝ, |f t|) ≤ ∫ t : ℝ, C / (1 + t^2) := by
    apply integral_mono_of_nonneg
    · filter_upwards with t; exact abs_nonneg _
    · simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C
    · filter_upwards with t; exact hf t
  rw [show (∫ t : ℝ, C / (1 + t^2)) = C * ∫ t : ℝ, (1 + t^2)⁻¹ from by
    rw [show (fun t : ℝ => C / (1 + t^2)) = fun t => C * (1 + t^2)⁻¹ from by
      ext t; rw [div_eq_mul_inv]]
    rw [integral_const_mul]] at hmono
  calc (∫ t : ℝ, |f t|) ≤ C * ∫ t : ℝ, (1 + t^2)⁻¹ := hmono
    _ ≤ C * 4 := mul_le_mul_of_nonneg_left integral_inv_one_add_sq_le_four hC
    _ = 4 * C := by ring

/-- If `|f t| ≤ C/(1+t^2)` then `∫_{{ρ ≤ |t|}} |f| ≤ 2C/ρ`. -/
lemma tail_abs_le_of_bound {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ t, |f t| ≤ C / (1 + t^2)) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ t in {t : ℝ | ρ ≤ |t|}, |f t|) ≤ 2 * C / ρ := by
  have hmono : (∫ t in {t : ℝ | ρ ≤ |t|}, |f t|)
      ≤ ∫ t in {t : ℝ | ρ ≤ |t|}, C / (1 + t^2) := by
    apply integral_mono_of_nonneg
    · filter_upwards with t; exact abs_nonneg _
    · exact (by simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C :
        Integrable (fun t : ℝ => C / (1 + t^2)) volume).integrableOn
    · filter_upwards with t; exact hf t
  have hstep : (∫ t in {t : ℝ | ρ ≤ |t|}, C / (1 + t^2)) = C * ∫ t in {t : ℝ | ρ ≤ |t|}, (1 + t^2)⁻¹ := by
    rw [show (fun t : ℝ => C / (1 + t^2)) = fun t => C * (1 + t^2)⁻¹ from by
      ext t; rw [div_eq_mul_inv]]
    rw [integral_const_mul]
  rw [hstep] at hmono
  calc (∫ t in {t : ℝ | ρ ≤ |t|}, |f t|) ≤ C * ∫ t in {t : ℝ | ρ ≤ |t|}, (1 + t^2)⁻¹ := hmono
    _ ≤ C * (2 / ρ) := mul_le_mul_of_nonneg_left (tail_inv_one_add_sq_le ρ hρ) hC
    _ = 2 * C / ρ := by ring

/-- If `f` is continuous with `|f t| ≤ C/(1+t^2)`, then `|f|` is integrable. -/
lemma integrable_abs_of_continuous_bound {f : ℝ → ℝ} {C : ℝ}
    (hfcont : Continuous f) (hf : ∀ t, |f t| ≤ C / (1 + t^2)) :
    Integrable (fun t : ℝ => |f t|) := by
  apply Integrable.mono' (g := fun t : ℝ => C / (1 + t^2))
  · simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C
  · exact hfcont.abs.aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_abs]
    exact hf t

/-! ## A mean-value bound for the shifted difference -/

/-- Mean value bound: if `m` bounds `|c|` below on the interval `(a,b)`, then
`|Φ b - Φ a| ≤ (b - a) * C/(1+m^2)`. -/
lemma abs_phi_sub_le_of_mvt {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hdiff : ∀ t, HasDerivAt Φ (deriv Φ t) t) (hΦ' : ∀ t, |deriv Φ t| ≤ C / (1 + t^2))
    {a b : ℝ} (hab : a < b) {m : ℝ} (hm0 : 0 ≤ m) (hm : ∀ c ∈ Set.Ioo a b, m ≤ |c|) :
    |Φ b - Φ a| ≤ (b - a) * (C / (1 + m^2)) := by
  obtain ⟨c, hc, hcval⟩ := exists_hasDerivAt_eq_slope Φ (deriv Φ) hab
    ((continuous_iff_continuousAt.mpr (fun x => (hdiff x).continuousAt)).continuousOn)
    (fun x hx => hdiff x)
  have hsum : Φ b - Φ a = deriv Φ c * (b - a) := by
    rw [hcval]
    exact (div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hab))).symm
  have hcm : m ≤ |c| := hm c hc
  rw [hsum, abs_mul, abs_of_pos (sub_pos.mpr hab), mul_comm (|deriv Φ c|) (b - a)]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (sub_pos.mpr hab))
  calc |deriv Φ c| ≤ C / (1 + c^2) := hΦ' c
    _ ≤ C / (1 + m^2) := by
        apply div_le_div_of_nonneg_left hC (by positivity)
        have : m^2 ≤ c^2 := by rw [sq_le_sq, abs_of_nonneg hm0]; exact hcm
        linarith

/-- Pointwise mean value bound for the shifted difference. -/
lemma abs_phi_sub_le_pointwise {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hdiff : ∀ t, HasDerivAt Φ (deriv Φ t) t) (hΦ' : ∀ t, |deriv Φ t| ≤ C / (1 + t^2))
    (u δ : ℝ) :
    |Φ u - Φ (u - δ)| ≤ |δ| * (C / (1 + (max 0 (|u| - |δ|))^2)) := by
  rcases eq_or_ne δ 0 with hδ | hδ
  · simp [hδ]
  · have hne : u ≠ u - δ := by intro h; exact hδ (by linarith)
    have hab : min u (u - δ) < max u (u - δ) := min_lt_max.mpr hne
    have hm : ∀ c ∈ Set.Ioo (min u (u - δ)) (max u (u - δ)), max 0 (|u| - |δ|) ≤ |c| := by
      intro c hc
      obtain ⟨hc1, hc2⟩ := Set.mem_Ioo.mp hc
      have hsub : |c - u| ≤ |δ| := by
        have h1 : |c - u| ≤ max u (u - δ) - min u (u - δ) := by
          rw [abs_sub_le_iff]
          exact ⟨by linarith [min_le_left u (u - δ)], by linarith [le_max_left u (u - δ)]⟩
        rw [max_sub_min_eq_abs] at h1
        rw [show u - δ - u = -δ by ring, abs_neg] at h1
        exact h1
      have h3 : |u| - |c - u| ≤ |c| := by
        have htr := abs_add_le c (-(c - u))
        rw [abs_neg] at htr
        have he : c + (-(c - u)) = u := by ring
        rw [he] at htr
        linarith
      exact max_le (abs_nonneg c) (by linarith)
    have heq : |Φ u - Φ (u - δ)| = |Φ (max u (u - δ)) - Φ (min u (u - δ))| := by
      rcases le_total u (u - δ) with h | h
      · rw [max_eq_right h, min_eq_left h, abs_sub_comm]
      · rw [max_eq_left h, min_eq_right h]
    rw [heq]
    calc |Φ (max u (u - δ)) - Φ (min u (u - δ))|
        ≤ (max u (u - δ) - min u (u - δ)) * (C / (1 + (max 0 (|u| - |δ|))^2)) :=
          abs_phi_sub_le_of_mvt hC hdiff hΦ' hab (le_max_left 0 _) hm
      _ = |δ| * (C / (1 + (max 0 (|u| - |δ|))^2)) := by
          rw [max_sub_min_eq_abs, show u - δ - u = -δ by ring, abs_neg]

lemma inv_one_add_max_le_six (u δ : ℝ) (hδ : |δ| < 1) :
    1 / (1 + (max 0 (|u| - |δ|))^2) ≤ 6 / (1 + u^2) := by
  set M := max 0 (|u| - |δ|) with hM
  have hM0 : 0 ≤ M := le_max_left _ _
  have hMu : |u| - |δ| ≤ M := le_max_right _ _
  have hδ1 : |δ| ≤ 1 := le_of_lt hδ
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  simp only [one_mul]
  by_cases hu : 2 ≤ |u|
  · have hM2 : |u| / 2 ≤ M := by linarith
    have hsq : (|u|/2)^2 ≤ M^2 := pow_le_pow_left₀ (by positivity) hM2 2
    have hu2 : (|u|/2)^2 = u^2/4 := by rw [div_pow, sq_abs]; ring
    nlinarith [hsq, hu2, sq_nonneg u]
  · push_neg at hu
    nlinarith [sq_nonneg M, hu, sq_abs u, abs_nonneg u]

/-- The pointwise bound `|Φ u - Φ (u-δ)| ≤ 6C|δ|/(1+u^2)` for `|δ| < 1`. -/
lemma abs_phi_sub_le_six {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hdiff : ∀ t, HasDerivAt Φ (deriv Φ t) t) (hΦ' : ∀ t, |deriv Φ t| ≤ C / (1 + t^2))
    (u δ : ℝ) (hδ : |δ| < 1) :
    |Φ u - Φ (u - δ)| ≤ 6 * C * |δ| / (1 + u^2) := by
  have h1 := abs_phi_sub_le_pointwise hC hdiff hΦ' u δ
  have h2 := inv_one_add_max_le_six u δ hδ
  have hCδ : 0 ≤ C * |δ| := by positivity
  calc |Φ u - Φ (u - δ)| ≤ |δ| * (C / (1 + (max 0 (|u| - |δ|))^2)) := h1
    _ = C * |δ| * (1 / (1 + (max 0 (|u| - |δ|))^2)) := by ring
    _ ≤ C * |δ| * (6 / (1 + u^2)) := mul_le_mul_of_nonneg_left h2 hCδ
    _ = 6 * C * |δ| / (1 + u^2) := by ring

/-- The full-line bound `∫ |Φ u - Φ(u-δ)| ≤ 24 C |δ|` for `|δ| < 1`. -/
lemma integral_abs_phi_sub_le {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hdiff : ∀ t, HasDerivAt Φ (deriv Φ t) t) (hΦ' : ∀ t, |deriv Φ t| ≤ C / (1 + t^2))
    (δ : ℝ) (hδ : |δ| < 1) :
    (∫ u : ℝ, |Φ u - Φ (u - δ)|) ≤ 24 * C * |δ| := by
  have hmono : (∫ u : ℝ, |Φ u - Φ (u - δ)|) ≤ ∫ u : ℝ, 6 * C * |δ| / (1 + u^2) := by
    apply integral_mono_of_nonneg
    · filter_upwards with u; exact abs_nonneg _
    · have heq : (fun u : ℝ => 6 * C * |δ| / (1 + u^2))
          = fun u => (6 * C * |δ|) * (1 + u^2)⁻¹ := by
        ext u; rw [div_eq_mul_inv]
      rw [heq]; exact integrable_inv_one_add_sq.const_mul _
    · filter_upwards with u; exact abs_phi_sub_le_six hC hdiff hΦ' u δ hδ
  have hstep : (∫ u : ℝ, 6 * C * |δ| / (1 + u^2)) = 6 * C * |δ| * ∫ u : ℝ, (1 + u^2)⁻¹ := by
    rw [show (∫ u : ℝ, 6 * C * |δ| / (1 + u^2)) = ∫ u : ℝ, (6 * C * |δ|) * (1 + u^2)⁻¹ from by
      apply integral_congr_ae; filter_upwards with u; rw [div_eq_mul_inv]]
    rw [integral_const_mul]
  calc (∫ u : ℝ, |Φ u - Φ (u - δ)|) ≤ ∫ u : ℝ, 6 * C * |δ| / (1 + u^2) := hmono
    _ = 6 * C * |δ| * ∫ u : ℝ, (1 + u^2)⁻¹ := hstep
    _ ≤ 6 * C * |δ| * 4 := mul_le_mul_of_nonneg_left integral_inv_one_add_sq_le_four (by positivity)
    _ = 24 * C * |δ| := by ring


/-! ## Packaging the set-integral bounds for `Φ` -/

/-- Integrability of the shifted difference. -/
lemma integrable_abs_phi_sub {Φ : ℝ → ℝ} {C : ℝ} (hcont : Continuous Φ)
    (hΦ : ∀ t, |Φ t| ≤ C / (1 + t^2)) (δ : ℝ) :
    Integrable (fun u : ℝ => |Φ u - Φ (u - δ)|) := by
  have hbase : Integrable (fun u : ℝ => C / (1 + u^2)) := by
    simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C
  have hg1 : Integrable (fun u : ℝ => C / (1 + (u - δ)^2)) := by
    have := (measurePreserving_add_right (volume : Measure ℝ) (-δ)).integrable_comp_of_integrable hbase
    simpa [Function.comp_def, sub_eq_add_neg] using this
  apply Integrable.mono' (g := fun u : ℝ => C / (1 + u^2) + C / (1 + (u - δ)^2))
  · exact hbase.add hg1
  · exact ((hcont.sub (hcont.comp (continuous_id.sub continuous_const))).abs).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_abs]
    calc |Φ u - Φ (u - δ)| ≤ |Φ u| + |Φ (u - δ)| := by
          simpa using abs_sub_le (Φ u) 0 (Φ (u - δ))
      _ ≤ C / (1 + u^2) + C / (1 + (u - δ)^2) := add_le_add (hΦ u) (hΦ (u - δ))

/-- Integrability of a translate of `|Φ|`. -/
lemma integrable_abs_phi_shift {Φ : ℝ → ℝ} {C : ℝ} (hcont : Continuous Φ)
    (hΦ : ∀ t, |Φ t| ≤ C / (1 + t^2)) (δ : ℝ) :
    Integrable (fun u : ℝ => |Φ (u - δ)|) := by
  have hbase : Integrable (fun u : ℝ => |Φ u|) := integrable_abs_of_continuous_bound hcont hΦ
  have := (measurePreserving_add_right (volume : Measure ℝ) (-δ)).integrable_comp_of_integrable hbase
  simpa [Function.comp_def, sub_eq_add_neg] using this

/-- `∫_S |Φ u - Φ(u-δ)|` is bounded by the full-line bound, for any `S`. -/
lemma setIntegral_abs_phi_sub_le_full {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hcont : Continuous Φ) (hdiff : ∀ t, HasDerivAt Φ (deriv Φ t) t)
    (hΦ : ∀ t, |Φ t| ≤ C / (1 + t^2)) (hΦ' : ∀ t, |deriv Φ t| ≤ C / (1 + t^2))
    (δ : ℝ) (hδ : |δ| < 1) (S : Set ℝ) :
    (∫ u in S, |Φ u - Φ (u - δ)|) ≤ 24 * C * |δ| :=
  le_trans (setIntegral_le_integral (integrable_abs_phi_sub hcont hΦ δ)
      (Filter.Eventually.of_forall (fun u => abs_nonneg _)))
    (integral_abs_phi_sub_le hC hdiff hΦ' δ hδ)

/-- `∫_S |Φ|` is bounded by the tail bound when `S ⊆ {ρ ≤ |t|}`. -/
lemma setIntegral_abs_phi_le_tail {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hcont : Continuous Φ) (hΦ : ∀ t, |Φ t| ≤ C / (1 + t^2))
    {S : Set ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hS : S ⊆ {t : ℝ | ρ ≤ |t|}) :
    (∫ t in S, |Φ t|) ≤ 2 * C / ρ :=
  le_trans (setIntegral_mono_set (integrable_abs_of_continuous_bound hcont hΦ).integrableOn
      (Filter.Eventually.of_forall (fun t => abs_nonneg _)) (Filter.Eventually.of_forall hS))
    (tail_abs_le_of_bound hC hΦ hρ)

/-- `∫_S |Φ(u-δ)|` is bounded by a tail bound when `S ⊆ {ρ ≤ |t|}` and `|δ| ≤ ρ/2`. -/
lemma setIntegral_abs_phi_shift_le_tail {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hcont : Continuous Φ) (hΦ : ∀ t, |Φ t| ≤ C / (1 + t^2))
    (δ : ℝ) {S : Set ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hS : S ⊆ {t : ℝ | ρ ≤ |t|})
    (hδρ : |δ| ≤ ρ / 2) :
    (∫ t in S, |Φ (t - δ)|) ≤ 2 * C / (ρ - |δ|) := by
  have hmeas : MeasurableSet {t : ℝ | ρ ≤ |t|} := measurableSet_le measurable_const (by fun_prop)
  have h1 : (∫ t in S, |Φ (t - δ)|) ≤ ∫ t in {t : ℝ | ρ ≤ |t|}, |Φ (t - δ)| :=
    setIntegral_mono_set (integrable_abs_phi_shift hcont hΦ δ).integrableOn
      (Filter.Eventually.of_forall (fun t => abs_nonneg _)) (Filter.Eventually.of_forall hS)
  have h2 : (∫ t in {t : ℝ | ρ ≤ |t|}, |Φ (t - δ)|)
      = ∫ w in {w : ℝ | w + δ ∈ {t : ℝ | ρ ≤ |t|}}, |Φ w| :=
    setIntegral_comp_sub (fun w => |Φ w|) δ {t : ℝ | ρ ≤ |t|} hmeas
  have h3 : (∫ w in {w : ℝ | w + δ ∈ {t : ℝ | ρ ≤ |t|}}, |Φ w|)
      ≤ ∫ w in {w : ℝ | ρ - |δ| ≤ |w|}, |Φ w| := by
    apply setIntegral_mono_set (integrable_abs_of_continuous_bound hcont hΦ).integrableOn
      (Filter.Eventually.of_forall (fun w => abs_nonneg _))
    filter_upwards with w hw
    have h := abs_add_le w δ
    have hw' : ρ ≤ |w + δ| := hw
    show ρ - |δ| ≤ |w|
    linarith
  have h4 : (∫ w in {w : ℝ | ρ - |δ| ≤ |w|}, |Φ w|) ≤ 2 * C / (ρ - |δ|) := by
    apply tail_abs_le_of_bound hC hΦ
    linarith
  linarith [h1, h2 ▸ h3, h4]

/-- `∫_S |Φ(u-δ) - Φ u| ≤ 8 C` for any `S`. -/
lemma setIntegral_abs_phi_sub_le_eight {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hcont : Continuous Φ) (hΦ : ∀ t, |Φ t| ≤ C / (1 + t^2)) (δ : ℝ) (S : Set ℝ) :
    (∫ u in S, |Φ (u - δ) - Φ u|) ≤ 8 * C := by
  have hI : Integrable (fun u : ℝ => |Φ (u - δ) - Φ u|) := by
    rw [show (fun u : ℝ => |Φ (u - δ) - Φ u|) = fun u => |Φ u - Φ (u - δ)| from by
      ext u; rw [abs_sub_comm]]
    exact integrable_abs_phi_sub hcont hΦ δ
  have hInt1 : Integrable (fun u : ℝ => |Φ (u - δ)|) := integrable_abs_phi_shift hcont hΦ δ
  have hInt0 : Integrable (fun u : ℝ => |Φ u|) := integrable_abs_of_continuous_bound hcont hΦ
  refine le_trans (setIntegral_le_integral hI (Filter.Eventually.of_forall (fun u => abs_nonneg _))) ?_
  have hmono : (∫ u : ℝ, |Φ (u - δ) - Φ u|) ≤ ∫ u : ℝ, (|Φ (u - δ)| + |Φ u|) := by
    apply integral_mono_of_nonneg
    · filter_upwards with u; exact abs_nonneg _
    · exact hInt1.add hInt0
    · filter_upwards with u; simpa using abs_sub_le (Φ (u - δ)) 0 (Φ u)
  calc (∫ u : ℝ, |Φ (u - δ) - Φ u|) ≤ ∫ u : ℝ, (|Φ (u - δ)| + |Φ u|) := hmono
    _ = (∫ u : ℝ, |Φ (u - δ)|) + ∫ u : ℝ, |Φ u| := integral_add hInt1 hInt0
    _ = (∫ u : ℝ, |Φ u|) + ∫ u : ℝ, |Φ u| := by
        rw [show (∫ u : ℝ, |Φ (u - δ)|) = ∫ u : ℝ, |Φ u| from integral_comp_sub_right (fun u => |Φ u|) δ]
    _ ≤ 4 * C + 4 * C := add_le_add (integral_abs_le_of_bound hC hΦ) (integral_abs_le_of_bound hC hΦ)
    _ = 8 * C := by ring

/-- `∫_{{ρ ≤ |u|}} |Φ(u-δ) - Φ u| ≤ 2C/ρ + 2C/(ρ-|δ|)` for `|δ| ≤ ρ/2`. -/
lemma setIntegral_abs_phi_sub_le_tail_bound {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hcont : Continuous Φ) (hΦ : ∀ t, |Φ t| ≤ C / (1 + t^2))
    (δ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hδρ : |δ| ≤ ρ / 2) :
    (∫ u in {u : ℝ | ρ ≤ |u|}, |Φ (u - δ) - Φ u|) ≤ 2 * C / ρ + 2 * C / (ρ - |δ|) := by
  have hInt1 : Integrable (fun u : ℝ => |Φ (u - δ)|) := integrable_abs_phi_shift hcont hΦ δ
  have hInt0 : Integrable (fun u : ℝ => |Φ u|) := integrable_abs_of_continuous_bound hcont hΦ
  have hsub : (∫ u in {u : ℝ | ρ ≤ |u|}, |Φ (u - δ) - Φ u|)
      ≤ ∫ u in {u : ℝ | ρ ≤ |u|}, (|Φ (u - δ)| + |Φ u|) := by
    apply integral_mono_of_nonneg
    · filter_upwards with u; exact abs_nonneg _
    · exact (hInt1.add hInt0).integrableOn
    · filter_upwards with u; simpa using abs_sub_le (Φ (u - δ)) 0 (Φ u)
  calc (∫ u in {u : ℝ | ρ ≤ |u|}, |Φ (u - δ) - Φ u|)
      ≤ ∫ u in {u : ℝ | ρ ≤ |u|}, (|Φ (u - δ)| + |Φ u|) := hsub
    _ = (∫ u in {u : ℝ | ρ ≤ |u|}, |Φ (u - δ)|) + ∫ u in {u : ℝ | ρ ≤ |u|}, |Φ u| :=
        integral_add hInt1.integrableOn hInt0.integrableOn
    _ ≤ 2 * C / (ρ - |δ|) + 2 * C / ρ :=
        add_le_add (setIntegral_abs_phi_shift_le_tail hC hcont hΦ δ hρ (subset_rfl) hδρ)
          (setIntegral_abs_phi_le_tail hC hcont hΦ hρ subset_rfl)
    _ = 2 * C / ρ + 2 * C / (ρ - |δ|) := by ring

/-! ## The main theorem -/

private lemma lacunary_sum_le_max {Λ : ℝ} (hΛ : 1 < Λ) (d : ℕ) (hd : 1 ≤ d) (A : ℝ) (hA : 0 < A)
    (D : Finset ℝ) (hDpos : ∀ N ∈ D, 0 < N)
    (hlac : ∀ M ∈ D, ∀ N ∈ D, M < N → Λ * M ≤ N)
    (T : Finset ℝ) (hTD : T ⊆ D) (hT : T.Nonempty) :
    ∑ N ∈ T, A * N ^ d ≤ (1 - (Λ ^ d)⁻¹)⁻¹ * (A * (T.max' hT)^d) := by
  set G := (1 - (Λ^d)⁻¹)⁻¹ with hGdef
  have hΛd : 1 < Λ ^ d := one_lt_pow₀ hΛ (by omega)
  have hΛdpos : 0 < Λ ^ d := lt_trans zero_lt_one hΛd
  have hGpos : 0 < G := by
    rw [hGdef]; apply inv_pos.mpr; rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hΛd
  have hG1 : 1 ≤ G := by
    rw [hGdef]
    have hpos : 0 < 1 - (Λ^d)⁻¹ := by rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hΛd
    rw [one_le_inv₀ hpos]
    linarith [inv_nonneg.mpr hΛdpos.le]
  have hGid : G / Λ^d + 1 = G := by
    have hne : (1 - (Λ^d)⁻¹) ≠ 0 := by
      rw [sub_ne_zero]; exact ne_of_gt (inv_lt_one_of_one_lt₀ hΛd)
    have hfac : G * (1 - (Λ^d)⁻¹) = 1 := by rw [hGdef]; exact inv_mul_cancel₀ hne
    have hexp : G * (1 - (Λ^d)⁻¹) = G - G * (Λ^d)⁻¹ := by ring
    have hsplit : G / Λ^d = G * (Λ^d)⁻¹ := by rw [div_eq_mul_inv]
    rw [hsplit]; linarith
  revert hTD hT
  refine Finset.induction_on_max
    (motive := fun T => T ⊆ D → ∀ (hT : T.Nonempty),
      ∑ N ∈ T, A * N ^ d ≤ G * (A * (T.max' hT)^d)) T ?_ ?_
  · intro _ hT; exact absurd hT Finset.not_nonempty_empty
  · intro b S hmax ih hsub hne
    have hbD : b ∈ D := hsub (Finset.mem_insert_self b S)
    have hbp : 0 < b := hDpos b hbD
    have hSD : S ⊆ D := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    have hmaxeq : (insert b S).max' hne = b := by
      apply le_antisymm
      · apply Finset.max'_le
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact le_rfl
        · exact le_of_lt (hmax y hy')
      · exact Finset.le_max' _ b (Finset.mem_insert_self b S)
    have hb_notin : b ∉ S := fun hb => absurd (hmax b hb) (lt_irrefl b)
    rw [hmaxeq, Finset.sum_insert hb_notin]
    rcases Finset.eq_empty_or_nonempty S with hSe | hSne
    · rw [hSe, Finset.sum_empty, add_zero]
      calc A * b ^ d = 1 * (A * b ^ d) := (one_mul _).symm
        _ ≤ G * (A * b ^ d) := mul_le_mul_of_nonneg_right hG1 (mul_pos hA (pow_pos hbp d)).le
    · have ih' := ih hSD hSne
      have hmS : S.max' hSne ∈ S := Finset.max'_mem S hSne
      have hmSp : 0 < S.max' hSne := hDpos _ (hSD hmS)
      have hlt : S.max' hSne < b := hmax _ hmS
      have hlac' : Λ * (S.max' hSne) ≤ b := hlac _ (hSD hmS) _ hbD hlt
      have hbound : A * (S.max' hSne)^d ≤ A * b^d / Λ^d := by
        have h1 : (S.max' hSne) ≤ b / Λ := by
          rw [le_div_iff₀ (lt_trans zero_lt_one hΛ)]; linarith
        have h2 : (S.max' hSne)^d ≤ (b/Λ)^d := pow_le_pow_left₀ hmSp.le h1 d
        calc A * (S.max' hSne)^d ≤ A * (b/Λ)^d := mul_le_mul_of_nonneg_left h2 hA.le
          _ = A * b^d / Λ^d := by rw [div_pow]; ring
      calc A * b ^ d + ∑ N ∈ S, A * N ^ d
          ≤ A * b ^ d + G * (A * (S.max' hSne)^d) := by linarith [ih']
        _ ≤ A * b ^ d + G * (A * b^d / Λ^d) := by
              linarith [mul_le_mul_of_nonneg_left hbound hGpos.le]
        _ = G * (A * b^d) := by
              rw [show A * b^d + G * (A * b^d / Λ^d) = A * b^d * (1 + G / Λ^d) by ring]
              rw [show (1:ℝ) + G / Λ^d = G by linarith [hGid]]
              ring

private lemma lacunary_filtered_sum_le {Λ : ℝ} (hΛ : 1 < Λ) (d : ℕ) (hd : 1 ≤ d) (A : ℝ) (hA : 0 < A)
    (D : Finset ℝ) (hDpos : ∀ N ∈ D, 0 < N) (hlac : ∀ M ∈ D, ∀ N ∈ D, M < N → Λ * M ≤ N)
    {Y : ℝ} (hY : 0 < Y) :
    ∑ N ∈ D.filter (fun N => A * N ^ d ≤ Y), A * N ^ d ≤ (1 - (Λ ^ d)⁻¹)⁻¹ * Y := by
  set G := (1 - (Λ^d)⁻¹)⁻¹ with hGdef
  have hGpos : 0 < G := by
    rw [hGdef]; apply inv_pos.mpr; rw [sub_pos]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hΛ (by omega))
  set S := D.filter (fun N => A * N ^ d ≤ Y) with hSdef
  rcases Finset.eq_empty_or_nonempty S with hSe | hSne
  · rw [hSe, Finset.sum_empty]; positivity
  · have hSD : S ⊆ D := Finset.filter_subset _ _
    have hkey := lacunary_sum_le_max hΛ d hd A hA D hDpos hlac S hSD hSne
    have hmaxY : A * (S.max' hSne)^d ≤ Y := (Finset.mem_filter.mp (Finset.max'_mem S hSne)).2
    calc ∑ N ∈ S, A * N ^ d ≤ G * (A * (S.max' hSne)^d) := hkey
      _ ≤ G * Y := mul_le_mul_of_nonneg_left hmaxY hGpos.le

theorem lacunary_shifted_kernel_sum_le
    (C : ℝ) (hC : 0 < C) (Λ : ℝ) (hΛ : 1 < Λ) (A : ℝ) (hA : 0 < A) (d : ℕ) (hd : 1 ≤ d) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (K L : ℝ) (hK : 1 ≤ K) (hL : 0 < L)
        (D : Finset ℝ) (hDpos : ∀ N ∈ D, 0 < N)
        (hlac : ∀ M ∈ D, ∀ N ∈ D, M < N → Λ * M ≤ N)
        (lam : ℝ → ℝ) (hlam : ∀ N ∈ D, |lam N| ≤ 2 ^ K)
        (Φ : ℝ → ℝ) (hΦ : ∀ t, |Φ t| ≤ C / (1 + t ^ 2))
        (hdiff : ∀ t, HasDerivAt Φ (deriv Φ t) t)
        (hΦ' : ∀ t, |deriv Φ t| ≤ C / (1 + t ^ 2))
        (y : ℝ) (hy : |y| ≤ L / 2),
      (∑ N ∈ D, ∫ x in {x : ℝ | 50 * L ≤ |x|},
          (1 / (A * N ^ d))
            * |Φ ((x - lam N * A * N ^ d - y) / (A * N ^ d))
                - Φ ((x - lam N * A * N ^ d) / (A * N ^ d))|) ≤ C' * K := by
  have hC0 : 0 ≤ C := hC.le
  have hΛpos : 0 < Λ := lt_trans zero_lt_one hΛ
  have hlogΛ : 0 < Real.log Λ := Real.log_pos hΛ
  have hd0 : d ≠ 0 := by omega
  have hΛd : 1 < Λ ^ d := one_lt_pow₀ hΛ hd0
  have hdRpos : 0 < (d : ℝ) := by positivity
  have hdLpos : 0 < (d : ℝ) * Real.log Λ := mul_pos hdRpos hlogΛ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set G : ℝ := (1 - (Λ ^ d)⁻¹)⁻¹ with hGdef
  have hGpos : 0 < G := by
    rw [hGdef]; apply inv_pos.mpr; rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hΛd
  have hbrpos : 0 < (19/4) * G + 8 * (Real.log 2 / ((d:ℝ) * Real.log Λ) + 1) := by
    have h2 : 0 < Real.log 2 / ((d:ℝ) * Real.log Λ) + 1 := by
      have := div_pos hlog2pos hdLpos; linarith
    have h1 : 0 < (19/4) * G := by positivity
    have h3 : 0 < 8 * (Real.log 2 / ((d:ℝ) * Real.log Λ) + 1) := by positivity
    linarith
  refine ⟨C * ((19/4) * G + 8 * (Real.log 2 / ((d:ℝ) * Real.log Λ) + 1)) + 1, ?_, ?_⟩
  · have := mul_pos hC hbrpos; linarith
  · intro K L hK hL D hDpos hlac lam hlam Φ hΦ hdiff hΦ' y hy
    have hcont : Continuous Φ := continuous_iff_continuousAt.mpr (fun t => (hdiff t).continuousAt)
    set S0 : Set ℝ := {x : ℝ | 50 * L ≤ |x|} with hS0def
    have hS0 : MeasurableSet S0 := by
      rw [hS0def]; exact measurableSet_le measurable_const (by fun_prop)
    let I : ℝ → ℝ := fun N => ∫ x in S0,
        (1 / (A * N ^ d))
          * |Φ ((x - lam N * A * N ^ d - y) / (A * N ^ d))
              - Φ ((x - lam N * A * N ^ d) / (A * N ^ d))|
    change (∑ N ∈ D, I N) ≤ (C * ((19/4) * G + 8 * (Real.log 2 / ((d:ℝ) * Real.log Λ) + 1)) + 1) * K
    have hper : ∀ N ∈ D, I N
        = ∫ u in {u : ℝ | lam N * A * N ^ d + (A * N ^ d) * u ∈ S0},
            |Φ (u - y / (A * N ^ d)) - Φ u| := by
      intro N hN
      have haN : 0 < A * N ^ d := mul_pos hA (pow_pos (hDpos N hN) d)
      change (∫ x in S0, (1 / (A * N ^ d))
          * |Φ ((x - lam N * A * N ^ d - y) / (A * N ^ d))
              - Φ ((x - lam N * A * N ^ d) / (A * N ^ d))|) = _
      rw [integral_const_mul]
      rw [show (∫ x in S0, |Φ ((x - lam N * A * N ^ d - y) / (A * N ^ d))
            - Φ ((x - lam N * A * N ^ d) / (A * N ^ d))|)
          = ∫ x in S0, (fun u : ℝ => |Φ (u - y / (A * N ^ d)) - Φ u|)
              ((x - lam N * A * N ^ d) / (A * N ^ d)) from by
        apply setIntegral_congr_fun hS0
        intro x hx
        simp only []
        have harg : (x - lam N * A * N ^ d - y) / (A * N ^ d)
            = (x - lam N * A * N ^ d) / (A * N ^ d) - y / (A * N ^ d) := by
          field_simp; try ring
        rw [harg]]
      rw [setIntegral_comp_div_sub (fun u : ℝ => |Φ (u - y / (A * N ^ d)) - Φ u|)
        (A * N ^ d) (lam N * A * N ^ d) haN S0 hS0]
      rw [one_div, ← mul_assoc, inv_mul_cancel₀ haN.ne', one_mul]
    have hb1 : ∀ N ∈ D, I N ≤ 8 * C := by
      intro N hN
      rw [hper N hN]
      exact setIntegral_abs_phi_sub_le_eight hC0 hcont hΦ (y / (A * N ^ d)) _
    have hb2 : ∀ N ∈ D, 3 * L < A * N ^ d → I N ≤ 12 * C * L / (A * N ^ d) := by
      intro N hN h3
      have haN : 0 < A * N ^ d := mul_pos hA (pow_pos (hDpos N hN) d)
      rw [hper N hN]
      have hδlt : |y / (A * N ^ d)| < 1 := by
        rw [abs_div, abs_of_pos haN, div_lt_one haN]; linarith
      have hI : Integrable (fun u : ℝ => |Φ (u - y / (A * N ^ d)) - Φ u|) := by
        rw [show (fun u : ℝ => |Φ (u - y/(A*N^d)) - Φ u|) = fun u => |Φ u - Φ (u - y/(A*N^d))| from by
          ext u; rw [abs_sub_comm]]
        exact integrable_abs_phi_sub hcont hΦ _
      calc (∫ u in {u : ℝ | lam N * A * N ^ d + (A * N ^ d) * u ∈ S0},
              |Φ (u - y / (A * N ^ d)) - Φ u|)
          ≤ ∫ u : ℝ, |Φ (u - y / (A * N ^ d)) - Φ u| :=
            setIntegral_le_integral hI (Filter.Eventually.of_forall (fun u => abs_nonneg _))
        _ ≤ 24 * C * |y / (A * N ^ d)| := by
            simpa [abs_sub_comm] using integral_abs_phi_sub_le hC0 hdiff hΦ' (y / (A * N ^ d)) hδlt
        _ ≤ 12 * C * L / (A * N ^ d) := by
            rw [abs_div, abs_of_pos haN]
            rw [show 24 * C * (|y| / (A * N ^ d)) = 24 * C * |y| / (A * N ^ d) by ring]
            apply div_le_div_of_nonneg_right _ haN.le
            have := mul_le_mul_of_nonneg_left hy (by positivity : (0:ℝ) ≤ 24 * C)
            linarith
    have hb3 : ∀ N ∈ D, |lam N * A * N ^ d| ≤ 25 * L → I N ≤ C * (A * N ^ d) / (4 * L) := by
      intro N hN hc25
      have haN : 0 < A * N ^ d := mul_pos hA (pow_pos (hDpos N hN) d)
      rw [hper N hN]
      set ρ := 25 * L / (A * N ^ d) with hρdef
      have hρ : 0 < ρ := by rw [hρdef]; positivity
      have hδ : |y / (A * N ^ d)| ≤ ρ / 2 := by
        rw [hρdef, abs_div, abs_of_pos haN]
        rw [show 25 * L / (A * N ^ d) / 2 = 25 * L / (2 * (A * N ^ d)) by field_simp; try ring]
        rw [div_le_div_iff₀ haN (by positivity)]
        nlinarith [hy, haN.le, hL.le]
      have hsub : {u : ℝ | lam N * A * N ^ d + (A * N ^ d) * u ∈ S0} ⊆ {u : ℝ | ρ ≤ |u|} := by
        intro u hu
        rw [hS0def] at hu
        simp only [Set.mem_setOf_eq] at hu ⊢
        have h1 : 25 * L ≤ (A * N ^ d) * |u| := by
          have h3 : |(A * N ^ d) * u| = (A * N ^ d) * |u| := by rw [abs_mul, abs_of_pos haN]
          have h4 := abs_add_le (lam N * A * N ^ d) ((A * N ^ d) * u)
          linarith [abs_nonneg (lam N * A * N ^ d), h3 ▸ h4]
        rw [hρdef, div_le_iff₀ haN]
        linarith [h1]
      have hI : Integrable (fun u : ℝ => |Φ (u - y / (A * N ^ d)) - Φ u|) := by
        rw [show (fun u : ℝ => |Φ (u - y/(A*N^d)) - Φ u|) = fun u => |Φ u - Φ (u - y/(A*N^d))| from by
          ext u; rw [abs_sub_comm]]
        exact integrable_abs_phi_sub hcont hΦ _
      have hstep : (∫ u in {u : ℝ | lam N * A * N ^ d + (A * N ^ d) * u ∈ S0},
            |Φ (u - y / (A * N ^ d)) - Φ u|)
          ≤ ∫ u in {u : ℝ | ρ ≤ |u|}, |Φ (u - y / (A * N ^ d)) - Φ u| :=
        setIntegral_mono_set hI.integrableOn (Filter.Eventually.of_forall (fun u => abs_nonneg _))
          (Filter.Eventually.of_forall hsub)
      have htail := setIntegral_abs_phi_sub_le_tail_bound hC0 hcont hΦ (y / (A * N ^ d)) hρ hδ
      refine le_trans hstep (le_trans htail ?_)
      have h1 : 2 * C / ρ ≤ C * (A * N ^ d) / (8 * L) := by
        rw [hρdef, show 2 * C / (25 * L / (A * N ^ d)) = 2 * C * (A * N ^ d) / (25 * L) by
          field_simp; try ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg hC0 haN.le) hL.le]
      have h2 : 2 * C / (ρ - |y / (A * N ^ d)|) ≤ C * (A * N ^ d) / (8 * L) := by
        have hyl : |y| ≤ L / 2 := hy
        have hden : 49 * L / (2 * (A * N ^ d)) ≤ ρ - |y / (A * N ^ d)| := by
          rw [hρdef, abs_div, abs_of_pos haN, div_sub_div_same]
          rw [div_le_div_iff₀ (by positivity) haN]
          nlinarith [hyl, haN.le, hL.le]
        have hdpos : 0 < 49 * L / (2 * (A * N ^ d)) := by positivity
        calc 2 * C / (ρ - |y / (A * N ^ d)|) ≤ 2 * C / (49 * L / (2 * (A * N ^ d))) :=
              div_le_div_of_nonneg_left (by positivity) hdpos hden
          _ ≤ C * (A * N ^ d) / (8 * L) := by
              rw [show 2 * C / (49 * L / (2 * (A * N ^ d))) = 4 * C * (A * N ^ d) / (49 * L) by
                field_simp; try ring]
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith [mul_nonneg (mul_nonneg hC0 haN.le) hL.le]
      have hsum_eq : C * (A * N ^ d) / (8 * L) + C * (A * N ^ d) / (8 * L)
          = C * (A * N ^ d) / (4 * L) := by field_simp; try ring
      linarith [h1, h2, hsum_eq]
    have hbdd : (∑ N ∈ D, I N)
        ≤ (∑ N ∈ D.filter (fun N => 3 * L < A * N ^ d), 12 * C * L / (A * N ^ d))
          + (∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ 25 * L / (A * N ^ d) < |lam N|), 8 * C)
          + (∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ ¬(25 * L / (A * N ^ d) < |lam N|)),
              C * (A * N ^ d) / (4 * L)) := by
      have e1 := Finset.sum_filter_add_sum_filter_not D (fun N => 3 * L < A * N ^ d) (fun N => I N)
      have e2 := Finset.sum_filter_add_sum_filter_not
        (D.filter (fun N => ¬(3 * L < A * N ^ d))) (fun N => 25 * L / (A * N ^ d) < |lam N|) (fun N => I N)
      rw [Finset.filter_filter, Finset.filter_filter] at e2
      have h0 : (∑ N ∈ D.filter (fun N => 3 * L < A * N ^ d), I N)
          ≤ ∑ N ∈ D.filter (fun N => 3 * L < A * N ^ d), 12 * C * L / (A * N ^ d) :=
        Finset.sum_le_sum (fun N hN => hb2 N (Finset.filter_subset _ _ hN) (Finset.mem_filter.mp hN).2)
      have h1 : (∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ 25 * L / (A * N ^ d) < |lam N|), I N)
          ≤ ∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ 25 * L / (A * N ^ d) < |lam N|), 8 * C :=
        Finset.sum_le_sum (fun N hN => hb1 N (Finset.filter_subset _ _ hN))
      have h2 : (∑ N ∈ D.filter
            (fun N => ¬(3 * L < A * N ^ d) ∧ ¬(25 * L / (A * N ^ d) < |lam N|)), I N)
          ≤ ∑ N ∈ D.filter
            (fun N => ¬(3 * L < A * N ^ d) ∧ ¬(25 * L / (A * N ^ d) < |lam N|)),
              C * (A * N ^ d) / (4 * L) := by
        apply Finset.sum_le_sum
        intro N hN
        have hND : N ∈ D := (Finset.filter_subset _ _ hN)
        have hcond := (Finset.mem_filter.mp hN).2
        apply hb3 N hND
        have haN : 0 < A * N ^ d := mul_pos hA (pow_pos (hDpos N hND) d)
        rw [show lam N * A * N ^ d = lam N * (A * N ^ d) by ring, abs_mul, abs_of_pos haN]
        have hne : ¬ (25 * L / (A * N ^ d) < |lam N|) := hcond.2
        rw [not_lt] at hne
        rw [le_div_iff₀ haN] at hne
        exact hne
      calc (∑ N ∈ D, I N)
          = (∑ N ∈ D.filter (fun N => 3 * L < A * N ^ d), I N)
              + (∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d)), I N) := e1.symm
        _ = (∑ N ∈ D.filter (fun N => 3 * L < A * N ^ d), I N)
              + ((∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ 25 * L / (A * N ^ d) < |lam N|), I N)
                + (∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ ¬(25 * L / (A * N ^ d) < |lam N|)), I N)) := by rw [e2]
        _ = (∑ N ∈ D.filter (fun N => 3 * L < A * N ^ d), I N)
              + (∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ 25 * L / (A * N ^ d) < |lam N|), I N)
              + (∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ ¬(25 * L / (A * N ^ d) < |lam N|)), I N) := by ring
        _ ≤ (∑ N ∈ D.filter (fun N => 3 * L < A * N ^ d), 12 * C * L / (A * N ^ d))
              + (∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ 25 * L / (A * N ^ d) < |lam N|), 8 * C)
              + (∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ ¬(25 * L / (A * N ^ d) < |lam N|)),
                  C * (A * N ^ d) / (4 * L)) := by
              linarith [h0, h1, h2]
    have hP0 : (∑ N ∈ D.filter (fun N => 3 * L < A * N ^ d), 12 * C * L / (A * N ^ d)) ≤ 4 * C * G := by
      have hsum := Commons.Analysis.Sum.lacunary_finset_sum_inv_le hΛ d hd A hA D hDpos hlac (3 * L) (by positivity)
      rw [← hGdef] at hsum
      rw [show (∑ N ∈ D.filter (fun N => 3 * L < A * N ^ d), 12 * C * L / (A * N ^ d))
          = (12 * C * L) * ∑ N ∈ D.filter (fun N => 3 * L < A * N ^ d), (A * N ^ d)⁻¹ from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro N hN; rw [div_eq_mul_inv]]
      calc (12 * C * L) * ∑ N ∈ D.filter (fun N => 3 * L < A * N ^ d), (A * N ^ d)⁻¹
          ≤ (12 * C * L) * (G * (3 * L)⁻¹) := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 4 * C * G := by rw [inv_eq_one_div]; field_simp; try ring
    have hcount : ((D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ 25 * L / (A * N ^ d) < |lam N|)).card : ℝ)
        ≤ K * Real.log 2 / ((d:ℝ) * Real.log Λ) + 1 := by
      have hsub : D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ 25 * L / (A * N ^ d) < |lam N|)
          ⊆ D.filter (fun N => 25 * L / 2 ^ K < A * N ^ d ∧ A * N ^ d ≤ 3 * L) := by
        intro N hN
        rw [Finset.mem_filter] at hN ⊢
        obtain ⟨hND, h1, h2⟩ := hN
        have haN : 0 < A * N ^ d := mul_pos hA (pow_pos (hDpos N hND) d)
        refine ⟨hND, ?_, by linarith⟩
        have h2K : 0 < (2:ℝ) ^ K := Real.rpow_pos_of_pos (by norm_num) K
        rw [div_lt_iff₀ haN] at h2
        rw [div_lt_iff₀ h2K]
        calc 25 * L < |lam N| * (A * N ^ d) := h2
          _ ≤ 2 ^ K * (A * N ^ d) := mul_le_mul_of_nonneg_right (hlam N hND) haN.le
          _ = (A * N ^ d) * 2 ^ K := by ring
      by_cases hXY : 25 * L / 2 ^ K < 3 * L
      · have hc := Commons.Analysis.Sum.lacunary_finset_card_le hΛ d hd A hA D hDpos hlac
          (25 * L / 2 ^ K) (3 * L) (by positivity) hXY
        have hlog : Real.log (3 * L / (25 * L / 2 ^ K)) / Real.log (Λ ^ d)
            ≤ K * Real.log 2 / ((d:ℝ) * Real.log Λ) := by
          have h2K : (2:ℝ) ^ K ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) K).ne'
          have hYL_le : 3 * L / (25 * L / 2 ^ K) ≤ 2 ^ K := by
            rw [div_le_iff₀ (by positivity)]
            rw [show (2:ℝ) ^ K * (25 * L / 2 ^ K) = 25 * L by
              rw [mul_div_assoc', mul_div_cancel_left₀ (25 * L) h2K]]
            linarith [hL]
          have hpos1 : 0 < 3 * L / (25 * L / 2 ^ K) := by positivity
          have hlogbound : Real.log (3 * L / (25 * L / 2 ^ K)) ≤ K * Real.log 2 := by
            calc Real.log (3 * L / (25 * L / 2 ^ K)) ≤ Real.log (2 ^ K) :=
                  Real.log_le_log hpos1 hYL_le
              _ = K * Real.log 2 := Real.log_rpow (by norm_num) K
          rw [Real.log_pow]
          rw [div_le_div_iff₀ hdLpos hdLpos]
          nlinarith [hlogbound, hdLpos]
        calc ((D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ 25 * L / (A * N ^ d) < |lam N|)).card : ℝ)
            ≤ ((D.filter (fun N => 25 * L / 2 ^ K < A * N ^ d ∧ A * N ^ d ≤ 3 * L)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
          _ ≤ Real.log (3 * L / (25 * L / 2 ^ K)) / Real.log (Λ ^ d) + 1 := hc
          _ ≤ K * Real.log 2 / ((d:ℝ) * Real.log Λ) + 1 := by linarith [hlog]
      · push_neg at hXY
        have hempty : D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ 25 * L / (A * N ^ d) < |lam N|) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro N hN
          rw [Finset.mem_filter] at hN
          obtain ⟨hND, h1, h2⟩ := hN
          have haN : 0 < A * N ^ d := mul_pos hA (pow_pos (hDpos N hND) d)
          have h2K : 0 < (2:ℝ) ^ K := Real.rpow_pos_of_pos (by norm_num) K
          rw [div_lt_iff₀ haN] at h2
          have h1' : A * N ^ d ≤ 3 * L := not_lt.mp h1
          have h3K : 3 * (2:ℝ) ^ K ≤ 25 := by
            have h := hXY
            rw [le_div_iff₀ h2K] at h
            rw [show 3 * L * (2:ℝ) ^ K = 3 * (2:ℝ) ^ K * L by ring] at h
            exact le_of_mul_le_mul_right h hL
          have hle : |lam N| * (A * N ^ d) ≤ 25 * L := by
            calc |lam N| * (A * N ^ d) ≤ 2 ^ K * (A * N ^ d) :=
                  mul_le_mul_of_nonneg_right (hlam N hND) haN.le
              _ ≤ 2 ^ K * (3 * L) := by
                  apply mul_le_mul_of_nonneg_left h1' (by positivity)
              _ = 3 * (2:ℝ) ^ K * L := by ring
              _ ≤ 25 * L := mul_le_mul_of_nonneg_right h3K hL.le
          linarith [h2, hle]
        rw [hempty, Finset.card_empty]
        push_cast
        have : 0 < K * Real.log 2 / ((d:ℝ) * Real.log Λ) + 1 := by
          have := div_pos (mul_pos (lt_of_lt_of_le zero_lt_one hK) hlog2pos) hdLpos; linarith
        linarith
    have hP1 : (∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ 25 * L / (A * N ^ d) < |lam N|), 8 * C)
        ≤ 8 * C * (K * Real.log 2 / ((d:ℝ) * Real.log Λ) + 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcardnn : (0:ℝ) ≤ ((D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ 25*L/(A*N^d) < |lam N|)).card : ℝ) := by positivity
      nlinarith [hC0, hcount, hcardnn]
    have hP2 : (∑ N ∈ D.filter
          (fun N => ¬(3 * L < A * N ^ d) ∧ ¬(25 * L / (A * N ^ d) < |lam N|)),
            C * (A * N ^ d) / (4 * L)) ≤ 3 * C * G / 4 := by
      have hsub : D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ ¬(25 * L / (A * N ^ d) < |lam N|))
          ⊆ D.filter (fun N => A * N ^ d ≤ 3 * L) := by
        intro N hN
        rw [Finset.mem_filter] at hN ⊢
        exact ⟨hN.1, not_lt.mp hN.2.1⟩
      have hsum := lacunary_filtered_sum_le hΛ d hd A hA D hDpos hlac (Y := 3 * L) (by positivity)
      rw [← hGdef] at hsum
      calc (∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ ¬(25 * L / (A * N ^ d) < |lam N|)),
              C * (A * N ^ d) / (4 * L))
          ≤ ∑ N ∈ D.filter (fun N => A * N ^ d ≤ 3 * L), C * (A * N ^ d) / (4 * L) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun N hN _ =>
              div_nonneg (mul_nonneg hC0 (mul_nonneg hA.le
                (pow_nonneg (hDpos N (Finset.mem_filter.mp hN).1).le d))) (by positivity))
        _ = C / (4 * L) * ∑ N ∈ D.filter (fun N => A * N ^ d ≤ 3 * L), A * N ^ d := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro N hN; ring
        _ ≤ C / (4 * L) * (G * (3 * L)) := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 3 * C * G / 4 := by field_simp; try ring
    calc (∑ N ∈ D, I N)
        ≤ (∑ N ∈ D.filter (fun N => 3 * L < A * N ^ d), 12 * C * L / (A * N ^ d))
          + (∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ 25 * L / (A * N ^ d) < |lam N|), 8 * C)
          + (∑ N ∈ D.filter (fun N => ¬(3 * L < A * N ^ d) ∧ ¬(25 * L / (A * N ^ d) < |lam N|)),
              C * (A * N ^ d) / (4 * L)) := hbdd
      _ ≤ 4 * C * G + 8 * C * (K * Real.log 2 / ((d:ℝ) * Real.log Λ) + 1) + 3 * C * G / 4 := by
            linarith [hP0, hP1, hP2]
      _ ≤ (C * ((19/4) * G + 8 * (Real.log 2 / ((d:ℝ) * Real.log Λ) + 1)) + 1) * K := by
            have hA : 0 ≤ (19/4) * C * G := by positivity
            have hB : 0 ≤ 8 * C := by positivity
            have hK1 : 0 ≤ K - 1 := by linarith
            have hK0 : 0 ≤ K := by linarith
            have key : (C * ((19/4) * G + 8 * (Real.log 2 / ((d:ℝ) * Real.log Λ) + 1)) + 1) * K
                - (4 * C * G + 8 * C * (K * Real.log 2 / ((d:ℝ) * Real.log Λ) + 1) + 3 * C * G / 4)
                = (19/4) * C * G * (K - 1) + 8 * C * (K - 1) + K := by ring
            linarith [key, mul_nonneg hA hK1, mul_nonneg hB hK1, hK0]

end Commons.Analysis.CalderonZygmund
