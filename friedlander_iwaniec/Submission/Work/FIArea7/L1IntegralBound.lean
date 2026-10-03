import Mathlib

namespace Work.FIArea7

open MeasureTheory Real Set

/-- Integral of `c / t^2` over `(T, ∞)`: `c / T` when `T > 0`. -/
lemma L1_far_integral (c T : ℝ) (hT : 0 < T) :
    ∫ t in Set.Ioi T, c / t^2 = c * (1/T) := by
  have h1 : ∫ t in Set.Ioi T, c / t^2 = ∫ t in Set.Ioi T, c * t^(-2:ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    show c / t^2 = c * t^(-2:ℝ)
    rw [Real.rpow_neg (le_of_lt (hT.trans ht)), Real.rpow_two, div_eq_mul_inv]
  rw [h1, integral_const_mul]
  congr 1
  rw [integral_Ioi_rpow_of_lt (by norm_num) hT]
  rw [show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  ring

/-- Integrability of `c / t^2` on `(T, ∞)`. -/
lemma L1_far_integrable (c T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => c / t^2) (Set.Ioi T) := by
  have h1 : IntegrableOn (fun t : ℝ => t^(-2:ℝ)) (Set.Ioi T) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hT
  have h2 : IntegrableOn (fun t : ℝ => c * t^(-2:ℝ)) (Set.Ioi T) := h1.integrable.const_mul c
  refine h2.congr_fun ?_ measurableSet_Ioi
  intro t ht
  show c * t^(-2:ℝ) = c / t^2
  rw [Real.rpow_neg (le_of_lt (hT.trans ht)), Real.rpow_two, div_eq_mul_inv]

/-- Integrability of `min (2λ) (1/(π t))` on `(0, T]`. -/
lemma L1_near_integrable (lam T : ℝ) (hlam : 0 < lam) :
    IntegrableOn (fun u : ℝ => min (2*lam) (1/(Real.pi*u))) (Set.Ioc 0 T) := by
  refine IntegrableOn.of_bound (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) ?_ (2*lam) ?_
  · exact (by measurability : Measurable (fun u : ℝ => min (2*lam) (1/(Real.pi*u)))).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    apply Filter.Eventually.of_forall
    intro u hu
    rw [Set.mem_Ioc] at hu
    have hupos : 0 < Real.pi * u := by nlinarith [Real.pi_pos, hu.1]
    have hge : (0:ℝ) ≤ min (2*lam) (1/(Real.pi*u)) :=
      le_min (by positivity) (le_of_lt (one_div_pos.mpr hupos))
    rw [norm_eq_abs, abs_of_nonneg hge]
    exact min_le_left _ _

/-- The near integral: for `a = 1/(2πλ) ≤ T`, `∫_{(0,T]} min (2λ) (1/(π t)) = 2λa + (1/π)log(T/a)`. -/
lemma L1_near_integral (lam T a : ℝ) (hlam : 0 < lam) (hT : 0 < T) (ha : a = 1/(2*Real.pi*lam))
    (haT : a ≤ T) :
    ∫ u in Set.Ioc 0 T, min (2*lam) (1/(Real.pi*u))
      = 2*lam*a + (1/Real.pi)*Real.log (T/a) := by
  have hπ := Real.pi_pos
  have ha0 : 0 < a := by rw [ha]; positivity
  have hunion : Set.Ioc (0:ℝ) T = Set.Ioc 0 a ∪ Set.Ioc a T :=
    (Set.Ioc_union_Ioc_eq_Ioc (le_of_lt ha0) haT).symm
  have hdisj : Disjoint (Set.Ioc (0:ℝ) a) (Set.Ioc a T) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_Ioc] at hx hx'
    linarith [hx.2, hx'.1]
  have hcongr1 : ∀ u ∈ Set.Ioc (0:ℝ) a, min (2*lam) (1/(Real.pi*u)) = 2*lam := by
    intro u hu
    rw [Set.mem_Ioc] at hu
    obtain ⟨hu0, hua⟩ := hu
    apply min_eq_left
    have hua' : u ≤ 1/(2*Real.pi*lam) := by rwa [ha] at hua
    have h1 := (le_div_iff₀ (show (0:ℝ) < 2*Real.pi*lam by positivity)).mp hua'
    rw [le_div_iff₀ (show (0:ℝ) < Real.pi*u by positivity)]
    nlinarith [h1, hπ, hlam, hu0]
  have hcongr2 : ∀ u ∈ Set.Ioc a T, min (2*lam) (1/(Real.pi*u)) = 1/(Real.pi*u) := by
    intro u hu
    rw [Set.mem_Ioc] at hu
    obtain ⟨hau, huT⟩ := hu
    apply min_eq_right
    calc 1/(Real.pi*u) ≤ 1/(Real.pi*a) := by
            apply one_div_le_one_div_of_le (show (0:ℝ) < Real.pi*a by positivity)
            nlinarith [hau, hπ]
         _ = 2*lam := by rw [ha]; field_simp
  have hint1 : IntegrableOn (fun u => min (2*lam) (1/(Real.pi*u))) (Set.Ioc 0 a) := by
    refine IntegrableOn.congr_fun (f := fun _ : ℝ => 2*lam) ?_ ?_ measurableSet_Ioc
    · exact integrableOn_const (s := Set.Ioc (0:ℝ) a) (C := 2*lam)
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    · intro u hu; exact (hcongr1 u hu).symm
  have hint2 : IntegrableOn (fun u => min (2*lam) (1/(Real.pi*u))) (Set.Ioc a T) := by
    refine IntegrableOn.congr_fun (f := fun u : ℝ => 1/(Real.pi*u)) ?_ ?_ measurableSet_Ioc
    · refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set Set.Ioc_subset_Icc_self
      apply ContinuousOn.div continuousOn_const (continuousOn_const.mul continuousOn_id)
      intro u hu
      have : 0 < Real.pi * u := by nlinarith [Real.pi_pos, ha0, hu.1]
      exact ne_of_gt this
    · intro u hu; exact (hcongr2 u hu).symm
  rw [hunion, setIntegral_union hdisj measurableSet_Ioc hint1 hint2]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr1, setIntegral_congr_fun measurableSet_Ioc hcongr2]
  rw [setIntegral_const]
  simp only [Measure.real, smul_eq_mul]
  rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ a - 0)]
  have hB1 : ∫ u in Set.Ioc a T, 1/(Real.pi*u) = ∫ u in Set.Ioc a T, (1/Real.pi) * u⁻¹ := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    show 1/(Real.pi*u) = (1/Real.pi) * u⁻¹
    rw [one_div, mul_inv, one_div]
  rw [hB1, integral_const_mul, ← intervalIntegral.integral_of_le haT, integral_inv_of_pos ha0 hT]
  ring

/-- An integral bound assembled from three pointwise estimates: if `0 ≤ B`, `B ≤ 2λ`,
`B t ≤ |sin(2πλt)|/(π|t|)` for `t ≠ 0`, and `B t ≤ 8/(15π²ε t²)` for `|t| ≥ 8/(15π ε)`, then
`∫ B ≤ (2/π)(2 + log (16λ/(15ε)))`.

Proof route (the reviewer's): set `T = 8/(15πε)`. On `|t| ≥ T` use the `t^{-2}` bound, whose
integral is `2/π`; on `|t| ≤ T` use `|sin(2πλt)|/(π|t|)` and `|sin v| ≤ min(1,v)` to write it as
at most `(2/π)(1 + log(2πλT))`; case split on `Integrable B` (if `B` is not integrable the
Bochner integral is `0` and the RHS is positive since `16λ/(15ε) ≥ 16/15 > 1`). -/
theorem L1IntegralBound (lam eps : ℝ) (hε : 0 < eps) (hle : eps ≤ lam) (B : ℝ → ℝ)
    (hB0 : ∀ t, 0 ≤ B t)
    (hB1 : ∀ t, B t ≤ 2 * lam)
    (hB2 : ∀ t, t ≠ 0 → B t ≤ |Real.sin (2 * Real.pi * lam * t)| / (Real.pi * |t|))
    (hB3 : ∀ t, 8 / (15 * Real.pi * eps) ≤ |t| →
      B t ≤ 8 / (15 * Real.pi ^ 2 * eps * t ^ 2)) :
    ∫ t : ℝ, B t ≤ (2 / Real.pi) * (2 + Real.log (16 * lam / (15 * eps))) := by
  have hπ := Real.pi_pos
  have hlam : 0 < lam := lt_of_lt_of_le hε hle
  set T : ℝ := 8/(15*Real.pi*eps) with hTdef
  set c : ℝ := 8/(15*Real.pi^2*eps) with hcdef
  set a : ℝ := 1/(2*Real.pi*lam) with hadef
  have hT : 0 < T := by rw [hTdef]; positivity
  have hc : 0 < c := by rw [hcdef]; positivity
  have ha : 0 < a := by rw [hadef]; positivity
  have haT : a ≤ T := by
    rw [hadef, hTdef, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hle, hε, Real.pi_pos]
  have hlog : T/a = 16*lam/(15*eps) := by
    rw [hadef, hTdef]; field_simp; ring
  set G : ℝ → ℝ := (fun u => if u ≤ T then min (2*lam) (1/(Real.pi*u)) else c/u^2) with hGdef
  set g : ℝ → ℝ := (fun t => G |t|) with hgdef
  have hGmin : ∀ u ∈ Set.Ioc (0:ℝ) T, G u = min (2*lam) (1/(Real.pi*u)) := by
    intro u hu
    show (if u ≤ T then min (2*lam) (1/(Real.pi*u)) else c/u^2) = min (2*lam) (1/(Real.pi*u))
    rw [if_pos (Set.mem_Ioc.mp hu).2]
  have hGfar : ∀ u ∈ Set.Ioi T, G u = c/u^2 := by
    intro u hu
    show (if u ≤ T then min (2*lam) (1/(Real.pi*u)) else c/u^2) = c/u^2
    rw [if_neg (not_le.mpr (Set.mem_Ioi.mp hu))]
  have hIntGIoc : IntegrableOn G (Set.Ioc 0 T) := by
    refine (L1_near_integrable lam T hlam).congr_fun ?_ measurableSet_Ioc
    intro u hu
    show min (2*lam) (1/(Real.pi*u)) = (if u ≤ T then min (2*lam) (1/(Real.pi*u)) else c/u^2)
    rw [if_pos (Set.mem_Ioc.mp hu).2]
  have hIntGIoi : IntegrableOn G (Set.Ioi T) := by
    refine (L1_far_integrable c T hT).congr_fun ?_ measurableSet_Ioi
    intro u hu
    show c/u^2 = (if u ≤ T then min (2*lam) (1/(Real.pi*u)) else c/u^2)
    rw [if_neg (not_le.mpr (Set.mem_Ioi.mp hu))]
  have hunion2 : Set.Ioc (0:ℝ) T ∪ Set.Ioi T = Set.Ioi 0 := by
    ext x; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact h1
      · exact lt_trans hT h3
    · intro h
      by_cases hx : x ≤ T
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (lt_of_not_ge hx)
  have hdisj2 : Disjoint (Set.Ioc (0:ℝ) T) (Set.Ioi T) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_Ioc] at hx; rw [Set.mem_Ioi] at hx'
    linarith [hx.2, hx']
  have hIntG0 : IntegrableOn G (Set.Ioi 0) := by
    rw [← hunion2]; exact hIntGIoc.union hIntGIoi
  have hIntgIoi : IntegrableOn g (Set.Ioi 0) := by
    refine hIntG0.congr_fun ?_ measurableSet_Ioi
    intro t ht
    show G t = G |t|
    rw [abs_of_pos (Set.mem_Ioi.mp ht)]
  have hIntgIic : IntegrableOn g (Set.Iic 0) := by
    have hGIci : IntegrableOn G (Set.Ici 0) := (integrableOn_Ici_iff_integrableOn_Ioi).mpr hIntG0
    have hcomp : IntegrableOn (fun x : ℝ => G (-x)) (Set.Iic 0) :=
      (show IntegrableOn G (Set.Ici (-0)) by simpa using hGIci).comp_neg_Iic
    refine hcomp.congr_fun ?_ measurableSet_Iic
    intro t ht
    show G (-t) = G |t|
    rw [abs_of_nonpos (Set.mem_Iic.mp ht)]
  have hIntg : Integrable g := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0:ℝ))]
    exact hIntgIic.union hIntgIoi
  have hBt : ∀ t ≠ 0, B t ≤ g t := by
    intro t ht
    show B t ≤ (if |t| ≤ T then min (2*lam) (1/(Real.pi*|t|)) else c/|t|^2)
    by_cases hcase : |t| ≤ T
    · rw [if_pos hcase]
      refine le_min (hB1 t) ?_
      calc B t ≤ |Real.sin (2*Real.pi*lam*t)| / (Real.pi*|t|) := hB2 t ht
        _ ≤ 1 / (Real.pi*|t|) := by
              apply div_le_div_of_nonneg_right (abs_sin_le_one _) (by positivity)
    · rw [if_neg hcase]
      rw [hcdef, div_div, sq_abs]
      exact hB3 t (by
        have hh : T < |t| := lt_of_not_ge hcase
        rw [hTdef] at hh; exact le_of_lt hh)
  have hBle : B ≤ᵐ[volume] g := by
    show ∀ᵐ t ∂volume, B t ≤ g t
    rw [MeasureTheory.ae_iff]
    apply measure_mono_null _ (by simp : volume ({0} : Set ℝ) = 0)
    intro t ht
    by_contra hne
    exact ht (hBt t hne)
  have hgval : ∫ t, g t = (2/Real.pi)*(2 + Real.log (16*lam/(15*eps))) := by
    have hcomp : ∫ t, g t = 2 * ∫ u in Set.Ioi 0, G u := by
      show ∫ t, G |t| = 2 * ∫ u in Set.Ioi 0, G u
      rw [integral_comp_abs]
    have hsplit : ∫ u in Set.Ioi 0, G u
        = (∫ u in Set.Ioc 0 T, G u) + (∫ u in Set.Ioi T, G u) := by
      rw [← hunion2]
      rw [setIntegral_union hdisj2 measurableSet_Ioi hIntGIoc hIntGIoi]
    have hIoc : ∫ u in Set.Ioc 0 T, G u = 2*lam*a + (1/Real.pi)*Real.log (T/a) := by
      rw [setIntegral_congr_fun measurableSet_Ioc hGmin]
      exact L1_near_integral lam T a hlam hT hadef haT
    have hIoi : ∫ u in Set.Ioi T, G u = c * (1/T) := by
      rw [setIntegral_congr_fun measurableSet_Ioi hGfar]
      exact L1_far_integral c T hT
    rw [hcomp, hsplit, hIoc, hIoi, hlog]
    rw [hadef, hcdef, hTdef]
    field_simp
    ring
  calc ∫ t, B t ≤ ∫ t, g t := integral_mono_of_nonneg (Filter.Eventually.of_forall hB0) hIntg hBle
    _ = (2/Real.pi)*(2 + Real.log (16*lam/(15*eps))) := hgval

end Work.FIArea7
