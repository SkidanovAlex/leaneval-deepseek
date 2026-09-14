import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Asymptotics

open Filter Set MeasureTheory
open scoped Topology

/-- `t ↦ -t⁻¹` is an antiderivative of `t ↦ (t²)⁻¹` on intervals contained in `(0,∞)`. -/
private theorem integral_inv_sq_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, (t ^ 2)⁻¹ = a⁻¹ - b⁻¹ := by
  have hderiv : deriv (fun x : ℝ => -(x⁻¹)) = fun x => (x ^ 2)⁻¹ := by
    funext x
    simp [deriv_inv]
  have hdiff : ∀ x ∈ uIcc a b, DifferentiableAt ℝ (fun x : ℝ => -(x⁻¹)) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact (differentiableAt_inv_iff.mpr (ne_of_gt (lt_of_lt_of_le ha hx.1))).neg
  have hcont : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (uIcc a b) := by
    apply ContinuousOn.inv₀
    · exact (continuous_id.pow 2).continuousOn
    · intro x hx
      rw [uIcc_of_le hab] at hx
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hx.1))
  rw [intervalIntegral.integral_deriv_eq_sub' (fun x : ℝ => -(x⁻¹)) hderiv hdiff hcont]
  ring

/-- Integral of `K / t²` over `[a,b]` with `0 < a ≤ b`. -/
private theorem integral_const_div_sq {a b K : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, K / t ^ 2 = K * (a⁻¹ - b⁻¹) := by
  rw [show (fun t : ℝ => K / t ^ 2) = fun t => K * (t ^ 2)⁻¹ by
    funext t; rw [div_eq_mul_inv]]
  rw [intervalIntegral.integral_const_mul, integral_inv_sq_of_pos ha hab]

theorem exists_tendsto_atTop_of_eventually_norm_le_inv_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f f' : ℝ → E} {a K : ℝ}
    (ha : 0 < a) (hf : ∀ t ∈ Set.Ici a, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Ici a))
    (hbd : ∀ᶠ t : ℝ in Filter.atTop, ‖f' t‖ ≤ K / t ^ 2) :
    ∃ l : E, Filter.Tendsto f Filter.atTop (𝓝 l) := by
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.mp hbd
  set c : ℝ := max b₀ (max a 1) with hc_def
  have hc_b₀ : b₀ ≤ c := le_max_left b₀ (max a 1)
  have hc_a : a ≤ c := le_trans (le_max_left a 1) (le_max_right b₀ (max a 1))
  have hc_1 : 1 ≤ c := le_trans (le_max_right a 1) (le_max_right b₀ (max a 1))
  have hc_pos : 0 < c := lt_of_lt_of_le one_pos hc_1
  have hbc : ∀ t : ℝ, c ≤ t → ‖f' t‖ ≤ K / t ^ 2 := fun t ht => hb₀ t (le_trans hc_b₀ ht)
  -- the constant `K` is nonnegative
  have hK : 0 ≤ K := by
    have hc2pos : 0 < c ^ 2 := pow_pos hc_pos 2
    have h1 : 0 ≤ K / c ^ 2 := le_trans (norm_nonneg (f' c)) (hbc c le_rfl)
    have h2 : 0 ≤ (K / c ^ 2) * c ^ 2 := mul_nonneg h1 (le_of_lt hc2pos)
    rwa [div_mul_cancel₀ _ (ne_of_gt hc2pos)] at h2
  -- key displacement estimate
  have hbound : ∀ {u v : ℝ}, c ≤ u → c ≤ v → u ≤ v → ‖f v - f u‖ ≤ K / u := by
    intro u v hu hv huv
    have hau : a ≤ u := le_trans hc_a hu
    have hu_pos : 0 < u := lt_of_lt_of_le one_pos (le_trans hc_1 hu)
    have hsub : uIcc u v ⊆ Set.Ici a := by
      intro x hx
      rw [uIcc_of_le huv] at hx
      exact le_trans hau hx.1
    have hfint : IntervalIntegrable f' volume u v := (hf'.mono hsub).intervalIntegrable
    have hFTC : ∫ t in u..v, f' t = f v - f u :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hf x (hsub hx)) hfint
    have hnorm : ‖∫ t in u..v, f' t‖ ≤ ∫ t in u..v, ‖f' t‖ :=
      intervalIntegral.norm_integral_le_integral_norm huv
    have hFi : IntervalIntegrable (fun t : ℝ => ‖f' t‖) volume u v :=
      ((hf'.norm).mono hsub).intervalIntegrable
    have hKi : IntervalIntegrable (fun t : ℝ => K / t ^ 2) volume u v := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const (continuous_id.pow 2).continuousOn
      intro x hx
      rw [uIcc_of_le huv] at hx
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hu_pos hx.1))
    have hmono : ∫ t in u..v, ‖f' t‖ ≤ ∫ t in u..v, K / t ^ 2 :=
      intervalIntegral.integral_mono_on huv hFi hKi (fun x hx => hbc x (le_trans hu hx.1))
    have hInt : ∫ t in u..v, K / t ^ 2 = K * (u⁻¹ - v⁻¹) := integral_const_div_sq hu_pos huv
    calc ‖f v - f u‖ = ‖∫ t in u..v, f' t‖ := by rw [hFTC]
      _ ≤ ∫ t in u..v, ‖f' t‖ := hnorm
      _ ≤ ∫ t in u..v, K / t ^ 2 := hmono
      _ = K * (u⁻¹ - v⁻¹) := hInt
      _ ≤ K / u := by
        have hvu : v⁻¹ ≤ u⁻¹ := inv_anti₀ hu_pos huv
        have hle : u⁻¹ - v⁻¹ ≤ u⁻¹ := by
          have : 0 ≤ v⁻¹ := inv_nonneg.mpr (le_trans (le_of_lt hu_pos) huv)
          linarith
        have hmul : K * (u⁻¹ - v⁻¹) ≤ K * u⁻¹ := mul_le_mul_of_nonneg_left hle hK
        rw [div_eq_mul_inv]
        exact hmul
  -- `f` is Cauchy along `atTop`
  have hcauchy : Cauchy (map f atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    refine ⟨f '' (Set.Ici (max c (K / ε + 1))), image_mem_map (Ici_mem_atTop _), ?_⟩
    intro x hx y hy
    rcases hx with ⟨u, hu, rfl⟩
    rcases hy with ⟨v, hv, rfl⟩
    have hcu : c ≤ u := le_trans (le_max_left _ _) hu
    have hcv : c ≤ v := le_trans (le_max_left _ _) hv
    have key : ∀ w : ℝ, max c (K / ε + 1) ≤ w → K / w < ε := by
      intro w hw
      have hwpos : 0 < w :=
        lt_of_lt_of_le one_pos (le_trans hc_1 (le_trans (le_max_left _ _) hw))
      rw [div_lt_iff₀ hwpos]
      have hwK : K / ε < w :=
        lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hw)
      have hlt := mul_lt_mul_of_pos_left hwK hε
      have heK : ε * (K / ε) = K := by
        rw [mul_comm ε (K / ε), div_mul_cancel₀ K (ne_of_gt hε)]
      rwa [heK] at hlt
    have hku : K / u < ε := key u hu
    have hkv : K / v < ε := key v hv
    rw [dist_eq_norm]
    rcases le_total u v with huv | hvu
    · rw [norm_sub_rev]
      exact lt_of_le_of_lt (hbound hcu hcv huv) hku
    · exact lt_of_le_of_lt (hbound hcv hcu hvu) hkv
  exact (cauchy_map_iff_exists_tendsto (l := atTop)).mp hcauchy

end Commons.Analysis.Asymptotics