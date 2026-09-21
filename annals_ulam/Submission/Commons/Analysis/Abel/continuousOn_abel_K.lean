import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Commons.Analysis.Abel.hasDerivAt_invSqrt_weighted_affine
import Submission.Commons.Analysis.Abel.volterra_double_integral

set_option linter.unusedVariables false

open scoped Interval Topology
open Set Filter MeasureTheory
noncomputable section

namespace Commons.Analysis.Abel

lemma intervalIntegral_abel_subst
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x b : ℝ} (hxb : x ≤ b) (K : ℝ → ℝ → E) :
    ∫ σ in x..b, (Real.sqrt (σ - x))⁻¹ • K x σ =
      (2 * Real.sqrt (b - x)) • ∫ u in (0 : ℝ)..1, K x (x + (b - x) * u ^ 2) := by
  let f : ℝ → ℝ := fun u => x + (b - x) * u^2
  let f' : ℝ → ℝ := fun u => 2 * (b - x) * u
  let g : ℝ → E := fun σ => (Real.sqrt (σ - x))⁻¹ • K x σ
  have hf_cont : ContinuousOn f [[(0:ℝ), 1]] := by
    dsimp [f]
    fun_prop
  have hf_deriv : ∀ u ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), HasDerivAt f (f' u) u := by
    intro u hu
    have huI : u ∈ Ioo (0:ℝ) 1 := by
      simpa [min_eq_left zero_le_one, max_eq_right zero_le_one] using hu
    dsimp [f, f']
    have hsq : HasDerivAt (fun t : ℝ => t^2) (2 * u) u := by
      have h := hasDerivAt_pow (n := 2) (x := u)
      simpa [pow_one] using h
    have hmul := hsq.const_mul (b - x)
    have hderiv_val : (b - x) * (2 * u) = 2 * (b - x) * u := by ring
    have hmul' := hmul.congr_deriv hderiv_val
    have hadd := hmul'.const_add x
    simpa [add_comm, add_left_comm, add_assoc] using hadd
  have hf'_nonneg : ∀ u ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), 0 ≤ f' u := by
    intro u hu
    have huI : u ∈ Ioo (0:ℝ) 1 := by
      simpa [min_eq_left zero_le_one, max_eq_right zero_le_one] using hu
    dsimp [f']
    exact mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.mpr hxb)) (le_of_lt huI.1)
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (f := f) (f' := f') (g := g) (a := (0:ℝ)) (b := 1) hf_cont hf_deriv hf'_nonneg
  have hcongr : (∫ u in (0:ℝ)..1, f' u • (g ∘ f) u) =
      ∫ u in (0:ℝ)..1, (2 * Real.sqrt (b - x)) • K x (x + (b - x) * u^2) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (show (0:ℝ) ≤ 1 by norm_num)
    intro u hu
    have hu0 : 0 < u := hu.1
    have hu1 : u < 1 := hu.2
    have hb_nonneg : 0 ≤ b - x := sub_nonneg.mpr hxb
    by_cases hbx : b = x
    · have hfx : f u = x := by
        dsimp [f]; rw [hbx]; ring
      have hright_zero : (2 * Real.sqrt (b - x)) • K x (x + (b - x) * u^2) = 0 := by
        rw [hbx]; simp
      dsimp [f', g]
      rw [hfx, hright_zero]
      simp [hbx]
    · have hsqrt_pos : 0 < Real.sqrt (b - x) :=
        Real.sqrt_pos_of_pos (sub_pos.mpr (lt_of_le_of_ne hxb (Ne.symm hbx)))
      have hpos : 0 < Real.sqrt (b - x) * u := mul_pos hsqrt_pos hu0
      have hden_ne : Real.sqrt (b - x) * u ≠ 0 := ne_of_gt hpos
      have hsqrt_sq : Real.sqrt ((b - x) * u^2) = Real.sqrt (b - x) * u := by
        rw [Real.sqrt_mul hb_nonneg (u^2), Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hu0)]
      have hscalar : (2 * (b - x) * u) * (Real.sqrt (b - x) * u)⁻¹ = 2 * Real.sqrt (b - x) := by
        have hsqrt_ne : Real.sqrt (b - x) ≠ 0 := ne_of_gt hsqrt_pos
        have h1 : u * (Real.sqrt (b - x) * u)⁻¹ = (Real.sqrt (b - x))⁻¹ := by
          field_simp [hden_ne, hsqrt_ne]
        calc
          (2 * (b - x) * u) * (Real.sqrt (b - x) * u)⁻¹
              = (2 * (b - x)) * (u * (Real.sqrt (b - x) * u)⁻¹) := by ring
          _ = (2 * (b - x)) * (Real.sqrt (b - x))⁻¹ := by rw [h1]
          _ = 2 * Real.sqrt (b - x) := by
            field_simp [hsqrt_ne]
            rw [Real.sq_sqrt hb_nonneg]
      have harg : x + (b - x) * u^2 - x = (b - x) * u^2 := by ring
      calc
        f' u • (g ∘ f) u
            = (2 * (b - x) * u) • ((Real.sqrt ((b - x) * u^2))⁻¹ • K x (x + (b - x) * u^2)) := by
                dsimp [f', g, f]
                rw [harg]
        _ = (2 * (b - x) * u) • (((Real.sqrt (b - x) * u)⁻¹) • K x (x + (b - x) * u^2)) := by
                rw [hsqrt_sq]
        _ = ((2 * (b - x) * u) * (Real.sqrt (b - x) * u)⁻¹) • K x (x + (b - x) * u^2) := by
                rw [smul_smul]
        _ = (2 * Real.sqrt (b - x)) • K x (x + (b - x) * u^2) := by
                rw [hscalar]
  calc
    ∫ σ in x..b, (Real.sqrt (σ - x))⁻¹ • K x σ = ∫ σ in f 0..f 1, g σ := by
      simp [f, g]
    _ = ∫ u in (0:ℝ)..1, f' u • (g ∘ f) u := by
      rw [hsub]
    _ = ∫ u in (0:ℝ)..1, (2 * Real.sqrt (b - x)) • K x (x + (b - x) * u^2) := hcongr
    _ = (2 * Real.sqrt (b - x)) • ∫ u in (0:ℝ)..1, K x (x + (b - x) * u^2) := by
      rw [intervalIntegral.integral_smul]

lemma continuousOn_intervalIntegral_of_continuousOn_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} (hs : IsCompact s)
    {A B : ℝ} (hAB : A ≤ B)
    {F : ℝ → ℝ → E}
    (hF_cont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (s ×ˢ Set.uIcc A B)) :
    ContinuousOn (fun x => ∫ t in A..B, F x t) s := by
  let G : ℝ × ℝ → E := fun p => F p.1 p.2
  have hG_cont : ContinuousOn G (s ×ˢ Set.uIcc A B) := hF_cont
  have hprod_compact : IsCompact (s ×ˢ Set.uIcc A B) := hs.prod isCompact_uIcc
  obtain ⟨C0, hC0⟩ := hprod_compact.exists_bound_of_continuousOn hG_cont
  let C : ℝ := max C0 0
  have hC_nonneg : 0 ≤ C := le_max_right _ _
  have hC_bound : ∀ p ∈ s ×ˢ Set.uIcc A B, ‖G p‖ ≤ C := by
    intro p hp
    exact le_trans (hC0 p hp) (le_max_left _ _)
  have hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) (volume.restrict (Ι A B)) := by
    intro x hx
    have hcont_t : ContinuousOn (fun t : ℝ => F x t) (Set.uIcc A B) := by
      have hpath_cont : ContinuousOn (fun t : ℝ => (x, t)) (Set.uIcc A B) :=
        (continuousOn_const (s := Set.uIcc A B) (c := x)).prodMk continuousOn_id
      have hpath_mem : Set.MapsTo (fun t : ℝ => (x, t)) (Set.uIcc A B) (s ×ˢ Set.uIcc A B) := by
        intro t ht; exact ⟨hx, ht⟩
      exact hG_cont.comp' hpath_cont hpath_mem
    exact hcont_t.aestronglyMeasurable_of_subset_isCompact isCompact_uIcc measurableSet_uIoc
      Set.uIoc_subset_uIcc
  have h_bound : ∀ x ∈ s, ∀ᵐ t ∂(volume.restrict (Ι A B)), ‖F x t‖ ≤ C := by
    intro x hx
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with t ht
    have ht' : t ∈ Set.uIcc A B := Set.uIoc_subset_uIcc ht
    exact hC_bound (x, t) ⟨hx, ht'⟩
  have h_bound_int : Integrable (fun _ : ℝ => C) (volume.restrict (Ι A B)) := by
    have hfin : volume (Ι A B) ≠ ⊤ := by
      have hlt := measure_Ioc_lt_top (μ := volume) (a := A) (b := B)
      simpa [uIoc_of_le hAB] using hlt.ne
    exact integrableOn_const (μ := volume) (s := Ι A B) (C := C) hfin
  have h_cont_ae : ∀ᵐ t ∂(volume.restrict (Ι A B)), ContinuousOn (fun x => F x t) s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with t ht
    have ht' : t ∈ Set.uIcc A B := Set.uIoc_subset_uIcc ht
    have hcont_x : ContinuousOn (fun x : ℝ => F x t) s := by
      have hpath_cont : ContinuousOn (fun x : ℝ => (x, t)) s :=
        continuousOn_id.prodMk (continuousOn_const (s := s) (c := t))
      have hpath_mem : Set.MapsTo (fun x : ℝ => (x, t)) s (s ×ˢ Set.uIcc A B) := by
        intro x hx; exact ⟨hx, ht'⟩
      exact hG_cont.comp' hpath_cont hpath_mem
    exact hcont_x
  have hdom := continuousOn_of_dominated (μ := volume.restrict (Ι A B))
    (F := F) (bound := fun _ : ℝ => C) (s := s)
    hF_meas h_bound h_bound_int h_cont_ae
  have hfun' : ∀ x, ∫ t, F x t ∂(volume.restrict (Ι A B)) = ∫ t in A..B, F x t := by
    intro x
    rw [intervalIntegral.integral_of_le hAB, uIoc_of_le hAB]
  exact hdom.congr (by intro x hx; exact (hfun' x).symm)

lemma continuousOn_abel_K
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b)) :
    ContinuousOn (fun x : ℝ => ∫ σ in x..b, (Real.sqrt (σ - x))⁻¹ • K x σ) (Set.Icc a b) := by
  let F : ℝ → ℝ → E := fun x u => K x (x + (b - x) * u^2)
  have hK_continuous : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b) :=
    hK_cont.continuousOn
  have hF_cont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc a b ×ˢ Set.uIcc (0:ℝ) 1) := by
    dsimp [F]
    have hpath_cont : ContinuousOn (fun p : ℝ × ℝ => (p.1, p.1 + (b - p.1) * p.2^2))
        (Set.Icc a b ×ˢ Set.uIcc (0:ℝ) 1) := by
      fun_prop
    have hpath_mem : Set.MapsTo (fun p : ℝ × ℝ => (p.1, p.1 + (b - p.1) * p.2^2))
        (Set.Icc a b ×ˢ Set.uIcc (0:ℝ) 1) (Set.Icc a b ×ˢ Set.Icc a b) := by
      intro p hp
      have hx : p.1 ∈ Set.Icc a b := hp.1
      have hu : p.2 ∈ Set.uIcc (0:ℝ) 1 := hp.2
      have hu' : p.2 ∈ Set.Icc (0:ℝ) 1 := by
        simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hu
      have hu0 : 0 ≤ p.2 := hu'.1
      have hu1 : p.2 ≤ 1 := hu'.2
      have hnonneg : 0 ≤ (b - p.1) * p.2^2 := mul_nonneg (sub_nonneg.mpr hx.2) (sq_nonneg p.2)
      have hy_lower : p.1 ≤ p.1 + (b - p.1) * p.2^2 := by linarith
      have hu_le_one : p.2^2 ≤ 1 := by nlinarith [sq_nonneg (1 - p.2)]
      have hmul : (b - p.1) * p.2^2 ≤ (b - p.1) * 1 :=
        mul_le_mul_of_nonneg_left hu_le_one (sub_nonneg.mpr hx.2)
      have hy_upper : p.1 + (b - p.1) * p.2^2 ≤ b := by nlinarith
      constructor
      · exact hx
      · constructor
        · exact le_trans hx.1 hy_lower
        · exact hy_upper
    exact hK_continuous.comp' hpath_cont hpath_mem
  have h_int_cont : ContinuousOn (fun x => ∫ u in (0:ℝ)..1, F x u) (Set.Icc a b) := by
    exact continuousOn_intervalIntegral_of_continuousOn_compact (s := Set.Icc a b) isCompact_Icc
      (A := (0:ℝ)) (B := 1) (show (0:ℝ) ≤ 1 by norm_num) hF_cont
  have hsqrt_cont : ContinuousOn (fun x : ℝ => 2 * Real.sqrt (b - x)) (Set.Icc a b) := by
    fun_prop
  have hformula_cont : ContinuousOn
      (fun x => (2 * Real.sqrt (b - x)) • ∫ u in (0:ℝ)..1, F x u) (Set.Icc a b) := by
    exact hsqrt_cont.smul h_int_cont
  exact hformula_cont.congr (by
    intro x hx
    have hx_le_b : x ≤ b := hx.2
    simpa [F] using intervalIntegral_abel_subst (x := x) (b := b) hx_le_b K)

end Commons.Analysis.Abel