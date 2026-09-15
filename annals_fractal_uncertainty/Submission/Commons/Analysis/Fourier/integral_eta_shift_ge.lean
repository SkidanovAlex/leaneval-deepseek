import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace Commons.Analysis.Fourier

open MeasureTheory

theorem integral_eta_shift_ge (d : ℕ) {c₂ : ℝ}
    (F Ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (hF : MeasureTheory.MemLp F 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hΨ : MeasureTheory.MemLp Ψ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hΨge : c₂ ^ 2 ≤ ∫ x in {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, -1 ≤ x i ∧ x i ≤ 1}, ‖Ψ x‖ ^ 2) :
    c₂ ^ 2 * ∫ ξ in {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, -1 ≤ x i ∧ x i ≤ 1}, ‖F ξ‖ ^ 2
      ≤ ∫ η in {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, -2 ≤ x i ∧ x i ≤ 2}, ∫ ξ, ‖F (ξ - η)‖ ^ 2 * ‖Ψ ξ‖ ^ 2 := by
  classical
  let 𝔼 := EuclideanSpace ℝ (Fin d)
  -- measurability of the cubes
  have hcube : ∀ a b : ℝ,
      MeasurableSet ({x : 𝔼 | ∀ i : Fin d, a ≤ x i ∧ x i ≤ b} : Set 𝔼) := by
    intro a b
    have h : ({x : 𝔼 | ∀ i : Fin d, a ≤ x i ∧ x i ≤ b} : Set 𝔼)
        = ⋂ i : Fin d, {x : 𝔼 | x i ∈ Set.Icc a b} := by
      ext x; simp [Set.mem_Icc]
    rw [h]
    exact MeasurableSet.iInter (fun i => measurableSet_Icc.preimage
      (by change Measurable (fun x : EuclideanSpace ℝ (Fin d) => x i); fun_prop))
  set Q1 : Set 𝔼 := {x : 𝔼 | ∀ i : Fin d, -1 ≤ x i ∧ x i ≤ 1} with hQ1
  set Q2 : Set 𝔼 := {x : 𝔼 | ∀ i : Fin d, -2 ≤ x i ∧ x i ≤ 2} with hQ2
  have hQ1m : MeasurableSet Q1 := hcube (-1) 1
  have hQ2m : MeasurableSet Q2 := hcube (-2) 2
  set G : 𝔼 → ℝ := (fun u => ‖F u‖ ^ 2) with hG
  set P : 𝔼 → ℝ := (fun u => ‖Ψ u‖ ^ 2) with hP
  have hGint : Integrable G (volume : Measure 𝔼) := by
    rw [hG]; exact (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hPint : Integrable P (volume : Measure 𝔼) := by
    rw [hP]; exact (memLp_two_iff_integrable_sq_norm hΨ.aestronglyMeasurable).mp hΨ
  have hGn : ∀ u, 0 ≤ G u := fun u => by rw [hG]; positivity
  have hPn : ∀ u, 0 ≤ P u := fun u => by rw [hP]; positivity
  -- coordinate facts
  have hcoord : ∀ (ξ u : 𝔼) (i : Fin d), (ξ - u) i = ξ i - u i := by
    intro ξ u i
    simp only [𝔼, WithLp.ofLp_sub, Pi.sub_apply]
  have hQ1_sub_Q2 : Q1 ⊆ Q2 := by
    intro x hx
    rw [hQ1] at hx; rw [hQ2] at ⊢
    intro i; have h := hx i; constructor <;> linarith [h.1, h.2]
  have hsub_mem : ∀ ξ ∈ Q1, ∀ u ∈ Q1, ξ - u ∈ Q2 := by
    intro ξ hξ u hu
    rw [hQ1] at hξ hu; rw [hQ2] at ⊢
    intro i
    have h1 := hξ i; have h2 := hu i
    rw [hcoord ξ u i]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- integrability of the double integrand
  have hInt' : Integrable (fun p : 𝔼 × 𝔼 => G (p.2 - p.1) * P p.2)
      (((volume : Measure 𝔼).restrict Q2).prod (volume : Measure 𝔼)) := by
    set f : 𝔼 × 𝔼 → ℝ := fun p => G (p.2 - p.1) * P p.2 with hf
    have hQMP : Measure.QuasiMeasurePreserving (fun p : 𝔼 × 𝔼 => p.2 - p.1)
        (((volume : Measure 𝔼).restrict Q2).prod (volume : Measure 𝔼)) (volume : Measure 𝔼) := by
      have h : Measure.QuasiMeasurePreserving (fun p : 𝔼 × 𝔼 => p.1 - p.2)
          ((volume : Measure 𝔼).prod ((volume : Measure 𝔼).restrict Q2)) (volume : Measure 𝔼) :=
        quasiMeasurePreserving_sub volume _
      have hsw : MeasurePreserving Prod.swap
          (((volume : Measure 𝔼).restrict Q2).prod (volume : Measure 𝔼))
          ((volume : Measure 𝔼).prod ((volume : Measure 𝔼).restrict Q2)) :=
        Measure.measurePreserving_swap
      have := h.comp hsw.quasiMeasurePreserving
      simpa [Function.comp_def] using this
    have h1 : AEStronglyMeasurable (fun p : 𝔼 × 𝔼 => G (p.2 - p.1))
        (((volume : Measure 𝔼).restrict Q2).prod (volume : Measure 𝔼)) :=
      hGint.aestronglyMeasurable.comp_quasiMeasurePreserving hQMP
    have h2 : AEStronglyMeasurable (fun p : 𝔼 × 𝔼 => P p.2)
        (((volume : Measure 𝔼).restrict Q2).prod (volume : Measure 𝔼)) :=
      hPint.aestronglyMeasurable.comp_snd
    have hfaesm : AEStronglyMeasurable f (((volume : Measure 𝔼).restrict Q2).prod (volume : Measure 𝔼)) := by
      rw [hf]; exact h1.mul h2
    have hcond1 : ∀ᵐ ξ ∂(volume : Measure 𝔼), Integrable (fun η : 𝔼 => f (η, ξ))
        ((volume : Measure 𝔼).restrict Q2) := by
      apply Filter.Eventually.of_forall
      intro ξ
      have hmp : MeasurePreserving (fun t : 𝔼 => ξ - t) (volume : Measure 𝔼) (volume : Measure 𝔼) :=
        Measure.measurePreserving_sub_left volume ξ
      have hGξ : Integrable (fun η : 𝔼 => G (ξ - η)) (volume : Measure 𝔼) := by
        have := hmp.integrable_comp_of_integrable hGint
        simpa [Function.comp_def] using this
      have hGξ' : Integrable (fun η : 𝔼 => G (ξ - η)) ((volume : Measure 𝔼).restrict Q2) :=
        hGξ.mono_measure Measure.restrict_le_self
      simpa [hf] using hGξ'.mul_const (P ξ)
    have hcond2 : Integrable (fun ξ : 𝔼 => ∫ η : 𝔼, ‖f (η, ξ)‖ ∂((volume : Measure 𝔼).restrict Q2))
        (volume : Measure 𝔼) := by
      set M : ℝ := ∫ u, G u with hM
      have hfaesm' : AEStronglyMeasurable (fun z : 𝔼 × 𝔼 => ‖f z‖)
          (((volume : Measure 𝔼).restrict Q2).prod (volume : Measure 𝔼)) := hfaesm.norm
      have haesm : AEStronglyMeasurable
          (fun ξ : 𝔼 => ∫ η : 𝔼, ‖f (η, ξ)‖ ∂((volume : Measure 𝔼).restrict Q2)) (volume : Measure 𝔼) := by
        have := (hfaesm'.prod_swap).integral_prod_right'
        simpa [Function.comp_def] using this
      refine Integrable.mono' (hPint.const_mul M) haesm ?_
      filter_upwards with ξ
      simp only [Real.norm_eq_abs]
      have hval : (∫ η : 𝔼, |f (η, ξ)| ∂((volume : Measure 𝔼).restrict Q2))
          = (∫ η : 𝔼, G (ξ - η) ∂((volume : Measure 𝔼).restrict Q2)) * P ξ := by
        rw [← integral_mul_const (P ξ) (fun η : 𝔼 => G (ξ - η))]
        apply integral_congr_ae
        filter_upwards with η
        rw [hf]
        exact abs_of_nonneg (mul_nonneg (hGn _) (hPn _))
      have hmp' : MeasurePreserving (fun t : 𝔼 => ξ - t) (volume : Measure 𝔼) (volume : Measure 𝔼) :=
        Measure.measurePreserving_sub_left volume ξ
      have hGξ : Integrable (fun η : 𝔼 => G (ξ - η)) (volume : Measure 𝔼) := by
        have := hmp'.integrable_comp_of_integrable hGint
        simpa [Function.comp_def] using this
      have hMbound : ∫ η : 𝔼, G (ξ - η) ∂((volume : Measure 𝔼).restrict Q2) ≤ M := by
        have hEq : (∫ η : 𝔼, G (ξ - η) ∂(volume : Measure 𝔼)) = M := by
          rw [hM]; exact integral_sub_left_eq_self G volume ξ
        rw [← hEq]
        have := setIntegral_mono_set (μ := (volume : Measure 𝔼)) (f := fun η : 𝔼 => G (ξ - η))
          (s := Q2) (t := Set.univ) hGξ.integrableOn
          (by filter_upwards with x using hGn (ξ - x))
          (by filter_upwards with x hx using trivial)
        simpa using this
      rw [hval, abs_of_nonneg (mul_nonneg (integral_nonneg (fun η => hGn _)) (hPn ξ))]
      exact mul_le_mul_of_nonneg_right hMbound (hPn ξ)
    exact (integrable_prod_iff' hfaesm).mpr ⟨hcond1, hcond2⟩
  have hInt : Integrable (Function.uncurry (fun η ξ : 𝔼 => G (ξ - η) * P ξ))
      (((volume : Measure 𝔼).restrict Q2).prod (volume : Measure 𝔼)) := hInt'
  -- the key set estimate
  have hB_ge_A : ∀ ξ ∈ Q1, (∫ u in Q1, G u) ≤ ∫ η in Q2, G (ξ - η) := by
    intro ξ hξ
    have hξ' : ∀ i : Fin d, -1 ≤ ξ i ∧ ξ i ≤ 1 := by rw [hQ1] at hξ; exact hξ
    have hSsub : ((fun x : 𝔼 => ξ - x) ⁻¹' Q1) ⊆ Q2 := by
      intro x hx
      rw [Set.mem_preimage, hQ1] at hx
      rw [hQ2] at ⊢
      intro i
      have h1 := hx i; have h2 := hξ' i
      rw [hcoord ξ x i] at h1
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hSm : MeasurableSet ((fun x : 𝔼 => ξ - x) ⁻¹' Q1) := hQ1m.preimage (by fun_prop)
    have hmp' : MeasurePreserving (fun t : 𝔼 => ξ - t) (volume : Measure 𝔼) (volume : Measure 𝔼) :=
      Measure.measurePreserving_sub_left volume ξ
    have hGξ : Integrable (fun η : 𝔼 => G (ξ - η)) (volume : Measure 𝔼) := by
      have := hmp'.integrable_comp_of_integrable hGint
      simpa [Function.comp_def] using this
    have step1 : (∫ u in Q1, G u) = ∫ x in ((fun x : 𝔼 => ξ - x) ⁻¹' Q1), G (ξ - x) := by
      rw [← integral_indicator hQ1m]
      rw [← integral_sub_left_eq_self (fun v => Q1.indicator G v) volume ξ]
      rw [← integral_indicator hSm]
      apply integral_congr_ae
      filter_upwards with x
      simp only [Set.indicator_apply, Set.mem_preimage]
    rw [step1]
    refine setIntegral_mono_set (μ := (volume : Measure 𝔼)) (f := fun x : 𝔼 => G (ξ - x))
      (s := (fun x : 𝔼 => ξ - x) ⁻¹' Q1) (t := Q2) ?_ ?_ ?_
    · exact (hGξ.mono_measure Measure.restrict_le_self)
    · filter_upwards with x using hGn (ξ - x)
    · filter_upwards with x hx using hSsub hx
  -- pointwise bound on the inner integral
  have hA_nonneg : 0 ≤ ∫ u in Q1, G u := integral_nonneg (fun u => hGn u)
  have hpt : ∀ ξ : 𝔼, Q1.indicator (fun ξ => (∫ u in Q1, G u) * P ξ) ξ
      ≤ ∫ η in Q2, G (ξ - η) * P ξ := by
    intro ξ
    by_cases hξ : ξ ∈ Q1
    · rw [Set.indicator_of_mem hξ]
      have hinner : ∫ η in Q2, G (ξ - η) * P ξ = (∫ η in Q2, G (ξ - η)) * P ξ := by
        rw [integral_mul_const]
      rw [hinner]
      exact mul_le_mul_of_nonneg_right (hB_ge_A ξ hξ) (hPn ξ)
    · rw [Set.indicator_of_notMem hξ]
      have hnn : 0 ≤ ∫ η : 𝔼, G (ξ - η) * P ξ ∂((volume : Measure 𝔼).restrict Q2) :=
        integral_nonneg (fun η => mul_nonneg (hGn (ξ - η)) (hPn ξ))
      simpa using hnn
  -- integrability of the two sides
  have hLint : Integrable (Q1.indicator (fun ξ => (∫ u in Q1, G u) * P ξ)) (volume : Measure 𝔼) :=
    (hPint.const_mul (∫ u in Q1, G u)).indicator hQ1m
  have hRint : Integrable (fun ξ : 𝔼 => ∫ η in Q2, G (ξ - η) * P ξ) (volume : Measure 𝔼) := by
    have h := hInt'.integral_norm_prod_right
    convert h using 1
    funext ξ
    apply integral_congr_ae
    filter_upwards with η
    exact (Real.norm_of_nonneg (mul_nonneg (hGn (ξ - η)) (hPn ξ))).symm
  have hmono : (∫ ξ : 𝔼, Q1.indicator (fun ξ => (∫ u in Q1, G u) * P ξ) ξ)
      ≤ ∫ ξ : 𝔼, ∫ η in Q2, G (ξ - η) * P ξ :=
    integral_mono hLint hRint (fun ξ => hpt ξ)
  have hLeq : (∫ ξ : 𝔼, Q1.indicator (fun ξ => (∫ u in Q1, G u) * P ξ) ξ)
      = (∫ u in Q1, G u) * (∫ u in Q1, P u) := by
    rw [integral_indicator hQ1m, integral_const_mul]
  have hswap := integral_integral_swap (μ := (volume : Measure 𝔼).restrict Q2) (ν := (volume : Measure 𝔼))
    (f := fun η ξ : 𝔼 => G (ξ - η) * P ξ) hInt
  have key : (∫ u in Q1, G u) * (∫ u in Q1, P u)
      ≤ ∫ η in Q2, ∫ ξ, G (ξ - η) * P ξ := by
    calc (∫ u in Q1, G u) * (∫ u in Q1, P u)
        = ∫ ξ : 𝔼, Q1.indicator (fun ξ => (∫ u in Q1, G u) * P ξ) ξ := hLeq.symm
      _ ≤ ∫ ξ : 𝔼, ∫ η in Q2, G (ξ - η) * P ξ := hmono
      _ = ∫ η in Q2, ∫ ξ, G (ξ - η) * P ξ := hswap.symm
  have hc : c₂ ^ 2 ≤ ∫ u in Q1, P u := by
    rw [hP, hQ1]; exact hΨge
  have key2 : c₂ ^ 2 * (∫ u in Q1, G u)
      ≤ ∫ η in Q2, ∫ ξ, G (ξ - η) * P ξ := by
    calc c₂ ^ 2 * (∫ u in Q1, G u) ≤ (∫ u in Q1, P u) * (∫ u in Q1, G u) :=
          mul_le_mul_of_nonneg_right hc hA_nonneg
      _ = (∫ u in Q1, G u) * (∫ u in Q1, P u) := by ring
      _ ≤ ∫ η in Q2, ∫ ξ, G (ξ - η) * P ξ := key
  simpa [hQ1, hQ2, hG, hP] using key2

end Commons.Analysis.Fourier