import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.LocData6.Main
import Submission.Work.FTS_LocDatum3a.integral_comp_mul_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Scratch: the interchange of `L₁₂dens` with the mollifier `J_ε` (backup development) -/

/-- `K` vanishes at the endpoints of `Iθ`. -/
lemma K_eq_zero_of_not_mem_Ioo_L12J {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (h : θ ∉ Set.Ioo (0 : ℝ) (π / 2)) : Work.Spaces.K θ = 0 := by
  have hcases : θ = 0 ∨ θ = π / 2 := by
    rcases not_and_or.mp h with h' | h'
    · exact Or.inl (le_antisymm (not_lt.mp h') hθ.1)
    · exact Or.inr (le_antisymm hθ.2 (not_lt.mp h'))
  rcases hcases with rfl | rfl <;> simp [Work.Spaces.K]

/-- `Work.Spaces.K` is continuous. -/
lemma continuous_K_L12J : Continuous Work.Spaces.K := by
  unfold Work.Spaces.K
  fun_prop

/-- `|K|` is integrable on `Iθ`. -/
lemma integrableOn_abs_K_L12J : IntegrableOn (fun θ : ℝ => |Work.Spaces.K θ|) Work.Spaces.Iθ := by
  simpa only [Work.Spaces.Iθ] using
    (continuous_K_L12J.abs.continuousOn.integrableOn_compact isCompact_Icc)

/-- **The interchange at the level of the angular density**, for fixed `s > 0`. -/
lemma L12dens_Jeps_eq {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {F : ℝ → ℝ → ℝ} {a C : ℝ} (ha : 0 < a)
    (hFm : Measurable (Function.uncurry F))
    (hF0 : ∀ z θ, 0 < z → z ≤ a → F z θ = 0)
    (hFg : ∀ z θ, 0 < z → |F z θ| ≤ C / (1 + z))
    {s : ℝ} (hs : 0 < s) :
    Work.FM.L12dens Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε F) s
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s := by
  have hCnn : 0 ≤ C := by
    have h1 : (0 : ℝ) < 1 + a / 2 := by linarith
    have h2 : 0 ≤ C / (1 + a / 2) := by
      have h := hFg (a / 2) 0 (by linarith)
      rw [hF0 (a / 2) 0 (by linarith) (by linarith), abs_zero] at h
      exact h
    have h3 : 0 ≤ C / (1 + a / 2) * (1 + a / 2) := mul_nonneg h2 h1.le
    rwa [div_mul_cancel₀ _ (ne_of_gt h1)] at h3
  -- the pointwise identity on `Iθ`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.K θ * (Work.FTS.StrongEps.Jeps ρ ε F) s θ / s
        = ∫ p : ℝ × ℝ, Work.Spaces.K θ * (Work.FTS.StrongEps.Jker ρ ε p
            * F (Work.FTS.StrongEps.zShift s p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) / s := by
    intro θ hθ
    by_cases hθo : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
    · rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε F hs hθo]
      rw [show (∫ p : ℝ × ℝ, Work.Spaces.K θ * (Work.FTS.StrongEps.Jker ρ ε p
              * F (Work.FTS.StrongEps.zShift s p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) / s)
          = ∫ p : ℝ × ℝ, (Work.Spaces.K θ / s) * (Work.FTS.StrongEps.Jker ρ ε p
              * F (Work.FTS.StrongEps.zShift s p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) from
        integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring))]
      rw [MeasureTheory.integral_const_mul]
      ring
    · have hK0 := K_eq_zero_of_not_mem_Ioo_L12J hθ hθo
      rw [hK0]
      simp
  have hL : Work.FM.L12dens Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε F) s
      = ∫ θ in Work.Spaces.Iθ, ∫ p : ℝ × ℝ, Work.Spaces.K θ
          * (Work.FTS.StrongEps.Jker ρ ε p * F (Work.FTS.StrongEps.zShift s p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) / s := by
    rw [show Work.FM.L12dens Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε F) s
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
            * (Work.FTS.StrongEps.Jeps ρ ε F) s θ / s from rfl]
    exact setIntegral_congr_fun measurableSet_Icc hpt
  -- integrability of the `(θ,p)`-integrand
  have hInt : Integrable (fun z : ℝ × (ℝ × ℝ) => Work.Spaces.K z.1
      * (Work.FTS.StrongEps.Jker ρ ε z.2 * F (Work.FTS.StrongEps.zShift s z.2.1)
          (Work.FTS.StrongEps.thShift z.1 z.2.2)) / s)
      ((volume.restrict Work.Spaces.Iθ).prod volume) := by
    refine Integrable.mono'
      ((integrableOn_abs_K_L12J.mul_prod (Work.FTS.StrongEps.Jker_integrable hρ hε).abs).mul_const
        (C * Real.exp ε / s ^ 2)) ?_ ?_
    · -- measurability
      refine Measurable.aestronglyMeasurable ?_
      have hK' : Measurable fun z : ℝ × (ℝ × ℝ) => Work.Spaces.K z.1 :=
        continuous_K_L12J.measurable.comp measurable_fst
      have hJ' : Measurable fun z : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.Jker ρ ε z.2 :=
        (Work.FTS.StrongEps.Jker_continuous hρ ε).measurable.comp measurable_snd
      have hF' : Measurable fun z : ℝ × (ℝ × ℝ) => F (Work.FTS.StrongEps.zShift s z.2.1)
          (Work.FTS.StrongEps.thShift z.1 z.2.2) := by
        have hzc : Measurable fun z : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.zShift s z.2.1 := by
          unfold Work.FTS.StrongEps.zShift; measurability
        have htc : Measurable fun z : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.thShift z.1 z.2.2 := by
          unfold Work.FTS.StrongEps.thShift
          have hzz : Measurable fun z : ℝ × (ℝ × ℝ) => z.2.2 :=
            measurable_snd.comp measurable_snd
          have htan : Measurable fun z : ℝ × (ℝ × ℝ) => Real.tan z.1 := by
            rw [show (fun z : ℝ × (ℝ × ℝ) => Real.tan z.1)
                = fun z => Real.sin z.1 / Real.cos z.1 from
              funext fun z => Real.tan_eq_sin_div_cos z.1]
            exact (Real.measurable_sin.div Real.measurable_cos).comp measurable_fst
          exact Real.measurable_arctan.comp (htan.mul (Real.measurable_exp.comp hzz.neg))
        exact hFm.comp (hzc.prodMk htc)
      exact (hK'.mul (hJ'.mul hF')).div_const s
    · -- the pointwise domination
      filter_upwards with z
      rw [Real.norm_eq_abs]
      rcases eq_or_ne (Work.FTS.StrongEps.Jker ρ ε z.2) 0 with hj | hj
      · rw [hj]; simp
      · have hp : z.2 ∈ Metric.closedBall (0 : ℝ × ℝ) ε := by
          by_contra hp
          exact hj (Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp)
        have hpabs : |z.2.1| ≤ ε := by
          have h := Metric.mem_closedBall.mp hp
          rw [dist_zero_right, Prod.norm_def, max_le_iff] at h
          exact h.1
        have hp1 : -ε ≤ z.2.1 := (abs_le.mp hpabs).1
        have hp2 : z.2.1 ≤ ε := (abs_le.mp hpabs).2
        have hzpos : 0 < Work.FTS.StrongEps.zShift s z.2.1 :=
          Work.FTS.StrongEps.zShift_pos hs
        have hb : |F (Work.FTS.StrongEps.zShift s z.2.1) (Work.FTS.StrongEps.thShift z.1 z.2.2)|
            ≤ C * Real.exp ε / s := by
          by_cases hza : Work.FTS.StrongEps.zShift s z.2.1 ≤ a
          · rw [hF0 _ _ hzpos hza, abs_zero]
            positivity
          · rw [not_le] at hza
            have h1 : |F (Work.FTS.StrongEps.zShift s z.2.1)
                (Work.FTS.StrongEps.thShift z.1 z.2.2)| ≤ C / (1 + s * Real.exp (-z.2.1)) := by
              simpa only [Work.FTS.StrongEps.zShift] using hFg _ _ hzpos
            have h2 : C / (1 + s * Real.exp (-z.2.1)) ≤ C * Real.exp ε / s := by
              have h3 : C / (1 + s * Real.exp (-z.2.1)) ≤ C / (s * Real.exp (-z.2.1)) :=
                div_le_div_of_nonneg_left hCnn (by positivity) (by linarith [Real.exp_pos (-z.2.1)])
              have h4 : C / (s * Real.exp (-z.2.1)) = C * Real.exp z.2.1 / s := by
                rw [Real.exp_neg]
                field_simp
              have h5 : C * Real.exp z.2.1 / s ≤ C * Real.exp ε / s := by
                have := Real.exp_le_exp.mpr hp2
                gcongr
              linarith [h3, h4.le, h4.ge]
            exact h1.trans h2
        calc |Work.Spaces.K z.1 * (Work.FTS.StrongEps.Jker ρ ε z.2
                * F (Work.FTS.StrongEps.zShift s z.2.1) (Work.FTS.StrongEps.thShift z.1 z.2.2)) / s|
            = |Work.Spaces.K z.1| * |Work.FTS.StrongEps.Jker ρ ε z.2|
                * |F (Work.FTS.StrongEps.zShift s z.2.1)
                    (Work.FTS.StrongEps.thShift z.1 z.2.2)| / s := by
              rw [abs_div, abs_mul, abs_mul, abs_of_pos hs]
              ring
          _ ≤ |Work.Spaces.K z.1| * |Work.FTS.StrongEps.Jker ρ ε z.2|
                * (C * Real.exp ε / s) / s := by
              gcongr
          _ = |Work.Spaces.K z.1| * |Work.FTS.StrongEps.Jker ρ ε z.2|
                * (C * Real.exp ε / s ^ 2) := by ring
  rw [hL, MeasureTheory.integral_integral_swap hInt]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  show (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * (Work.FTS.StrongEps.Jker ρ ε p
        * F (Work.FTS.StrongEps.zShift s p.1) (Work.FTS.StrongEps.thShift θ p.2)) / s)
      = Work.FTS.StrongEps.Jker ρ ε p * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
          * F (Work.FTS.StrongEps.zShift s p.1) (Work.FTS.StrongEps.thShift θ p.2) / s)
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * (Work.FTS.StrongEps.Jker ρ ε p
          * F (Work.FTS.StrongEps.zShift s p.1) (Work.FTS.StrongEps.thShift θ p.2)) / s)
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.Jker ρ ε p
          * (Work.Spaces.K θ * F (Work.FTS.StrongEps.zShift s p.1)
              (Work.FTS.StrongEps.thShift θ p.2) / s) from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]

/-- `1/s² = s^{-2}` for `s ≥ 0`. -/
lemma one_div_sq_eq_rpow_L12J (s : ℝ) (hs : 0 ≤ s) : 1 / s ^ 2 = s ^ (-2 : ℝ) := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hs, Real.rpow_two]
  ring

/-- `(s²)⁻¹ = s^{-2}` for `s ≥ 0`. -/
lemma inv_sq_eq_rpow_L12J (s : ℝ) (hs : 0 ≤ s) : (s ^ 2)⁻¹ = s ^ (-2 : ℝ) := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hs, Real.rpow_two]

/-- **The mollifier `J_ε` commutes with `L₁₂` in the zero mode.** -/
theorem L12_Jeps_interchange_mine {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {F : ℝ → ℝ → ℝ} {a C : ℝ} (ha : 0 < a)
    (hFm : Measurable (Function.uncurry F))
    (hF0 : ∀ z θ, 0 < z → z ≤ a → F z θ = 0)
    (hFg : ∀ z θ, 0 < z → |F z θ| ≤ C / (1 + z)) :
    Work.FM.L12 Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε F) 0
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (Work.FM.L12 Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) 0) := by
  have hCnn : 0 ≤ C := by
    have h1 : (0 : ℝ) < 1 + a / 2 := by linarith
    have h2 : 0 ≤ C / (1 + a / 2) := by
      have h := hFg (a / 2) 0 (by linarith)
      rw [hF0 (a / 2) 0 (by linarith) (by linarith), abs_zero] at h
      exact h
    have h3 : 0 ≤ C / (1 + a / 2) * (1 + a / 2) := mul_nonneg h2 h1.le
    rwa [div_mul_cancel₀ _ (ne_of_gt h1)] at h3
  set Kb : ℝ := ∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ| with hKb
  have hKbnn : 0 ≤ Kb := by rw [hKb]; exact integral_nonneg (fun θ => abs_nonneg _)
  set gpart : ℝ → ℝ := fun s => (C * Real.exp ε) * Kb
      * ((Set.Ici (a * Real.exp (-ε))).indicator (fun s => s ^ (-2 : ℝ)) s) with hgpart
  set ppart : ℝ × ℝ → ℝ := fun p => |Work.FTS.StrongEps.Jker ρ ε p| with hppart
  -- ### Step A: `L₁₂(J_ε F)(0)` as an iterated `s`–`p` integral
  have hA : Work.FM.L12 Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε F) 0
      = ∫ s in Set.Ioi 0, ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s := by
    rw [show Work.FM.L12 Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε F) 0
        = ∫ s in Set.Ioi 0, Work.FM.L12dens Work.Spaces.K
            (Work.FTS.StrongEps.Jeps ρ ε F) s from rfl]
    exact setIntegral_congr_fun measurableSet_Ioi
      (fun s hs => L12dens_Jeps_eq hρ hε ha hFm hF0 hFg hs)
  -- ### the integrability of the `s`–`p` integrand
  have hInt : Integrable (fun z : ℝ × (ℝ × ℝ) => if 0 < z.1 then
        Work.FTS.StrongEps.Jker ρ ε z.2 * Work.FM.L12dens Work.Spaces.K
          (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
            (Work.FTS.StrongEps.thShift θ z.2.2)) z.1 else 0)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    have hs_int : Integrable gpart (volume.restrict (Set.Ioi 0)) := by
      rw [hgpart]
      have hIoi : IntegrableOn (fun s : ℝ => s ^ (-2 : ℝ))
          (Set.Ioi (a * Real.exp (-ε) / 2)) :=
        integrableOn_Ioi_rpow_of_lt (by norm_num) (by positivity)
      have hIci : IntegrableOn (fun s : ℝ => s ^ (-2 : ℝ))
          (Set.Ici (a * Real.exp (-ε))) := by
        refine hIoi.mono_set (fun s hs => ?_)
        simp only [Set.mem_Ici] at hs
        simp only [Set.mem_Ioi]
        have hpos : 0 < a * Real.exp (-ε) := by positivity
        linarith
      exact (((integrable_indicator_iff measurableSet_Ici).mpr hIci).integrableOn).const_mul _
    have hp_int : Integrable ppart volume := by
      rw [hppart]
      exact (Work.FTS.StrongEps.Jker_integrable hρ hε).abs
    have hdom : Integrable (fun z : ℝ × (ℝ × ℝ) => gpart z.1 * ppart z.2)
        ((volume.restrict (Set.Ioi 0)).prod volume) := hs_int.mul_prod hp_int
    have hdom_nn : ∀ z : ℝ × (ℝ × ℝ), 0 ≤ gpart z.1 * ppart z.2 := by
      intro z
      rw [hgpart, hppart]
      have h1 : 0 ≤ (Set.Ici (a * Real.exp (-ε))).indicator
          (fun s : ℝ => s ^ (-2 : ℝ)) z.1 := by
        by_cases h : z.1 ∈ Set.Ici (a * Real.exp (-ε))
        · rw [Set.indicator_of_mem h]
          have hpos : 0 < a * Real.exp (-ε) := by positivity
          have hge : a * Real.exp (-ε) ≤ z.1 := by simpa [Set.mem_Ici] using h
          exact Real.rpow_nonneg (by linarith) _
        · rw [Set.indicator_of_notMem h]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hKbnn) h1) (abs_nonneg _)
    refine Integrable.mono' hdom ?_ ?_
    · -- measurability
      have hL12meas : StronglyMeasurable (fun z : ℝ × (ℝ × ℝ) => ∫ θ : ℝ, Work.Spaces.K θ
          * F (Work.FTS.StrongEps.zShift z.1 z.2.1) (Work.FTS.StrongEps.thShift θ z.2.2) / z.1
          ∂(volume.restrict Work.Spaces.Iθ)) := by
        refine StronglyMeasurable.integral_prod_right (ν := volume.restrict Work.Spaces.Iθ) ?_
        have hW : Measurable (fun w : (ℝ × (ℝ × ℝ)) × ℝ => Work.Spaces.K w.2
            * F (Work.FTS.StrongEps.zShift w.1.1 w.1.2.1)
              (Work.FTS.StrongEps.thShift w.2 w.1.2.2) / w.1.1) := by
          have hK : Measurable fun w : (ℝ × (ℝ × ℝ)) × ℝ => Work.Spaces.K w.2 :=
            continuous_K_L12J.measurable.comp measurable_snd
          have hzc : Measurable fun w : (ℝ × (ℝ × ℝ)) × ℝ =>
              Work.FTS.StrongEps.zShift w.1.1 w.1.2.1 := by
            unfold Work.FTS.StrongEps.zShift; measurability
          have htc : Measurable fun w : (ℝ × (ℝ × ℝ)) × ℝ =>
              Work.FTS.StrongEps.thShift w.2 w.1.2.2 := by
            unfold Work.FTS.StrongEps.thShift
            have hzz : Measurable fun w : (ℝ × (ℝ × ℝ)) × ℝ => w.1.2.2 :=
              (measurable_snd.comp measurable_snd).comp measurable_fst
            have htan : Measurable fun w : (ℝ × (ℝ × ℝ)) × ℝ => Real.tan w.2 := by
              rw [show (fun w : (ℝ × (ℝ × ℝ)) × ℝ => Real.tan w.2)
                  = fun w => Real.sin w.2 / Real.cos w.2 from
                funext fun w => Real.tan_eq_sin_div_cos w.2]
              exact (Real.measurable_sin.div Real.measurable_cos).comp measurable_snd
            exact Real.measurable_arctan.comp (htan.mul (Real.measurable_exp.comp hzz.neg))
          have harg : Measurable fun w : (ℝ × (ℝ × ℝ)) × ℝ =>
              ((Work.FTS.StrongEps.zShift w.1.1 w.1.2.1,
                Work.FTS.StrongEps.thShift w.2 w.1.2.2) : ℝ × ℝ) := hzc.prodMk htc
          exact ((hK.mul (hFm.comp harg)).div measurable_fst.fst)
        exact hW.stronglyMeasurable
      refine Measurable.aestronglyMeasurable ?_
      show Measurable (fun z : ℝ × (ℝ × ℝ) => if 0 < z.1 then Work.FTS.StrongEps.Jker ρ ε z.2
          * (∫ θ : ℝ, Work.Spaces.K θ * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
              (Work.FTS.StrongEps.thShift θ z.2.2) / z.1
              ∂(volume.restrict Work.Spaces.Iθ)) else 0)
      have hA : Measurable (fun z : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.Jker ρ ε z.2
          * (∫ θ : ℝ, Work.Spaces.K θ * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
              (Work.FTS.StrongEps.thShift θ z.2.2) / z.1
              ∂(volume.restrict Work.Spaces.Iθ))) :=
        ((Work.FTS.StrongEps.Jker_continuous hρ ε).measurable.comp measurable_snd).mul
          hL12meas.measurable
      exact hA.indicator (measurableSet_lt measurable_const measurable_fst)
    · -- the pointwise bound
      filter_upwards with z
      by_cases hz1 : 0 < z.1
      · rw [if_pos hz1, Real.norm_eq_abs]
        by_cases hj : Work.FTS.StrongEps.Jker ρ ε z.2 = 0
        · rw [hj, zero_mul, abs_zero]
          exact hdom_nn z
        · have hp : z.2 ∈ Metric.closedBall (0 : ℝ × ℝ) ε := by
            by_contra hp
            exact hj (Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp)
          have hpabs : |z.2.1| ≤ ε := by
            have h := Metric.mem_closedBall.mp hp
            rw [dist_zero_right, Prod.norm_def, max_le_iff] at h
            exact h.1
          have hp1 : -ε ≤ z.2.1 := (abs_le.mp hpabs).1
          have hp2 : z.2.1 ≤ ε := (abs_le.mp hpabs).2
          have hFb : ∀ θ : ℝ, |F (Work.FTS.StrongEps.zShift z.1 z.2.1)
              (Work.FTS.StrongEps.thShift θ z.2.2)| ≤ C * Real.exp ε / z.1 := by
            intro θ
            by_cases hza : Work.FTS.StrongEps.zShift z.1 z.2.1 ≤ a
            · rw [hF0 _ _ (Work.FTS.StrongEps.zShift_pos hz1) hza, abs_zero]
              positivity
            · rw [not_le] at hza
              have h1 : |F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                  (Work.FTS.StrongEps.thShift θ z.2.2)|
                  ≤ C / (1 + z.1 * Real.exp (-z.2.1)) := by
                simpa only [Work.FTS.StrongEps.zShift] using
                  hFg _ _ (Work.FTS.StrongEps.zShift_pos hz1)
              have h2 : C / (1 + z.1 * Real.exp (-z.2.1)) ≤ C * Real.exp ε / z.1 := by
                have h3 : C / (1 + z.1 * Real.exp (-z.2.1))
                    ≤ C / (z.1 * Real.exp (-z.2.1)) :=
                  div_le_div_of_nonneg_left hCnn (by positivity)
                    (by linarith [Real.exp_pos (-z.2.1)])
                have h4 : C / (z.1 * Real.exp (-z.2.1)) = C * Real.exp z.2.1 / z.1 := by
                  rw [Real.exp_neg]; field_simp
                have h5 : C * Real.exp z.2.1 / z.1 ≤ C * Real.exp ε / z.1 := by
                  have := Real.exp_le_exp.mpr hp2
                  gcongr
                linarith [h3, h4.le, h4.ge]
              exact h1.trans h2
          have hLb : |Work.FM.L12dens Work.Spaces.K
              (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                (Work.FTS.StrongEps.thShift θ z.2.2)) z.1|
              ≤ (C * Real.exp ε) * Kb * z.1 ^ (-2 : ℝ) := by
            rw [show Work.FM.L12dens Work.Spaces.K
                (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                  (Work.FTS.StrongEps.thShift θ z.2.2)) z.1
                = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
                    * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                      (Work.FTS.StrongEps.thShift θ z.2.2) / z.1 from rfl]
            have hbound : ∀ θ : ℝ, ‖Work.Spaces.K θ
                * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                  (Work.FTS.StrongEps.thShift θ z.2.2) / z.1‖
                ≤ ((C * Real.exp ε) * (z.1 ^ 2)⁻¹) * |Work.Spaces.K θ| := by
              intro θ
              rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hz1]
              calc |Work.Spaces.K θ| * |F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                    (Work.FTS.StrongEps.thShift θ z.2.2)| / z.1
                  ≤ |Work.Spaces.K θ| * (C * Real.exp ε / z.1) / z.1 := by
                    gcongr
                    exact hFb θ
                _ = ((C * Real.exp ε) * (z.1 ^ 2)⁻¹) * |Work.Spaces.K θ| := by
                    field_simp
            calc ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
                    * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                      (Work.FTS.StrongEps.thShift θ z.2.2) / z.1‖
                ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Spaces.K θ
                    * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                      (Work.FTS.StrongEps.thShift θ z.2.2) / z.1‖ :=
                  MeasureTheory.norm_integral_le_integral_norm _
              _ ≤ ∫ θ in Work.Spaces.Iθ, ((C * Real.exp ε) * (z.1 ^ 2)⁻¹)
                    * |Work.Spaces.K θ| := by
                  refine MeasureTheory.integral_mono_of_nonneg
                    (ae_of_all _ (fun θ => norm_nonneg _)) ?_ ?_
                  · exact integrableOn_abs_K_L12J.const_mul ((C * Real.exp ε) * (z.1 ^ 2)⁻¹)
                  · exact ae_of_all _ (fun θ => hbound θ)
              _ = (C * Real.exp ε) * Kb * (z.1 ^ 2)⁻¹ := by
                  rw [MeasureTheory.integral_const_mul, ← hKb]
                  ring
              _ = (C * Real.exp ε) * Kb * z.1 ^ (-2 : ℝ) := by
                  rw [show (z.1 ^ 2)⁻¹ = z.1 ^ (-2 : ℝ) from inv_sq_eq_rpow_L12J z.1 hz1.le]
          by_cases hs' : z.1 < a * Real.exp (-ε)
          · -- here the angular density vanishes
            have hzero : Work.FM.L12dens Work.Spaces.K
                (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                  (Work.FTS.StrongEps.thShift θ z.2.2)) z.1 = 0 := by
              rw [show Work.FM.L12dens Work.Spaces.K
                  (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                    (Work.FTS.StrongEps.thShift θ z.2.2)) z.1
                  = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
                      * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                        (Work.FTS.StrongEps.thShift θ z.2.2) / z.1 from rfl]
              rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
                      * F (Work.FTS.StrongEps.zShift z.1 z.2.1)
                        (Work.FTS.StrongEps.thShift θ z.2.2) / z.1)
                  = ∫ θ in Work.Spaces.Iθ, (0 : ℝ) from
                setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
                  have hzf : Work.FTS.StrongEps.zShift z.1 z.2.1 ≤ a := by
                    have he : Real.exp (-z.2.1) ≤ Real.exp ε :=
                      Real.exp_le_exp.mpr (by linarith [hp1])
                    calc Work.FTS.StrongEps.zShift z.1 z.2.1
                        = z.1 * Real.exp (-z.2.1) := rfl
                      _ ≤ z.1 * Real.exp ε := mul_le_mul_of_nonneg_left he hz1.le
                      _ ≤ (a * Real.exp (-ε)) * Real.exp ε :=
                          mul_le_mul_of_nonneg_right hs'.le (Real.exp_pos _).le
                      _ = a := by
                          rw [mul_assoc, ← Real.exp_add, show -ε + ε = 0 by ring,
                            Real.exp_zero, mul_one]
                  rw [hF0 _ _ (Work.FTS.StrongEps.zShift_pos hz1) hzf]
                  ring)]
              simp
            have hind : (Set.Ici (a * Real.exp (-ε))).indicator
                (fun s : ℝ => s ^ (-2 : ℝ)) z.1 = 0 :=
              Set.indicator_of_notMem (by simpa [Set.mem_Ici] using not_le.mpr hs') _
            change ‖Work.FTS.StrongEps.Jker ρ ε z.2
                * Work.FM.L12dens Work.Spaces.K
                    (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                      (Work.FTS.StrongEps.thShift θ z.2.2)) z.1‖
                ≤ ((C * Real.exp ε) * Kb * ((Set.Ici (a * Real.exp (-ε))).indicator
                    (fun s : ℝ => s ^ (-2 : ℝ)) z.1))
                  * |Work.FTS.StrongEps.Jker ρ ε z.2|
            rw [hzero, mul_zero, norm_zero, hind]
            simp
          · -- the general bound
            have hind : (Set.Ici (a * Real.exp (-ε))).indicator
                (fun s : ℝ => s ^ (-2 : ℝ)) z.1 = z.1 ^ (-2 : ℝ) :=
              Set.indicator_of_mem (by simpa [Set.mem_Ici] using not_lt.mp hs') _
            change ‖Work.FTS.StrongEps.Jker ρ ε z.2
                * Work.FM.L12dens Work.Spaces.K
                    (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                      (Work.FTS.StrongEps.thShift θ z.2.2)) z.1‖
                ≤ ((C * Real.exp ε) * Kb * ((Set.Ici (a * Real.exp (-ε))).indicator
                    (fun s : ℝ => s ^ (-2 : ℝ)) z.1))
                  * |Work.FTS.StrongEps.Jker ρ ε z.2|
            rw [hind, Real.norm_eq_abs, abs_mul]
            calc |Work.FTS.StrongEps.Jker ρ ε z.2|
                  * |Work.FM.L12dens Work.Spaces.K
                      (fun z' θ => F (Work.FTS.StrongEps.zShift z' z.2.1)
                        (Work.FTS.StrongEps.thShift θ z.2.2)) z.1|
                ≤ |Work.FTS.StrongEps.Jker ρ ε z.2|
                    * ((C * Real.exp ε) * Kb * z.1 ^ (-2 : ℝ)) :=
                  mul_le_mul_of_nonneg_left hLb (abs_nonneg _)
              _ = ((C * Real.exp ε) * Kb * z.1 ^ (-2 : ℝ))
                    * |Work.FTS.StrongEps.Jker ρ ε z.2| := by ring
      · rw [if_neg hz1]
        simpa using hdom_nn z
  -- ### the `s`–`p` exchange and the final computation
  rw [hA]
  rw [show (∫ s in Set.Ioi 0, ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * Work.FM.L12dens Work.Spaces.K
            (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) s)
      = ∫ p : ℝ × ℝ, ∫ s in Set.Ioi 0, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s from ?_]
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    show (∫ s in Set.Ioi 0, Work.FTS.StrongEps.Jker ρ ε p
        * Work.FM.L12dens Work.Spaces.K
            (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) s)
      = Work.FTS.StrongEps.Jker ρ ε p
        * (∫ s in Set.Ioi 0, Work.FM.L12dens Work.Spaces.K
            (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) s)
    rw [MeasureTheory.integral_const_mul]
  · have h1 : (∫ s in Set.Ioi 0, ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s)
        = ∫ s in Set.Ioi 0, ∫ p : ℝ × ℝ, (if 0 < s then Work.FTS.StrongEps.Jker ρ ε p
            * Work.FM.L12dens Work.Spaces.K
                (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) s else 0) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      show Work.FTS.StrongEps.Jker ρ ε p * Work.FM.L12dens Work.Spaces.K
            (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) s
          = (if 0 < s then Work.FTS.StrongEps.Jker ρ ε p
              * Work.FM.L12dens Work.Spaces.K
                  (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) s else 0)
      split_ifs with h
      · rfl
      · exact absurd hs h
    have h2 : (∫ s in Set.Ioi 0, ∫ p : ℝ × ℝ, (if 0 < s then Work.FTS.StrongEps.Jker ρ ε p
          * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s else 0))
        = ∫ p : ℝ × ℝ, ∫ s in Set.Ioi 0, (if 0 < s then Work.FTS.StrongEps.Jker ρ ε p
            * Work.FM.L12dens Work.Spaces.K
                (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) s else 0) :=
      MeasureTheory.integral_integral_swap hInt
    have h3 : (∫ p : ℝ × ℝ, ∫ s in Set.Ioi 0, (if 0 < s then Work.FTS.StrongEps.Jker ρ ε p
          * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s else 0))
        = ∫ p : ℝ × ℝ, ∫ s in Set.Ioi 0, Work.FTS.StrongEps.Jker ρ ε p
            * Work.FM.L12dens Work.Spaces.K
                (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) s := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      show (if 0 < s then Work.FTS.StrongEps.Jker ρ ε p
            * Work.FM.L12dens Work.Spaces.K
                (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) s else 0)
          = Work.FTS.StrongEps.Jker ρ ε p * Work.FM.L12dens Work.Spaces.K
              (fun z θ => F (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) s
      split_ifs with h
      · rfl
      · exact absurd hs h
    exact h1.trans (h2.trans h3)

end Work.FTS_LocDatum3a
