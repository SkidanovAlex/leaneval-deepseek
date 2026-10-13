import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_slotIntegrable
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongEps.EpsLocalPStar.LintegralExpCompIcc
import Submission.Work.FTS.StrongEps.EpsLocalPStar.AeCompExpNeg
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SqrtDLocInt
import Submission.Work.FTS.StrongEps.EpsLocalPStar.LamLocInt
import Submission.Work.FTS.StrongEps.EpsLocalPStar.RhoMargFubini
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsRhoForm
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SqrtDMeas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsLocalPStar

/-! ## Helpers -/

/-- A property that holds for a.e. `x` with `∀ y, P x y` holds for a.e. point of the plane. -/
private theorem ae_prod_of_ae_fst {P : ℝ → ℝ → Prop}
    (h : ∀ᵐ x ∂(volume : Measure ℝ), ∀ y, P x y) :
    ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), P z.1 z.2 := by
  rw [MeasureTheory.ae_iff] at h ⊢
  refine measure_mono_null (t := {a : ℝ | ¬ ∀ y : ℝ, P a y} ×ˢ Set.univ) ?_ ?_
  · intro z hz
    exact ⟨fun hc => hz (hc z.2), Set.mem_univ _⟩
  · rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod, h, zero_mul]

/-- A function of the first coordinate, integrable over `[-1,1]` in the `lintegral` sense,
times the indicators of `[-1,1]` in both coordinates, is integrable on the plane. -/
private theorem integrable_prod_of_lintegral_Icc {g : ℝ → ℝ}
    (hgm : AEStronglyMeasurable g (volume : Measure ℝ))
    (hg : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1, ‖g q₁‖ₑ < ⊤) :
    Integrable (fun q : ℝ × ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) q.1 * g q.1
      * (Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) q.2)
      (volume : Measure (ℝ × ℝ)) := by
  classical
  have hgon : IntegrableOn g (Set.Icc (-1 : ℝ) 1) := ⟨hgm.restrict, hg⟩
  have hf1 : Integrable
      (fun q₁ : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) q₁ * g q₁)
      (volume : Measure ℝ) := by
    rw [show (fun q₁ : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) q₁ * g q₁)
        = (Set.Icc (-1 : ℝ) 1).indicator g from by
      funext x
      by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]]
    exact (integrable_indicator_iff measurableSet_Icc).mpr hgon
  have hf2 : Integrable
      (fun q₂ : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) q₂)
      (volume : Measure ℝ) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by simpa using isCompact_Icc.measure_lt_top (μ := (volume : Measure ℝ))))
  have hprod := hf1.mul_prod hf2
  exact hprod

/-! ## The main theorem -/

theorem JepsMarginalZero_Pi {α : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} {lam : ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f)
    (hlamm : Measurable lam)
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)))
    (htr : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
        Filter.Tendsto (fun θ => f z θ)
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds (lam z)))
    (hbd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
        ∀ θ ∈ Set.Ioo (Real.pi/4) (Real.pi/2),
        (f z θ - lam z)^2
          ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
            * (∫ σ in Work.Spaces.Iθ,
                (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2))
    (hjtr : ∀ z ∈ Set.Ioi (0:ℝ), Filter.Tendsto (fun θ => Work.FTS.StrongEps.Jeps ρ ε f z θ)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0)) :
    ∀ z ∈ Set.Ioi (0:ℝ),
      (∫ s : ℝ, (∫ t : ℝ, ρ (s, t)) * lam (z * Real.exp (-(ε * s)))) = 0 := by
  intro z hz
  set Dfun : ℝ → ℝ := fun u => ∫ σ in Work.Spaces.Iθ,
      (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2 with hDfun
  set Cα : ℝ := Real.sqrt (100 / (Work.Spaces.gam α - 1)) with hCα
  have hCα0 : 0 ≤ Cα := Real.sqrt_nonneg _
  have hgam1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by
    simp only [Work.Spaces.gam]; linarith [hα.1]
  have h100 : (0 : ℝ) ≤ 100 / (Work.Spaces.gam α - 1) := div_nonneg (by norm_num) (le_of_lt hgam1)
  have hCαsq : Cα ^ 2 = 100 / (Work.Spaces.gam α - 1) := Real.sq_sqrt h100
  -- the uniform bound on `ρ`
  obtain ⟨Cρ, hCρ0, hCρ⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ × ℝ, ‖ρ q‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      hρ.moll.cont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun q => ?_⟩
    by_cases hq : q ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1
    · exact le_trans (hC q hq) (le_max_left _ _)
    · have hq0 : ρ q = 0 := by
        by_contra hne
        have hle : q.1 ^ 2 + q.2 ^ 2 ≤ 1 := hρ.moll.support q hne
        have h1 : 1 < q.1 ^ 2 ∨ 1 < q.2 ^ 2 := by
          have hq' : ¬ (q.1 ∈ Set.Icc (-1 : ℝ) 1) ∨ ¬ (q.2 ∈ Set.Icc (-1 : ℝ) 1) := by
            simpa only [Set.mem_prod, not_and_or] using hq
          rcases hq' with h | h
          · rw [Set.mem_Icc, not_and_or] at h
            rcases h with h | h
            · left; rw [not_le] at h; nlinarith
            · left; rw [not_le] at h; nlinarith
          · rw [Set.mem_Icc, not_and_or] at h
            rcases h with h | h
            · right; rw [not_le] at h; nlinarith
            · right; rw [not_le] at h; nlinarith
        rcases h1 with h1 | h1 <;> nlinarith [sq_nonneg q.1, sq_nonneg q.2]
      simp [hq0]
  -- `ρ` vanishes off the square
  have hρvan : ∀ q : ℝ × ℝ, q ∉ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 → ρ q = 0 := by
    intro q hq
    by_contra hne
    have hle : q.1 ^ 2 + q.2 ^ 2 ≤ 1 := hρ.moll.support q hne
    have h1 : |q.1| ≤ 1 := by nlinarith [sq_nonneg q.2, abs_nonneg q.1, sq_abs q.1]
    have h2 : |q.2| ≤ 1 := by nlinarith [sq_nonneg q.1, abs_nonneg q.2, sq_abs q.2]
    exact hq (Set.mem_prod.mpr ⟨abs_le.mp h1, abs_le.mp h2⟩)
  -- `Dfun` is nonnegative
  have hDnn : ∀ u : ℝ, 0 ≤ Dfun u := by
    intro u
    rw [show Dfun u = ∫ σ in Work.Spaces.Iθ,
      (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2 from rfl]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc]
      with σ hσ
    refine mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ?_) _) (sq_nonneg _)
    exact ⟨by linarith [hσ.1], by linarith [hσ.2, Real.pi_pos]⟩
  -- (1) local integrability on the interval `[z e^{-ε}, z e^{ε}]`
  have hza : 0 < z * Real.exp (-ε) := mul_pos hz (Real.exp_pos _)
  have hzab : z * Real.exp (-ε) ≤ z * Real.exp ε :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hz.le
  have hDint : ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε),
      ENNReal.ofReal (Real.sqrt (Dfun u)) < ⊤ :=
    SqrtDLocInt hα hm (a := z * Real.exp (-ε)) (b := z * Real.exp ε) hza
  have hLamInt : ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε),
      ENNReal.ofReal |lam u| < ⊤ :=
    LamLocInt hα hso hlamm htr hbd (a := z * Real.exp (-ε)) (b := z * Real.exp ε) hza hzab hDint
  -- (2) the `lintegral` bounds of the two factors over `[-1,1]`
  have hgD_lint : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1,
      ENNReal.ofReal (Cρ * Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁))))) < ⊤ := by
    have h1 : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1,
        ENNReal.ofReal (Cρ * Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁)))))
        = ENNReal.ofReal (Cρ * Cα) * ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1,
            ENNReal.ofReal (Real.sqrt (Dfun (z * Real.exp (-(ε * q₁))))) := by
      rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Cρ * Cα)) _
        ENNReal.ofReal_lt_top.ne]
      refine MeasureTheory.lintegral_congr fun q₁ => ?_
      rw [ENNReal.ofReal_mul (mul_nonneg hCρ0 hCα0)]
    rw [h1]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact lt_of_le_of_lt
      (LintegralExpCompIcc hz hε (fun u => ENNReal.ofReal (Real.sqrt (Dfun u))))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDint)
  have hgL_lint : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1,
      ENNReal.ofReal (Cρ * |lam (z * Real.exp (-(ε * q₁)))|) < ⊤ := by
    have h1 : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1,
        ENNReal.ofReal (Cρ * |lam (z * Real.exp (-(ε * q₁)))|)
        = ENNReal.ofReal Cρ * ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1,
            ENNReal.ofReal |lam (z * Real.exp (-(ε * q₁)))| := by
      rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal Cρ) _ ENNReal.ofReal_lt_top.ne]
      refine MeasureTheory.lintegral_congr fun q₁ => ?_
      rw [ENNReal.ofReal_mul hCρ0]
    rw [h1]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact lt_of_le_of_lt
      (LintegralExpCompIcc hz hε (fun u => ENNReal.ofReal |lam u|))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hLamInt)
  -- (3) the factors, the bound and its integrability
  set gD : ℝ → ℝ := fun q₁ => Cρ * Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁)))) with hgD
  set gL : ℝ → ℝ := fun q₁ => Cρ * |lam (z * Real.exp (-(ε * q₁)))| with hgL
  set hI : ℝ → ℝ := fun q₂ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) q₂ with hhI
  have hgD_meas : AEStronglyMeasurable gD (volume : Measure ℝ) :=
    (SqrtDMeas hα hz hε hso).const_mul (Cρ * Cα)
  have hgL_meas : AEStronglyMeasurable gL (volume : Measure ℝ) :=
    ((hlamm.comp (by fun_prop : Measurable fun q₁ : ℝ => z * Real.exp (-(ε * q₁)))).abs).aestronglyMeasurable.const_mul Cρ
  have hgD_lint' : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1, ‖gD q₁‖ₑ < ⊤ := by
    rw [MeasureTheory.lintegral_congr (fun q₁ => ?_)]
    exact hgD_lint
    rw [Real.enorm_eq_ofReal_abs,
      show gD q₁ = Cρ * Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁)))) from rfl]
    congr 1
    exact abs_of_nonneg (mul_nonneg (mul_nonneg hCρ0 hCα0) (Real.sqrt_nonneg _))
  have hgL_lint' : ∫⁻ q₁ in Set.Icc (-1 : ℝ) 1, ‖gL q₁‖ₑ < ⊤ := by
    rw [MeasureTheory.lintegral_congr (fun q₁ => ?_)]
    exact hgL_lint
    rw [Real.enorm_eq_ofReal_abs,
      show gL q₁ = Cρ * |lam (z * Real.exp (-(ε * q₁)))| from rfl]
    congr 1
    exact abs_of_nonneg (mul_nonneg hCρ0 (abs_nonneg _))
  have hboundInt : Integrable (fun q : ℝ × ℝ => hI q.1 * gD q.1 * hI q.2)
      (volume : Measure (ℝ × ℝ)) :=
    integrable_prod_of_lintegral_Icc hgD_meas hgD_lint'
  have hkMajInt : Integrable (fun q : ℝ × ℝ => hI q.1 * gL q.1 * hI q.2)
      (volume : Measure (ℝ × ℝ)) :=
    integrable_prod_of_lintegral_Icc hgL_meas hgL_lint'
  -- (4) the trace part is integrable
  have hk : Integrable (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1))))
      (volume : Measure (ℝ × ℝ)) := by
    refine Integrable.mono' hkMajInt ?_ ?_
    · exact hρ.moll.cont.aestronglyMeasurable.mul
        ((hlamm.comp (by fun_prop : Measurable fun q : ℝ × ℝ => z * Real.exp (-(ε * q.1)))).aestronglyMeasurable)
    · filter_upwards with q
      by_cases hq : q ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1
      · have h1 : q.1 ∈ Set.Icc (-1 : ℝ) 1 := (Set.mem_prod.mp hq).1
        have h2 : q.2 ∈ Set.Icc (-1 : ℝ) 1 := (Set.mem_prod.mp hq).2
        have hle : ‖ρ q * lam (z * Real.exp (-(ε * q.1)))‖
            ≤ Cρ * |lam (z * Real.exp (-(ε * q.1)))| := by
          rw [norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hCρ q) (abs_nonneg _)
        rw [show hI q.1 = 1 from Set.indicator_of_mem h1 (fun _ => (1 : ℝ)),
          show hI q.2 = 1 from Set.indicator_of_mem h2 (fun _ => (1 : ℝ))]
        simpa using hle
      · rw [hρvan q hq, zero_mul, norm_zero]
        exact mul_nonneg (mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
          (mul_nonneg hCρ0 (abs_nonneg _))) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  -- (5) the a.e. "good in `q₁`" statement
  have hgood : ∀ᵐ u ∂(volume.restrict (Set.Ioi (0:ℝ))),
      (Filter.Tendsto (fun θ => f u θ) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds (lam u)))
      ∧ (∀ θ ∈ Set.Ioo (Real.pi/4) (Real.pi/2),
          (f u θ - lam u)^2 ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1) * Dfun u) := by
    filter_upwards [htr, hbd] with u h1 h2
    exact ⟨h1, fun θ hθ => h2 θ hθ⟩
  have hgood_q : ∀ᵐ q₁ ∂(volume : Measure ℝ),
      (Filter.Tendsto (fun θ => f (z * Real.exp (-(ε * q₁))) θ)
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds (lam (z * Real.exp (-(ε * q₁))))))
      ∧ (∀ θ ∈ Set.Ioo (Real.pi/4) (Real.pi/2),
          (f (z * Real.exp (-(ε * q₁))) θ - lam (z * Real.exp (-(ε * q₁))))^2
            ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
              * Dfun (z * Real.exp (-(ε * q₁)))) :=
    AeCompExpNeg hz hε hgood
  -- (6) the map `Gfun`
  set Gfun : ℝ → ℝ × ℝ → ℝ := fun θ q => ρ q *
    (f (z * Real.exp (-(ε * q.1))) (Real.arctan (Real.tan θ * Real.exp (-(ε * q.2))))
      - lam (z * Real.exp (-(ε * q.1)))) with hGfun
  have hGfun_meas : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      AEStronglyMeasurable (Gfun θ) (volume : Measure (ℝ × ℝ)) := by
    intro θ hθ
    have hΦcont : Continuous (fun q : ℝ × ℝ =>
        (z * Real.exp (-(ε * q.1)), Work.FTS.StrongEps.thShift θ (ε * q.2))) := by
      refine Continuous.prodMk ?_ ?_
      · fun_prop
      · simp only [Work.FTS.StrongEps.thShift]; fun_prop
    have hΦmem : ∀ q : ℝ × ℝ,
        (z * Real.exp (-(ε * q.1)), Work.FTS.StrongEps.thShift θ (ε * q.2)) ∈ Work.FTS.EllipticEst.Q0 := by
      intro q
      refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨?_, ?_, ?_⟩
      · exact mul_pos hz (Real.exp_pos _)
      · exact (Work.FTS.StrongEps.thShift_mem hθ).1
      · exact (Work.FTS.StrongEps.thShift_mem hθ).2
    have hf_cont : Continuous (fun q : ℝ × ℝ =>
        f (z * Real.exp (-(ε * q.1))) (Work.FTS.StrongEps.thShift θ (ε * q.2))) :=
      ((Work.FTS.EllipticEst.SmoothOpen.forall hso 0).continuousOn).comp_continuous hΦcont hΦmem
    have h1 : AEStronglyMeasurable (fun q : ℝ × ℝ =>
        f (z * Real.exp (-(ε * q.1))) (Work.FTS.StrongEps.thShift θ (ε * q.2)))
        (volume : Measure (ℝ × ℝ)) := hf_cont.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun q : ℝ × ℝ => lam (z * Real.exp (-(ε * q.1))))
        (volume : Measure (ℝ × ℝ)) :=
      (hlamm.comp (by fun_prop : Measurable fun q : ℝ × ℝ => z * Real.exp (-(ε * q.1)))).aestronglyMeasurable
    exact hρ.moll.cont.aestronglyMeasurable.mul (h1.sub h2)
  -- (7) the eventual set in `θ`
  have hS : Set.Ioo (0:ℝ) (Real.pi/2) ∩ {θ : ℝ | Real.exp ε < Real.tan θ}
      ∈ nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)) :=
    Filter.inter_mem (Ioo_mem_nhdsLT (by positivity))
      (Real.tendsto_tan_pi_div_two.eventually (eventually_gt_atTop (Real.exp ε)))
  have hbnd_pt : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) ∩ {θ : ℝ | Real.exp ε < Real.tan θ},
      ∀ᵐ q ∂(volume : Measure (ℝ × ℝ)), ‖Gfun θ q‖ ≤ hI q.1 * gD q.1 * hI q.2 := by
    intro θ hθS
    obtain ⟨hθ, htanθ⟩ := hθS
    have hae : ∀ᵐ q₁ ∂(volume : Measure ℝ), ∀ q₂ : ℝ,
        ‖Gfun θ (q₁, q₂)‖ ≤ hI q₁ * gD q₁ * hI q₂ := by
      filter_upwards [hgood_q] with q₁ hq₁ q₂
      obtain ⟨-, hbdq⟩ := hq₁
      by_cases hq1 : q₁ ∈ Set.Icc (-1 : ℝ) 1
      · by_cases hq2 : q₂ ∈ Set.Icc (-1 : ℝ) 1
        · -- main case: the `hbd` bound applies
          have hΘ : Work.FTS.StrongEps.thShift θ (ε * q₂) ∈ Set.Ioo (Real.pi/4) (Real.pi/2) := by
            refine ⟨?_, (Work.FTS.StrongEps.thShift_mem hθ).2⟩
            have hexp : Real.exp (-ε) ≤ Real.exp (-(ε * q₂)) :=
              Real.exp_le_exp.mpr (by nlinarith [hq2.2])
            have h1 : 1 < Real.tan θ * Real.exp (-(ε * q₂)) := by
              have h2 : 1 < Real.tan θ * Real.exp (-ε) := by
                have hmul : Real.exp ε * Real.exp (-ε) = 1 := by
                  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
                rw [← hmul]
                exact mul_lt_mul_of_pos_right htanθ (Real.exp_pos (-ε))
              exact lt_of_lt_of_le h2
                (mul_le_mul_of_nonneg_left hexp (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2).le)
            calc Real.pi/4 = Real.arctan 1 := Real.arctan_one.symm
              _ < Real.arctan (Real.tan θ * Real.exp (-(ε * q₂))) := Real.arctan_strictMono h1
              _ = Work.FTS.StrongEps.thShift θ (ε * q₂) := rfl
          have hbd' := hbdq (Work.FTS.StrongEps.thShift θ (ε * q₂)) hΘ
          have hsin1 : (Real.sin (2 * Work.FTS.StrongEps.thShift θ (ε * q₂)))
              ^ (Work.Spaces.gam α - 1) ≤ 1 := by
            refine Real.rpow_le_one ?_ ?_ (le_of_lt hgam1)
            · exact Real.sin_nonneg_of_mem_Icc
                ⟨by linarith [hΘ.1, Real.pi_pos], by linarith [hΘ.2, Real.pi_pos]⟩
            · exact Real.sin_le_one _
          have hsq : (f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
              - lam (z * Real.exp (-(ε * q₁)))) ^ 2 ≤ (Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁))))) ^ 2 := by
            calc (f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
                  - lam (z * Real.exp (-(ε * q₁)))) ^ 2
                ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2 * Work.FTS.StrongEps.thShift θ (ε * q₂)))
                    ^ (Work.Spaces.gam α - 1) * Dfun (z * Real.exp (-(ε * q₁))) := hbd'
              _ ≤ 100 / (Work.Spaces.gam α - 1) * 1 * Dfun (z * Real.exp (-(ε * q₁))) := by
                  refine mul_le_mul_of_nonneg_right ?_ (hDnn _)
                  exact mul_le_mul_of_nonneg_left hsin1 h100
              _ = (Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁))))) ^ 2 := by
                  rw [mul_pow, hCαsq, Real.sq_sqrt (hDnn _)]
                  ring
          have habs : |f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
              - lam (z * Real.exp (-(ε * q₁)))| ≤ Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁)))) := by
            calc |f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
                  - lam (z * Real.exp (-(ε * q₁)))|
                = Real.sqrt ((f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
                  - lam (z * Real.exp (-(ε * q₁)))) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
              _ ≤ Real.sqrt ((Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁))))) ^ 2) := Real.sqrt_le_sqrt hsq
              _ = Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁)))) := by
                  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hCα0 (Real.sqrt_nonneg _))]
          have hmain : ‖Gfun θ (q₁, q₂)‖ ≤ Cρ * (Cα * Real.sqrt (Dfun (z * Real.exp (-(ε * q₁))))) := by
            rw [show Gfun θ (q₁, q₂) = ρ (q₁, q₂) * (f (z * Real.exp (-(ε * q₁)))
                (Work.FTS.StrongEps.thShift θ (ε * q₂)) - lam (z * Real.exp (-(ε * q₁)))) from rfl,
              norm_mul, Real.norm_eq_abs]
            exact mul_le_mul (hCρ (q₁, q₂)) habs (abs_nonneg _) hCρ0
          rw [show hI q₁ = 1 from Set.indicator_of_mem hq1 (fun _ => (1 : ℝ)),
            show hI q₂ = 1 from Set.indicator_of_mem hq2 (fun _ => (1 : ℝ))]
          simpa [gD, mul_assoc] using hmain
        · -- `q₂` outside the square: `ρ` vanishes
          have hq2' : ¬ (q₂ ∈ Set.Icc (-1 : ℝ) 1) := hq2
          have h0 : ρ (q₁, q₂) = 0 := by
            refine hρvan (q₁, q₂) fun hc => hq2' (Set.mem_prod.mp hc).2
          rw [show Gfun θ (q₁, q₂) = ρ (q₁, q₂) * (f (z * Real.exp (-(ε * q₁)))
              (Work.FTS.StrongEps.thShift θ (ε * q₂)) - lam (z * Real.exp (-(ε * q₁)))) from rfl, h0, zero_mul,
            norm_zero, show hI q₂ = 0 from Set.indicator_of_notMem hq2 (fun _ => (1 : ℝ))]
          simp
      · -- `q₁` outside the square: `ρ` vanishes
        have h0 : ρ (q₁, q₂) = 0 := by
          refine hρvan (q₁, q₂) fun hc => hq1 (Set.mem_prod.mp hc).1
        rw [show Gfun θ (q₁, q₂) = ρ (q₁, q₂) * (f (z * Real.exp (-(ε * q₁)))
            (Work.FTS.StrongEps.thShift θ (ε * q₂)) - lam (z * Real.exp (-(ε * q₁)))) from rfl, h0, zero_mul,
          norm_zero, show hI q₁ = 0 from Set.indicator_of_notMem hq1 (fun _ => (1 : ℝ))]
        simp
    exact ae_prod_of_ae_fst hae
  -- (8) integrability of `Gfun θ` for `θ` in the eventual set
  have hGint : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) ∩ {θ : ℝ | Real.exp ε < Real.tan θ},
      Integrable (Gfun θ) (volume : Measure (ℝ × ℝ)) := by
    intro θ hθS
    refine Integrable.mono' hboundInt (hGfun_meas θ hθS.1) ?_
    filter_upwards [hbnd_pt θ hθS] with q hq
    exact hq
  -- (9) the dominated convergence
  have hbnd_ev : ∀ᶠ θ in nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)),
      ∀ᵐ q ∂(volume : Measure (ℝ × ℝ)), ‖Gfun θ q‖ ≤ hI q.1 * gD q.1 * hI q.2 :=
    Filter.eventually_of_mem hS hbnd_pt
  have hmeas_ev : ∀ᶠ θ in nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)),
      AEStronglyMeasurable (Gfun θ) (volume : Measure (ℝ × ℝ)) :=
    Filter.eventually_of_mem hS (fun θ hθ => hGfun_meas θ hθ.1)
  have hlim : ∀ᵐ q ∂(volume : Measure (ℝ × ℝ)), Tendsto (fun θ => Gfun θ q)
      (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := by
    have hae : ∀ᵐ q₁ ∂(volume : Measure ℝ), ∀ q₂ : ℝ,
        Tendsto (fun θ => Gfun θ (q₁, q₂)) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := by
      filter_upwards [hgood_q] with q₁ hq₁ q₂
      obtain ⟨htrq, -⟩ := hq₁
      have hshift : Tendsto (fun θ : ℝ => Work.FTS.StrongEps.thShift θ (ε * q₂))
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)))
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) :=
        Real.tendsto_arctan_atTop.comp
          (Real.tendsto_tan_pi_div_two.atTop_mul_const (Real.exp_pos (-(ε * q₂))))
      have h1 : Tendsto (fun θ : ℝ => f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂)))
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds (lam (z * Real.exp (-(ε * q₁))))) :=
        htrq.comp hshift
      have h2 : Tendsto (fun θ : ℝ => f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
          - lam (z * Real.exp (-(ε * q₁)))) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)))
          (nhds (lam (z * Real.exp (-(ε * q₁))) - lam (z * Real.exp (-(ε * q₁))))) :=
        h1.sub tendsto_const_nhds
      have h3 : Tendsto (fun θ : ℝ => ρ (q₁, q₂) *
          (f (z * Real.exp (-(ε * q₁))) (Work.FTS.StrongEps.thShift θ (ε * q₂))
            - lam (z * Real.exp (-(ε * q₁)))))
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := by
        simpa [sub_self] using h2.const_mul (ρ (q₁, q₂))
      have h3' : Tendsto (fun θ : ℝ => ρ (q₁, q₂) *
          (f (z * Real.exp (-(ε * q₁))) (Real.arctan (Real.tan θ * Real.exp (-(ε * q₂))))
            - lam (z * Real.exp (-(ε * q₁)))))
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := h3
      simpa [Gfun] using h3'
    exact ae_prod_of_ae_fst hae
  have hDCT : Tendsto (fun θ => ∫ q, Gfun θ q) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := by
    have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure (ℝ × ℝ))) (F := Gfun) (f := fun _ => (0 : ℝ))
      (bound := fun q => hI q.1 * gD q.1 * hI q.2) hmeas_ev hbnd_ev hboundInt hlim
    simpa using h
  -- (10) assemble
  set A : ℝ := ∫ q : ℝ × ℝ, ρ q * lam (z * Real.exp (-(ε * q.1))) with hA
  have hKey : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) ∩ {θ : ℝ | Real.exp ε < Real.tan θ},
      Work.FTS.StrongEps.Jeps ρ ε f z θ = (∫ q, Gfun θ q) + A := by
    intro θ hθS
    rw [JepsRhoForm ρ ε f hε hz hθS.1]
    have h1 : Integrable (fun q : ℝ × ℝ => ρ q * (f (z * Real.exp (-(ε * q.1)))
        (Real.arctan (Real.tan θ * Real.exp (-(ε * q.2)))) - lam (z * Real.exp (-(ε * q.1)))))
        (volume : Measure (ℝ × ℝ)) := hGint θ hθS
    have h2 : Integrable (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1))))
        (volume : Measure (ℝ × ℝ)) := hk
    have hpt : ∀ q : ℝ × ℝ, ρ q * f (z * Real.exp (-(ε * q.1))) (Real.arctan (Real.tan θ * Real.exp (-(ε * q.2))))
        = ρ q * (f (z * Real.exp (-(ε * q.1))) (Real.arctan (Real.tan θ * Real.exp (-(ε * q.2))))
            - lam (z * Real.exp (-(ε * q.1)))) + ρ q * lam (z * Real.exp (-(ε * q.1))) :=
      fun q => by ring
    rw [MeasureTheory.integral_congr_ae (Eventually.of_forall hpt), MeasureTheory.integral_add h1 h2]
  have hA0 : A = 0 := by
    have h1 : Tendsto (fun θ => (∫ q, Gfun θ q) + A) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) :=
      (hjtr z hz).congr' (Filter.eventually_of_mem hS hKey)
    have h2 : Tendsto (fun θ => (∫ q, Gfun θ q) + A) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)))
        (nhds (0 + A)) := hDCT.add tendsto_const_nhds
    have h3 := tendsto_nhds_unique h1 h2
    linarith
  rw [← RhoMargFubini hε hk]
  exact hA0

end Work.FTS.StrongEps.EpsLocalPStar
