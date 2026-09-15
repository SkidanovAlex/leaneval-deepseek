import Mathlib
import Submission.Commons.Analysis.Convolution.contDiff_integral_mul_sub
import Submission.Commons.Analysis.Convolution.fderiv_integral_mul_sub
import Submission.Commons.Analysis.Convolution.tendsto_integral_norm_sq_moll_sub_compact_complex
import Submission.Commons.Analysis.Convolution.fderiv_moll_weakGrad
import Submission.Commons.Analysis.Complex.differentiable_complex_of_dbar_eq_zero
import Submission.Commons.Analysis.Complex.meanValue_polydisc
import Submission.Commons.Analysis.Complex.norm_le_integral_of_differentiable_complex
import Submission.Commons.Analysis.Complex.exists_bound_norm_fderiv_sq_of_differentiable_complex
import Submission.Commons.Analysis.Sobolev.integral_mul_eq_neg_integral_fderiv_of_contDiff_two
import Submission.Commons.Analysis.Complex.fderiv_bound_uniform_of_differentiable_complex

set_option maxHeartbeats 1000000

open MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace Commons.Analysis.Complex

variable {d : ℕ}

/-! ## Auxiliary lemmas -/

/-- Translation/reflection invariance of the Lebesgue integral on `Fin d → ℂ`:
the convolution `∫ t, ρ (z - t) • F t` may be written `∫ y, ρ y • F (z - y)`. -/
theorem integral_shift_sub {F : (Fin d → ℂ) → ℂ} (ρ : (Fin d → ℂ) → ℝ) (z : Fin d → ℂ) :
    (∫ t, ρ (z - t) • F t) = ∫ y, ρ y • F (z - y) := by
  set f : (Fin d → ℂ) → ℂ := fun w => ρ w • F (z - w) with hf
  have key : (∫ t, f (z - t)) = ∫ t, f t := by
    have h1 : (∫ t, f (z - t)) = ∫ t, f (z + (-t)) := by
      apply integral_congr_ae; filter_upwards with t; rw [sub_eq_add_neg]
    have h2 : (∫ t, f (z + (-t))) = ∫ t, f (z + t) := by
      have h := integral_neg_eq_self (fun s : Fin d → ℂ => f (z + s)) (volume : Measure (Fin d → ℂ))
      simpa only using h
    have h3 : (∫ t, f (z + t)) = ∫ t, f t := integral_add_left_eq_self f z
    rw [h1, h2, h3]
  have hleft : (∫ t, ρ (z - t) • F t) = ∫ t, f (z - t) := by
    apply integral_congr_ae; filter_upwards with t
    rw [hf]; simp only [sub_sub_cancel]
  rw [hleft, key, hf]

/-- The Wirtinger condition tested against real-valued test functions. -/
theorem weak_real {F : (Fin d → ℂ) → ℂ}
    (hweak : ∀ (j : Fin d) (ξ : (Fin d → ℂ) → ℂ),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ξ → HasCompactSupport ξ →
      ∫ x, F x * ((fderiv ℝ ξ x (Pi.single j (1 : ℂ))
        + Complex.I * fderiv ℝ ξ x (Pi.single j Complex.I)) / 2)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) = 0) :
    ∀ (j : Fin d) (φ : (Fin d → ℂ) → ℝ),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ → HasCompactSupport φ →
      ∫ x, F x * ((((fderiv ℝ φ x (Pi.single j (1 : ℂ)) : ℝ) : ℂ)
        + Complex.I * ((fderiv ℝ φ x (Pi.single j Complex.I) : ℝ) : ℂ)) / 2)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) = 0 := by
  intro j φ hφC hφs
  have hξC : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun y => (φ y : ℂ)) := by
    have h := Complex.ofRealCLM.contDiff.comp hφC
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h
  have hξs : HasCompactSupport (fun y => (φ y : ℂ)) := by
    have h := HasCompactSupport.comp_left hφs (g := fun r : ℝ => (r : ℂ)) (by simp)
    simpa only [Function.comp_def] using h
  have hfun : (fun x => F x * ((fderiv ℝ (fun y : Fin d → ℂ => (φ y : ℂ)) x (Pi.single j (1 : ℂ))
        + Complex.I * fderiv ℝ (fun y : Fin d → ℂ => (φ y : ℂ)) x (Pi.single j Complex.I)) / 2))
      = fun x => F x * ((((fderiv ℝ φ x (Pi.single j (1 : ℂ)) : ℝ) : ℂ)
        + Complex.I * ((fderiv ℝ φ x (Pi.single j Complex.I) : ℝ) : ℂ)) / 2) := by
    funext x
    have hd : fderiv ℝ (fun y : Fin d → ℂ => (φ y : ℂ)) x
        = Complex.ofRealCLM.comp (fderiv ℝ φ x) := by
      have h : HasFDerivAt (fun y : Fin d → ℂ => (φ y : ℂ))
          (Complex.ofRealCLM.comp (fderiv ℝ φ x)) x :=
        Complex.ofRealCLM.hasFDerivAt.comp x ((hφC.differentiable (by simp)).differentiableAt).hasFDerivAt
      exact h.fderiv
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  have h := hweak j (fun y => (φ y : ℂ)) hξC hξs
  rw [hfun] at h
  exact h

/-- The Wirtinger `∂̄`-equations for the mollification of `F` by a real-valued `C^∞`
compactly supported kernel. -/
theorem dbar_moll {F : (Fin d → ℂ) → ℂ}
    (hF1 : MeasureTheory.LocallyIntegrable F
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
    (hweak : ∀ (j : Fin d) (ξ : (Fin d → ℂ) → ℂ),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ξ → HasCompactSupport ξ →
      ∫ x, F x * ((fderiv ℝ ξ x (Pi.single j (1 : ℂ))
        + Complex.I * fderiv ℝ ξ x (Pi.single j Complex.I)) / 2)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) = 0)
    {ρ : (Fin d → ℂ) → ℝ} (hρC : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ρ)
    (hρs : HasCompactSupport ρ) :
    ∀ (j : Fin d) (z : Fin d → ℂ),
      (fderiv ℝ (fun z => ∫ t, ρ (z - t) • F t) z) (Pi.single j 1)
        + Complex.I * (fderiv ℝ (fun z => ∫ t, ρ (z - t) • F t) z) (Pi.single j Complex.I) = 0 := by
  intro j z
  have hweakR := weak_real hweak
  set φ : (Fin d → ℂ) → ℝ := fun y => ρ (z - y) with hφ
  have hφC : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ := by
    rw [hφ]
    have h := hρC.comp ((contDiff_const (c := z)).sub contDiff_id)
    simpa only [Function.comp_def, Pi.sub_apply, id_eq] using h
  have hφs : HasCompactSupport φ := by
    rw [hφ]
    have h := hρs.comp_homeomorph (Homeomorph.subLeft z)
    simpa only [Function.comp_def, Homeomorph.subLeft_apply] using h
  have hρdiff : Differentiable ℝ ρ := hρC.differentiable (by simp)
  have hφderiv : ∀ t : Fin d → ℂ,
      fderiv ℝ φ t = (fderiv ℝ ρ (z - t)).comp (-1 : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ)) := by
    intro t
    rw [hφ]
    exact Commons.Analysis.Convolution.fderiv_comp_sub ρ z t (hρdiff.differentiableAt)
  have hcont1 : Continuous (fun t : Fin d → ℂ => (fderiv ℝ ρ (z - t)) (Pi.single j (1:ℂ))) :=
    (hρC.continuous_fderiv_apply (by simp)).comp
      ((continuous_const.sub continuous_id).prodMk continuous_const)
  have hcomp1 : HasCompactSupport (fun t : Fin d → ℂ => (fderiv ℝ ρ (z - t)) (Pi.single j (1:ℂ))) := by
    have h1 : HasCompactSupport (fun t : Fin d → ℂ => fderiv ℝ ρ (z - t)) := by
      have h := (hρs.fderiv ℝ).comp_homeomorph (Homeomorph.subLeft z)
      simpa only [Function.comp_def, Homeomorph.subLeft_apply] using h
    refine HasCompactSupport.comp_left h1
      (g := fun (L : (Fin d → ℂ) →L[ℝ] ℝ) => L (Pi.single j (1:ℂ))) ?_
    show (0 : (Fin d → ℂ) →L[ℝ] ℝ) (Pi.single j (1:ℂ)) = 0
    exact zero_apply _
  have hcont2 : Continuous (fun t : Fin d → ℂ => (fderiv ℝ ρ (z - t)) (Pi.single j Complex.I)) :=
    (hρC.continuous_fderiv_apply (by simp)).comp
      ((continuous_const.sub continuous_id).prodMk continuous_const)
  have hcomp2 : HasCompactSupport (fun t : Fin d → ℂ => (fderiv ℝ ρ (z - t)) (Pi.single j Complex.I)) := by
    have h1 : HasCompactSupport (fun t : Fin d → ℂ => fderiv ℝ ρ (z - t)) := by
      have h := (hρs.fderiv ℝ).comp_homeomorph (Homeomorph.subLeft z)
      simpa only [Function.comp_def, Homeomorph.subLeft_apply] using h
    refine HasCompactSupport.comp_left h1
      (g := fun (L : (Fin d → ℂ) →L[ℝ] ℝ) => L (Pi.single j Complex.I)) ?_
    show (0 : (Fin d → ℂ) →L[ℝ] ℝ) (Pi.single j Complex.I) = 0
    exact zero_apply _
  have hInt1 : Integrable (fun t : Fin d → ℂ => (fderiv ℝ ρ (z - t)) (Pi.single j (1:ℂ)) • F t)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
    hF1.integrable_smul_left_of_hasCompactSupport hcont1 hcomp1
  have hInt2 : Integrable (fun t : Fin d → ℂ => (fderiv ℝ ρ (z - t)) (Pi.single j Complex.I) • F t)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
    hF1.integrable_smul_left_of_hasCompactSupport hcont2 hcomp2
  have hpt : ∀ t : Fin d → ℂ,
      (fderiv ℝ ρ (z - t)) (Pi.single j (1:ℂ)) • F t
        + Complex.I * ((fderiv ℝ ρ (z - t)) (Pi.single j Complex.I) • F t)
      = -2 * (F t * ((((fderiv ℝ φ t (Pi.single j (1:ℂ)) : ℝ) : ℂ)
          + Complex.I * ((fderiv ℝ φ t (Pi.single j Complex.I) : ℝ) : ℂ)) / 2)) := by
    intro t
    rw [hφderiv t]
    simp only [ContinuousLinearMap.comp_apply, neg_apply, one_apply_eq_self, map_neg]
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [Commons.Analysis.Convolution.fderiv_integral_mul_sub hρC hρs hF1 z (Pi.single j 1),
      Commons.Analysis.Convolution.fderiv_integral_mul_sub hρC hρs hF1 z (Pi.single j Complex.I)]
  rw [← integral_const_mul Complex.I
    (fun t : Fin d → ℂ => (fderiv ℝ ρ (z - t)) (Pi.single j Complex.I) • F t)]
  rw [← integral_add hInt1 (hInt2.const_mul Complex.I)]
  rw [show (fun t : Fin d → ℂ => (fderiv ℝ ρ (z - t)) (Pi.single j (1:ℂ)) • F t
      + Complex.I * ((fderiv ℝ ρ (z - t)) (Pi.single j Complex.I) • F t))
      = fun t => -2 * (F t * ((((fderiv ℝ φ t (Pi.single j (1:ℂ)) : ℝ) : ℂ)
          + Complex.I * ((fderiv ℝ φ t (Pi.single j Complex.I) : ℝ) : ℂ)) / 2))
      from funext hpt]
  rw [integral_const_mul, hweakR j φ hφC hφs]
  ring

/-- Mollifications of a locally integrable function satisfying the weak Wirtinger equations
are complex differentiable. -/
theorem differentiable_moll {F : (Fin d → ℂ) → ℂ}
    (hF1 : MeasureTheory.LocallyIntegrable F
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
    (hweak : ∀ (j : Fin d) (ξ : (Fin d → ℂ) → ℂ),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ξ → HasCompactSupport ξ →
      ∫ x, F x * ((fderiv ℝ ξ x (Pi.single j (1 : ℂ))
        + Complex.I * fderiv ℝ ξ x (Pi.single j Complex.I)) / 2)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) = 0)
    {ρ : (Fin d → ℂ) → ℝ} (hρC : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ρ)
    (hρs : HasCompactSupport ρ) :
    Differentiable ℂ (fun z => ∫ t, ρ (z - t) • F t) :=
  differentiable_complex_of_dbar_eq_zero
    ((Commons.Analysis.Convolution.contDiff_integral_mul_sub hρC hρs hF1).differentiable (by simp))
    (dbar_moll hF1 hweak hρC hρs)

/-- Mean value inequality with an explicit constant: for a complex differentiable `g` and `r > 0`,
`‖g z‖ ^ 2 ≤ ((π r ^ 2) ^ d)⁻¹ * ∫_{closedBall z r} ‖g‖ ^ 2`. -/
theorem norm_sq_le_inv_polydisc_mul_integral {g : (Fin d → ℂ) → ℂ}
    (hg : Differentiable ℂ g) {z : Fin d → ℂ} {r : ℝ} (hr : 0 < r) :
    ‖g z‖ ^ 2 ≤ ((Real.pi * r ^ 2) ^ d)⁻¹ *
      ∫ w in Metric.closedBall z r, ‖g w‖ ^ 2
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
  have h := norm_le_integral_of_differentiable_complex hg (z := z) hr
  rwa [polydisc_volume z hr] at h

/-- Integrability of `‖u - v‖ ^ 2` on a compact set, for `u` continuous and `v` locally square
integrable. -/
theorem integrableOn_sq_sub_of_continuous_of_locallyIntegrable {u : (Fin d → ℂ) → ℂ}
    {v : (Fin d → ℂ) → ℂ} (hu : Continuous u)
    (hv : MeasureTheory.LocallyIntegrable v
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
    (hv2 : MeasureTheory.LocallyIntegrable (fun y => ‖v y‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
    {K : Set (Fin d → ℂ)} (hK : IsCompact K) :
    IntegrableOn (fun y => ‖u y - v y‖ ^ 2) K
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
  have hmeas : AEStronglyMeasurable (fun y => ‖u y - v y‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
    ((hu.aestronglyMeasurable.sub hv.aestronglyMeasurable).norm).pow 2
  have h1 : Integrable (fun y => ‖u y‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict K) :=
    ContinuousOn.integrableOn_compact hK (hu.norm.pow 2).continuousOn
  have h2 : Integrable (fun y => ‖v y‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict K) :=
    hv2.integrableOn_isCompact hK
  have hdom : Integrable (fun y => 2 * ‖u y‖ ^ 2 + 2 * ‖v y‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict K) :=
    (h1.const_mul 2).add (h2.const_mul 2)
  show Integrable (fun y => ‖u y - v y‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict K)
  refine hdom.mono' (hmeas.mono_measure Measure.restrict_le_self) ?_
  filter_upwards with y
  rw [Real.norm_of_nonneg (by positivity)]
  have h1' : ‖u y - v y‖ ≤ ‖u y‖ + ‖v y‖ := norm_sub_le _ _
  calc ‖u y - v y‖ ^ 2 ≤ (‖u y‖ + ‖v y‖) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) h1'
      _ ≤ 2 * ‖u y‖ ^ 2 + 2 * ‖v y‖ ^ 2 := by
        nlinarith [sq_nonneg (‖u y‖ - ‖v y‖)]


/-- A sequence of mollifiers on `Fin d → ℂ` (which has no inner product space structure, so the
general commons lemma does not apply). -/
private theorem exists_mollifier_sequence_fin :
    ∃ (ρ : ℕ → (Fin d → ℂ) → ℝ) (R : ℕ → ℝ),
      (∀ n, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (ρ n)) ∧ (∀ n, HasCompactSupport (ρ n)) ∧
      (∀ n, Continuous (ρ n)) ∧ (∀ n, Integrable (ρ n) (volume : Measure (Fin d → ℂ))) ∧
      (∀ n x, 0 ≤ ρ n x) ∧ (∀ n, ∫ x, ρ n x = 1) ∧
      (∀ n, 0 ≤ R n) ∧ Tendsto R atTop (𝓝 0) ∧
      (∀ n x, R n < ‖x‖ → ρ n x = 0) := by
  let f : ℕ → ContDiffBump (0 : Fin d → ℂ) :=
    fun n => ⟨1 / ((n:ℝ) + 1), 2 / ((n:ℝ) + 1), by positivity,
      by rw [div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < (n:ℝ)+1)]; norm_num⟩
  refine ⟨fun n => (f n).normed volume, fun n => 2 / ((n:ℝ) + 1),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n; exact (f n).contDiff_normed
  · intro n; exact (f n).hasCompactSupport_normed
  · intro n; exact (f n).continuous_normed
  · intro n; exact (f n).integrable_normed
  · intro n x; exact (f n).nonneg_normed x
  · intro n; exact (f n).integral_normed
  · intro n; positivity
  · convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2 using 1
    · ext n; rw [div_eq_mul_one_div]
    · rw [mul_zero]
  · intro n x hx
    have hmem : x ∉ Function.support ((f n).normed volume) := by
      rw [(f n).support_normed_eq]
      simp only [Metric.mem_ball, dist_zero_right, not_lt]
      exact le_of_lt hx
    exact Function.notMem_support.mp hmem


/-- From `x ^ 2 ≤ ε ^ 2` and `0 < ε` deduce `x ≤ ε`. -/
private lemma le_of_sq_le_sq {x ε : ℝ} (hε : 0 < ε) (h : x ^ 2 ≤ ε ^ 2) : x ≤ ε := by
  by_contra hx
  have hx' : ε < x := not_le.mp hx
  have h1 : 0 < x + ε := by linarith
  have h2 : 0 < x - ε := by linarith
  nlinarith [h, mul_pos h2 h1]

/-! ## Complex differentiability of weakly holomorphic locally square integrable functions -/

theorem weyl_dbar {d : ℕ} {F : (Fin d → ℂ) → ℂ}
    (hF1 : MeasureTheory.LocallyIntegrable F
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
    (hF2 : MeasureTheory.LocallyIntegrable (fun z => ‖F z‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
    (hweak : ∀ (j : Fin d) (ξ : (Fin d → ℂ) → ℂ),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ξ → HasCompactSupport ξ →
      ∫ x, F x * ((fderiv ℝ ξ x (Pi.single j (1 : ℂ))
        + Complex.I * fderiv ℝ ξ x (Pi.single j Complex.I)) / 2)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) = 0) :
    ∃ H : (Fin d → ℂ) → ℂ, Differentiable ℂ H ∧ F =ᵐ[MeasureTheory.volume] H := by
  classical
  obtain ⟨ρ, R, hρC, hρs, hρc, hρi, hρnn, hρ1, hR0, hR, hRs⟩ := exists_mollifier_sequence_fin (d := d)
  -- the mollifications of `F`
  let G : ℕ → (Fin d → ℂ) → ℂ := fun n z => ∫ t, ρ n (z - t) • F t
  have hGdiff : ∀ n, Differentiable ℂ (G n) := fun n =>
    differentiable_moll hF1 hweak (hρC n) (hρs n)
  -- `L²` convergence of the mollifications on closed balls
  have hconv : ∀ (x : Fin d → ℂ) (r : ℝ),
      Tendsto (fun n => ∫ y in Metric.closedBall x r, ‖G n y - F y‖ ^ 2) atTop (𝓝 0) := by
    intro x r
    have h := Commons.Analysis.Convolution.tendsto_integral_norm_sq_moll_sub_compact_complex
      ρ R hρnn hρi hρ1 hR0 hR hRs F hF1 hF2 (Metric.closedBall x r) (isCompact_closedBall x r)
    refine h.congr' ?_
    filter_upwards with n
    apply integral_congr_ae
    filter_upwards with y
    show ‖(∫ t, ρ n t • F (y - t)) - F y‖ ^ 2 = ‖G n y - F y‖ ^ 2
    rw [show G n y = ∫ t, ρ n t • F (y - t) from integral_shift_sub (ρ n) y]
  -- the mean value bound with explicit constant
  have hMV : ∀ {h : (Fin d → ℂ) → ℂ}, Differentiable ℂ h → ∀ (x y : Fin d → ℂ) (r : ℝ),
      y ∈ Metric.closedBall x r →
      ‖h y‖ ^ 2 ≤ (Real.pi ^ d)⁻¹ * ∫ w in Metric.closedBall x (r + 1), ‖h w‖ ^ 2 := by
    intro h hh x y r hy
    have h1 := norm_sq_le_inv_polydisc_mul_integral hh (z := y) (r := 1) one_pos
    have hint : IntegrableOn (fun w => ‖h w‖ ^ 2) (Metric.closedBall x (r + 1))
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
      ContinuousOn.integrableOn_compact (isCompact_closedBall x (r + 1))
        ((hh.continuous.norm.pow 2).continuousOn)
    have hsub : Metric.closedBall y 1 ⊆ Metric.closedBall x (r + 1) := by
      intro w hw
      rw [mem_closedBall] at hw hy ⊢
      calc dist w x ≤ dist w y + dist y x := dist_triangle w y x
        _ ≤ 1 + r := add_le_add hw hy
        _ = r + 1 := by ring
    have hmono : ∫ w in Metric.closedBall y 1, ‖h w‖ ^ 2
        ≤ ∫ w in Metric.closedBall x (r + 1), ‖h w‖ ^ 2 :=
      setIntegral_mono_set hint (Eventually.of_forall (fun w => by positivity))
        (Eventually.of_forall (fun w hw => hsub hw))
    calc ‖h y‖ ^ 2 ≤ ((Real.pi * 1 ^ 2) ^ d)⁻¹ * ∫ w in Metric.closedBall y 1, ‖h w‖ ^ 2 := h1
      _ ≤ ((Real.pi * 1 ^ 2) ^ d)⁻¹ *
            ∫ w in Metric.closedBall x (r + 1), ‖h w‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (Real.pi ^ d)⁻¹ * ∫ w in Metric.closedBall x (r + 1), ‖h w‖ ^ 2 := by
          simp only [one_pow, mul_one]
  -- uniform Cauchy property of the values on balls
  have hcauchy : ∀ (x : Fin d → ℂ) (r ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      ∀ y ∈ Metric.closedBall x r, ‖G n y - G m y‖ ≤ ε := by
    intro x r ε hε
    have hprod : Tendsto (fun p : ℕ × ℕ =>
        ∫ y in Metric.closedBall x (r + 1), ‖G p.1 y - G p.2 y‖ ^ 2)
        (atTop ×ˢ atTop) (𝓝 0) := by
      have hA : Tendsto (fun p : ℕ × ℕ =>
          ∫ y in Metric.closedBall x (r + 1), ‖G p.1 y - F y‖ ^ 2)
          (atTop ×ˢ atTop) (𝓝 0) := (hconv x (r + 1)).comp tendsto_fst
      have hB : Tendsto (fun p : ℕ × ℕ =>
          ∫ y in Metric.closedBall x (r + 1), ‖G p.2 y - F y‖ ^ 2)
          (atTop ×ˢ atTop) (𝓝 0) := (hconv x (r + 1)).comp tendsto_snd
      have hg : Tendsto (fun p : ℕ × ℕ =>
          2 * (∫ y in Metric.closedBall x (r + 1), ‖G p.1 y - F y‖ ^ 2)
            + 2 * (∫ y in Metric.closedBall x (r + 1), ‖G p.2 y - F y‖ ^ 2))
          (atTop ×ˢ atTop) (𝓝 0) := by
        have h := (hA.const_mul 2).add (hB.const_mul 2)
        simpa using h
      refine squeeze_zero (fun p => by positivity) (fun p => ?_) hg
      obtain ⟨n, m⟩ := p
      have h1 : IntegrableOn (fun y => ‖G n y - G m y‖ ^ 2) (Metric.closedBall x (r + 1))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
        integrableOn_sq_sub_of_continuous_of_locallyIntegrable (u := G n) (v := G m)
          ((hGdiff n).continuous)
          (((hGdiff m).continuous).locallyIntegrable)
          ((((hGdiff m).continuous).norm.pow 2).locallyIntegrable) (isCompact_closedBall _ _)
      have ha : IntegrableOn (fun y => ‖G n y - F y‖ ^ 2) (Metric.closedBall x (r + 1))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
        integrableOn_sq_sub_of_continuous_of_locallyIntegrable (u := G n) (v := F)
          ((hGdiff n).continuous) hF1 hF2 (isCompact_closedBall _ _)
      have hb : IntegrableOn (fun y => ‖G m y - F y‖ ^ 2) (Metric.closedBall x (r + 1))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
        integrableOn_sq_sub_of_continuous_of_locallyIntegrable (u := G m) (v := F)
          ((hGdiff m).continuous) hF1 hF2 (isCompact_closedBall _ _)
      have h2 : IntegrableOn (fun y => 2 * ‖G n y - F y‖ ^ 2 + 2 * ‖G m y - F y‖ ^ 2)
          (Metric.closedBall x (r + 1)) (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
        (ha.const_mul 2).add (hb.const_mul 2)
      have hsplit : ∫ y in Metric.closedBall x (r + 1),
            (2 * ‖G n y - F y‖ ^ 2 + 2 * ‖G m y - F y‖ ^ 2)
          = 2 * (∫ y in Metric.closedBall x (r + 1), ‖G n y - F y‖ ^ 2)
            + 2 * (∫ y in Metric.closedBall x (r + 1), ‖G m y - F y‖ ^ 2) := by
        rw [integral_add (ha.const_mul 2) (hb.const_mul 2), integral_const_mul, integral_const_mul]
      rw [← hsplit]
      refine setIntegral_mono h1 h2 (fun y => ?_)
      have h3 : ‖G n y - G m y‖ ≤ ‖G n y - F y‖ + ‖G m y - F y‖ := by
        calc ‖G n y - G m y‖ = ‖(G n y - F y) - (G m y - F y)‖ := by ring_nf
          _ ≤ ‖G n y - F y‖ + ‖G m y - F y‖ := norm_sub_le _ _
      have h4 : ‖G n y - G m y‖ ^ 2 ≤ (‖G n y - F y‖ + ‖G m y - F y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h3 2
      nlinarith [h4, sq_nonneg (‖G n y - F y‖ - ‖G m y - F y‖)]
    set η : ℝ := ε ^ 2 * Real.pi ^ d with hηdef
    have hηpos : 0 < η := by rw [hηdef]; positivity
    obtain ⟨pa, hpa, pb, hpb, hmain⟩ := Filter.eventually_prod_iff.mp (hprod.eventually (gt_mem_nhds hηpos))
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hpa
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hpb
    refine ⟨max N₁ N₂, fun n hn m hm y hy => ?_⟩
    have hdiff : Differentiable ℂ (fun w => G n w - G m w) := (hGdiff n).sub (hGdiff m)
    have h1 : ‖G n y - G m y‖ ^ 2 ≤ (Real.pi ^ d)⁻¹ *
        ∫ w in Metric.closedBall x (r + 1), ‖G n w - G m w‖ ^ 2 := hMV hdiff x y r hy
    have h2 : ∫ w in Metric.closedBall x (r + 1), ‖G n w - G m w‖ ^ 2 < η :=
      hmain (hN₁ n (le_trans (le_max_left _ _) hn)) (hN₂ m (le_trans (le_max_right _ _) hm))
    have h3 : ‖G n y - G m y‖ ^ 2 ≤ ε ^ 2 := by
      refine h1.trans ?_
      rw [hηdef] at h2
      calc (Real.pi ^ d)⁻¹ * ∫ w in Metric.closedBall x (r + 1), ‖G n w - G m w‖ ^ 2
          ≤ (Real.pi ^ d)⁻¹ * (ε ^ 2 * Real.pi ^ d) :=
            mul_le_mul_of_nonneg_left h2.le (by positivity)
        _ = ε ^ 2 := by
            rw [mul_comm (ε ^ 2) (Real.pi ^ d), ← mul_assoc,
              inv_mul_cancel₀ (by positivity : (Real.pi ^ d) ≠ 0), one_mul]
    exact le_of_sq_le_sq hε h3
  -- the pointwise limit of the mollifications
  have hH_ex : ∀ x : Fin d → ℂ, ∃ a : ℂ, Tendsto (fun n => G n x) atTop (𝓝 a) := by
    intro x
    refine cauchySeq_tendsto_of_complete ?_
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy x 0 (ε / 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn x (by simp)
    rw [dist_eq_norm]
    linarith
  let H : (Fin d → ℂ) → ℂ := fun x => Classical.choose (hH_ex x)
  have hH_tend : ∀ x : Fin d → ℂ, Tendsto (fun n => G n x) atTop (𝓝 (H x)) := fun x =>
    Classical.choose_spec (hH_ex x)
  -- locally uniform convergence
  have hUnif : ∀ (x : Fin d → ℂ) (r : ℝ),
      TendstoUniformlyOn (fun n => G n) H atTop (Metric.closedBall x r) := by
    intro x r
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy x r (ε / 2) (by positivity)
    refine eventually_atTop.mpr ⟨N, fun n hn y hy => ?_⟩
    have hlim : Tendsto (fun m => ‖G n y - G m y‖) atTop (𝓝 ‖G n y - H y‖) :=
      (tendsto_const_nhds.sub (hH_tend y)).norm
    have hle : ‖G n y - H y‖ ≤ ε / 2 :=
      le_of_tendsto hlim (eventually_atTop.mpr ⟨N, fun m hm => hN n hn m hm y hy⟩)
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  -- the uniform derivative estimate
  obtain ⟨Cf, hCfpos, hCf⟩ :=
    Commons.Analysis.Complex.fderiv_bound_uniform_of_differentiable_complex (d := d) (R := 1) one_pos
  have hderiv_bound : ∀ (n m : ℕ) (x : Fin d → ℂ) (r : ℝ) (y : Fin d → ℂ),
      y ∈ Metric.closedBall x r →
      ‖fderiv ℂ (fun w => G n w - G m w) y‖ ^ 2 ≤
        Cf * ∫ w in Metric.closedBall x (r + 1), ‖G n w - G m w‖ ^ 2 := by
    intro n m x r y hy
    have hdiff : Differentiable ℂ (fun w => G n w - G m w) := (hGdiff n).sub (hGdiff m)
    have h1 := hCf (fun w => G n w - G m w) hdiff y
    have hint : IntegrableOn (fun w => ‖G n w - G m w‖ ^ 2) (Metric.closedBall x (r + 1))
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
      integrableOn_sq_sub_of_continuous_of_locallyIntegrable (u := G n) (v := G m)
        ((hGdiff n).continuous)
        (((hGdiff m).continuous).locallyIntegrable)
        ((((hGdiff m).continuous).norm.pow 2).locallyIntegrable) (isCompact_closedBall _ _)
    have hsub : Metric.closedBall y 1 ⊆ Metric.closedBall x (r + 1) := by
      intro w hw
      rw [mem_closedBall] at hw hy ⊢
      calc dist w x ≤ dist w y + dist y x := dist_triangle w y x
        _ ≤ 1 + r := add_le_add hw hy
        _ = r + 1 := by ring
    have hmono : ∫ w in Metric.closedBall y 1, ‖G n w - G m w‖ ^ 2
        ≤ ∫ w in Metric.closedBall x (r + 1), ‖G n w - G m w‖ ^ 2 :=
      setIntegral_mono_set hint (Eventually.of_forall (fun w => by positivity))
        (Eventually.of_forall (fun w hw => hsub hw))
    exact h1.trans (mul_le_mul_of_nonneg_left hmono hCfpos.le)
  -- uniform Cauchy property of the derivatives on balls
  have hcauchy' : ∀ (x : Fin d → ℂ) (r ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      ∀ y ∈ Metric.closedBall x r, ‖fderiv ℝ (G n) y - fderiv ℝ (G m) y‖ ≤ ε := by
    intro x r ε hε
    have hprod : Tendsto (fun p : ℕ × ℕ =>
        ∫ y in Metric.closedBall x (r + 1), ‖G p.1 y - G p.2 y‖ ^ 2) (atTop ×ˢ atTop) (𝓝 0) := by
      have hA : Tendsto (fun p : ℕ × ℕ =>
          ∫ y in Metric.closedBall x (r + 1), ‖G p.1 y - F y‖ ^ 2)
          (atTop ×ˢ atTop) (𝓝 0) := (hconv x (r + 1)).comp tendsto_fst
      have hB : Tendsto (fun p : ℕ × ℕ =>
          ∫ y in Metric.closedBall x (r + 1), ‖G p.2 y - F y‖ ^ 2)
          (atTop ×ˢ atTop) (𝓝 0) := (hconv x (r + 1)).comp tendsto_snd
      have hg : Tendsto (fun p : ℕ × ℕ =>
          2 * (∫ y in Metric.closedBall x (r + 1), ‖G p.1 y - F y‖ ^ 2)
            + 2 * (∫ y in Metric.closedBall x (r + 1), ‖G p.2 y - F y‖ ^ 2))
          (atTop ×ˢ atTop) (𝓝 0) := by
        have h := (hA.const_mul 2).add (hB.const_mul 2)
        simpa using h
      refine squeeze_zero (fun p => by positivity) (fun p => ?_) hg
      obtain ⟨n, m⟩ := p
      have h1 : IntegrableOn (fun y => ‖G n y - G m y‖ ^ 2) (Metric.closedBall x (r + 1))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
        integrableOn_sq_sub_of_continuous_of_locallyIntegrable (u := G n) (v := G m)
          ((hGdiff n).continuous)
          (((hGdiff m).continuous).locallyIntegrable)
          ((((hGdiff m).continuous).norm.pow 2).locallyIntegrable) (isCompact_closedBall _ _)
      have ha : IntegrableOn (fun y => ‖G n y - F y‖ ^ 2) (Metric.closedBall x (r + 1))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
        integrableOn_sq_sub_of_continuous_of_locallyIntegrable (u := G n) (v := F)
          ((hGdiff n).continuous) hF1 hF2 (isCompact_closedBall _ _)
      have hb : IntegrableOn (fun y => ‖G m y - F y‖ ^ 2) (Metric.closedBall x (r + 1))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
        integrableOn_sq_sub_of_continuous_of_locallyIntegrable (u := G m) (v := F)
          ((hGdiff m).continuous) hF1 hF2 (isCompact_closedBall _ _)
      have h2 : IntegrableOn (fun y => 2 * ‖G n y - F y‖ ^ 2 + 2 * ‖G m y - F y‖ ^ 2)
          (Metric.closedBall x (r + 1)) (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
        (ha.const_mul 2).add (hb.const_mul 2)
      have hsplit : ∫ y in Metric.closedBall x (r + 1),
            (2 * ‖G n y - F y‖ ^ 2 + 2 * ‖G m y - F y‖ ^ 2)
          = 2 * (∫ y in Metric.closedBall x (r + 1), ‖G n y - F y‖ ^ 2)
            + 2 * (∫ y in Metric.closedBall x (r + 1), ‖G m y - F y‖ ^ 2) := by
        rw [integral_add (ha.const_mul 2) (hb.const_mul 2), integral_const_mul, integral_const_mul]
      rw [← hsplit]
      refine setIntegral_mono h1 h2 (fun y => ?_)
      have h3 : ‖G n y - G m y‖ ≤ ‖G n y - F y‖ + ‖G m y - F y‖ := by
        calc ‖G n y - G m y‖ = ‖(G n y - F y) - (G m y - F y)‖ := by ring_nf
          _ ≤ ‖G n y - F y‖ + ‖G m y - F y‖ := norm_sub_le _ _
      have h4 : ‖G n y - G m y‖ ^ 2 ≤ (‖G n y - F y‖ + ‖G m y - F y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h3 2
      nlinarith [h4, sq_nonneg (‖G n y - F y‖ - ‖G m y - F y‖)]
    set η : ℝ := ε ^ 2 / Cf with hηdef
    have hηpos : 0 < η := by rw [hηdef]; positivity
    obtain ⟨pa, hpa, pb, hpb, hmain⟩ := Filter.eventually_prod_iff.mp (hprod.eventually (gt_mem_nhds hηpos))
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hpa
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hpb
    refine ⟨max N₁ N₂, fun n hn m hm y hy => ?_⟩
    have hnorm : ‖fderiv ℝ (G n) y - fderiv ℝ (G m) y‖
        = ‖fderiv ℂ (fun w => G n w - G m w) y‖ := by
      have hAB : fderiv ℝ (G n) y - fderiv ℝ (G m) y
          = (fderiv ℂ (fun w => G n w - G m w) y).restrictScalars ℝ := by
        rw [DifferentiableAt.fderiv_restrictScalars ℝ (𝕜' := ℂ) ((hGdiff n).differentiableAt),
          DifferentiableAt.fderiv_restrictScalars ℝ (𝕜' := ℂ) ((hGdiff m).differentiableAt)]
        change (fderiv ℂ (G n) y).restrictScalars ℝ - (fderiv ℂ (G m) y).restrictScalars ℝ
          = (fderiv ℂ (G n - G m) y).restrictScalars ℝ
        rw [fderiv_sub ((hGdiff n).differentiableAt) ((hGdiff m).differentiableAt)]
        ext v
        rfl
      rw [hAB, ContinuousLinearMap.norm_restrictScalars]
    rw [hnorm]
    have h1 := hderiv_bound n m x r y hy
    have h2 : ∫ w in Metric.closedBall x (r + 1), ‖G n w - G m w‖ ^ 2 < η :=
      hmain (hN₁ n (le_trans (le_max_left _ _) hn)) (hN₂ m (le_trans (le_max_right _ _) hm))
    have h3 : ‖fderiv ℂ (fun w => G n w - G m w) y‖ ^ 2 ≤ ε ^ 2 := by
      refine h1.trans ?_
      rw [hηdef] at h2
      calc Cf * ∫ w in Metric.closedBall x (r + 1), ‖G n w - G m w‖ ^ 2
          ≤ Cf * (ε ^ 2 / Cf) := mul_le_mul_of_nonneg_left h2.le hCfpos.le
        _ = ε ^ 2 := by rw [mul_div_cancel₀ _ hCfpos.ne']
    exact le_of_sq_le_sq hε h3
  -- the pointwise limit of the derivatives
  have hL_ex : ∀ x : Fin d → ℂ, ∃ a : (Fin d → ℂ) →L[ℝ] ℂ,
      Tendsto (fun n => fderiv ℝ (G n) x) atTop (𝓝 a) := by
    intro x
    refine cauchySeq_tendsto_of_complete ?_
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy' x 0 (ε / 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn x (by simp)
    rw [dist_eq_norm]
    linarith
  let L : (Fin d → ℂ) → (Fin d → ℂ) →L[ℝ] ℂ := fun x => Classical.choose (hL_ex x)
  have hL_tend : ∀ x : Fin d → ℂ, Tendsto (fun n => fderiv ℝ (G n) x) atTop (𝓝 (L x)) := fun x =>
    Classical.choose_spec (hL_ex x)
  have hUnif' : ∀ (x : Fin d → ℂ) (r : ℝ),
      TendstoUniformlyOn (fun n => fderiv ℝ (G n)) L atTop (Metric.closedBall x r) := by
    intro x r
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy' x r (ε / 2) (by positivity)
    refine eventually_atTop.mpr ⟨N, fun n hn y hy => ?_⟩
    have hlim : Tendsto (fun m => ‖fderiv ℝ (G n) y - fderiv ℝ (G m) y‖) atTop
        (𝓝 ‖fderiv ℝ (G n) y - L y‖) :=
      (tendsto_const_nhds.sub (hL_tend y)).norm
    have hle : ‖fderiv ℝ (G n) y - L y‖ ≤ ε / 2 :=
      le_of_tendsto hlim (eventually_atTop.mpr ⟨N, fun m hm => hN n hn m hm y hy⟩)
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  -- `H` is real differentiable with derivative `L`
  have hHdiff : ∀ x : Fin d → ℂ, HasFDerivAt H (L x) x := by
    intro x
    refine hasFDerivAt_of_tendstoUniformlyOnFilter (ι := ℕ) (l := Filter.atTop) (x := x)
      (f := fun n => G n) (f' := fun n => fderiv ℝ (G n)) ?_ ?_ ?_
    · rw [Metric.tendstoUniformlyOnFilter_iff]
      intro ε hε
      have hunif := hUnif' x 1
      rw [Metric.tendstoUniformlyOn_iff] at hunif
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif ε hε)
      refine eventually_prod_iff.mpr ⟨fun n => N ≤ n, eventually_atTop.mpr ⟨N, fun n hn => hn⟩,
        fun y => y ∈ Metric.closedBall x 1, ?_, ?_⟩
      · exact Metric.closedBall_mem_nhds x zero_lt_one
      · intro n hn y hy
        exact hN n hn y hy
    · filter_upwards with q
      exact (((hGdiff q.1).restrictScalars ℝ).differentiableAt).hasFDerivAt
    · filter_upwards with y
      exact hH_tend y
  have hHcont : Continuous H := continuous_iff_continuousAt.mpr fun x => (hHdiff x).continuousAt
  -- `H` satisfies the Wirtinger equations
  have hCR : ∀ (j : Fin d) (z : Fin d → ℂ),
      (L z) (Pi.single j (1 : ℂ)) + Complex.I * (L z) (Pi.single j Complex.I) = 0 := by
    intro j z
    have hc1 : Continuous (fun (T : (Fin d → ℂ) →L[ℝ] ℂ) => T (Pi.single j (1 : ℂ))) :=
      (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1 : ℂ) : Fin d → ℂ)).continuous
    have hc2 : Continuous (fun (T : (Fin d → ℂ) →L[ℝ] ℂ) => T (Pi.single j Complex.I)) :=
      (ContinuousLinearMap.apply ℝ ℂ (Pi.single j Complex.I : Fin d → ℂ)).continuous
    have hval1 : Tendsto (fun n => (fderiv ℝ (G n) z) (Pi.single j (1 : ℂ))) atTop
        (𝓝 ((L z) (Pi.single j (1 : ℂ)))) :=
      (hc1.tendsto (L z)).comp (hL_tend z)
    have hval2 : Tendsto (fun n => (fderiv ℝ (G n) z) (Pi.single j Complex.I)) atTop
        (𝓝 ((L z) (Pi.single j Complex.I))) :=
      (hc2.tendsto (L z)).comp (hL_tend z)
    have hsum := hval1.add (hval2.const_mul Complex.I)
    have hzero : (fun n => (fderiv ℝ (G n) z) (Pi.single j (1 : ℂ))
        + Complex.I * (fderiv ℝ (G n) z) (Pi.single j Complex.I)) = fun _ => 0 := by
      funext n
      exact dbar_moll hF1 hweak (hρC n) (hρs n) j z
    rw [hzero] at hsum
    exact tendsto_nhds_unique hsum tendsto_const_nhds
  -- conclusion
  have hHcdiff : Differentiable ℂ H := by
    refine differentiable_complex_of_dbar_eq_zero (fun x => (hHdiff x).differentiableAt) ?_
    intro j z
    rw [(hHdiff z).fderiv]
    exact hCR j z
  refine ⟨H, hHcdiff, ?_⟩
  -- `F = H` almost everywhere
  have hball : ∀ n : ℕ, H =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict
      (Metric.closedBall (0 : Fin d → ℂ) (n : ℝ))] F := by
    intro n
    set B : Set (Fin d → ℂ) := Metric.closedBall (0 : Fin d → ℂ) (n : ℝ) with hB
    have hBmeas : MeasurableSet B := hB ▸ measurableSet_closedBall
    have hBcomp : IsCompact B := hB ▸ isCompact_closedBall _ _
    have hBfin : (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) B ≠ ⊤ :=
      hBcomp.measure_lt_top.ne
    have h₁ : Tendsto (fun k => ∫ y in B, ‖H y - G k y‖ ^ 2) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro δ hδ
      set V : ℝ := (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).real B with hV
      have hVnn : 0 ≤ V := by rw [hV]; positivity
      set ε : ℝ := min 1 (δ / (V + 1)) with hεdef
      have hεpos : 0 < ε := lt_min one_pos (div_pos hδ (by linarith))
      have hεle : ε ≤ 1 := min_le_left _ _
      have hεδ : V * ε ^ 2 < δ := by
        have h1 : ε ^ 2 ≤ ε := by nlinarith [hεpos.le, hεle]
        have h2 : ε ≤ δ / (V + 1) := min_le_right _ _
        calc V * ε ^ 2 ≤ V * ε := mul_le_mul_of_nonneg_left h1 hVnn
          _ ≤ V * (δ / (V + 1)) := mul_le_mul_of_nonneg_left h2 hVnn
          _ = δ * (V / (V + 1)) := by ring
          _ < δ * 1 := by
              refine mul_lt_mul_of_pos_left ?_ hδ
              rw [div_lt_one (by linarith)]; linarith
          _ = δ := mul_one δ
      have hunif := hUnif 0 (n : ℝ)
      rw [Metric.tendstoUniformlyOn_iff] at hunif
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif ε hεpos)
      refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
      have hbdd : ∀ y ∈ B, ‖H y - G k y‖ ^ 2 ≤ ε ^ 2 := by
        intro y hy
        have hlt := hN k hk y (hB ▸ hy)
        rw [dist_eq_norm] at hlt
        exact pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
      have hcomp : ∫ y in B, ‖H y - G k y‖ ^ 2 ≤ V * ε ^ 2 := by
        have hconst : ∫ y in B, (ε ^ 2 : ℝ) = V * ε ^ 2 := by
          rw [setIntegral_const, smul_eq_mul, ← hV, mul_comm]
        rw [← hconst]
        refine integral_mono_ae ?_ ?_ ?_
        · exact integrableOn_sq_sub_of_continuous_of_locallyIntegrable (u := H) (v := G k) hHcont
            (((hGdiff k).continuous).locallyIntegrable)
            ((((hGdiff k).continuous).norm.pow 2).locallyIntegrable) hBcomp
        · exact integrableOn_const hBfin (by simp)
        · filter_upwards [MeasureTheory.ae_restrict_mem hBmeas] with y hy
          exact hbdd y hy
      have hnn : 0 ≤ ∫ y in B, ‖H y - G k y‖ ^ 2 := by positivity
      rw [dist_zero_right, Real.norm_of_nonneg hnn]
      linarith [hcomp, hεδ]
    have h₂ : Tendsto (fun k => ∫ y in B, ‖G k y - F y‖ ^ 2) atTop (𝓝 0) := by
      rw [hB]
      exact hconv 0 (n : ℝ)
    have h₃ : Tendsto (fun k => 2 * (∫ y in B, ‖H y - G k y‖ ^ 2)
        + 2 * (∫ y in B, ‖G k y - F y‖ ^ 2)) atTop (𝓝 0) := by
      have h := (h₁.const_mul 2).add (h₂.const_mul 2)
      simpa using h
    have hInt : Integrable (fun y => ‖H y - F y‖ ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict B) :=
      integrableOn_sq_sub_of_continuous_of_locallyIntegrable (u := H) (v := F) hHcont hF1 hF2 hBcomp
    have hint : ∫ y in B, ‖H y - F y‖ ^ 2 = 0 := by
      refine le_antisymm ?_ (by positivity)
      refine le_of_tendsto_of_tendsto tendsto_const_nhds h₃ ?_
      filter_upwards with k
      have h1 : IntegrableOn (fun y => ‖H y - F y‖ ^ 2) B
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := hInt
      have h2 : IntegrableOn (fun y => 2 * ‖H y - G k y‖ ^ 2 + 2 * ‖G k y - F y‖ ^ 2) B
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
        ((integrableOn_sq_sub_of_continuous_of_locallyIntegrable (u := H) (v := G k) hHcont
            (((hGdiff k).continuous).locallyIntegrable)
            ((((hGdiff k).continuous).norm.pow 2).locallyIntegrable) hBcomp).const_mul 2).add
          ((integrableOn_sq_sub_of_continuous_of_locallyIntegrable (u := G k) (v := F)
            ((hGdiff k).continuous) hF1 hF2 hBcomp).const_mul 2)
      have ha : IntegrableOn (fun y => ‖H y - G k y‖ ^ 2) B
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
        integrableOn_sq_sub_of_continuous_of_locallyIntegrable (u := H) (v := G k) hHcont
          (((hGdiff k).continuous).locallyIntegrable)
          ((((hGdiff k).continuous).norm.pow 2).locallyIntegrable) hBcomp
      have hb : IntegrableOn (fun y => ‖G k y - F y‖ ^ 2) B
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
        integrableOn_sq_sub_of_continuous_of_locallyIntegrable (u := G k) (v := F)
          ((hGdiff k).continuous) hF1 hF2 hBcomp
      have hsplit : ∫ y in B, (2 * ‖H y - G k y‖ ^ 2 + 2 * ‖G k y - F y‖ ^ 2)
          = 2 * (∫ y in B, ‖H y - G k y‖ ^ 2) + 2 * (∫ y in B, ‖G k y - F y‖ ^ 2) := by
        rw [integral_add (ha.const_mul 2) (hb.const_mul 2), integral_const_mul, integral_const_mul]
      rw [← hsplit]
      refine setIntegral_mono h1 h2 (fun y => ?_)
      have h3 : ‖H y - F y‖ ≤ ‖H y - G k y‖ + ‖G k y - F y‖ := by
        calc ‖H y - F y‖ = ‖(H y - G k y) - (F y - G k y)‖ := by ring_nf
          _ ≤ ‖H y - G k y‖ + ‖F y - G k y‖ := norm_sub_le _ _
          _ = ‖H y - G k y‖ + ‖G k y - F y‖ := by rw [norm_sub_rev (F y) (G k y)]
      have h4 : ‖H y - F y‖ ^ 2 ≤ (‖H y - G k y‖ + ‖G k y - F y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h3 2
      nlinarith [h4, sq_nonneg (‖H y - G k y‖ - ‖G k y - F y‖)]
    have hzero : (fun y => ‖H y - F y‖ ^ 2) =ᵐ[
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict B] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (fun y => by positivity)) hInt).mp hint
    filter_upwards [hzero] with y hy
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hy))
  have hae : H =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))] F := by
    have h1 : ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict
        (⋃ n : ℕ, Metric.closedBall (0 : Fin d → ℂ) (n : ℝ))), H x = F x :=
      (MeasureTheory.ae_restrict_iUnion_iff _ _).mpr hball
    rw [Metric.iUnion_closedBall_nat, Measure.restrict_univ] at h1
    exact h1
  exact hae.symm

end Commons.Analysis.Complex
