import Mathlib
import Submission.Work.Analysis.IonescuWainger.EtaCut
import Submission.Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing
import Submission.Work.Analysis.IonescuWainger.iwQl_le
import Submission.Work.Analysis.IonescuWainger.iw_height_card_le
import Submission.Work.Analysis.IonescuWainger.memLp_periodize
import Submission.Work.Analysis.IonescuWainger.multiplier_add
import Submission.Work.Analysis.IonescuWainger.multiplier_comp
import Submission.Work.Analysis.IonescuWainger.norm_iwOpSet_le
import Submission.Work.Analysis.IonescuWainger.one_div_le_norm_of_ne
import Submission.Work.Analysis.IonescuWainger.supportedInArc_periodize

/-!
# Uniqueness of Fourier coefficients for integrable functions on the circle

An integrable function on the frequency circle `ℝ/ℤ` all of whose Fourier coefficients vanish is
zero almost everywhere.

The argument is the classical one, in four steps.

1. Writing the hypothesis out, each character `χ_n = fourier n` pairs to zero with `u`:
   `∫ χ_n · u = 0` (the `fourierCoeff` definition integrates `fourier (-n) · u`, so this is just a
   change of sign in the index).
2. By linearity of the Bochner integral every trigonometric polynomial `Q` in
   `Submodule.span ℂ (Set.range fourier)` therefore satisfies `∫ Q · u = 0`.
3. The trigonometric polynomials are dense in `C(ℝ/ℤ, ℂ)` (`span_fourier_closure_eq_top`,
   Stone–Weierstrass) and, since `u ∈ L¹`, the pairing `ψ ↦ ∫ ψ · u` is continuous for the uniform
   norm: `‖∫ ψ · u‖ ≤ ‖ψ‖ · ∫ ‖u‖`.  Hence `∫ ψ · u = 0` for every continuous `ψ`.
4. Indicators of closed sets are dominated limits of bounded continuous functions
   (`HasOuterApproxClosed.exAppr`), so dominated convergence gives `∫_F u = 0` for every closed
   `F`, and Mathlib's `ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero` concludes.

Everything is proved for the concrete measure `circleMeasure = AddCircle.haarAddCircle`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7Hi

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
open Work.Analysis.IonescuWainger

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-- **Uniqueness of the Fourier coefficients on `L¹(ℝ/ℤ)`.**  An integrable function on the
frequency circle all of whose Fourier coefficients vanish is zero almost everywhere. -/
theorem fourierCoeff_eq_zero_ae {u : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hu : MeasureTheory.Integrable u Work.Analysis.IonescuWainger.circleMeasure)
    (h : ∀ n : ℤ, fourierCoeff u n = 0) :
    u =ᵐ[Work.Analysis.IonescuWainger.circleMeasure] 0 := by
  -- (1) the characters pair to zero with `u`
  have hgen : ∀ n : ℤ,
      ∫ t : Circ, fourier (T := 1) n t • u t ∂circleMeasure = 0 := by
    intro n
    have hh := h (-n)
    rw [fourierCoeff] at hh
    simpa using hh
  -- (2) finite linear combinations of characters
  have hspan : ∀ Q ∈ Submodule.span ℂ (Set.range (fourier (T := 1) : ℤ → C(Circ, ℂ))),
      ∫ t : Circ, (Q : Circ → ℂ) t * u t ∂circleMeasure = 0 := by
    intro Q hQ
    refine Submodule.span_induction
      (p := fun Q _ => ∫ t : Circ, Q t * u t ∂circleMeasure = 0) ?_ ?_ ?_ ?_ hQ
    · rintro _ ⟨n, rfl⟩
      simpa [smul_eq_mul] using hgen n
    · simp
    · intro x y hx hy hpx hpy
      have hxint : Integrable (fun t : Circ => (x : Circ → ℂ) t * u t) circleMeasure :=
        hu.bdd_mul (c := ‖x‖) x.continuous.aestronglyMeasurable
          (ae_of_all _ fun t => ContinuousMap.norm_coe_le_norm x t)
      have hyint : Integrable (fun t : Circ => (y : Circ → ℂ) t * u t) circleMeasure :=
        hu.bdd_mul (c := ‖y‖) y.continuous.aestronglyMeasurable
          (ae_of_all _ fun t => ContinuousMap.norm_coe_le_norm y t)
      have hfun : (fun t : Circ => ((x + y : C(Circ, ℂ)) : Circ → ℂ) t * u t)
          = fun t => (x : Circ → ℂ) t * u t + (y : Circ → ℂ) t * u t := by
        funext t; simp only [ContinuousMap.add_apply]; ring
      rw [hfun, integral_add hxint hyint, hpx, hpy, add_zero]
    · intro c x hx hpx
      have hfun : (fun t : Circ => ((c • x : C(Circ, ℂ)) : Circ → ℂ) t * u t)
          = fun t => c • ((x : Circ → ℂ) t * u t) := by
        funext t; simp only [ContinuousMap.smul_apply]; ring
      rw [hfun, integral_smul, hpx, smul_zero]
  -- (3) continuous test functions, by density of the trigonometric polynomials
  have hcont : ∀ ψ : C(Circ, ℂ), ∫ t : Circ, ψ t * u t ∂circleMeasure = 0 := by
    intro ψ
    have hdense : ψ ∈ closure ((Submodule.span ℂ
        (Set.range (fourier (T := 1) : ℤ → C(Circ, ℂ)))) : Set C(Circ, ℂ)) := by
      rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
      exact Submodule.mem_top
    have hK : (0 : ℝ) ≤ ∫ t : Circ, ‖u t‖ ∂circleMeasure :=
      integral_nonneg (fun t => norm_nonneg _)
    have hψint : Integrable (fun t : Circ => ψ t * u t) circleMeasure :=
      hu.bdd_mul (c := ‖ψ‖) ψ.continuous.aestronglyMeasurable
        (ae_of_all _ fun t => ContinuousMap.norm_coe_le_norm ψ t)
    have hbound : ∀ ε > 0,
        ‖∫ t : Circ, ψ t * u t ∂circleMeasure‖ ≤ ε * (∫ t : Circ, ‖u t‖ ∂circleMeasure) := by
      intro ε hε
      obtain ⟨Q, hQ, hdist⟩ := Metric.mem_closure_iff.1 hdense ε hε
      have hQint : Integrable (fun t : Circ => (Q : Circ → ℂ) t * u t) circleMeasure :=
        hu.bdd_mul (c := ‖Q‖) Q.continuous.aestronglyMeasurable
          (ae_of_all _ fun t => ContinuousMap.norm_coe_le_norm Q t)
      have hdiff : (∫ t : Circ, ψ t * u t ∂circleMeasure)
            - (∫ t : Circ, (Q : Circ → ℂ) t * u t ∂circleMeasure)
          = ∫ t : Circ, (ψ t - (Q : Circ → ℂ) t) * u t ∂circleMeasure := by
        rw [← integral_sub hψint hQint]
        exact integral_congr_ae (ae_of_all _ fun t => by ring)
      have hzero : (∫ t : Circ, (Q : Circ → ℂ) t * u t ∂circleMeasure) = 0 := hspan Q hQ
      have hint : Integrable (fun t : Circ => ‖(ψ t - (Q : Circ → ℂ) t) * u t‖) circleMeasure := by
        refine (hψint.sub hQint).norm.congr ?_
        filter_upwards with t
        rw [Pi.sub_apply]
        congr 1
        ring
      have hle : ∫ t : Circ, ‖(ψ t - (Q : Circ → ℂ) t) * u t‖ ∂circleMeasure
          ≤ ε * ∫ t : Circ, ‖u t‖ ∂circleMeasure := by
        have h1 : ∀ t : Circ, ‖(ψ t - (Q : Circ → ℂ) t) * u t‖ ≤ ε * ‖u t‖ := by
          intro t
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          calc ‖ψ t - (Q : Circ → ℂ) t‖ = ‖(ψ - Q : C(Circ, ℂ)) t‖ := by
                rw [ContinuousMap.sub_apply]
            _ ≤ ‖(ψ - Q : C(Circ, ℂ))‖ := ContinuousMap.norm_coe_le_norm _ t
            _ = dist ψ Q := by rw [dist_eq_norm]
            _ ≤ ε := le_of_lt hdist
        calc ∫ t : Circ, ‖(ψ t - (Q : Circ → ℂ) t) * u t‖ ∂circleMeasure
            ≤ ∫ t : Circ, ε * ‖u t‖ ∂circleMeasure :=
              integral_mono hint (hu.norm.const_mul ε) h1
          _ = ε * ∫ t : Circ, ‖u t‖ ∂circleMeasure := integral_const_mul ε _
      calc ‖∫ t : Circ, ψ t * u t ∂circleMeasure‖
          = ‖∫ t : Circ, (ψ t - (Q : Circ → ℂ) t) * u t ∂circleMeasure‖ := by
            rw [← hdiff, hzero, sub_zero]
        _ ≤ ∫ t : Circ, ‖(ψ t - (Q : Circ → ℂ) t) * u t‖ ∂circleMeasure :=
            norm_integral_le_integral_norm _
        _ ≤ ε * ∫ t : Circ, ‖u t‖ ∂circleMeasure := hle
    have hzero : ‖∫ t : Circ, ψ t * u t ∂circleMeasure‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      have h1 := hbound (ε / (∫ t : Circ, ‖u t‖ ∂circleMeasure + 1)) (by positivity)
      have h2 : (ε / (∫ t : Circ, ‖u t‖ ∂circleMeasure + 1))
          * (∫ t : Circ, ‖u t‖ ∂circleMeasure) ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [hK, hε.le]
      linarith [le_trans h1 h2]
    simpa using hzero
  -- (4) closed sets, via bounded continuous approximations to their indicators
  have hclosed : ∀ F : Set Circ, IsClosed F → ∫ t in F, u t ∂circleMeasure = 0 := by
    intro F hF
    obtain ⟨fs, hfs1, _hfsF, hfstend⟩ := HasOuterApproxClosed.exAppr F hF
    have hfs_cont : ∀ n : ℕ, Continuous fun t : Circ => ((fs n t : ℝ≥0) : ℂ) := fun n =>
      Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (fs n).continuous)
    have hfs_int : ∀ n : ℕ, ∫ t : Circ, ((fs n t : ℝ≥0) : ℂ) * u t ∂circleMeasure = 0 := by
      intro n
      have hh := hcont ⟨(fun t : Circ => ((fs n t : ℝ≥0) : ℂ)), hfs_cont n⟩
      simpa using hh
    have hlim : Tendsto (fun n : ℕ => ∫ t : Circ, ((fs n t : ℝ≥0) : ℂ) * u t ∂circleMeasure)
        atTop (𝓝 (∫ t : Circ, (F.indicator (fun _ => (1 : ℂ))) t * u t ∂circleMeasure)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (F := fun n (t : Circ) => ((fs n t : ℝ≥0) : ℂ) * u t)
        (f := fun t : Circ => (F.indicator (fun _ => (1 : ℂ))) t * u t)
        (bound := fun t : Circ => ‖u t‖) ?_ hu.norm ?_ ?_
      · intro n
        exact ((hfs_cont n).aestronglyMeasurable).mul hu.aestronglyMeasurable
      · intro n
        filter_upwards with t
        rw [norm_mul]
        have hb : ‖((fs n t : ℝ≥0) : ℂ)‖ ≤ 1 := by
          have h1 : ‖((((fs n t : ℝ≥0) : ℝ)) : ℂ)‖ = |(((fs n t : ℝ≥0) : ℝ))| := by simp
          rw [h1, abs_of_nonneg (by positivity)]
          exact_mod_cast hfs1 n t
        calc ‖((fs n t : ℝ≥0) : ℂ)‖ * ‖u t‖ ≤ 1 * ‖u t‖ :=
              mul_le_mul_of_nonneg_right hb (norm_nonneg _)
          _ = ‖u t‖ := one_mul _
      · filter_upwards with t
        have hpt : Tendsto (fun n : ℕ => fs n t) atTop
            (𝓝 ((F.indicator (fun _ => (1 : ℝ≥0))) t)) :=
          (tendsto_pi_nhds.mp hfstend) t
        have h2 : Tendsto (fun n : ℕ => ((fs n t : ℝ≥0) : ℂ)) atTop
            (𝓝 ((((F.indicator (fun _ => (1 : ℝ≥0))) t : ℝ≥0) : ℂ))) :=
          ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp hpt
        have h3 := h2.mul_const (u t)
        have hval : ((((F.indicator (fun _ => (1 : ℝ≥0))) t : ℝ≥0) : ℂ))
            = (F.indicator (fun _ => (1 : ℂ))) t := by
          by_cases ht : t ∈ F
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]; simp
          · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]; simp
        rwa [hval] at h3
    have h2 : Tendsto (fun n : ℕ => ∫ t : Circ, ((fs n t : ℝ≥0) : ℂ) * u t ∂circleMeasure)
        atTop (𝓝 0) := by
      rw [show (fun n : ℕ => ∫ t : Circ, ((fs n t : ℝ≥0) : ℂ) * u t ∂circleMeasure)
          = fun _ => 0 from funext hfs_int]
      exact tendsto_const_nhds
    have h3 : (∫ t : Circ, (F.indicator (fun _ => (1 : ℂ))) t * u t ∂circleMeasure) = 0 :=
      tendsto_nhds_unique hlim h2
    have hind : (fun t : Circ => (F.indicator (fun _ => (1 : ℂ))) t * u t) = F.indicator u := by
      funext t
      by_cases ht : t ∈ F
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]; simp
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]; simp
    rw [hind, integral_indicator hF.measurableSet] at h3
    exact h3
  -- (5) conclude almost everywhere
  exact ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hu hclosed

end

end Work.KMTAreas.A7Hi
