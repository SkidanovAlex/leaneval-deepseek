import Mathlib
import Submission.Work.KMTPlan.A6.ssuModelGain

/-!
# The convolution theorem for Fourier coefficients in the `ℓ¹` regime

If `F` and `G` are integrable on the circle and the Fourier coefficients of `F` and `G` are
(unconditionally, hence absolutely) summable, then the Fourier coefficients of the pointwise
product are the convolution of the coefficient sequences:

`fourierCoeff (F · G) m = ∑'_j fourierCoeff F j · fourierCoeff G (m - j)`.

The proof models `F` and `G` by their (absolutely convergent, hence continuous) Fourier series
`Fc`, `Gc`; the two agree with `F`, `G` almost everywhere by the Lebesgue uniqueness theorem for
Fourier coefficients (`fourierCoeff_eq_zero_ae` below), and for the continuous models the identity
is the `L²`-product theorem `Work.KMTAreas.A5.fourierCoeff_mul_eq_tsum_conv`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7Hi

open MeasureTheory Finset Filter
open scoped BigOperators NNReal ENNReal Topology
open Work.Analysis.IonescuWainger

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-- For `T = 1` the normalised Haar measure `circleMeasure` is `volume`. -/
private theorem circleMeasure_eq_volume :
    (Work.Analysis.IonescuWainger.circleMeasure : Measure Circ) = volume := by
  rw [Work.Analysis.IonescuWainger.circleMeasure, AddCircle.volume_eq_smul_haarAddCircle]
  simp

/-- **Uniqueness of the Fourier coefficients on `L¹(ℝ/ℤ)`.**  An integrable function all of whose
Fourier coefficients vanish is zero almost everywhere. -/
private theorem fourierCoeff_eq_zero_ae {u : Circ → ℂ}
    (hu : MeasureTheory.Integrable u circleMeasure)
    (h : ∀ n : ℤ, fourierCoeff u n = 0) : u =ᵐ[circleMeasure] 0 := by
  -- (1) the characters
  have hgen : ∀ n : ℤ, ∫ t : Circ, fourier (T := 1) n t • u t ∂circleMeasure = 0 := by
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
  -- (3) continuous test functions
  have hcont : ∀ ψ : C(Circ, ℂ), ∫ t : Circ, ψ t * u t ∂circleMeasure = 0 := by
    intro ψ
    have hdense : ψ ∈ closure ((Submodule.span ℂ
        (Set.range (fourier (T := 1) : ℤ → C(Circ, ℂ)))) : Set C(Circ, ℂ)) := by
      rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
      exact Submodule.mem_top
    have hK : (0 : ℝ) ≤ ∫ t : Circ, ‖u t‖ ∂circleMeasure := integral_nonneg (fun t => norm_nonneg _)
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
  -- (4) closed sets, via the `HasOuterApproxClosed` approximation
  have hclosed : ∀ F : Set Circ, IsClosed F → ∫ t in F, u t ∂circleMeasure = 0 := by
    intro F hF
    obtain ⟨fs, hfs1, hfsF, hfstend⟩ := HasOuterApproxClosed.exAppr F hF
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
  -- (5) almost everywhere, by Lebesgue differentiation
  haveI :=
    show IsUnifLocDoublingMeasure (Work.Analysis.IonescuWainger.circleMeasure) from by
    rw [circleMeasure_eq_volume]
    infer_instance
  have hloc : LocallyIntegrable u circleMeasure := hu.locallyIntegrable
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average (μ := circleMeasure) hloc 1
  filter_upwards [hdiff] with x hx
  have hx' := hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id
    (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
      have h1 : (0 : ℝ) ≤ 1 * r := by rw [one_mul]; exact hr0
      simpa using Metric.mem_closedBall_self (x := x) (ε := 1 * r) h1)
  have hzero : Tendsto (fun r : ℝ => ⨍ y in Metric.closedBall x r, u y ∂circleMeasure)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with r
    rw [setAverage_eq, hclosed _ Metric.isClosed_closedBall, smul_zero]
  exact tendsto_nhds_unique hx' hzero

/-- `fourierCoeff` is additive over differences of integrable functions (pointwise form). -/
private theorem fourierCoeff_sub_apply {f g : Circ → ℂ} (hf : MeasureTheory.Integrable f circleMeasure)
    (hg : MeasureTheory.Integrable g circleMeasure) (j : ℤ) :
    fourierCoeff (f - g) j = fourierCoeff f j - fourierCoeff g j := by
  have h1 : fourierCoeff (f + -g) j = fourierCoeff f j + fourierCoeff (-g) j :=
    congrFun (fourierCoeff.add hf hg.neg) j
  have h2 : fourierCoeff (-g) j = - fourierCoeff g j := by
    have h3 := fourierCoeff.const_smul g (-1 : ℂ) j
    rw [show ((-1 : ℂ) • g) = -g from by funext ξ; simp, smul_eq_mul] at h3
    simpa using h3
  rw [show (f - g) = f + -g from sub_eq_add_neg f g, h1, h2]
  ring

/-- **The product theorem for Fourier coefficients.**  If `F` and `G` are integrable with
absolutely summable Fourier coefficients, then the Fourier coefficients of the pointwise product
are the convolution of the coefficient sequences. -/
theorem fourierCoeff_mul_l1 {F G : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hF : MeasureTheory.Integrable F Work.Analysis.IonescuWainger.circleMeasure)
    (hG : MeasureTheory.Integrable G Work.Analysis.IonescuWainger.circleMeasure)
    (hFG : MeasureTheory.Integrable (fun ξ => F ξ * G ξ)
      Work.Analysis.IonescuWainger.circleMeasure)
    (hFs : Summable (fun j : ℤ => fourierCoeff F j))
    (hGs : Summable (fun j : ℤ => fourierCoeff G j)) (m : ℤ) :
    fourierCoeff (fun ξ => F ξ * G ξ) m
      = ∑' j : ℤ, fourierCoeff F j * fourierCoeff G (m - j) := by
  have hFnorm : Summable (fun j : ℤ => ‖fourierCoeff F j‖) := hFs.norm
  have hGnorm : Summable (fun j : ℤ => ‖fourierCoeff G j‖) := hGs.norm
  -- the continuous model of `F`
  obtain ⟨Fc, hFc⟩ : ∃ Fc : C(Circ, ℂ),
      ∀ ξ, HasSum (fun j => fourierCoeff F j * fourier (T := 1) j ξ) (Fc ξ) := by
    have hsummC : Summable
        (fun j : ℤ => fourierCoeff F j • (fourier (T := 1) j : C(Circ, ℂ))) := by
      refine Summable.of_norm_bounded hFnorm (fun j => ?_)
      rw [norm_smul, fourier_norm, mul_one]
    refine ⟨∑' j, fourierCoeff F j • (fourier (T := 1) j : C(Circ, ℂ)), fun ξ => ?_⟩
    simpa using (ContinuousMap.evalCLM ℂ ξ).hasSum hsummC.hasSum
  have hFc_coeff : fourierCoeff (⇑Fc) = fun j => fourierCoeff F j :=
    Work.Analysis.Fourier.fourierCoeff_summable_series hFnorm hFc
  have hFc_int : MeasureTheory.Integrable (⇑Fc) circleMeasure :=
    (MeasureTheory.MemLp.of_bound Fc.continuous.aestronglyMeasurable ‖Fc‖
      (ae_of_all _ fun ξ => ContinuousMap.norm_coe_le_norm Fc ξ)).integrable le_rfl
  have hFeq : F =ᵐ[circleMeasure] ⇑Fc := by
    have hz : (F - ⇑Fc) =ᵐ[circleMeasure] 0 :=
      fourierCoeff_eq_zero_ae (hF.sub hFc_int) (fun j => by
        rw [fourierCoeff_sub_apply hF hFc_int j, congrFun hFc_coeff j, sub_self])
    filter_upwards [hz] with ξ hξ
    simpa using sub_eq_zero.mp hξ
  -- the continuous model of `G`
  obtain ⟨Gc, hGc⟩ : ∃ Gc : C(Circ, ℂ),
      ∀ ξ, HasSum (fun j => fourierCoeff G j * fourier (T := 1) j ξ) (Gc ξ) := by
    have hsummC : Summable
        (fun j : ℤ => fourierCoeff G j • (fourier (T := 1) j : C(Circ, ℂ))) := by
      refine Summable.of_norm_bounded hGnorm (fun j => ?_)
      rw [norm_smul, fourier_norm, mul_one]
    refine ⟨∑' j, fourierCoeff G j • (fourier (T := 1) j : C(Circ, ℂ)), fun ξ => ?_⟩
    simpa using (ContinuousMap.evalCLM ℂ ξ).hasSum hsummC.hasSum
  have hGc_coeff : fourierCoeff (⇑Gc) = fun j => fourierCoeff G j :=
    Work.Analysis.Fourier.fourierCoeff_summable_series hGnorm hGc
  have hGc_int : MeasureTheory.Integrable (⇑Gc) circleMeasure :=
    (MeasureTheory.MemLp.of_bound Gc.continuous.aestronglyMeasurable ‖Gc‖
      (ae_of_all _ fun ξ => ContinuousMap.norm_coe_le_norm Gc ξ)).integrable le_rfl
  have hGeq : G =ᵐ[circleMeasure] ⇑Gc := by
    have hz : (G - ⇑Gc) =ᵐ[circleMeasure] 0 :=
      fourierCoeff_eq_zero_ae (hG.sub hGc_int) (fun j => by
        rw [fourierCoeff_sub_apply hG hGc_int j, congrFun hGc_coeff j, sub_self])
    filter_upwards [hz] with ξ hξ
    simpa using sub_eq_zero.mp hξ
  -- the coefficients of the products agree almost everywhere
  have hprod := Work.KMTAreas.A5.fourierCoeff_mul_eq_tsum_conv
    (F := ⇑Fc) (G := ⇑Gc)
    (MeasureTheory.MemLp.of_bound Fc.continuous.aestronglyMeasurable ‖Fc‖
      (ae_of_all _ fun ξ => ContinuousMap.norm_coe_le_norm Fc ξ))
    (MeasureTheory.MemLp.of_bound Gc.continuous.aestronglyMeasurable ‖Gc‖
      (ae_of_all _ fun ξ => ContinuousMap.norm_coe_le_norm Gc ξ))
    (by simpa [hFc_coeff] using hFnorm) m
  have hcongr : fourierCoeff (fun ξ => F ξ * G ξ)
      = fourierCoeff (fun ξ => (⇑Fc) ξ * (⇑Gc) ξ) :=
    fourierCoeff_congr_ae (hFeq.mul hGeq)
  rw [congrFun hcongr m, hprod]
  exact tsum_congr (fun j => by rw [congrFun hFc_coeff j, congrFun hGc_coeff (m - j)])

end

end Work.KMTAreas.A7Hi
