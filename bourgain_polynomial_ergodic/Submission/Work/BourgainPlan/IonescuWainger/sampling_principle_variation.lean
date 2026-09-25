import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.msw_of_cutoff_extension
import Submission.Work.BourgainPlan.IonescuWainger.SamplingVariation
import Submission.Work.BourgainPlan.IonescuWainger.varRhoFrom_two_le_liminf
import Submission.Work.BourgainPlan.IonescuWainger.cutoff_extension_lp

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped ENNReal BigOperators FourierTransform Interval

set_option maxHeartbeats 2000000
-- the two hypotheses `hOp` and `ha` of the (fixed) statement occur only as hypotheses
set_option linter.unusedVariables false

noncomputable section

/-- `(liminf u)^p ≤ liminf (u^p)` in `ℝ≥0∞`, for `p > 0`: raising to a positive power preserves
indexed suprema of `ℝ≥0∞`-valued families (`Monotone.map_iSup_of_continuousAt` applied to the
continuous monotone map `x ↦ x^p`), and the `⨅` of a family is carried to a lower bound of the
`⨅` of the powers by monotonicity. -/
theorem liminf_rpow_le_liminf_rpow {p : ℝ} (hp : 0 < p) (u : ℕ → ℝ≥0∞) :
    (Filter.liminf u Filter.atTop) ^ p ≤ Filter.liminf (fun n => (u n) ^ p) Filter.atTop := by
  set c : ℕ → ℝ≥0∞ := fun n => ⨅ i : ℕ, ⨅ (_ : i ≥ n), u i with hc
  have hmap : (⨆ n, c n) ^ p = ⨆ n, (c n) ^ p :=
    Monotone.map_iSup_of_continuousAt ENNReal.continuous_rpow_const.continuousAt
      (fun a b hab => ENNReal.rpow_le_rpow hab hp.le) (ENNReal.zero_rpow_of_pos hp)
  calc (Filter.liminf u Filter.atTop) ^ p
      = (⨆ n, c n) ^ p := by rw [Filter.liminf_eq_iSup_iInf_of_nat, ← hc]
    _ = ⨆ n, (c n) ^ p := hmap
    _ ≤ ⨆ n, ⨅ i : ℕ, ⨅ (_ : i ≥ n), (u i) ^ p := by
        refine iSup_le fun n => ?_
        refine le_trans ?_ (le_iSup (fun m => ⨅ i : ℕ, ⨅ (_ : i ≥ m), (u i) ^ p) n)
        exact le_iInf fun i => le_iInf fun hi =>
          ENNReal.rpow_le_rpow (le_trans (iInf_le _ i) (iInf_le _ hi)) hp.le
    _ = Filter.liminf (fun n => (u n) ^ p) Filter.atTop := by
        rw [Filter.liminf_eq_iSup_iInf_of_nat]

/-- **Fatou bound for a lower-semicontinuous pointwise limit.**  If `g ≤ liminf_j F j` pointwise
and each `∫⁻ (F j)^p` is bounded by `K`, then `∫⁻ g^p ≤ K`. -/
theorem lintegral_le_of_le_liminf {p : ℝ} (hp : 0 < p) {F : ℕ → ℝ → ℝ≥0∞}
    {g : ℝ → ℝ≥0∞} {K : ℝ≥0∞}
    (hFmeas : ∀ j : ℕ, AEMeasurable (F j) MeasureTheory.volume)
    (hlim : ∀ x : ℝ, g x ≤ Filter.liminf (fun j => F j x) Filter.atTop)
    (hK : ∀ j : ℕ, ∫⁻ x : ℝ, (F j x) ^ p ∂MeasureTheory.volume ≤ K) :
    ∫⁻ x : ℝ, (g x) ^ p ∂MeasureTheory.volume ≤ K := by
  have h1 : ∫⁻ x : ℝ, (g x) ^ p ∂MeasureTheory.volume
      ≤ ∫⁻ x : ℝ, Filter.liminf (fun j => (F j x) ^ p) Filter.atTop
          ∂MeasureTheory.volume :=
    lintegral_mono (fun x => le_trans (ENNReal.rpow_le_rpow (hlim x) hp.le)
      (liminf_rpow_le_liminf_rpow hp (fun j => F j x)))
  have h2 : ∫⁻ x : ℝ, Filter.liminf (fun j => (F j x) ^ p) Filter.atTop
        ∂MeasureTheory.volume
      ≤ Filter.liminf (fun j => ∫⁻ x : ℝ, (F j x) ^ p ∂MeasureTheory.volume)
          Filter.atTop :=
    MeasureTheory.lintegral_liminf_le' (u := Filter.atTop)
      (fun j => (hFmeas j).pow_const p)
  have h3 : Filter.liminf (fun j => ∫⁻ x : ℝ, (F j x) ^ p ∂MeasureTheory.volume)
        Filter.atTop ≤ K :=
    Filter.liminf_le_of_frequently_le (Filter.Frequently.of_forall hK)
  exact h1.trans (h2.trans h3)

-- Route (a copy of `IonescuWainger/msw_of_cutoff_extension.lean` with the norm replaced by the
-- `2`-variation; read that file first).  Write `trig ξ = Σ_{j ∈ s} a_j * e^{-2πi j ξ}` (continuous,
-- bounded by `c = Σ_{j ∈ s} ‖a_j‖`).
-- * `Work.BourgainPlan.IonescuWainger.exists_band_decay_kernel` gives an integrable `w` with
--   `‖w z‖ ≤ B/(1+z²)` and `𝓕w ≡ 1` on `[-1/2,1/2]`; then
--   `Work.BourgainPlan.IonescuWainger.exists_lattice_varRhoFrom_fourierInv_le`
--   (`Submission/Work/BourgainPlan/IonescuWainger/SamplingVariation.lean`) applied to
--   `W n = fun ξ => m n ξ * trig ξ` (integrable because `hm n` times a bounded function; its support
--   lies in `[-1/2,1/2]` by `hsupp`, so `𝓕w ≡ 1` there) bounds the lattice variation by the
--   continuous one.
-- * Introduce the smoothed cutoffs `U j n ξ = m n ξ * trig ξ * plateau (1/(j+2)) ξ` and
--   `g j = 𝓕⁻(fun ξ => trig ξ * plateau (1/(j+2)) ξ)`; then `m n * 𝓕(g j) = U j n` and
--   `hOp (g j)` bounds `∫⁻_x (V²_n(𝓕⁻(U j n)(x)))^p` by `ofReal (A^p) * ∫⁻‖g j‖^p`, while
--   `Work.BourgainPlan.IonescuWainger.cutoff_extension_lp` bounds `∫⁻‖g j‖^p` by
--   `ofReal (Cβ^p) * Σ_{j∈s} ofReal ‖a_j‖^p`.
-- * Pass `j → ∞` using `tendsto_fourierInv_plateau` (pointwise convergence at each `x` and each `n`),
--   `Work.BourgainPlan.IonescuWainger.varRhoFrom_two_le_liminf` (the variation is lower
--   semicontinuous along pointwise convergence) and Fatou's lemma `lintegral_liminf_le`.
-- * Conclude by `sum_intervalIntegral_eq_fourierInv`, which identifies
--   `Σ_{j∈s} (∫ ξ in (-1/2)..(1/2), m n ξ * exp (2πi (k-j) ξ)) * a_j` with `𝓕⁻(W n) k`.
theorem sampling_principle_variation {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : ℕ) (m : ℕ → ℝ → ℂ) (hm : ∀ n, MeasureTheory.Integrable (m n))
      (hsupp : ∀ (n : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → m n ξ = 0)
      (A : ℝ) (hA : 0 ≤ A)
      (hOp : ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → FourierTransform.fourier g ξ = 0) →
        ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
            (fun n => FourierTransformInv.fourierInv
              (fun ξ : ℝ => m n ξ * FourierTransform.fourier g ξ) x)) ^ p
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂MeasureTheory.volume)
      (s : Finset ℤ) (a : ℤ → ℂ) (ha : ∀ k, k ∉ s → a k = 0),
      ∫⁻ k : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n =>
          ∑ j ∈ s, (∫ ξ in (-(1/2):ℝ)..(1/2), m n ξ *
            Complex.exp (2 * Real.pi * Complex.I * ((k - j : ℤ) : ℂ) * (ξ : ℂ))) * a j)) ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((C * A) ^ p) * ∑ j ∈ s, ENNReal.ofReal ‖a j‖ ^ p := by
  obtain ⟨Cβ, hCβpos, hCβ⟩ := cutoff_extension_lp p hp
  obtain ⟨w, B, hw_int, hBpos, hw_dec, hw_four⟩ := exists_band_decay_kernel
  obtain ⟨C₁, hC₁pos, hC₁⟩ := exists_lattice_varRhoFrom_fourierInv_le (p := p) hp
  refine ⟨(C₁ * B ^ p) ^ (1 / p) * Cβ, ?_, ?_⟩
  · exact mul_pos (Real.rpow_pos_of_pos (mul_pos hC₁pos (Real.rpow_pos_of_pos hBpos p)) _)
      hCβpos
  intro κ m hm hsupp A hA hOp s a ha
  classical
  set trig : ℝ → ℂ :=
    fun ξ => ∑ k ∈ s, a k * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ)))
    with htrig
  set c : ℝ := ∑ k ∈ s, ‖a k‖ with hc
  set Sp : ℝ≥0∞ := ∑ k ∈ s, ENNReal.ofReal ‖a k‖ ^ p with hSp
  -- basic facts on `trig`
  have htrig_diff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) trig := by
    rw [htrig]
    refine ContDiff.sum (fun k hk => ?_)
    refine contDiff_const.mul ?_
    refine Complex.contDiff_exp.comp ?_
    have hlin : (fun ξ : ℝ => -(2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ)))
        = fun ξ : ℝ => (-(2 * Real.pi * Complex.I * (k : ℂ))) * (ξ : ℂ) := by
      funext ξ; ring
    rw [hlin]
    exact contDiff_const.mul Complex.ofRealCLM.contDiff
  have htrig_cont : Continuous trig := htrig_diff.continuous
  have htrig_meas : AEStronglyMeasurable trig volume := htrig_cont.aestronglyMeasurable
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have htrig_bound : ∀ ξ : ℝ, ‖trig ξ‖ ≤ c := by
    intro ξ
    rw [htrig, hc]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun k hk => ?_))
    have h1 : -(2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ))
        = ((-(2 * Real.pi * ((k : ℝ) * ξ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [norm_mul, h1, Complex.norm_exp_ofReal_mul_I, mul_one]
  -- the amplitude family `W n = m n · trig`
  set W : ℕ → ℝ → ℂ := fun n ξ => m n ξ * trig ξ with hW
  have hW_int : ∀ n : ℕ, Integrable (W n) := by
    intro n
    have hmul : Integrable (fun ξ : ℝ => trig ξ * m n ξ) :=
      (hm n).bdd_mul htrig_meas (Filter.Eventually.of_forall htrig_bound)
    refine hmul.congr (Filter.Eventually.of_forall (fun ξ => ?_))
    show trig ξ * m n ξ = W n ξ
    rw [hW]; ring
  have hW_ne : ∀ (n : ℕ) (β : ℝ), W n β ≠ 0 → FourierTransform.fourier w β = 1 := by
    intro n β hβ
    have h1 : m n β ≠ 0 := by
      intro h0
      exact hβ (by show m n β * trig β = 0; rw [h0, zero_mul])
    exact hw_four β (by by_contra hcon; exact h1 (hsupp n β hcon))
  -- the family of smooth cut-off amplitudes
  set U : ℕ → ℕ → ℝ → ℂ :=
    fun j n ξ => m n ξ * trig ξ * ((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ) with hU
  have hU_int : ∀ (j n : ℕ), Integrable (U j n) := by
    intro j n
    have hbdd : ∀ ξ : ℝ, ‖trig ξ * ((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ)‖ ≤ c := by
      intro ξ
      have hpn : ‖((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ)‖ = plateau (1/((j:ℝ)+2)) ξ := by
        rw [← Complex.ofRealLI_apply (plateau (1/((j:ℝ)+2)) ξ), Complex.ofRealLI.norm_map,
          Real.norm_eq_abs, abs_of_nonneg (plateau_nonneg _ _)]
      rw [norm_mul, hpn]
      calc ‖trig ξ‖ * plateau (1/((j:ℝ)+2)) ξ
          ≤ c * 1 := mul_le_mul (htrig_bound ξ)
              (plateau_le_one _ (by positivity) ξ) (plateau_nonneg _ _) hc0
        _ = c := mul_one c
    have hcont : Continuous (fun ξ : ℝ => trig ξ * ((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ)) :=
      htrig_cont.mul ((Complex.continuous_ofReal.comp (plateau_continuous _)))
    have hmm : Integrable
        (fun ξ : ℝ => trig ξ * ((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ) * m n ξ) :=
      (hm n).bdd_mul hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbdd)
    refine hmm.congr (Filter.Eventually.of_forall (fun ξ => ?_))
    show trig ξ * ((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ) * m n ξ = U j n ξ
    rw [hU]; ring
  -- per-scale bound: the continuous operator bound composed with the smooth extension bound
  have key : ∀ j : ℕ, ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
      (fun n => FourierTransformInv.fourierInv (U j n) x)) ^ p ∂volume
      ≤ ENNReal.ofReal ((A * Cβ) ^ p) * Sp := by
    intro j
    set ε : ℝ := 1/((j:ℝ)+2) with hεdef
    have hεpos' : (0:ℝ) < ε := by rw [hεdef]; positivity
    have hεle' : ε ≤ 1/2 := by
      rw [hεdef, div_le_iff₀ (by positivity)]
      have h : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      linarith
    set amp : ℝ → ℂ := fun ξ => trig ξ * ((plateau ε ξ : ℝ) : ℂ) with hamp
    have hpl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : ℝ => ((plateau ε ξ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (plateau_contDiff ε)
    have hamp_diff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) amp := by
      rw [hamp]
      exact htrig_diff.mul hpl
    have hplateau_cs : HasCompactSupport (fun ξ : ℝ => ((plateau ε ξ : ℝ) : ℂ)) := by
      refine HasCompactSupport.of_support_subset_isCompact
        (K := Set.Icc (-(1/2):ℝ) (1/2)) isCompact_Icc ?_
      intro ξ hξ
      by_contra hmem
      have h0 : plateau ε ξ = 0 := by
        by_contra hne
        exact hmem (plateau_support ε hεpos' (Function.mem_support.mpr hne))
      exact hξ (by simp [h0])
    have hamp_cs : HasCompactSupport amp := by
      rw [hamp]
      exact HasCompactSupport.mul_left hplateau_cs
    let χ : SchwartzMap ℝ ℂ := hamp_cs.toSchwartzMap hamp_diff
    have hχ_coe : ⇑χ = amp := funext (HasCompactSupport.toSchwartzMap_toFun hamp_cs hamp_diff)
    set g : ℝ → ℂ := ⇑(FourierTransformInv.fourierInv χ) with hg
    have hg_int : Integrable g :=
      SchwartzMap.integrable (μ := volume) (FourierTransformInv.fourierInv χ)
    have hFg : ∀ ξ : ℝ, FourierTransform.fourier g ξ = amp ξ := by
      intro ξ
      have h1 : FourierTransform.fourier g = ⇑χ := by
        show FourierTransform.fourier (⇑(FourierTransformInv.fourierInv χ)) = ⇑χ
        rw [← SchwartzMap.fourier_coe (FourierTransformInv.fourierInv χ)]
        exact congrArg DFunLike.coe (FourierTransform.fourier_fourierInv_eq χ)
      rw [h1, hχ_coe]
    have hg_band : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) →
        FourierTransform.fourier g ξ = 0 := by
      intro ξ hξ
      rw [hFg ξ]
      have h0 : plateau ε ξ = 0 := by
        rcases lt_or_ge ξ (-(1/2)) with h | h
        · exact plateau_eq_zero_of_le ε hεpos' (le_of_lt h)
        · exact plateau_eq_zero_of_ge ε hεpos' (le_of_not_gt (fun hlt => hξ ⟨h, le_of_lt hlt⟩))
      show trig ξ * ((plateau ε ξ : ℝ) : ℂ) = 0
      rw [h0]; simp
    have hop := hOp g hg_int hg_band
    have hg_eq : g = FourierTransformInv.fourierInv
        (fun ξ : ℝ => trig ξ * ((plateau ε ξ : ℝ) : ℂ)) := by
      show ⇑(FourierTransformInv.fourierInv χ) = _
      rw [SchwartzMap.fourierInv_coe, hχ_coe]
    have hβj : ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂volume ≤ ENNReal.ofReal (Cβ ^ p) * Sp := by
      have h := hCβ ε hεpos' hεle' s a ha
      rw [hg_eq, htrig, hSp]
      exact h
    -- identify the amplitude family `m n · 𝓕 g` with `U j n`
    have hid : ∀ n : ℕ, (fun ξ : ℝ => m n ξ * FourierTransform.fourier g ξ) = U j n := by
      intro n
      funext ξ
      rw [hFg ξ, hamp, hU, hεdef]
      ring
    have hfun : ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
        (fun n => FourierTransformInv.fourierInv
          (fun ξ : ℝ => m n ξ * FourierTransform.fourier g ξ) x)) ^ p ∂volume
        = ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
          (fun n => FourierTransformInv.fourierInv (U j n) x)) ^ p ∂volume := by
      apply lintegral_congr
      intro x
      congr 1
      congr 1
      funext n
      rw [hid n]
    have hop' : ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
        (fun n => FourierTransformInv.fourierInv (U j n) x)) ^ p ∂volume
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂volume := by
      rw [← hfun]
      exact hop
    calc ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
          (fun n => FourierTransformInv.fourierInv (U j n) x)) ^ p ∂volume
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂volume := hop'
      _ ≤ ENNReal.ofReal (A ^ p) * (ENNReal.ofReal (Cβ ^ p) * Sp) :=
          mul_le_mul_right hβj _
      _ = ENNReal.ofReal ((A * Cβ) ^ p) * Sp := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hA p),
            Real.mul_rpow hA hCβpos.le]
  -- the limit as the cut-off opens up
  have hcont : ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
      (fun n => FourierTransformInv.fourierInv (W n) x)) ^ p ∂volume
      ≤ ENNReal.ofReal ((A * Cβ) ^ p) * Sp := by
    refine lintegral_le_of_le_liminf (p := p) (lt_trans zero_lt_one hp)
      (F := fun j x => Work.BourgainPlan.Maximal.varRhoFrom 2 κ
        (fun n => FourierTransformInv.fourierInv (U j n) x))
      (g := fun x => Work.BourgainPlan.Maximal.varRhoFrom 2 κ
        (fun n => FourierTransformInv.fourierInv (W n) x))
      (K := ENNReal.ofReal ((A * Cβ) ^ p) * Sp) ?_ ?_ key
    · intro j
      refine AEMeasurable.iSup (fun hi : ℕ =>
        aemeasurable_varRho_family 2 κ hi (fun n => ?_))
      exact continuous_fourierInv_of_integrable (hU_int j n)
    · intro x
      have hconv : ∀ n : ℕ, Filter.Tendsto
          (fun j : ℕ => FourierTransformInv.fourierInv (U j n) x) Filter.atTop
          (nhds (FourierTransformInv.fourierInv (W n) x)) := by
        intro n
        have h := tendsto_fourierInv_plateau (m n) (hm n) (hsupp n) htrig_meas htrig_bound
          hc0 x
        simpa only [hU, hW] using h
      exact varRhoFrom_two_le_liminf κ
        (fun n => FourierTransformInv.fourierInv (W n) x)
        (fun j n => FourierTransformInv.fourierInv (U j n) x) hconv
  -- the lattice sampling bound
  have hsamp := hC₁ W hW_int w B hw_int hBpos hw_dec hW_ne κ
  -- identification of the discrete convolution with the inverse Fourier transform
  have hId : ∀ n : ℤ, (fun n' : ℕ => ∑ j ∈ s, (∫ ξ in (-(1/2):ℝ)..(1/2), m n' ξ *
        Complex.exp (2 * Real.pi * Complex.I * ((n - j : ℤ) : ℂ) * (ξ : ℂ))) * a j)
      = fun n' : ℕ => FourierTransformInv.fourierInv (W n') (n : ℝ) := by
    intro n
    funext n'
    have h1 : (∑ j ∈ s, (∫ ξ in (-(1/2):ℝ)..(1/2), m n' ξ *
        Complex.exp (2 * Real.pi * Complex.I * ((n - j : ℤ) : ℂ) * (ξ : ℂ))) * a j)
        = ∑ j ∈ s, (∫ ξ in Set.Ioc (-(1/2):ℝ) (1/2), m n' ξ *
            Complex.exp (2 * Real.pi * Complex.I * ((n - j : ℤ) : ℂ) * (ξ : ℂ))) * a j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)]
    rw [h1, hW, htrig]
    exact sum_intervalIntegral_eq_fourierInv (m n') (hm n') (hsupp n') s a n
  calc ∫⁻ k : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n =>
        ∑ j ∈ s, (∫ ξ in (-(1/2):ℝ)..(1/2), m n ξ *
          Complex.exp (2 * Real.pi * Complex.I * ((k - j : ℤ) : ℂ) * (ξ : ℂ))) * a j)) ^ p
        ∂MeasureTheory.Measure.count
      = ∫⁻ k : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n =>
          FourierTransformInv.fourierInv (W n) (k : ℝ))) ^ p
          ∂MeasureTheory.Measure.count := by
        apply lintegral_congr
        intro k
        rw [hId k]
    _ ≤ ENNReal.ofReal (C₁ * B ^ p) * ∫⁻ y : ℝ,
          (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
            (fun n => FourierTransformInv.fourierInv (W n) y)) ^ p ∂volume := hsamp
    _ ≤ ENNReal.ofReal (C₁ * B ^ p) * (ENNReal.ofReal ((A * Cβ) ^ p) * Sp) :=
        mul_le_mul_right hcont _
    _ = ENNReal.ofReal ((((C₁ * B ^ p) ^ (1 / p) * Cβ) * A) ^ p) * Sp := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C₁ * B ^ p)]
        congr 1
        rw [show (C₁ * B ^ p) ^ (1 / p) * Cβ * A
            = ((C₁ * B ^ p) ^ (1 / p)) * (A * Cβ) by ring]
        rw [Real.mul_rpow (Real.rpow_nonneg (mul_pos hC₁pos
            (Real.rpow_pos_of_pos hBpos p)).le _) (mul_nonneg hA hCβpos.le)]
        rw [← Real.rpow_mul (mul_pos hC₁pos (Real.rpow_pos_of_pos hBpos p)).le,
          show (1 / p) * p = 1 by field_simp, Real.rpow_one]
    _ = ENNReal.ofReal ((((C₁ * B ^ p) ^ (1 / p) * Cβ) * A) ^ p)
          * ∑ j ∈ s, ENNReal.ofReal ‖a j‖ ^ p := by rw [hSp]

end

end Work.BourgainPlan.IonescuWainger
