import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.SmallBoxTBWord.rhs_slot_peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `swap_p_slot` — Fubini for the slot-`i` windowed fibre kinetic energy

The one-body slot-`i` kinetic energy of the windowed fibre is a nonnegative
function of `(p, r)`; swapping the `p`-integral with the `r`-integral over the
compact box `abox n a` is Tonelli/Fubini.  The integrability input is a
uniform-in-`r` bound on the fibre energy, obtained from the Plancherel identity
`kinFT_energy_cspt` and the smoothness of `W` and `Φ` on the compact box.
-/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform

namespace Work.SmallBoxTBWord

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1  Integrability of the `p`-energy of a compactly supported smooth fibre -/

/-- The `p`-energy of a smooth compactly supported one-particle function is integrable. -/
theorem kinFT_energy_integrable (u : ℝ³ → ℝ) (hu : ContDiff ℝ ∞ u)
    (hcs : HasCompactSupport u) :
    Integrable (fun p : ℝ³ => ‖p‖ ^ 2 * ‖kinFT (fun z => (u z : ℂ)) p‖ ^ 2) := by
  let F : SchwartzMap ℝ³ ℂ := (hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hu)
  have hF_coe : (F : ℝ³ → ℂ) = fun z => ((u z : ℝ) : ℂ) := rfl
  have hIntξ : Integrable (fun ξ : ℝ³ => ‖ξ‖ ^ 2 * ‖(𝓕 F) ξ‖ ^ 2) :=
    Work.SmallBoxBridge.Fourier.integrable_norm_sq_fourier F
  have hInt2 : Integrable (fun p : ℝ³ => ‖(((2 * Real.pi)⁻¹ : ℝ)) • p‖ ^ 2 *
      ‖(𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p)‖ ^ 2) :=
    hIntξ.comp_smul (R := (2 * Real.pi)⁻¹) (by positivity)
  have hnorm : ∀ p : ℝ³, ‖p‖ ^ 2 * ‖(𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p)‖ ^ 2
      = (2 * Real.pi) ^ 2 * (‖(((2 * Real.pi)⁻¹ : ℝ)) • p‖ ^ 2 *
          ‖(𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p)‖ ^ 2) := by
    intro p
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹)]
    field_simp
  have hkft : ∀ p : ℝ³, kinFT (fun z : ℝ³ => (u z : ℂ)) p
      = (𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p) := by
    intro p
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    have hfun : (fun z : ℝ³ => (u z : ℂ)) = ⇑F := by
      funext z; rw [hF_coe]
    rw [hfun, SchwartzMap.fourier_coe]
  refine (hInt2.const_mul ((2 * Real.pi) ^ 2)).congr (Eventually.of_forall (fun p => ?_))
  simp only [hnorm p, hkft p]

/-! ## 2  A uniform (in the configuration `r`) bound on the fibre energy -/

/-- **Uniform bound on the fibre `p`-energy.**  For every `r` in the box the fibre
`z ↦ W z · Φ(kcInsN n i (z,r))` is smooth with support in `acube a`, so its kinetic
energy is the Dirichlet integral of the ambient slot-`i` function over a compact set;
that Dirichlet integrand is continuous on `abox (n+1) a`, hence bounded uniformly. -/
theorem fibre_energy_uniform_bound {n : ℕ} {a : ℝ} (ha : 0 < a)
    {W : ℝ³ → ℝ} (hW : ContDiff ℝ ∞ W) (hWcs : HasCompactSupport W)
    (htsupp : tsupport W ⊆ acube a)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin (n + 1)) :
    ∃ C : ℝ, ∀ r ∈ abox n a,
      (∫ p : ℝ³, ‖p‖ ^ 2 *
        ‖kinFT (fun z : ℝ³ => (W z : ℂ) *
          (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2) ≤ C := by
  have hAc : ContDiff ℝ ∞ (fun x : X (n + 1) => W (x i) * Φ x) :=
    (hW.comp (by fun_prop)).mul hΦ
  have hfd : Continuous (fun x : X (n + 1) =>
      fderiv ℝ (fun x : X (n + 1) => W (x i) * Φ x) x) :=
    hAc.continuous_fderiv (by simp)
  have hcont : Continuous (fun x : X (n + 1) => ∑ k : Fin 3,
      (fderiv ℝ (fun x : X (n + 1) => W (x i) * Φ x) x (kcDir (n + 1) i k)) ^ 2) :=
    continuous_finsetSum _ (fun k _ => ((hfd.clm_apply continuous_const).pow 2))
  obtain ⟨C₀, hC₀⟩ := (abox_compact (n + 1) ha).exists_bound_of_continuousOn hcont.continuousOn
  have hC₀' : ∀ x ∈ abox (n + 1) a,
      (∑ k : Fin 3, (fderiv ℝ (fun x : X (n + 1) => W (x i) * Φ x) x
        (kcDir (n + 1) i k)) ^ 2) ≤ C₀ := by
    intro x hx
    have h := hC₀ x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun k _ => sq_nonneg _))] at h
  refine ⟨(2 * Real.pi) ^ 3 * (C₀ * a ^ 3), fun r hr => ?_⟩
  have hzeroW : ∀ z : ℝ³, z ∉ acube a → W z = 0 := by
    intro z hz
    by_contra h
    exact hz (htsupp (subset_tsupport W (Function.mem_support.mpr h)))
  have hucd : ContDiff ℝ ∞ (fun z : ℝ³ => W z * Φ (kcInsN n i (z, r))) :=
    hW.mul (hΦ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r))
  have hucs : HasCompactSupport (fun z : ℝ³ => W z * Φ (kcInsN n i (z, r))) := hWcs.mul_right
  have hplan := Work.SmallBoxBridge.Fourier.kinFT_energy_cspt
    (fun z : ℝ³ => W z * Φ (kcInsN n i (z, r))) hucd hucs
  have harg : (fun z : ℝ³ => (W z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ))
      = (fun z : ℝ³ => ((W z * Φ (kcInsN n i (z, r)) : ℝ) : ℂ)) := by
    funext z; exact (Complex.ofReal_mul _ _).symm
  rw [harg]
  -- the fibre Dirichlet integrand vanishes off `acube a`
  have hzero_fd : ∀ z : ℝ³, z ∉ acube a →
      (∑ k : Fin 3, (fderiv ℝ (fun w : ℝ³ => W w * Φ (kcInsN n i (w, r))) z
        (kcStdBasis k)) ^ 2) = 0 := by
    intro z hz
    have hsu : Function.support (fun w : ℝ³ => W w * Φ (kcInsN n i (w, r))) ⊆ acube a := by
      intro w hw
      by_contra hc
      rw [Function.mem_support] at hw
      exact hw (mul_eq_zero.mpr (Or.inl (hzeroW w hc)))
    have hev : (fun w : ℝ³ => W w * Φ (kcInsN n i (w, r))) =ᶠ[𝓝 z] (fun _ => 0) := by
      have hopen : IsOpen (acube a)ᶜ := (acube_isClosed a).isOpen_compl
      filter_upwards [hopen.mem_nhds hz] with w hw
      by_contra h
      exact hw (hsu (Function.mem_support.mpr h))
    have hfd0 : fderiv ℝ (fun w : ℝ³ => W w * Φ (kcInsN n i (w, r))) z = 0 := by
      rw [hev.fderiv_eq, fderiv_const_apply]
    simp [hfd0]
  have hshrink := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := acube a)
    (f := fun z : ℝ³ => ∑ k : Fin 3, (fderiv ℝ (fun w : ℝ³ => W w * Φ (kcInsN n i (w, r))) z
      (kcStdBasis k)) ^ 2) hzero_fd
  have hmem : ∀ z : ℝ³, z ∈ acube a → kcInsN n i (z, r) ∈ abox (n + 1) a := by
    intro z hz j
    by_cases hj : j = i
    · rw [hj, kc_insN_apply_same]; exact hz
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      rw [kc_insN_apply_succ]; exact hr j'
  have hpt : ∀ z : ℝ³, z ∈ acube a →
      (∑ k : Fin 3, (fderiv ℝ (fun w : ℝ³ => W w * Φ (kcInsN n i (w, r))) z
        (kcStdBasis k)) ^ 2) ≤ C₀ := by
    intro z hz
    have hsum : (∑ k : Fin 3, (fderiv ℝ (fun w : ℝ³ => W w * Φ (kcInsN n i (w, r))) z
          (kcStdBasis k)) ^ 2)
        = ∑ k : Fin 3, (fderiv ℝ (fun x : X (n + 1) => W (x i) * Φ x)
            (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2 := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact congrArg (fun t => t ^ 2) (fderiv_slot_eq_fibre_W hW hΦ i r z k).symm
    rw [hsum]
    exact hC₀' _ (hmem z hz)
  have hcontu : Continuous (fun z : ℝ³ => ∑ k : Fin 3,
      (fderiv ℝ (fun w : ℝ³ => W w * Φ (kcInsN n i (w, r))) z (kcStdBasis k)) ^ 2) := by
    have hfdu : Continuous (fun z : ℝ³ =>
        fderiv ℝ (fun w : ℝ³ => W w * Φ (kcInsN n i (w, r))) z) :=
      hucd.continuous_fderiv (by simp)
    exact continuous_finsetSum _ (fun k _ => ((hfdu.clm_apply continuous_const).pow 2))
  have hbound : (∫ z : ℝ³, ∑ k : Fin 3, (fderiv ℝ (fun w : ℝ³ => W w * Φ (kcInsN n i (w, r))) z
        (kcStdBasis k)) ^ 2) ≤ C₀ * a ^ 3 := by
    rw [← hshrink]
    calc (∫ z in acube a, ∑ k : Fin 3, (fderiv ℝ (fun w : ℝ³ => W w * Φ (kcInsN n i (w, r))) z
            (kcStdBasis k)) ^ 2)
        ≤ ∫ z in acube a, C₀ := by
          apply integral_mono_ae
          · exact ContinuousOn.integrableOn_compact (acube_compact ha) hcontu.continuousOn
          · exact integrableOn_const (by rw [acube_volume a ha.le]; exact ENNReal.ofReal_lt_top.ne)
          · filter_upwards [ae_restrict_mem (acube_measurable a)] with z hz
            exact hpt z hz
      _ = C₀ * a ^ 3 := integral_const_acube a ha C₀
  have hpi : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
  calc (∫ p : ℝ³, ‖p‖ ^ 2 *
          ‖kinFT (fun z : ℝ³ => ((W z * Φ (kcInsN n i (z, r)) : ℝ) : ℂ)) p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖p‖ ^ 2 *
          ‖kinFT (fun z : ℝ³ => ((W z * Φ (kcInsN n i (z, r)) : ℝ) : ℂ)) p‖ ^ 2) := by
        rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
    _ = (2 * Real.pi) ^ 3 * ∫ z : ℝ³, ∑ k : Fin 3,
          (fderiv ℝ (fun w : ℝ³ => W w * Φ (kcInsN n i (w, r))) z (kcStdBasis k)) ^ 2 := by
        rw [hplan]
    _ ≤ (2 * Real.pi) ^ 3 * (C₀ * a ^ 3) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)

/-! ## 3  Joint measurability of the `(p,r)`-integrand -/

/-- The uncurried `(p,r)`-integrand of the slot fibre is `AEStronglyMeasurable` for the
product measure `volume × (volume ↾ abox n a)`. -/
theorem fibre_energy_aemeas {n : ℕ} {a : ℝ}
    {W : ℝ³ → ℝ} (hW : ContDiff ℝ ∞ W)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin (n + 1)) :
    AEStronglyMeasurable (Function.uncurry (fun (p : ℝ³) (r : X n) => ‖p‖ ^ 2 *
        ‖kinFT (fun z : ℝ³ => (W z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2))
      (volume.prod ((volume : Measure (X n)).restrict (abox n a))) := by
  have hjoint : AEStronglyMeasurable (fun w : (ℝ³ × X n) × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ w.1.1 w.2 : ℂ))) *
        ((W w.2 : ℂ) * (Φ (kcInsN n i (w.2, w.1.2)) : ℂ)))
      ((volume.prod ((volume : Measure (X n)).restrict (abox n a))).prod volume) := by
    have h1 : Continuous (fun w : (ℝ³ × X n) × ℝ³ =>
        Complex.exp (-(Complex.I * (inner ℝ w.1.1 w.2 : ℂ)))) :=
      Complex.continuous_exp.comp ((continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_inner.comp
          (continuous_fst.fst.prodMk continuous_snd)))).neg)
    have h2 : Continuous (fun w : (ℝ³ × X n) × ℝ³ => (W w.2 : ℂ)) :=
      Complex.continuous_ofReal.comp (hW.continuous.comp continuous_snd)
    have h3 : Continuous (fun w : (ℝ³ × X n) × ℝ³ =>
        (Φ (kcInsN n i (w.2, w.1.2)) : ℂ)) :=
      Complex.continuous_ofReal.comp (hΦ.continuous.comp
        ((kcInsN_cont i).comp (continuous_snd.prodMk continuous_fst.snd)))
    exact ((h1.mul (h2.mul h3))).stronglyMeasurable.aestronglyMeasurable
  have hK : AEStronglyMeasurable (fun q : ℝ³ × X n => ∫ z : ℝ³,
      Complex.exp (-(Complex.I * (inner ℝ q.1 z : ℂ))) *
        ((W z : ℂ) * (Φ (kcInsN n i (z, q.2)) : ℂ)))
      (volume.prod ((volume : Measure (X n)).restrict (abox n a))) :=
    hjoint.integral_prod_right'
  have h2 : AEStronglyMeasurable (fun q : ℝ³ × X n => ‖q.1‖ ^ 2)
      (volume.prod ((volume : Measure (X n)).restrict (abox n a))) :=
    ((continuous_norm.comp continuous_fst).pow 2).aestronglyMeasurable
  exact h2.mul (hK.norm.pow 2)

/-! ## 4  The swap -/

theorem swap_p_slot {n : ℕ} {a : ℝ} (ha : 0 < a) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : ContDiff ℝ (⊤ : ENat) W) (hWcs : HasCompactSupport W)
    (htsupp : tsupport W ⊆ Submission.BoseGases.acube a)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    (∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 *
        (∫ r in Submission.BoseGases.abox n a,
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (W z : ℂ) *
            (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2))
      = ∫ r in Submission.BoseGases.abox n a,
          ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (W z : ℂ) *
              (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 := by
  set ν : Measure (X n) := (volume : Measure (X n)).restrict (abox n a) with hν
  obtain ⟨C, hC⟩ := fibre_energy_uniform_bound ha hW hWcs htsupp hΦ i
  let f : ℝ³ → X n → ℝ := fun p r => ‖p‖ ^ 2 *
      ‖kinFT (fun z : ℝ³ => (W z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2
  have hf_nonneg : ∀ p r, 0 ≤ f p r := fun p r => by positivity
  have hmeas : AEStronglyMeasurable (Function.uncurry f) (volume.prod ν) := by
    simpa only [f, hν] using fibre_energy_aemeas (a := a) hW hΦ i
  have hint : Integrable (Function.uncurry f) (volume.prod ν) := by
    refine Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite
      (μ := volume) (ν := ν) (g := fun _ : X n => ENNReal.ofReal (max C 0)) hmeas ?_ ?_
    · rw [lintegral_const]
      have hfin : ν Set.univ < ⊤ := by
        rw [hν, Measure.restrict_apply_univ]
        exact abox_lt_top n a ha.le
      exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne
    · filter_upwards [ae_restrict_mem (abox_measurable n a)] with r hr
      have hInt : Integrable (fun p : ℝ³ => f p r) volume := by
        have hkey := kinFT_energy_integrable
          (fun z : ℝ³ => W z * Φ (kcInsN n i (z, r)))
          (hW.mul (hΦ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r)))
          (hWcs.mul_right)
        refine hkey.congr (Eventually.of_forall (fun p => ?_))
        simp only [f]
        have hflip : (fun z : ℝ³ => ((W z * Φ (kcInsN n i (z, r)) : ℝ) : ℂ))
            = (fun z : ℝ³ => (W z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) := by
          funext z; exact Complex.ofReal_mul _ _
        rw [hflip]
      have hnn : 0 ≤ᵐ[volume] (fun p : ℝ³ => f p r) :=
        Eventually.of_forall (fun p => hf_nonneg p r)
      have hcongr : (∫⁻ p, ENNReal.ofReal ‖f p r‖ ∂volume)
          = ∫⁻ p, ENNReal.ofReal (f p r) ∂volume :=
        lintegral_congr (fun p => by rw [Real.norm_of_nonneg (hf_nonneg p r)])
      rw [hcongr, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
      exact ENNReal.ofReal_le_ofReal (le_trans (hC r hr) (le_max_left C 0))
  have hL : (∫ p : ℝ³, ‖p‖ ^ 2 * (∫ r : X n, ‖kinFT (fun z : ℝ³ => (W z : ℂ) *
        (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 ∂ν) ∂volume)
      = ∫ p : ℝ³, ∫ r : X n, f p r ∂ν ∂volume := by
    refine integral_congr_ae (Eventually.of_forall (fun p => ?_))
    simp only [f]
    rw [← MeasureTheory.integral_const_mul]
  rw [hL, MeasureTheory.integral_integral_swap (μ := volume) (ν := ν) hint]

end Work.SmallBoxTBWord
