/-
`Work.Found.record_modulus_of_bound`: the uniform record modulus for a *fixed* family of
admissible coefficients `μs j` with records `d j`, under the extra hypothesis that the
approximating coefficients `(d j).μn n` are bounded by the caller's `k`.

The uniform modulus is assembled from three pieces:

* `Work.MRMT.Found.record_weakDeriv_energy` (this workspace): for every record
  `d : PrincipalData μ` the `L²_loc` limit `recD d` of `∂(d.Fn n)` is a weak `∂`-derivative of
  `d.φ`, `μ · recD d` is a weak `∂̄`-derivative, and the deviation satisfies the *uniform*
  energy bound `eLpNorm (recD d - 1) 2 ≤ ofReal (√(π R²)/(1-k)) · eLpNorm μ ⊤`;
* `exists_uniform_tail_clean` (below): the energy bound plus the Cauchy-transform
  representation `φ - id = C(μ ∂φ)` gives a *uniform* tail `‖φ z - z‖ ≤ Cd/‖z‖` for
  `‖z‖ ≥ Rd`, with `Cd, Rd` depending only on `k` and `R`;
* `modulus_of_approx` (below): Courant–Lebesgue applied to the `C¹` approximants
  `(d j).Fn n` (with dilatation bound `k`, justified by `hkn` and `beltrami_Fn`) together with
  the uniform tail of `(d j).φ` and the locally uniform convergence `(d j).Fn n → (d j).φ`
  produces one constant `C` valid for all `j`.

The two lemmas `exists_uniform_tail_clean` and `modulus_of_approx` are copied from
`Submission/Work/MRMT/Found/modulus_of_records_clean.lean`, where they carry the same
statements and proofs; they are reproduced here because that module lies in the
`Work.MRMT.QC.eq_zero_of_beltrami_of_decay` camp and cannot be imported together with
`Work.MRMT.QC.principal_unique` (which `records_agree` needs).
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.records_agree
import Submission.Work.MRMT.Found.record_weakDeriv_energy
import Submission.Work.MRMT.Found.courantLebesgue_uniform
import Submission.Work.MRMT.Found.norm_image_le_of_decay
import Submission.Work.MRMT.Found.fw_decay_cauchyTransform_le
import Submission.Work.MRMT.Found.ae_eq_cauchyTransform_of_isDbarDeriv
import Submission.Work.MRMT.Found.memLp_two_mul_of_memL2Loc
import Submission.Work.MRMT.Sobolev.isDzDeriv_id_add
import Submission.Work.MRMT.Weyl.isDbarDeriv_moll_contDiff
import Submission.Work.MRMT.Sobolev.mollification_pairing_tendsto

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Metric Filter Topology Complex Function
open scoped Topology ENNReal

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.MRMT.Found

/-- An a.e. inequality between functions continuous on an **open** set holds everywhere on it. -/
private theorem le_on_open_of_ae_le {f g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (h : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → f z ≤ g z) :
    ∀ z ∈ U, f z ≤ g z := by
  have hmin : ContinuousOn (fun z => min (f z) (g z)) U := by fun_prop
  have hae : (fun z => min (f z) (g z)) =ᵐ[(volume : Measure ℂ).restrict U] f := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
    filter_upwards [h] with z hz hzU
    exact min_eq_left (hz hzU)
  have heq : Set.EqOn (fun z => min (f z) (g z)) f U :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hae hU hmin hf
  intro z hz
  have h1 : min (f z) (g z) = f z := heq hz
  calc f z = min (f z) (g z) := h1.symm
    _ ≤ g z := min_le_right _ _
/-- Pointwise convergence from locally uniform convergence. -/
private theorem tendsto_of_tendstoLocallyUniformly' {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformly F f Filter.atTop) (z : ℂ) :
    Tendsto (fun n => F n z) Filter.atTop (𝓝 (f z)) := by
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.mp h) {z} isCompact_singleton
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hunif) ε hε] with n hn
  simpa [dist_comm] using hn z rfl
/-- `∫ ‖f‖²` is the square of the `L²` norm of the class of `f`. -/
private theorem norm_sq_toLp_eq {f : ℂ → ℂ} (hf : MemLp f 2 (volume : Measure ℂ)) :
    ∫ z, ‖f z‖ ^ 2 = ‖hf.toLp f‖ ^ 2 := by
  have hnn : 0 ≤ ∫ z, ‖f z‖ ^ 2 := integral_nonneg fun z => by positivity
  have h1 : ENNReal.toReal (eLpNorm f 2 (volume : Measure ℂ))
      = Real.sqrt (∫ z, ‖f z‖ ^ 2) := by
    rw [MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm (p := 2) (by norm_num) (by norm_num) hf,
      ENNReal.toReal_ofReal (by positivity),
      show ((2 : ℝ≥0∞).toReal : ℝ) = 2 by norm_num,
      show ((2 : ℝ))⁻¹ = 1 / 2 by norm_num]
    rw [show (∫ a : ℂ, ‖f a‖ ^ (2 : ℝ)) = ∫ z : ℂ, ‖f z‖ ^ 2 from by
      refine integral_congr_ae (Eventually.of_forall fun a => ?_)
      change ‖f a‖ ^ (2 : ℝ) = ‖f a‖ ^ (2 : ℕ)
      exact Real.rpow_natCast _ 2]
    exact (Real.sqrt_eq_rpow _).symm
  rw [MeasureTheory.Lp.norm_toLp, h1, Real.sq_sqrt hnn]
/-- The support of a product is contained in the support of the first factor. -/
private theorem support_mul_subset' {μ D : ℂ → ℂ} :
    Function.support (fun z => μ z * D z) ⊆ Function.support μ := by
  intro z hz
  exact Function.mem_support.mpr fun h => hz (by simp [h])

/-- An L2-loc function is square integrable on compact sets (local copy). -/
private theorem memL2Loc_integrableOn' {f : ℂ → ℂ} (h : MemL2Loc f) {K : Set ℂ}
    (hK : IsCompact K) : IntegrableOn (fun z => ‖f z‖ ^ 2) K (volume : Measure ℂ) := by
  simpa using h K hK

/-- The weak (distributional) `∂̄`-derivatives form a linear relation. -/
private theorem IsDbarDeriv_sub' {f₁ f₂ g₁ g₂ : ℂ → ℂ} (h₁ : IsDbarDeriv f₁ g₁)
    (h₂ : IsDbarDeriv f₂ g₂) : IsDbarDeriv (f₁ - f₂) (g₁ - g₂) := by
  obtain ⟨hf₁, hg₁, hm₁⟩ := h₁
  obtain ⟨hf₂, hg₂, hm₂⟩ := h₂
  refine ⟨hf₁.sub hf₂, hg₁.sub hg₂, fun φ => ?_⟩
  obtain ⟨i₁, j₁, e₁⟩ := hm₁ φ
  obtain ⟨i₂, j₂, e₂⟩ := hm₂ φ
  have hi : Integrable (fun z => (f₁ z - f₂ z) * dzbar (φ : ℂ → ℂ) z) :=
    (i₁.sub i₂).congr (Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]; ring)
  have hj : Integrable (fun z => (g₁ z - g₂ z) * (φ : ℂ → ℂ) z) :=
    (j₁.sub j₂).congr (Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]; ring)
  refine ⟨hi, hj, ?_⟩
  have hL : ∫ z, (f₁ z - f₂ z) * dzbar (φ : ℂ → ℂ) z
      = (∫ z, f₁ z * dzbar (φ : ℂ → ℂ) z) - ∫ z, f₂ z * dzbar (φ : ℂ → ℂ) z := by
    rw [← integral_sub i₁ i₂]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  have hR : ∫ z, (g₁ z - g₂ z) * (φ : ℂ → ℂ) z
      = (∫ z, g₁ z * (φ : ℂ → ℂ) z) - ∫ z, g₂ z * (φ : ℂ → ℂ) z := by
    rw [← integral_sub j₁ j₂]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  simp only [Pi.sub_apply]
  rw [hL, hR, e₁, e₂]
  ring

/-! ## Uniform decay of the record from the uniform energy bound -/

/-- **Uniform decay of a solution of the Beltrami equation with uniform `L²` deviation data.**

Let `φ` be continuous with weak `∂̄`-derivative `μ · D`, where `μ` is a.e. bounded by `K` and
supported in `closedBall 0 R`, and let the weak `∂`-derivative deviation satisfy
`eLpNorm (D - 1) 2 ≤ ofReal (√(πR²)/(1-k)) · eLpNorm μ ⊤` with `k < 1`.  If `φ` decays like
`C/‖z‖` at infinity, then `‖φ z - z‖ ≤ Cd/‖z‖` for `‖z‖ ≥ Rd`, with `Cd, Rd` depending only on
`k, K` and `R`. -/
theorem exists_uniform_tail_clean (k K R : ℝ) (hk : k < 1) (hK0 : 0 ≤ K) (hK1 : K < 1) :
    ∃ Cd Rd : ℝ, 0 ≤ Cd ∧ 1 ≤ Rd ∧
      ∀ (φ μ D : ℂ → ℂ),
        Continuous φ →
        (∃ C R', ∀ z : ℂ, R' ≤ ‖z‖ → ‖φ z - z‖ ≤ C / ‖z‖) →
        Function.support μ ⊆ Metric.closedBall 0 R →
        AEStronglyMeasurable μ (volume : Measure ℂ) →
        (∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ K) →
        MemL2Loc D →
        Work.MRMT.IsDbarDeriv φ (fun z => μ z * D z) →
        eLpNorm (fun z => D z - 1) 2 (volume : Measure ℂ)
          ≤ ENNReal.ofReal (Real.sqrt (Real.pi * R ^ 2) / (1 - k)) *
            eLpNorm μ ⊤ (volume : Measure ℂ) →
        ∀ z : ℂ, Rd ≤ ‖z‖ → ‖φ z - z‖ ≤ Cd / ‖z‖ := by
  set M : ℝ := max R 0 with hMdef
  have hRM : R ≤ M := le_max_left R 0
  have hM0 : 0 ≤ M := le_max_right R 0
  set V : ℝ := ((volume : Measure ℂ) (Metric.closedBall (0 : ℂ) R)).toReal with hVdef
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set E0 : ℝ := Real.sqrt (Real.pi * R ^ 2) * K / (1 - k) with hE0def
  have hE00 : 0 ≤ E0 := by rw [hE0def]; positivity
  set E1 : ℝ := K * Real.sqrt (2 * V + 2 * E0 ^ 2 + 1) with hE1def
  have hE10 : 0 ≤ E1 := by rw [hE1def]; positivity
  set VM : ℝ := ((volume : Measure ℂ) (Metric.closedBall (0 : ℂ) M)).toReal with hVMdef
  refine ⟨2 * E1 * Real.sqrt VM / Real.pi, max (2 * M) 1 + 1, by positivity, ?_, ?_⟩
  · have := le_max_right (2 * M) 1; linarith
  · intro φ μ D hφc hdec hsupp hμmeas hb hDloc hdzbar hbound
    have hμtop : eLpNorm μ ⊤ (volume : Measure ℂ) ≤ ENNReal.ofReal K := by
      rw [MeasureTheory.eLpNorm_exponent_top hμmeas]
      exact MeasureTheory.eLpNormEssSup_le_of_ae_bound hb
    have hE0eq : ENNReal.ofReal E0
        = ENNReal.ofReal (Real.sqrt (Real.pi * R ^ 2) / (1 - k)) * ENNReal.ofReal K := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.sqrt (Real.pi * R ^ 2) / (1 - k))]
      congr 1
      rw [hE0def]; ring
    have hdev_le : eLpNorm (fun z => D z - 1) 2 (volume : Measure ℂ) ≤ ENNReal.ofReal E0 := by
      rw [hE0eq]
      exact hbound.trans (mul_le_mul_of_nonneg_left hμtop (by positivity))
    have hdev : MemLp (fun z => D z - 1) 2 (volume : Measure ℂ) :=
      MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hdev_le ENNReal.ofReal_lt_top)
    have hdevint : Integrable (fun z => ‖D z - 1‖ ^ 2) (volume : Measure ℂ) :=
      (MeasureTheory.memLp_two_iff_integrable_sq_norm hdev.aestronglyMeasurable).mp hdev
    have hdev_energy : ∫ z, ‖D z - 1‖ ^ 2 ≤ E0 ^ 2 := by
      calc ∫ z, ‖D z - 1‖ ^ 2 = ‖hdev.toLp (fun z => D z - 1)‖ ^ 2 := norm_sq_toLp_eq hdev
        _ = ((eLpNorm (fun z => D z - 1) 2 (volume : Measure ℂ)).toReal) ^ 2 := by
              rw [MeasureTheory.Lp.norm_toLp]
        _ ≤ E0 ^ 2 := by
              refine pow_le_pow_left₀ ENNReal.toReal_nonneg ?_ 2
              calc (eLpNorm (fun z => D z - 1) 2 (volume : Measure ℂ)).toReal
                  ≤ (ENNReal.ofReal E0).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdev_le
                _ = E0 := ENNReal.toReal_ofReal hE00
    set ω : ℂ → ℂ := fun z => μ z * D z with hωdef
    have hωmeas : AEStronglyMeasurable ω (volume : Measure ℂ) :=
      hdzbar.2.1.aestronglyMeasurable
    have hωLp : MemLp ω 2 (volume : Measure ℂ) :=
      memLp_two_mul_of_memL2Loc hωmeas hDloc hb hsupp
    have hωsupp : ∀ z : ℂ, ω z ≠ 0 → ‖z‖ ≤ M := by
      intro z hz
      have h1 : z ∈ Metric.closedBall (0 : ℂ) R :=
        hsupp (support_mul_subset' (Function.mem_support.mpr hz))
      have h2 : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using h1
      exact h2.trans hRM
    have hωcs : HasCompactSupport ω :=
      HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) R)
        (support_mul_subset'.trans hsupp)
    have hintω : Integrable ω (volume : Measure ℂ) :=
      Work.MRMT.Sobolev.integrable_of_memLp_two_hasCompactSupport hωLp hωcs
    have hDOn : IntegrableOn (fun z => ‖D z‖ ^ 2) (Metric.closedBall (0 : ℂ) R) volume :=
      memL2Loc_integrableOn' hDloc (isCompact_closedBall (0 : ℂ) R)
    have hdevOn : IntegrableOn (fun z => ‖D z - 1‖ ^ 2) (Metric.closedBall (0 : ℂ) R) volume :=
      hdevint.integrableOn
    have hdevB : ∫ z in Metric.closedBall (0 : ℂ) R, ‖D z - 1‖ ^ 2 ≤ E0 ^ 2 :=
      (setIntegral_le_integral hdevint (Eventually.of_forall fun z => sq_nonneg _)).trans hdev_energy
    have hpt : ∀ z : ℂ, ‖D z‖ ^ 2 ≤ 2 + 2 * ‖D z - 1‖ ^ 2 := by
      intro z
      have h1 : ‖D z‖ ≤ 1 + ‖D z - 1‖ := by
        calc ‖D z‖ = ‖(D z - 1) + 1‖ := by ring_nf
          _ ≤ ‖D z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ = ‖D z - 1‖ + 1 := by norm_num
          _ = 1 + ‖D z - 1‖ := by ring
      have h2 : (1 + ‖D z - 1‖) ^ 2 ≤ 2 + 2 * ‖D z - 1‖ ^ 2 := by
        nlinarith [sq_nonneg (‖D z - 1‖ - 1)]
      have h3 : ‖D z‖ ^ 2 ≤ (1 + ‖D z - 1‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      linarith
    have hInt2 : IntegrableOn (fun z => 2 + 2 * ‖D z - 1‖ ^ 2)
        (Metric.closedBall (0 : ℂ) R) volume :=
      (integrableOn_const (C := (2 : ℝ)) (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne).add
        (hdevOn.const_mul 2)
    have hIntEq : ∫ z in Metric.closedBall (0 : ℂ) R, (2 + 2 * ‖D z - 1‖ ^ 2)
        = 2 * V + 2 * ∫ z in Metric.closedBall (0 : ℂ) R, ‖D z - 1‖ ^ 2 := by
      have hA : IntegrableOn (fun _ : ℂ => (2 : ℝ)) (Metric.closedBall (0 : ℂ) R) volume :=
        integrableOn_const (C := (2 : ℝ)) (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne
      have hB : IntegrableOn (fun z : ℂ => 2 * ‖D z - 1‖ ^ 2) (Metric.closedBall (0 : ℂ) R) volume :=
        hdevOn.const_mul 2
      rw [integral_add hA hB, integral_const_mul, MeasureTheory.setIntegral_const, smul_eq_mul,
        MeasureTheory.Measure.real_def, hVdef]
      ring
    have hDB : ∫ z in Metric.closedBall (0 : ℂ) R, ‖D z‖ ^ 2 ≤ 2 * V + 2 * E0 ^ 2 := by
      calc ∫ z in Metric.closedBall (0 : ℂ) R, ‖D z‖ ^ 2
          ≤ ∫ z in Metric.closedBall (0 : ℂ) R, (2 + 2 * ‖D z - 1‖ ^ 2) :=
            setIntegral_mono_on hDOn hInt2 measurableSet_closedBall (fun z _ => hpt z)
        _ = 2 * V + 2 * ∫ z in Metric.closedBall (0 : ℂ) R, ‖D z - 1‖ ^ 2 := hIntEq
        _ ≤ 2 * V + 2 * E0 ^ 2 := by linarith
    have hωenergy : ∫ z, ‖ω z‖ ^ 2 ≤ E1 ^ 2 := by
      have hωsq_int : Integrable (fun z => ‖ω z‖ ^ 2) (volume : Measure ℂ) :=
        (MeasureTheory.memLp_two_iff_integrable_sq_norm hωmeas).mp hωLp
      have hind_int : Integrable
          (fun z => (Metric.closedBall (0 : ℂ) R).indicator (fun z => K ^ 2 * ‖D z‖ ^ 2) z)
          (volume : Measure ℂ) :=
        (integrable_indicator_iff measurableSet_closedBall).mpr (hDOn.const_mul (K ^ 2))
      have hle : ∀ᵐ z ∂(volume : Measure ℂ), ‖ω z‖ ^ 2 ≤
          (Metric.closedBall (0 : ℂ) R).indicator (fun z => K ^ 2 * ‖D z‖ ^ 2) z := by
        filter_upwards [hb] with z hz
        by_cases hzR : z ∈ Metric.closedBall (0 : ℂ) R
        · rw [Set.indicator_of_mem hzR, hωdef, norm_mul, mul_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz 2) (sq_nonneg _)
        · rw [Set.indicator_of_notMem hzR]
          have h0 : μ z = 0 := by
            by_contra hne
            exact hzR (hsupp (Function.mem_support.mpr hne))
          simp [hωdef, h0]
      calc ∫ z, ‖ω z‖ ^ 2
          ≤ ∫ z, (Metric.closedBall (0 : ℂ) R).indicator (fun z => K ^ 2 * ‖D z‖ ^ 2) z :=
            integral_mono_ae hωsq_int hind_int hle
        _ = K ^ 2 * ∫ z in Metric.closedBall (0 : ℂ) R, ‖D z‖ ^ 2 := by
            rw [integral_indicator measurableSet_closedBall, integral_const_mul]
        _ ≤ K ^ 2 * (2 * V + 2 * E0 ^ 2) := mul_le_mul_of_nonneg_left hDB (sq_nonneg K)
        _ ≤ E1 ^ 2 := by
            rw [hE1def, mul_pow, Real.sq_sqrt (by positivity)]
            nlinarith [sq_nonneg K, sq_nonneg E0]
    have hCdecay : ∀ z : ℂ, max (2 * M) 1 ≤ ‖z‖ →
        ‖Work.MRMT.cauchyTransform ω z‖ ≤ (2 * E1 * Real.sqrt VM / Real.pi) / ‖z‖ := by
      intro z hz
      simpa [hVMdef] using fw_decay_cauchyTransform_le hM0 hE10 hωLp hωsupp hωenergy z hz
    have hid : Work.MRMT.IsDbarDeriv (fun z : ℂ => z) (0 : ℂ → ℂ) :=
      Work.MRMT.Sobolev.isDbarDeriv_id_zero_aux
    have hsub0 : Work.MRMT.IsDbarDeriv (fun z => φ z - z) (fun z => μ z * D z - 0) :=
      IsDbarDeriv_sub' hdzbar hid
    have hsub : Work.MRMT.IsDbarDeriv (fun z => φ z - z) ω :=
      Work.MRMT.Weyl.isDbarDeriv_congr hsub0 (fun z => by simp [hωdef])
    have hae : (fun z => φ z - z) =ᵐ[(volume : Measure ℂ)] Work.MRMT.cauchyTransform ω :=
      ae_eq_cauchyTransform_of_isDbarDeriv hsub.1 hsub hintω
        (support_mul_subset'.trans hsupp) hdec
    have hae' : ∀ᵐ z ∂(volume : Measure ℂ), max (2 * M) 1 < ‖z‖ →
        ‖φ z - z‖ ≤ (2 * E1 * Real.sqrt VM / Real.pi) / ‖z‖ := by
      filter_upwards [hae] with z hz hzR
      rw [hz]
      exact hCdecay z (le_of_lt hzR)
    have hmain := le_on_open_of_ae_le (U := {z : ℂ | max (2 * M) 1 < ‖z‖})
      (isOpen_lt continuous_const continuous_norm)
      ((hφc.sub continuous_id).norm).continuousOn
      (continuousOn_const.div continuous_norm.continuousOn (fun z hz => by
        have h1 : 0 < max (2 * M) 1 := lt_of_lt_of_le one_pos (le_max_right (2 * M) 1)
        exact ne_of_gt (lt_trans h1 hz)))
      hae'
    intro z hz
    exact hmain z (lt_of_lt_of_le (lt_add_one _) hz)

/-! ## The uniform Courant--Lebesgue modulus for a locally uniform limit -/

/-- **Uniform Courant--Lebesgue modulus for a locally uniform limit of `C¹` Beltrami solutions.**

Let `Φ : ℂ ≃ₜ ℂ` be a homeomorphism with the decay `‖Φ z - z‖ ≤ Cd / ‖z‖` for `‖z‖ ≥ Rd`
(`Cd ≥ 0`, `Rd ≥ 1`), which is the locally uniform limit of `C¹` homeomorphisms `Fn` whose
dilatations are bounded by `K < 1` pointwise.  Then there is a constant `C > 0`, depending only
on `K, Cd, Rd, ρ`, with `‖Φ z - Φ z₀‖² ≤ C / log (1/‖z - z₀‖)` for `‖z₀‖ ≤ ρ`,
`‖z - z₀‖ ≤ 1/4`. -/
theorem modulus_of_approx (K Cd Rd ρ : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hCd : 0 ≤ Cd) (hRd : 1 ≤ Rd) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Φ : ℂ ≃ₜ ℂ) (Fn : ℕ → ℂ ≃ₜ ℂ),
      (∀ n, ContDiff ℝ 1 (Fn n : ℂ → ℂ)) →
      (∀ n w, ‖dzbar (Fn n : ℂ → ℂ) w‖ ≤ K * ‖dz (Fn n : ℂ → ℂ) w‖) →
      TendstoLocallyUniformly (fun n => (Fn n : ℂ → ℂ)) (Φ : ℂ → ℂ) Filter.atTop →
      (∀ w : ℂ, Rd ≤ ‖w‖ → ‖(Φ : ℂ → ℂ) w - w‖ ≤ Cd / ‖w‖) →
      ∀ z₀ z : ℂ, ‖z₀‖ ≤ ρ → ‖z - z₀‖ ≤ 1 / 4 →
        ‖(Φ : ℂ → ℂ) z - (Φ : ℂ → ℂ) z₀‖ ^ 2 ≤ C / Real.log (1 / ‖z - z₀‖) := by
  obtain ⟨c, hc, hCL⟩ := courantLebesgue_uniform K hK0 hK1
  set Mφ : ℝ := max Rd (ρ + 1) + Cd with hMφdef
  have hMφ0 : 0 ≤ Mφ := by
    have h1 : (0 : ℝ) ≤ max Rd (ρ + 1) := le_trans (by linarith : (0 : ℝ) ≤ Rd) (le_max_left _ _)
    rw [hMφdef]; linarith
  refine ⟨c * (Real.pi * (Mφ + 1) ^ 2 + 1), by positivity, ?_⟩
  intro Φ Fn hF hdil hconv htail z₀ z hz₀ hz
  rcases eq_or_ne z z₀ with h | h
  · subst h; simp
  have hdec : ∀ w : ℂ, Rd ≤ ‖w‖ → ‖(Φ : ℂ → ℂ) w - w‖ ≤ Cd / ‖w‖ := htail
  have hφbd : ∀ w : ℂ, ‖w‖ ≤ ρ + 1 → ‖(Φ : ℂ → ℂ) w‖ ≤ Mφ := by
    intro w hw
    have h1 := norm_image_le_of_decay hRd hCd hdec w
    have h2 : max Rd ‖w‖ ≤ max Rd (ρ + 1) := max_le_max le_rfl hw
    rw [hMφdef]
    linarith
  have hunif : TendstoUniformlyOn (fun n => (Fn n : ℂ → ℂ)) (Φ : ℂ → ℂ) Filter.atTop
      (Metric.closedBall z₀ 1) :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) _ (isCompact_closedBall z₀ 1)
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ∀ w ∈ Metric.closedBall z₀ 1,
      dist ((Φ : ℂ → ℂ) w) ((Fn n : ℂ → ℂ) w) < 1 := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hunif) 1 one_pos)
    exact ⟨N, fun n hn => hN n hn⟩
  have harea : ∀ n ≥ N, ((volume : Measure ℂ) ((Fn n : ℂ → ℂ) '' Metric.ball z₀ 1)).toReal
      ≤ Real.pi * (Mφ + 1) ^ 2 := by
    intro n hn
    have hsub : (Fn n : ℂ → ℂ) '' Metric.ball z₀ 1 ⊆ Metric.closedBall (0 : ℂ) (Mφ + 1) := by
      rintro y ⟨w, hw, rfl⟩
      have hw1 : ‖w - z₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hwρ : ‖w‖ ≤ ρ + 1 := by
        calc ‖w‖ = ‖z₀ + (w - z₀)‖ := by ring_nf
          _ ≤ ‖z₀‖ + ‖w - z₀‖ := norm_add_le _ _
          _ ≤ ρ + 1 := by linarith
      have h1 : ‖(Φ : ℂ → ℂ) w‖ ≤ Mφ := hφbd w hwρ
      have h2 : dist ((Φ : ℂ → ℂ) w) ((Fn n : ℂ → ℂ) w) < 1 :=
        hN n hn w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw1.le))
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖(Fn n : ℂ → ℂ) w‖
          ≤ ‖(Fn n : ℂ → ℂ) w - (Φ : ℂ → ℂ) w‖ + ‖(Φ : ℂ → ℂ) w‖ := by
            have h3 := norm_add_le ((Fn n : ℂ → ℂ) w - (Φ : ℂ → ℂ) w) ((Φ : ℂ → ℂ) w)
            simpa using h3
        _ ≤ 1 + Mφ := by
            have h4 : ‖(Fn n : ℂ → ℂ) w - (Φ : ℂ → ℂ) w‖ < 1 := by
              rw [dist_eq_norm, norm_sub_rev] at h2; exact h2
            linarith
        _ = Mφ + 1 := by ring
    calc ((volume : Measure ℂ) ((Fn n : ℂ → ℂ) '' Metric.ball z₀ 1)).toReal
        ≤ ((volume : Measure ℂ) (Metric.closedBall (0 : ℂ) (Mφ + 1))).toReal :=
          ENNReal.toReal_mono ((isCompact_closedBall (0 : ℂ) (Mφ + 1)).measure_lt_top.ne)
            (measure_mono hsub)
      _ = Real.pi * (Mφ + 1) ^ 2 := by
          rw [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
            ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal, NNReal.coe_real_pi]
          ring
  have hδpos : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  have hlogpos : 0 < Real.log (1 / ‖z - z₀‖) := by
    apply Real.log_pos
    rw [one_lt_div hδpos]
    linarith
  have hCLn : ∀ᶠ n in Filter.atTop,
      ‖(Fn n : ℂ → ℂ) z - (Fn n : ℂ → ℂ) z₀‖ ^ 2
        ≤ c * (Real.pi * (Mφ + 1) ^ 2) / Real.log (1 / ‖z - z₀‖) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    refine (hCL (hF n) (Fn n).injective (hdil n) z₀ z hz).trans ?_
    gcongr
    exact harea n hn
  have htend : Tendsto (fun n => ‖(Fn n : ℂ → ℂ) z - (Fn n : ℂ → ℂ) z₀‖ ^ 2) Filter.atTop
      (𝓝 (‖(Φ : ℂ → ℂ) z - (Φ : ℂ → ℂ) z₀‖ ^ 2)) := by
    have h1 : Tendsto (fun n => (Fn n : ℂ → ℂ) z) Filter.atTop (𝓝 ((Φ : ℂ → ℂ) z)) :=
      tendsto_of_tendstoLocallyUniformly' hconv z
    have h2 : Tendsto (fun n => (Fn n : ℂ → ℂ) z₀) Filter.atTop (𝓝 ((Φ : ℂ → ℂ) z₀)) :=
      tendsto_of_tendstoLocallyUniformly' hconv z₀
    exact (h1.sub h2).norm.pow 2
  have hmain : ‖(Φ : ℂ → ℂ) z - (Φ : ℂ → ℂ) z₀‖ ^ 2
      ≤ c * (Real.pi * (Mφ + 1) ^ 2) / Real.log (1 / ‖z - z₀‖) :=
    le_of_tendsto htend hCLn
  refine hmain.trans ?_
  rw [div_le_div_iff_of_pos_right hlogpos]
  nlinarith [hMφ0, Real.pi_pos, sq_nonneg (Mφ + 1), hc.le]


end Work.MRMT.Found

namespace Work.Found

/-- **The requested lemma.**  A uniform record modulus for the fixed family `μs` of admissible
coefficients with records `d j`, with the extra hypothesis `hkn` that the approximating
coefficients `(d j).μn n` are bounded by the caller's `k`. -/
theorem record_modulus_of_bound {μs : ℕ → ℂ → ℂ} (hμ : ∀ j, Work.MRMT.Found.Admissible (μs j))
    (d : ∀ j, Work.MRMT.Found.PrincipalData (μs j)) {R k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hR : 0 ≤ R)
    (hsupp : ∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 R)
    (hb : ∀ j, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μs j z‖ ≤ k)
    (hkn : ∀ j n z, ‖(d j).μn n z‖ ≤ k)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (z₀ z : ℂ), ‖z₀‖ ≤ ρ → ‖z - z₀‖ ≤ 1 / 4 →
      ‖(((d j).φ : ℂ → ℂ) z) - (((d j).φ : ℂ → ℂ) z₀)‖ ^ 2
        ≤ C / Real.log (1 / ‖z - z₀‖) := by
  -- A *uniform* tail bound `‖φⱼ w − w‖ ≤ Cd/‖w‖` for `‖w‖ ≥ Rd`, from the uniform energy bound.
  obtain ⟨Cd, Rd, hCd, hRd, htail⟩ :=
    Work.MRMT.Found.exists_uniform_tail_clean k k R hk1 hk0 hk1
  -- Courant–Lebesgue applied to the `C¹` approximants, with the tail of the limit, uniformly.
  obtain ⟨C, hC, hmod⟩ :=
    Work.MRMT.Found.modulus_of_approx k Cd Rd ρ hk0 hk1 hCd hRd hρ
  refine ⟨C, hC, ?_⟩
  intro j z₀ z hz₀ hz
  obtain ⟨D, hDloc, _hDdz, hDdzbar, hDbnd⟩ :=
    Work.MRMT.Found.record_weakDeriv_energy (hμ j) (d j) hk1 (hsupp j) (hb j)
  have htailj : ∀ w : ℂ, Rd ≤ ‖w‖ → ‖(((d j).φ : ℂ → ℂ) w) - w‖ ≤ Cd / ‖w‖ :=
    htail ((d j).φ : ℂ → ℂ) (μs j) D ((d j).φ).continuous
      ⟨(d j).C, (d j).R, (d j).decay⟩ (hsupp j) (hμ j).meas (hb j) hDloc hDdzbar hDbnd
  have hdil : ∀ n w, ‖Work.MRMT.dzbar ((d j).Fn n : ℂ → ℂ) w‖
      ≤ k * ‖Work.MRMT.dz ((d j).Fn n : ℂ → ℂ) w‖ := by
    intro n w
    rw [(d j).beltrami_Fn n w, norm_mul]
    exact mul_le_mul_of_nonneg_right (hkn j n w) (norm_nonneg _)
  exact hmod ((d j).φ) (fun n => (d j).Fn n) (fun n => (d j).contDiff_Fn n) hdil
    (d j).tendsto_Fn htailj z₀ z hz₀ hz

end Work.Found
