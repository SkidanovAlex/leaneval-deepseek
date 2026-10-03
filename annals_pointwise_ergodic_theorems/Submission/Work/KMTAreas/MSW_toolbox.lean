import Mathlib
import Submission.Work.KMTAreas.MSW_iwConv_integral
import Submission.Work.KMTAreas.MSW_fourier_interp
import Submission.Work.KMTAreas.MSW_symbol_sum
import Submission.Work.KMTAreas.MSW_periodize_integral
import Submission.Port.Aesm

/-!
# `MSW` single-torsion sampling: the analytic toolbox

Toolbox for the proof of `Work.KMTAreas.MSW_single_torsion`: manipulations of trigonometric
polynomials on the circle, the Plancherel and Hölder steps, the `χ`-step (where the cutoff is `1`
on the support of the symbol) and the resulting single-term bound `msw_term_bound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators ENNReal NNReal FourierTransform
open MeasureTheory

namespace Work.KMTAreas

abbrev mswCircle : Type := Work.Analysis.IonescuWainger.Circle

theorem mswTrigC_apply (s : Finset ℤ) (u : ℤ → ℂ) (t : mswCircle) :
    mswTrigC s u t = ∑ m ∈ s, u m * (fourier m : mswCircle → ℂ) t := by
  simp [mswTrigC, smul_eq_mul]

theorem msw_fourier_norm (m : ℤ) (t : mswCircle) :
    ‖(fourier m : mswCircle → ℂ) t‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

theorem mswTrigC_norm_le (s : Finset ℤ) (u : ℤ → ℂ) (t : mswCircle) :
    ‖mswTrigC s u t‖ ≤ ∑ m ∈ s, ‖u m‖ := by
  rw [mswTrigC_apply]
  calc ‖∑ m ∈ s, u m * (fourier m : mswCircle → ℂ) t‖
      ≤ ∑ m ∈ s, ‖u m * (fourier m : mswCircle → ℂ) t‖ := norm_sum_le _ _
    _ = ∑ m ∈ s, ‖u m‖ := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [norm_mul, msw_fourier_norm, mul_one]

theorem mswTrigC_continuous (s : Finset ℤ) (u : ℤ → ℂ) : Continuous (mswTrigC s u) := by
  rw [funext (mswTrigC_apply s u)]
  exact continuous_finsetSum _ fun m _ => continuous_const.mul (ContinuousMap.continuous (fourier m))

theorem mswTrigC_conj_apply (s : Finset ℤ) (u : ℤ → ℂ) (t : mswCircle) :
    starRingEnd ℂ (mswTrigC s u t)
      = ∑ m ∈ s, starRingEnd ℂ (u m) * (fourier (-m) : mswCircle → ℂ) t := by
  rw [mswTrigC_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, ← fourier_neg]

theorem mswTrigC_coe (s : Finset ℤ) (u : ℤ → ℂ) (x : ℝ) :
    mswTrigC s u ((x : ℝ) : mswCircle) = mswTrig s u x := by
  rw [mswTrigC_apply, mswTrig]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [fourier_coe_apply, show ((1 : ℝ) : ℂ) = 1 by norm_num, div_one]

theorem mswTrig_mod (s : Finset ℤ) (u : ℤ → ℂ) (c x : ℝ) :
    mswTrig s (mswMod c u) x = mswTrig s u (x + c) := by
  rw [mswTrig, mswTrig]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mswMod]
  have h : Complex.exp (2 * ↑Real.pi * Complex.I * (m : ℂ) * (c : ℂ)) *
      Complex.exp (2 * ↑Real.pi * Complex.I * (m : ℂ) * (x : ℂ))
      = Complex.exp (2 * ↑Real.pi * Complex.I * (m : ℂ) * ((x + c : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [mul_assoc, h]

theorem msw_trigC_add (s : Finset ℤ) (u : ℤ → ℂ) (c x : ℝ) :
    mswTrigC s u (((x : ℝ) : mswCircle) + ((c : ℝ) : mswCircle)) = mswTrig s (mswMod c u) x := by
  rw [← AddCircle.coe_add, mswTrigC_coe, mswTrig_mod]

/-- Integrability of `Ψ` times a trigonometric polynomial times a character. -/
theorem msw_integrable_aux {Ψ : mswCircle → ℂ} (hΨ : Integrable Ψ Work.Analysis.IonescuWainger.circleMeasure)
    (s : Finset ℤ) (u : ℤ → ℂ) (n : ℤ) :
    Integrable (fun τ => Ψ τ * mswTrigC s u τ * (fourier (-n) : mswCircle → ℂ) τ)
      Work.Analysis.IonescuWainger.circleMeasure := by
  set C : ℝ := ∑ m ∈ s, ‖u m‖ with hC
  have hcont : Continuous (fun τ : mswCircle => mswTrigC s u τ * (fourier (-n) : mswCircle → ℂ) τ) :=
    (mswTrigC_continuous s u).mul (ContinuousMap.continuous (fourier (-n)))
  have hbdd : ∀ᵐ τ ∂Work.Analysis.IonescuWainger.circleMeasure,
      ‖mswTrigC s u τ * (fourier (-n) : mswCircle → ℂ) τ‖ ≤ C := by
    refine Filter.Eventually.of_forall fun τ => ?_
    rw [norm_mul, msw_fourier_norm, mul_one]
    exact mswTrigC_norm_le s u τ
  have h := hΨ.bdd_mul (hcont.aestronglyMeasurable) hbdd
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- The pairing identity. -/
theorem msw_pairing_eq {Ψ : mswCircle → ℂ}
    (hΨ : Integrable Ψ Work.Analysis.IonescuWainger.circleMeasure)
    {s t : Finset ℤ} {f g : ℤ → ℂ} (hs : ∀ m, m ∉ s → f m = 0) (ht : ∀ m, m ∉ t → g m = 0) :
    tsum (fun n : ℤ => (∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel Ψ j • f (n - j))
        * starRingEnd ℂ (g n))
      = ∫ τ, Ψ τ * (mswTrigC s f τ * starRingEnd ℂ (mswTrigC t g τ))
          ∂Work.Analysis.IonescuWainger.circleMeasure := by
  classical
  have hcollapse : tsum (fun n : ℤ => (∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel Ψ j •
        f (n - j)) * starRingEnd ℂ (g n))
      = ∑ n ∈ t, (∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel Ψ j • f (n - j))
          * starRingEnd ℂ (g n) :=
    tsum_eq_sum fun n hn => by rw [ht n hn, map_zero, mul_zero]
  rw [hcollapse]
  have hterm : ∀ n : ℤ, (∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel Ψ j • f (n - j))
      = ∫ τ, Ψ τ * mswTrigC s f τ * (fourier (-n) : mswCircle → ℂ) τ
          ∂Work.Analysis.IonescuWainger.circleMeasure :=
    fun n => MSW_iwConv_integral hΨ hs n
  rw [Finset.sum_congr rfl (fun n _ => by rw [hterm n])]
  rw [Finset.sum_congr rfl (fun n _ => (integral_mul_const _ _).symm)]
  rw [← integral_finsetSum]
  · congr with τ
    rw [mswTrigC_conj_apply, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  · intro n hn
    exact (msw_integrable_aux hΨ s f n).mul_const (starRingEnd ℂ (g n))

/-! ### The Plancherel/Hölder toolbox -/

/-- `𝓕⁻(φ · 𝓕 u)`, i.e. the continuous multiplier `T_φ` applied to `u`, bundled as a Schwartz
function. -/
noncomputable def mswW (φ u : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
    (SchwartzMap.hasTemperateGrowth (𝓕 u)) φ)

theorem mswW_coe (φ u : SchwartzMap ℝ ℂ) :
    (mswW φ u : ℝ → ℂ) = Work.Analysis.IWMultiplier.contMulOp (φ : ℝ → ℂ) (u : ℝ → ℂ) := by
  rw [mswW, SchwartzMap.fourierInv_coe]
  rfl

theorem mswW_fourier_apply (φ u : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (mswW φ u) ξ = φ ξ * 𝓕 u ξ := by
  rw [mswW, FourierInvPair.fourier_fourierInv_eq, SchwartzMap.bilinLeftCLM_apply]
  rfl

/-- **Plancherel for the multiplier.**  For Schwartz `w`, `v`:
`∫ 𝓕w · conj (𝓕v) = ∫ w · conj v`. -/
theorem msw_plancherel (w v : SchwartzMap ℝ ℂ) :
    (∫ ξ : ℝ, 𝓕 w ξ * starRingEnd ℂ (𝓕 v ξ)) = ∫ x : ℝ, w x * starRingEnd ℂ (v x) := by
  have h := SchwartzMap.integral_inner_fourier_fourier v w
  simpa [RCLike.inner_apply] using h

/-- **Hölder's inequality** for the pairing `∫ w · conj v`. -/
theorem msw_holder {p r : ENNReal} (hpr : p.HolderConjugate r) {w v : ℝ → ℂ}
    (hw : AEMeasurable w volume) (hv : AEMeasurable v volume) :
    enorm (∫ x : ℝ, w x * starRingEnd ℂ (v x))
      ≤ eLpNorm w p volume * eLpNorm (fun x : ℝ => starRingEnd ℂ (v x)) r volume := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (f := w)
    (g := fun x : ℝ => starRingEnd ℂ (v x)) (fun a b : ℂ => a * b) 1 (by first | fun_prop | exact continuous_mul | exact continuous_inner | (simp only [Function.uncurry_def]; fun_prop)) hw.aestronglyMeasurable hv.aestronglyMeasurable.star (by filter_upwards with x; simp [nnnorm_mul]) (hpqr := hpr)
  calc enorm (∫ x : ℝ, w x * starRingEnd ℂ (v x))
      ≤ ∫⁻ x : ℝ, ‖w x * starRingEnd ℂ (v x)‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x : ℝ => w x * starRingEnd ℂ (v x)) 1 volume :=
        (eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)).symm
    _ ≤ 1 * eLpNorm w p volume * eLpNorm (fun x : ℝ => starRingEnd ℂ (v x)) r volume := h
    _ = _ := by rw [one_mul]

theorem msw_eLpNorm_conj {r : ENNReal} {v : ℝ → ℂ} (hv : AEMeasurable v volume) :
    eLpNorm (fun x : ℝ => starRingEnd ℂ (v x)) r volume = eLpNorm v r volume := by
  refine le_antisymm ?_ ?_
  · refine eLpNorm_mono (hf := by pw_aesm) (fun x => ?_)
    simp
  · refine eLpNorm_mono (hf := by pw_aesm) (fun x => ?_)
    simp

theorem mswInterp_apply (s : Finset ℤ) (u : ℤ → ℂ) (y : ℝ) :
    (mswInterp s u : ℝ → ℂ) y = ∑ m ∈ s, u m * mswK (y + m) := by
  rw [mswInterp, sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_apply, smul_eq_mul, SchwartzMap.compSubConstCLM_apply]
  ring_nf

/-- The modulation preserves the `ℓ^p` norm. -/
theorem mswMod_eLpNorm (c : ℝ) (u : ℤ → ℂ) (q : ENNReal) :
    eLpNorm (mswMod c u) q Measure.count = eLpNorm u q Measure.count := by
  refine le_antisymm ?_ ?_
  · refine eLpNorm_mono (hf := by pw_aesm) (fun m => ?_)
    rw [mswMod, norm_mul, Complex.norm_exp]
    simp
  · refine eLpNorm_mono (hf := by pw_aesm) (fun m => ?_)
    rw [mswMod, norm_mul, Complex.norm_exp]
    simp

theorem mswW_plancherel_cont (φ u v : SchwartzMap ℝ ℂ) :
    (∫ ξ : ℝ, (φ ξ * 𝓕 u ξ) * starRingEnd ℂ (𝓕 v ξ))
      = ∫ x : ℝ, Work.Analysis.IWMultiplier.contMulOp (φ : ℝ → ℂ) (u : ℝ → ℂ) x
          * starRingEnd ℂ (v x) := by
  have h := msw_plancherel (mswW φ u) v
  simp only [mswW_fourier_apply] at h
  rw [← mswW_coe φ u]
  exact h

/-- The support condition gives `x ∈ realArc k ⟹ |x| ≤ 2` whenever `2^k · 2Q ≤ 1`. -/
theorem msw_realArc_abs_le {k : ℤ} {Q : ℕ} (hQ : 1 ≤ Q)
    (hk : (2 : ℝ) ^ k * (2 * (Q : ℝ)) ≤ 1) {x : ℝ}
    (hx : x ∈ Work.Analysis.IonescuWainger.realArc k) : |x| ≤ 2 := by
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hpos : (0 : ℝ) < 2 * (Q : ℝ) := by linarith
  have h2k : (2 : ℝ) ^ k ≤ 1 / (2 * (Q : ℝ)) := by
    rw [le_div_iff₀ hpos]; linarith
  have hhalf : 1 / (2 * (Q : ℝ)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hx2 : |x| ≤ (2 : ℝ) ^ k := by
    rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at hx
    exact abs_le.mpr hx
  linarith

/-- The `χ`-step: on the support of `φ`, the trigonometric polynomial is the Fourier transform of
the interpolation. -/
theorem msw_chi_step {k : ℤ} {Q : ℕ} (hQ : 1 ≤ Q) (hk : (2 : ℝ) ^ k * (2 * (Q : ℝ)) ≤ 1)
    {φ : SchwartzMap ℝ ℂ} (hφ : ∀ x, φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k)
    (s t : Finset ℤ) (u w : ℤ → ℂ) (x : ℝ) :
    φ x * (mswTrig s u x * starRingEnd ℂ (mswTrig t w x))
      = φ x * (𝓕 (mswInterp s u) x * starRingEnd ℂ (𝓕 (mswInterp t w) x)) := by
  by_cases hx : φ x = 0
  · rw [hx, zero_mul, zero_mul]
  · have hx2 : |x| ≤ 2 := msw_realArc_abs_le hQ hk (hφ x hx)
    rw [MSW_fourier_interp s u, MSW_fourier_interp t w]
    simp only []
    rw [mswChi_eq_one hx2]
    simp

/-- **The single-torsion term bound.**  Each of the `Q` terms of the symbol sum is bounded by
`M · CK² · ‖f‖_{ℓ^p} · ‖g‖_{ℓ^r}`, where `M` is the continuous-multiplier bound and `CK` the
Shannon-interpolation constant. -/
theorem msw_term_bound {Q : ℕ} (hQ : 1 ≤ Q) {k : ℤ}
    (hk : (2 : ℝ) ^ k * (2 * (Q : ℝ)) ≤ 1)
    {φ : SchwartzMap ℝ ℂ}
    (hφ : ∀ x, φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k)
    {p r : ENNReal} (hpr : p.HolderConjugate r) (hp1 : 1 ≤ p) (hr1 : 1 ≤ r)
    {M : NNReal} (hM : Work.Analysis.IWMultiplier.IsLqMultiplierBound p (φ : ℝ → ℂ) M)
    {CK : NNReal} (hCK : ∀ (q : ENNReal), 1 ≤ q → ∀ (s : Finset ℤ) (u : ℤ → ℂ),
      (∀ m, m ∉ s → u m = 0) →
      eLpNorm (fun y : ℝ => ∑ m ∈ s, u m * mswK (y + m)) q volume
        ≤ ENNReal.ofReal (CK : ℝ) * eLpNorm u q Measure.count)
    {s t : Finset ℤ} {f g : ℤ → ℂ} (hs : ∀ m, m ∉ s → f m = 0)
    (ht : ∀ m, m ∉ t → g m = 0) (a : ℕ) :
    enorm (∫ τ : mswCircle, (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ))
        (τ - (((a : ℝ) / (Q : ℝ) : ℝ) : mswCircle))
        * (mswTrigC s f τ * starRingEnd ℂ (mswTrigC t g τ))
        ∂Work.Analysis.IonescuWainger.circleMeasure)
      ≤ ENNReal.ofReal ((M : ℝ) * (CK : ℝ) * (CK : ℝ))
          * eLpNorm f p Measure.count * eLpNorm g r Measure.count := by
  set c : ℝ := (a : ℝ) / (Q : ℝ) with hc
  have hX : Continuous (fun τ : mswCircle => mswTrigC s f τ * starRingEnd ℂ (mswTrigC t g τ)) :=
    (mswTrigC_continuous s f).mul (Complex.continuous_conj.comp (mswTrigC_continuous t g))
  rw [MSW_periodize_integral φ (fun τ => mswTrigC s f τ * starRingEnd ℂ (mswTrigC t g τ)) hX c]
  simp only [msw_trigC_add]
  set u : SchwartzMap ℝ ℂ := mswInterp s (mswMod c f) with hu
  set v : SchwartzMap ℝ ℂ := mswInterp t (mswMod c g) with hv
  simp only [msw_chi_step hQ hk hφ s t (mswMod c f) (mswMod c g)]
  simp only [← mul_assoc]
  rw [mswW_plancherel_cont φ u v]
  have hw : AEMeasurable (Work.Analysis.IWMultiplier.contMulOp (φ : ℝ → ℂ) (u : ℝ → ℂ)) volume := by
    rw [← mswW_coe φ u]
    exact (mswW φ u).continuous.measurable.aemeasurable
  have hvu : AEMeasurable (v : ℝ → ℂ) volume := v.continuous.measurable.aemeasurable
  have hCKf : eLpNorm (u : ℝ → ℂ) p volume
      ≤ ENNReal.ofReal (CK : ℝ) * eLpNorm (mswMod c f) p Measure.count := by
    rw [show (u : ℝ → ℂ) = fun y : ℝ => ∑ m ∈ s, mswMod c f m * mswK (y + m) from
      funext fun y => mswInterp_apply s (mswMod c f) y]
    exact hCK p hp1 s (mswMod c f) (fun m hm => by rw [mswMod, hs m hm, zero_mul])
  have hCKg : eLpNorm (v : ℝ → ℂ) r volume
      ≤ ENNReal.ofReal (CK : ℝ) * eLpNorm (mswMod c g) r Measure.count := by
    rw [show (v : ℝ → ℂ) = fun y : ℝ => ∑ m ∈ t, mswMod c g m * mswK (y + m) from
      funext fun y => mswInterp_apply t (mswMod c g) y]
    exact hCK r hr1 t (mswMod c g) (fun m hm => by rw [mswMod, ht m hm, zero_mul])
  calc enorm (∫ x : ℝ, Work.Analysis.IWMultiplier.contMulOp (φ : ℝ → ℂ) (u : ℝ → ℂ) x
        * starRingEnd ℂ ((v : ℝ → ℂ) x))
      ≤ eLpNorm (Work.Analysis.IWMultiplier.contMulOp (φ : ℝ → ℂ) (u : ℝ → ℂ)) p volume
          * eLpNorm (fun x : ℝ => starRingEnd ℂ ((v : ℝ → ℂ) x)) r volume :=
        msw_holder hpr hw hvu
    _ = eLpNorm (Work.Analysis.IWMultiplier.contMulOp (φ : ℝ → ℂ) (u : ℝ → ℂ)) p volume
          * eLpNorm (v : ℝ → ℂ) r volume := by rw [msw_eLpNorm_conj hvu]
    _ ≤ (ENNReal.ofReal (M : ℝ) * eLpNorm (u : ℝ → ℂ) p volume)
          * (ENNReal.ofReal (CK : ℝ) * eLpNorm (mswMod c g) r Measure.count) := by
        gcongr
        exact hM u
    _ ≤ (ENNReal.ofReal (M : ℝ)
            * (ENNReal.ofReal (CK : ℝ) * eLpNorm (mswMod c f) p Measure.count))
          * (ENNReal.ofReal (CK : ℝ) * eLpNorm (mswMod c g) r Measure.count) := by
        gcongr
    _ = ENNReal.ofReal ((M : ℝ) * (CK : ℝ) * (CK : ℝ))
          * eLpNorm f p Measure.count * eLpNorm g r Measure.count := by
        rw [mswMod_eLpNorm c f p, mswMod_eLpNorm c g r,
          ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ M * CK),
          ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ M)]
        ac_rfl

end Work.KMTAreas
