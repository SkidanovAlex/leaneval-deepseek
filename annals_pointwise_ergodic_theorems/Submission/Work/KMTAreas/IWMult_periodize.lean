import Mathlib
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp
import Submission.Work.Thm52.integrable_circleLift
import Submission.Work.KMTAreas.circleLift_periodize_eq
import Submission.Work.KMTAreas.isLqMultiplierBound_comp_neg

/-!
# `IWMult` for the periodisation of a narrow Schwartz symbol

The target of this file is

```
Work.BourgainPlan.Maximal.IWMult r (periodize φ) M
```

from the `ℝ`-multiplier-norm hypothesis `IsLqMultiplierBound (2r) φ M` on the *narrow* Schwartz
symbol `φ` (supported in `realArc k`, `2 ^ k ≤ 1/2`), which is the input of the Ionescu–Wainger
step of the paper (§5, `iw-prop`).

The mathematical content is that for a symbol supported in `ℝ_{≤k}` with `2^k ≤ 1/2` the
periodisation does not overlap itself, so `circleLift (periodize φ) =ᵐ φ ∘ (-·)`
(`Work.KMTAreas.circleLift_periodize_eq`), and a Fourier multiplier has the same `L^q` operator
norm as its reflection (`Work.KMTAreas.isLqMultiplierBound_comp_neg`).  The remaining work, carried
out here, is measure-theoretic: `IsLqMultiplierBound` is tested on Schwartz functions, while
`IWMult` is tested on *integrable* functions, so the a priori inequality has to be transferred from
the Schwartz class to all of `L^1(ℝ,ℂ)`.

## Main results

* `Work.KMTAreas.fourierInv_congr_ae`, `…fourier_congr_ae` — `𝓕⁻`, `𝓕` only see the a.e. class;
* `Work.KMTAreas.ae_eq_comp_neg` — negation preserves a.e. equality;
* `Work.KMTAreas.fourierInv_eq_fourier_of_ae_eq` — `𝓕⁻ Φ = 𝓕 φ` when `Φ =ᵐ φ ∘ (-·)`;
* `Work.KMTAreas.contMulOp_eq_conv_kernel`, `…contMulOp_congr_ae`;
* `Work.KMTAreas.lintegral_le_of_integrable_memLp` — the `L^1 ∩ L^q` case of the transfer;
* `Work.KMTAreas.lintegral_le_of_schwartz_conv_bound` — the full transfer for `C > 0`;
* `Work.KMTAreas.IWMult_periodize` — the target.

The two periodisation inputs are proved in companion modules:
`Work.KMTAreas.circleLift_periodize_eq` (the a.e. identity `circleLift (periodize φ) =ᵐ φ ∘ (-·)`,
i.e. the periodisation does not overlap itself) and `Work.KMTAreas.isLqMultiplierBound_comp_neg`
(the reflection invariance of the multiplier norm).
-/

open MeasureTheory
open scoped ENNReal FourierTransform BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas

/-! ## Elementary Fourier bookkeeping -/

/-- **`𝓕⁻` only sees the almost-everywhere class of its argument.** -/
lemma fourierInv_congr_ae {m m' : ℝ → ℂ} (h : m =ᵐ[volume] m') : 𝓕⁻ m = 𝓕⁻ m' := by
  funext x
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  refine integral_congr_ae ?_
  filter_upwards [h] with v hv
  rw [hv]

/-- **`𝓕` only sees the almost-everywhere class of its argument.** -/
lemma fourier_congr_ae {m m' : ℝ → ℂ} (h : m =ᵐ[volume] m') : 𝓕 m = 𝓕 m' := by
  funext x
  rw [Real.fourier_eq', Real.fourier_eq']
  refine integral_congr_ae ?_
  filter_upwards [h] with v hv
  rw [hv]

/-- **The inverse Fourier transform of the zero function is zero.** -/
lemma fourierInv_zero_fun : 𝓕⁻ (0 : ℝ → ℂ) = 0 := by
  funext x
  rw [Real.fourierInv_eq']
  simp

/-- **Negation preserves almost-everywhere equality.** -/
lemma ae_eq_comp_neg {u v : ℝ → ℂ} (h : u =ᵐ[volume] v) :
    (fun x : ℝ => u (-x)) =ᵐ[volume] (fun x => v (-x)) := by
  have hmap : (volume : Measure ℝ).map (fun x : ℝ => -x) = volume :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).map_eq
  have h' : u =ᵐ[(volume : Measure ℝ).map (fun x : ℝ => -x)] v := by rw [hmap]; exact h
  have h2 := MeasureTheory.ae_eq_comp (μ := (volume : Measure ℝ)) (f := fun x : ℝ => -x)
    (g := u) (g' := v) measurable_neg.aemeasurable h'
  simpa [Function.comp_def] using h2

/-- **`𝓕⁻ Φ = 𝓕 φ` when `Φ` agrees a.e. with the reflection of `φ`.** -/
lemma fourierInv_eq_fourier_of_ae_eq {Φ φ : ℝ → ℂ}
    (h : Φ =ᵐ[volume] (fun x => φ (-x))) : 𝓕⁻ Φ = 𝓕 φ := by
  have h2 : (fun x : ℝ => Φ (-x)) =ᵐ[volume] (fun x => φ x) := by
    simpa using ae_eq_comp_neg h
  rw [Real.fourierInv_eq_fourier_comp_neg Φ]
  exact fourier_congr_ae h2

/-- **`contMulOp` only depends on the a.e. class of the symbol.** -/
lemma contMulOp_congr_ae {Φ ψ : ℝ → ℂ} (h : Φ =ᵐ[volume] ψ) (f : ℝ → ℂ) :
    Work.Analysis.IWMultiplier.contMulOp Φ f = Work.Analysis.IWMultiplier.contMulOp ψ f := by
  refine fourierInv_congr_ae ?_
  filter_upwards [h] with ξ hξ
  show Φ ξ * 𝓕 f ξ = ψ ξ * 𝓕 f ξ
  rw [hξ]

/-- **The continuous multiplier is the convolution with the inverse Fourier transform of its
symbol.** -/
lemma contMulOp_eq_conv_kernel {Φ : ℝ → ℂ} (hΦ : Integrable Φ) (G : SchwartzMap ℝ ℂ) :
    Work.Analysis.IWMultiplier.contMulOp Φ (G : ℝ → ℂ)
      = fun x => ∫ y, 𝓕⁻ Φ (x - y) * (G : ℝ → ℂ) y := by
  have h := Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution
    (m := Φ) (f := (G : ℝ → ℂ)) hΦ G.integrable
  funext x
  exact (h x).trans (integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _))

/-! ## The transfer from a Schwartz-tested multiplier bound to integrable inputs -/

/-- **The `L^1 ∩ L^q` case of the transfer.** -/
lemma lintegral_le_of_integrable_memLp {q : ℝ} (hq : 1 < q) {Φ κ : ℝ → ℂ}
    (hΦint : Integrable Φ) (hκeq : ∀ x, κ x = 𝓕⁻ Φ x) (hκ1 : MemLp κ 1 volume) {C : ℝ}
    (hC : 0 ≤ C)
    (hS : ∀ G : SchwartzMap ℝ ℂ, eLpNorm (fun x => ∫ y, κ (x - y) * (G : ℝ → ℂ) y)
        (ENNReal.ofReal q) volume
        ≤ ENNReal.ofReal C * eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal q) volume)
    {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal q) volume) (hfi : Integrable f) :
    ∫⁻ x, ‖𝓕⁻ (fun ξ => Φ ξ * 𝓕 f ξ) x‖ₑ ^ q
      ≤ ENNReal.ofReal (C ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have h1 : eLpNorm (fun x => ∫ y, κ (x - y) * f y) (ENNReal.ofReal q) volume
      ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal q) volume :=
    Work.BourgainPlan.Maximal.eLpNorm_convolution_le_of_schwartz hq hκ1 hC hS hf
  have hpt : ∀ x, 𝓕⁻ (fun ξ => Φ ξ * 𝓕 f ξ) x = ∫ y, κ (x - y) * f y := by
    intro x
    rw [Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution hΦint hfi x]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
      show f y * 𝓕⁻ Φ (x - y) = κ (x - y) * f y
      rw [hκeq (x - y), mul_comm])
  calc ∫⁻ x, ‖𝓕⁻ (fun ξ => Φ ξ * 𝓕 f ξ) x‖ₑ ^ q
      = ∫⁻ x, ‖∫ y, κ (x - y) * f y‖ₑ ^ q := by
        refine lintegral_congr fun x => ?_
        rw [hpt x]
    _ = (eLpNorm (fun x => ∫ y, κ (x - y) * f y) (ENNReal.ofReal q) volume) ^ q :=
        (Work.BourgainPlan.IonescuWainger.eLpNorm_rpow_eq_lintegral hqpos _
          (MeasureTheory.memLp_iff.mpr (h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            hf.eLpNorm_lt_top))).aestronglyMeasurable).symm
    _ ≤ (ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal q) volume) ^ q :=
        ENNReal.rpow_le_rpow h1 hqpos.le
    _ = ENNReal.ofReal (C ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hqpos.le,
          ENNReal.ofReal_rpow_of_nonneg hC hqpos.le,
          Work.BourgainPlan.IonescuWainger.eLpNorm_rpow_eq_lintegral hqpos f hf.aestronglyMeasurable]

/-- **The full transfer for a positive constant.** -/
lemma lintegral_le_of_schwartz_conv_bound {q : ℝ} (hq : 1 < q) {Φ : ℝ → ℂ}
    (hΦint : Integrable Φ) (hκ1 : MemLp (𝓕⁻ Φ) 1 volume) {C : ℝ} (hC : 0 < C)
    (hS : ∀ G : SchwartzMap ℝ ℂ, eLpNorm (fun x => ∫ y, 𝓕⁻ Φ (x - y) * (G : ℝ → ℂ) y)
        (ENNReal.ofReal q) volume
        ≤ ENNReal.ofReal C * eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal q) volume)
    {g : ℝ → ℂ} (hg : Integrable g) :
    ∫⁻ x, ‖𝓕⁻ (fun ξ => Φ ξ * 𝓕 g ξ) x‖ₑ ^ q
      ≤ ENNReal.ofReal (C ^ q) * ∫⁻ x, ‖g x‖ₑ ^ q := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  by_cases hfin : ∫⁻ x : ℝ, ‖g x‖ₑ ^ q = ⊤
  · have hRHS : ENNReal.ofReal (C ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q = ⊤ := by
      rw [hfin, ENNReal.mul_top]
      exact ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hC q)
    rw [hRHS]
    exact le_top
  · have hmem : MemLp g (ENNReal.ofReal q) volume := by
      refine MeasureTheory.memLp_iff.mpr ?_
      rw [lt_top_iff_ne_top]
      intro htop
      have h := Work.BourgainPlan.IonescuWainger.eLpNorm_rpow_eq_lintegral hqpos g hg.aestronglyMeasurable
      rw [htop] at h
      have htopq : (⊤ : ℝ≥0∞) ^ q = ⊤ := by
        rw [ENNReal.rpow_eq_top_iff]
        exact Or.inr ⟨rfl, hqpos⟩
      rw [htopq] at h
      exact hfin h.symm
    exact lintegral_le_of_integrable_memLp hq hΦint (fun x => rfl) hκ1 hC.le hS hmem hg

/-! ## The target -/

/-- **`IWMult` for the periodisation of a narrow Schwartz symbol.**  From the `ℝ`-multiplier-norm
bound `M` for the narrow Schwartz symbol `φ` one gets the same bound for the periodisation
`periodize φ : ℝ/ℤ → ℂ`, lifted to `ℝ` by `circleLift`.

The two Fourier inputs are `Work.KMTAreas.circleLift_periodize_eq` (the periodisation does not
overlap itself, so `circleLift (periodize φ) =ᵐ φ ∘ (-·)`) and
`Work.KMTAreas.isLqMultiplierBound_comp_neg` (the multiplier norm is reflection invariant); the
transfer from the Schwartz class to all integrable inputs is
`Work.KMTAreas.lintegral_le_of_schwartz_conv_bound`. -/
theorem IWMult_periodize {r : ℕ} (hr : 2 ≤ r) {k : ℤ} (hk : (2 : ℝ) ^ k ≤ 1 / 2)
    {φ : SchwartzMap ℝ ℂ}
    (hφ : ∀ x, φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k) {M : NNReal}
    (hM : Work.Analysis.IWMultiplier.IsLqMultiplierBound ((2 * r : ℕ) : ENNReal) (φ : ℝ → ℂ) M) :
    Work.BourgainPlan.Maximal.IWMult r
      (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)) M := by
  have hD1 : (fun x : ℝ => Work.BourgainPlan.Thm52.circleLift
      (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)) x) =ᵐ[volume] (fun x => φ (-x)) :=
    Work.KMTAreas.circleLift_periodize_eq hk hφ
  have hD2 : Work.Analysis.IWMultiplier.IsLqMultiplierBound ((2 * r : ℕ) : ENNReal)
      (fun ξ : ℝ => φ (-ξ)) M :=
    Work.KMTAreas.isLqMultiplierBound_comp_neg hM
  intro g hg
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hqpos : 0 < 2 * (r : ℝ) := by linarith
  have hq1 : 1 < 2 * (r : ℝ) := by linarith
  have hpq : ((2 * r : ℕ) : ENNReal) = ENNReal.ofReal (2 * (r : ℝ)) := by
    rw [← ENNReal.ofReal_natCast (2 * r)]
    congr 1
    push_cast
    ring
  set Φ : ℝ → ℂ := Work.BourgainPlan.Thm52.circleLift
    (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)) with hΦdef
  have hΦae : Φ =ᵐ[volume] (fun x => φ (-x)) := hD1
  by_cases hM0 : M = 0
  · -- ## The degenerate case `M = 0`: the hypothesis forces `Φ` to vanish a.e.
    obtain ⟨G₀, hG₀⟩ := Commons.Analysis.Fourier.exists_schwartzMap_fourier_eq_one_Icc
    have hφarc : ∀ t : ℝ, φ t ≠ 0 → |t| ≤ 1 := by
      intro t ht
      have ht' := hφ t ht
      simp only [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at ht'
      have h2 : (2 : ℝ) ^ k ≤ 1 := le_trans hk (by norm_num)
      exact abs_le.mpr ⟨by linarith [ht'.1, h2], by linarith [ht'.2, h2]⟩
    have hFG : ∀ ξ : ℝ, φ ξ * 𝓕 (G₀ : ℝ → ℂ) ξ = φ ξ := by
      intro ξ
      by_cases hξ : φ ξ = 0
      · rw [hξ, zero_mul]
      · rw [hG₀ ξ (hφarc ξ hξ), mul_one]
    have hone : Work.Analysis.IWMultiplier.contMulOp (φ : ℝ → ℂ) (G₀ : ℝ → ℂ)
        = 𝓕⁻ (φ : ℝ → ℂ) := by
      rw [Work.Analysis.IWMultiplier.contMulOp]
      exact fourierInv_congr_ae (Filter.Eventually.of_forall hFG)
    have hz : eLpNorm (𝓕⁻ (φ : ℝ → ℂ)) (ENNReal.ofReal (2 * (r : ℝ))) volume = 0 := by
      have h1 := hM G₀
      rw [hpq, hM0] at h1
      simp only [NNReal.coe_zero, ENNReal.ofReal_zero, zero_mul] at h1
      rw [hone] at h1
      exact le_antisymm h1 zero_le
    set Ψ : SchwartzMap ℝ ℂ :=
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (ContinuousLinearEquiv.neg ℝ)) φ with hΨdef
    have hΨcoe : (Ψ : ℝ → ℂ) = fun x => φ (-x) := by
      rw [hΨdef, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      rfl
    have hcoefun : 𝓕 (fun x => φ (-x)) = ⇑(𝓕 Ψ : SchwartzMap ℝ ℂ) := by
      rw [← hΨcoe]
      exact (SchwartzMap.fourier_coe Ψ).symm
    have hΨsm : AEStronglyMeasurable (𝓕⁻ (φ : ℝ → ℂ)) volume := by
      rw [Real.fourierInv_eq_fourier_comp_neg, hcoefun]
      exact (𝓕 Ψ : SchwartzMap ℝ ℂ).continuous.aestronglyMeasurable
    have hae₀ : 𝓕⁻ (φ : ℝ → ℂ) =ᵐ[volume] 0 :=
      (eLpNorm_eq_zero_iff (ENNReal.ofReal_ne_zero_iff.mpr hqpos)).mp hz
    have h1 : 𝓕 (fun x => φ (-x)) =ᵐ[volume] 0 := by
      rw [← Real.fourierInv_eq_fourier_comp_neg (φ : ℝ → ℂ)]
      exact hae₀
    have hint1 : Integrable (fun x => φ (-x)) volume := by
      rw [← hΨcoe]; exact Ψ.integrable
    have hint2 : Integrable (𝓕 (fun x => φ (-x))) volume := by
      rw [hcoefun]
      exact (𝓕 Ψ : SchwartzMap ℝ ℂ).integrable
    have hcont : Continuous (fun x => φ (-x)) := by rw [← hΨcoe]; exact Ψ.continuous
    have hinv : (fun x => φ (-x)) = 𝓕⁻ (𝓕 (fun x => φ (-x))) :=
      (Continuous.fourierInv_fourier_eq hcont hint1 hint2).symm
    have hfunzero : (fun x => φ (-x)) =ᵐ[volume] 0 := by
      rw [hinv, fourierInv_congr_ae h1, fourierInv_zero_fun]
    have hΦae0 : Φ =ᵐ[volume] 0 := hΦae.trans hfunzero
    have hLHS : ∫⁻ x : ℝ, ‖𝓕⁻ (fun ξ => Φ ξ * 𝓕 g ξ) x‖ₑ ^ (2 * (r : ℝ)) = 0 := by
      have hfun : 𝓕⁻ (fun ξ => Φ ξ * 𝓕 g ξ) = 0 := by
        have hinner : (fun ξ => Φ ξ * 𝓕 g ξ) =ᵐ[volume] (0 : ℝ → ℂ) := by
          filter_upwards [hΦae0] with ξ hξ
          rw [hξ]
          simp
        rw [fourierInv_congr_ae hinner, fourierInv_zero_fun]
      rw [hfun]
      simp [ENNReal.zero_rpow_of_pos hqpos]
    rw [hLHS, hM0, NNReal.coe_zero, Real.zero_rpow (x := 2 * (r : ℝ)) (ne_of_gt hqpos),
      ENNReal.ofReal_zero, zero_mul]
  · -- ## The non-degenerate case `M > 0`
    have hMpos : (0 : ℝ) < (M : ℝ) := by
      have hpos : 0 < M := lt_of_le_of_ne zero_le (Ne.symm hM0)
      exact_mod_cast hpos
    have hsuppR : ∀ x : ℝ, (2 : ℝ) ^ k < |x| → φ x = 0 := by
      intro x hx
      by_contra hne
      have hx' := hφ x hne
      simp only [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at hx'
      rcases le_or_gt 0 x with h0 | h0
      · rw [abs_of_nonneg h0] at hx; linarith [hx'.2]
      · rw [abs_of_neg h0] at hx; linarith [hx'.1]
    have hbdd : ∀ x : ℝ, ‖(φ : ℝ → ℂ) x‖ ≤ SchwartzMap.seminorm ℝ 0 0 φ :=
      fun x => SchwartzMap.norm_le_seminorm ℝ φ x
    have hper : MemLp (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)) ⊤
        Work.Analysis.IonescuWainger.circleMeasure :=
      Work.Analysis.IonescuWainger.memLp_periodize (φ.continuous.measurable) (by positivity)
        hsuppR hbdd
    have hΦint : Integrable Φ := by
      have h := Work.Thm52.integrable_circleLift
        (f := Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)) hper
      simpa [hΦdef] using h
    have hκeqfun : 𝓕⁻ Φ = 𝓕 (φ : ℝ → ℂ) := fourierInv_eq_fourier_of_ae_eq hΦae
    have hκ1 : MemLp (𝓕⁻ Φ) 1 volume := by
      rw [hκeqfun, ← SchwartzMap.fourier_coe (φ : SchwartzMap ℝ ℂ)]
      exact memLp_one_iff_integrable.mpr (SchwartzMap.integrable (𝓕 (φ : SchwartzMap ℝ ℂ)))
    have hD2' : Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal (2 * (r : ℝ)))
        (fun ξ : ℝ => φ (-ξ)) M := by
      rw [← hpq]
      exact hD2
    have hS : ∀ G : SchwartzMap ℝ ℂ,
        eLpNorm (fun x : ℝ => ∫ y, 𝓕⁻ Φ (x - y) * (G : ℝ → ℂ) y)
          (ENNReal.ofReal (2 * (r : ℝ))) volume
          ≤ ENNReal.ofReal (M : ℝ) * eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal (2 * (r : ℝ))) volume := by
      intro G
      have hconv : (fun x : ℝ => ∫ y, 𝓕⁻ Φ (x - y) * (G : ℝ → ℂ) y)
          = Work.Analysis.IWMultiplier.contMulOp Φ (G : ℝ → ℂ) :=
        (contMulOp_eq_conv_kernel hΦint G).symm
      rw [hconv, contMulOp_congr_ae hΦae]
      exact hD2' G
    by_cases hfin : ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 * (r : ℝ)) = ⊤
    · have hRHS : ENNReal.ofReal ((M : ℝ) ^ (2 * (r : ℝ)))
          * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 * (r : ℝ)) = ⊤ := by
        rw [hfin, ENNReal.mul_top]
        exact ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hMpos _)
      rw [hRHS]
      exact le_top
    · have hmem : MemLp g (ENNReal.ofReal (2 * (r : ℝ))) volume := by
        refine MeasureTheory.memLp_iff.mpr ?_
        rw [lt_top_iff_ne_top]
        intro htop
        have h := Work.BourgainPlan.IonescuWainger.eLpNorm_rpow_eq_lintegral hqpos g hg.aestronglyMeasurable
        rw [htop] at h
        have htopq : (⊤ : ℝ≥0∞) ^ (2 * (r : ℝ)) = ⊤ := by
          rw [ENNReal.rpow_eq_top_iff]
          exact Or.inr ⟨rfl, hqpos⟩
        rw [htopq] at h
        exact hfin h.symm
      exact lintegral_le_of_integrable_memLp hq1 hΦint (κ := 𝓕⁻ Φ) (fun x => rfl) hκ1
        hMpos.le hS hmem hg

end Work.KMTAreas
