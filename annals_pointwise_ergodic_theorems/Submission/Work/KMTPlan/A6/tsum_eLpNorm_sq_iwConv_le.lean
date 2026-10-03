import Mathlib
import Submission.Work.KMTPlan.A6.multiplierOfPlancherel
import Submission.Work.KMTPlan.A6.memlpOfMemLpCount
import Submission.Work.KMTPlan.A6.iwConvEqIwOpSetMemlp
import Submission.Work.KMTAreas.A7.LargeInterface

/-!
# The `ℓ²` square-sum bound for a family of Ionescu–Wainger multipliers

If the Ionescu–Wainger symbols `m_n = iwSymbolSet A (periodize (ψ n))` of a countable family of
multipliers satisfy the pointwise square-sum bound `∑'_n ‖m_n θ‖² ≤ W²` on the whole frequency
circle, then the corresponding family of convolutions `T_n h = iwConv A (periodize (ψ n)) h`
satisfies the vector-valued Plancherel bound

`(∑'_n ‖T_n h‖_{ℓ²}²)^{1/2} ≤ W ‖h‖_{ℓ²}`.

The proof is the `q = 2` Plancherel identity `multiplierOfPlancherel` applied to each multiplier,
combined with Tonelli's theorem for the `n`-sum.  The family `ψ` is *not* assumed measurable, so
each symbol is first replaced by the a.e. strongly measurable representative `measRep`; when the
symbol is not a.e. strongly measurable all its Fourier coefficients (hence the whole multiplier)
vanish, so the replacement does not change the left-hand side.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace Work.KMTPlan.A6

open Work.Analysis.IonescuWainger

attribute [local instance] Classical.propDecidable

/-- The frequency circle `ℝ/ℤ`, under a local name (there is a clashing `_root_.Circle`). -/
abbrev KCircle : Type := Work.Analysis.IonescuWainger.Circle

/-! ## The a.e. strongly measurable representative of a symbol -/

/-- If `m : ℝ/ℤ → ℂ` is not a.e. strongly measurable, then all its Fourier coefficients vanish
(the defining integrand of `fourierCoeff` is then not integrable). -/
theorem fourierCoeff_eq_zero_of_not_aestronglyMeasurable {m : KCircle → ℂ}
    (hm : ¬ AEStronglyMeasurable m circleMeasure) (j : ℤ) : fourierCoeff m j = 0 := by
  have hne : ∀ t : KCircle, fourier (T := 1) (-j) t ≠ 0 := by
    intro t h0
    rw [fourier_apply] at h0
    have h1 := _root_.Circle.norm_coe ((-j : ℤ) • t).toCircle
    rw [h0] at h1
    simp at h1
  have hc : Continuous fun t : KCircle => (fourier (T := 1) (-j) t)⁻¹ :=
    (map_continuous (fourier (T := 1) (-j))).inv₀ hne
  have hnotint : ¬ Integrable (fun t : KCircle => fourier (-j) t • m t) circleMeasure := by
    intro hint
    refine hm ?_
    have h2 : AEStronglyMeasurable
        (fun t : KCircle => (fourier (T := 1) (-j) t)⁻¹ • (fourier (-j) t • m t))
        circleMeasure :=
      (hc.aestronglyMeasurable).smul hint.aestronglyMeasurable
    refine h2.congr (ae_of_all circleMeasure fun t => ?_)
    simp only [smul_smul, inv_mul_cancel₀ (hne t), one_smul]
  have hcoe : fourierCoeff m j = ∫ t : KCircle, fourier (-j) t • m t ∂circleMeasure := rfl
  rw [hcoe, integral_undef hnotint]

/-- A measurable representative of a symbol: the symbol itself when it is a.e. strongly
measurable, and the zero function otherwise. -/
noncomputable def measRep (m : KCircle → ℂ) : KCircle → ℂ :=
  if AEStronglyMeasurable m circleMeasure then m else 0

theorem measRep_aestronglyMeasurable (m : KCircle → ℂ) :
    AEStronglyMeasurable (measRep m) circleMeasure := by
  rw [measRep]
  split_ifs with h
  · exact h
  · exact aestronglyMeasurable_zero

theorem measRep_enorm_le (m : KCircle → ℂ) (θ : KCircle) : ‖measRep m θ‖ ≤ ‖m θ‖ := by
  rw [measRep]
  split_ifs with h
  · exact le_rfl
  · simp

/-- The representative has the same Fourier coefficients as the original symbol. -/
theorem fourierCoeff_measRep (m : KCircle → ℂ) (j : ℤ) :
    fourierCoeff (measRep m) j = fourierCoeff m j := by
  rw [measRep]
  split_ifs with h
  · rfl
  · rw [fourierCoeff_eq_zero_of_not_aestronglyMeasurable h]
    simp [fourierCoeff]

/-! ## The multiplier as an explicit Fourier series -/

/-- The Ionescu–Wainger convolution as the (unconditionally convergent) Fourier series of the
symbol. -/
theorem iwConv_eq_tsum (A : Finset KCircle) (Φ : KCircle → ℂ) (f : ℤ → ℂ) (n : ℤ) :
    Work.Analysis.IWMultiplier.iwConv A Φ f n
      = ∑' j : ℤ, fourierCoeff (iwSymbolSet A Φ) j * f (n - j) := by
  rw [Work.Analysis.IWMultiplier.iwConv_apply]
  refine tsum_congr fun j => ?_
  rw [Work.Analysis.IWMultiplier.iwKernel, smul_eq_mul]

/-- The `n`-th value of the Fourier multiplier with a bounded symbol `m` is the `n`-th Fourier
coefficient of `m · 𝓕_ℤ F`. -/
theorem multiplierOf_apply_eq_fourierCoeff (m : KCircle → ℂ) (hm : MemLp m ⊤ circleMeasure)
    (F : L2Z) (n : ℤ) :
    ⇑(multiplierOf m hm F) n = fourierCoeff (⇑(hm.toLp m • fourierZ F)) n := by
  have hsymm : fourierZ.symm = (fourierBasis (T := 1)).repr := rfl
  have h1 : ⇑(multiplierOf m hm F) n = (fourierZ.symm (hm.toLp m • fourierZ F)) n := rfl
  rw [h1, hsymm]
  exact fourierBasis_repr _ n

/-- The `n`-th value of the Fourier multiplier with a bounded symbol `m` is the convolution of
the Fourier coefficients of `m` with `F`. -/
theorem multiplierOf_apply_eq_tsum (m : KCircle → ℂ) (hm : MemLp m ⊤ circleMeasure)
    (F : L2Z) (n : ℤ) :
    ⇑(multiplierOf m hm F) n = ∑' j : ℤ, fourierCoeff m j * ⇑F (n - j) := by
  rw [multiplierOf_apply_eq_fourierCoeff m hm F n, fourierCoeff_lpSMul_fourierZ_l2 hm F n]

/-- If two symbols have the same Fourier coefficients and one of them is a bounded symbol, then
the IW convolution with the first equals the Fourier multiplier with the second. -/
private theorem iwConv_eq_multiplierOf {A : Finset KCircle} {Φ : KCircle → ℂ} {m : KCircle → ℂ}
    (hm : MemLp m ⊤ circleMeasure)
    (hcoeff : ∀ j : ℤ, fourierCoeff (iwSymbolSet A Φ) j = fourierCoeff m j) (F : L2Z) :
    Work.Analysis.IWMultiplier.iwConv A Φ ⇑F = ⇑(multiplierOf m hm F) := by
  funext n
  rw [iwConv_eq_tsum, multiplierOf_apply_eq_tsum]
  exact tsum_congr (fun j => by rw [hcoeff j])

/-- **Plancherel's identity for the IW convolution**: for a bounded symbol `m` with the same
Fourier coefficients as `iwSymbolSet A Φ`, the squared `ℓ²`-norm of the convolution is the
`‖m‖²`-weighted integral of `|𝓕_ℤ f|²`. -/
theorem eLpNorm_sq_iwConv_eq_lintegral {A : Finset KCircle} {Φ : KCircle → ℂ} {m : KCircle → ℂ}
    (hm : MemLp m ⊤ circleMeasure)
    (hcoeff : ∀ j : ℤ, fourierCoeff (iwSymbolSet A Φ) j = fourierCoeff m j)
    {f : ℤ → ℂ} (hf : Memℓp f 2) :
    (eLpNorm (Work.Analysis.IWMultiplier.iwConv A Φ f) 2 Measure.count) ^ (2 : ℕ)
      = ∫⁻ ξ, ‖m ξ‖ₑ ^ (2 : ℕ) * ‖fourierZ (⟨f, hf⟩ : L2Z) ξ‖ₑ ^ (2 : ℕ)
          ∂circleMeasure := by
  have hconv : Work.Analysis.IWMultiplier.iwConv A Φ f
      = ⇑(multiplierOf m hm (⟨f, hf⟩ : L2Z)) :=
    iwConv_eq_multiplierOf hm hcoeff (⟨f, hf⟩ : L2Z)
  rw [hconv]
  exact multiplierOfPlancherel m hm (⟨f, hf⟩ : L2Z)

/-! ## The main theorem -/

theorem tsum_eLpNorm_sq_iwConv_le (A : Finset Work.Analysis.IonescuWainger.Circle)
    (ψ : ℕ → ℝ → ℂ) (h : ℤ → ℂ) (hh : MeasureTheory.MemLp h 2 MeasureTheory.Measure.count)
    (W : NNReal)
    (hW : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      (∑' n : ℕ, ‖Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize (ψ n)) θ‖ₑ ^ (2 : ℝ)) ≤ (W : ENNReal) ^ 2) :
    (∑' n : ℕ, (MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv A
        (Work.Analysis.IonescuWainger.periodize (ψ n)) h) 2 MeasureTheory.Measure.count) ^ (2 : ℝ))
        ^ (1 / 2 : ℝ)
      ≤ (W : ENNReal) * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count := by
  classical
  have hmem : Memℓp h 2 := memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hh
  set m : ℕ → KCircle → ℂ := fun n => iwSymbolSet A (periodize (ψ n)) with hm_def
  set rep : ℕ → KCircle → ℂ := fun n => measRep (m n) with hrep_def
  -- converting between the natural and the real power `2`
  have hpow2 : ∀ x : ENNReal, x ^ (2 : ℕ) = x ^ (2 : ℝ) := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  -- every symbol is pointwise bounded by `W`
  have hm_bound : ∀ (n : ℕ) (θ : KCircle), ‖m n θ‖ ≤ (W : ℝ) := by
    intro n θ
    have hWθ : (∑' b : ℕ, ‖m b θ‖ₑ ^ (2 : ℕ)) ≤ (W : ENNReal) ^ 2 := by
      simpa only [hm_def, ← hpow2] using hW θ
    have h1 : ‖m n θ‖ₑ ^ (2 : ℕ) ≤ (W : ENNReal) ^ 2 := le_trans (ENNReal.le_tsum (f := fun b : ℕ => ‖m b θ‖ₑ ^ (2 : ℕ)) n) hWθ
    have h2 : ENNReal.ofReal (‖m n θ‖ ^ 2) ≤ ENNReal.ofReal ((W : ℝ) ^ 2) := by
      rw [← ofReal_norm, ENNReal.coe_nnreal_eq W] at h1
      rw [← ENNReal.ofReal_pow (norm_nonneg (m n θ)) 2,
        ← ENNReal.ofReal_pow (show (0 : ℝ) ≤ (W : ℝ) by positivity) 2] at h1
      exact h1
    have h3 : ‖m n θ‖ ^ 2 ≤ (W : ℝ) ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
    have h4 : |‖m n θ‖| ≤ |(W : ℝ)| := sq_le_sq.mp h3
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h4
  have hrep_bound : ∀ (n : ℕ) (θ : KCircle), ‖rep n θ‖ ≤ (W : ℝ) := fun n θ =>
    le_trans (measRep_enorm_le (m n) θ) (hm_bound n θ)
  have hrep_aesm : ∀ n : ℕ, AEStronglyMeasurable (rep n) circleMeasure := fun n =>
    measRep_aestronglyMeasurable (m n)
  have hrep_mem : ∀ n : ℕ, MemLp (rep n) ⊤ circleMeasure := fun n =>
    memLp_top_of_bound (hrep_aesm n) (W : ℝ) (ae_of_all circleMeasure (hrep_bound n))
  have hrep_coeff : ∀ (n : ℕ) (j : ℤ),
      fourierCoeff (iwSymbolSet A (periodize (ψ n))) j = fourierCoeff (rep n) j := by
    intro n j
    have hh' := fourierCoeff_measRep (m n) j
    simp only [hm_def] at hh'
    simp only [hrep_def, hm_def]
    exact hh'.symm
  -- the per-`n` Plancherel identity
  have hterm : ∀ n : ℕ,
      (eLpNorm (Work.Analysis.IWMultiplier.iwConv A (periodize (ψ n)) h)
          2 Measure.count) ^ (2 : ℕ)
        = ∫⁻ ξ, ‖rep n ξ‖ₑ ^ (2 : ℕ) * ‖fourierZ (⟨h, hmem⟩ : L2Z) ξ‖ₑ ^ (2 : ℕ)
            ∂circleMeasure := fun n =>
    eLpNorm_sq_iwConv_eq_lintegral (A := A) (Φ := periodize (ψ n)) (m := rep n)
      (hrep_mem n) (hrep_coeff n) (f := h) hmem
  -- measurability of the summands
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun ξ => ‖rep n ξ‖ₑ ^ (2 : ℕ) * ‖fourierZ (⟨h, hmem⟩ : L2Z) ξ‖ₑ ^ (2 : ℕ))
      circleMeasure := by
    intro n
    have h1 : AEMeasurable (fun ξ => ‖rep n ξ‖ₑ ^ (2 : ℕ)) circleMeasure :=
      ((hrep_aesm n).aemeasurable.enorm).pow_const 2
    have h2 : AEMeasurable
        (fun ξ => ‖fourierZ (⟨h, hmem⟩ : L2Z) ξ‖ₑ ^ (2 : ℕ)) circleMeasure :=
      ((Lp.aestronglyMeasurable (fourierZ (⟨h, hmem⟩ : L2Z))).aemeasurable.enorm).pow_const 2
    exact h1.mul h2
  -- the pointwise square-sum bound for the representatives
  have hle : ∀ ξ : KCircle, (∑' n : ℕ, ‖rep n ξ‖ₑ ^ (2 : ℕ)) ≤ (W : ENNReal) ^ 2 := by
    intro ξ
    have hWξ : (∑' b : ℕ, ‖m b ξ‖ₑ ^ (2 : ℕ)) ≤ (W : ENNReal) ^ 2 := by
      simpa only [hm_def, ← hpow2] using hW ξ
    refine le_trans (ENNReal.tsum_le_tsum (fun n => ?_)) hWξ
    have h2 : ‖rep n ξ‖ₑ ≤ ‖m n ξ‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (measRep_enorm_le (m n) ξ)
    exact pow_le_pow_left' h2 2
  -- the `ℓ²` square-sum bound
  have key : (∑' n : ℕ,
        (eLpNorm (Work.Analysis.IWMultiplier.iwConv A (periodize (ψ n)) h)
          2 Measure.count) ^ (2 : ℕ))
      ≤ ((W : ENNReal) * eLpNorm h 2 Measure.count) ^ (2 : ℕ) := by
    calc (∑' n : ℕ,
          (eLpNorm (Work.Analysis.IWMultiplier.iwConv A (periodize (ψ n)) h)
            2 Measure.count) ^ (2 : ℕ))
        = ∑' n : ℕ, ∫⁻ ξ,
            ‖rep n ξ‖ₑ ^ (2 : ℕ) * ‖fourierZ (⟨h, hmem⟩ : L2Z) ξ‖ₑ ^ (2 : ℕ)
            ∂circleMeasure := tsum_congr hterm
      _ = ∫⁻ ξ, ∑' n : ℕ,
            ‖rep n ξ‖ₑ ^ (2 : ℕ) * ‖fourierZ (⟨h, hmem⟩ : L2Z) ξ‖ₑ ^ (2 : ℕ)
            ∂circleMeasure := (lintegral_tsum hmeas).symm
      _ = ∫⁻ ξ, (∑' n : ℕ, ‖rep n ξ‖ₑ ^ (2 : ℕ)) *
            ‖fourierZ (⟨h, hmem⟩ : L2Z) ξ‖ₑ ^ (2 : ℕ) ∂circleMeasure :=
            lintegral_congr (fun ξ => ENNReal.tsum_mul_right)
      _ ≤ ∫⁻ ξ, (W : ENNReal) ^ 2 * ‖fourierZ (⟨h, hmem⟩ : L2Z) ξ‖ₑ ^ (2 : ℕ)
            ∂circleMeasure := lintegral_mono (fun ξ => mul_le_mul_of_nonneg_right (hle ξ) (by positivity))
      _ = (W : ENNReal) ^ 2 * ∫⁻ ξ,
            ‖fourierZ (⟨h, hmem⟩ : L2Z) ξ‖ₑ ^ (2 : ℕ) ∂circleMeasure :=
            lintegral_const_mul' _ _ (by simp [ENNReal.coe_ne_top])
      _ = (W : ENNReal) ^ 2 * (eLpNorm h 2 Measure.count) ^ (2 : ℕ) := by
            rw [← eLpNorm_two_sq _ (Lp.aestronglyMeasurable _), ← norm_fourierZ_sq]
      _ = ((W : ENNReal) * eLpNorm h 2 Measure.count) ^ (2 : ℕ) := (mul_pow _ _ 2).symm
  have hs : (∑' n : ℕ, (eLpNorm (Work.Analysis.IWMultiplier.iwConv A
        (periodize (ψ n)) h) 2 Measure.count) ^ (2 : ℝ))
      = (∑' n : ℕ, (eLpNorm (Work.Analysis.IWMultiplier.iwConv A
        (periodize (ψ n)) h) 2 Measure.count) ^ (2 : ℕ)) :=
    tsum_congr (fun n => (hpow2 _).symm)
  have hfin : (((W : ENNReal) * eLpNorm h 2 Measure.count) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)
      = (W : ENNReal) * eLpNorm h 2 Measure.count := by
    rw [hpow2]
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
  rw [hs]
  exact le_trans (ENNReal.rpow_le_rpow key (by norm_num)) (le_of_eq hfin)

end Work.KMTPlan.A6
