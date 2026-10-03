/-
# Boundedness and measurability in `t` of the IW projection of the modulated bump `φ_{N,t}`

`Work.KMTAreas.A7.varphiNt N k t` is the modulated KMT bump `φ_{N,t}(ξ) = φ_N(ξ)·e(Ntξ)` of
Krause--Mirek--Tao §6--§8.  The model tuple of §8 integrates in `t ∈ [1/2,1]` the
Ionescu--Wainger projections `T^{≤l}_{φ_{N,t}}` of the two functions `f`, `g`, and the two facts
needed there are:

* for **every** finite set `A` of circle frequencies (not only `A = (ℚ/ℤ)_{≤l}`), the operator
  `iwConv A (periodize (φ_{N,t}))` maps bounded sequences to bounded sequences with a bound
  which is uniform in `t ∈ [1/2,1]` (`iwConv_varphiNt_bounded`): the `ℓ¹`-kernel estimate
  `‖T f‖_∞ ≤ (∑_j ‖κ_j‖)·‖f‖_∞` applied to the quadratic kernel decay
  `iwKernel_decay_of_bump` (itself a consequence of the two integration by parts
  `FourierDecayExplicit` and of `varphiNt_bounds`);
* the function `t ↦ iwConv A (periodize (φ_{N,t})) f y` is measurable
  (`measurable_iwConv_varphiNt`), so that the `t`-integral of the model tuple makes sense.  This
  is `Measurable.tsum` applied to the kernel coefficients, whose measurability in `t` is
  `measurable_iwKernel_varphiNt_general` — the general-frequency-set form of
  `Work.KMTAreas.A7.measurable_iwKernel_varphiNt`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FiberGeneral
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded
import Submission.Work.KMTAreas.A7.FpieceEqTm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## The convolution form of `iwConv` -/

/-- `iwConv` for scalar (i.e. `ℂ`-valued) sequences is convolution with the kernel, written with a
multiplication instead of the scalar action. -/
theorem iwConv_eq_tsum_mul (A : Finset Work.Analysis.IonescuWainger.Circle) (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) (f : ℤ → ℂ) (y : ℤ) :
    iwConv A Φ f y = ∑' j : ℤ, iwKernel (iwSymbolSet A Φ) j * f (y - j) := by
  rw [iwConv]
  exact tsum_congr (fun j => smul_eq_mul _ _)

/-! ## Measurability in `t` of the IW kernel coefficients -/

/-- **The periodisation of a jointly measurable family is jointly measurable.**  If
`φ : ℝ → ℝ → ℂ` is jointly measurable, then `(t, ξ) ↦ periodize (φ t) ξ` is measurable on
`ℝ × ℝ/ℤ`. -/
private lemma measurable_periodize_uncurry_varphiNt {φ : ℝ → ℝ → ℂ}
    (hφ : Measurable (fun q : ℝ × ℝ => φ q.1 q.2)) :
    Measurable (fun p : ℝ × Work.Analysis.IonescuWainger.Circle => periodize (φ p.1) p.2) := by
  have hx : Measurable (fun ξ : Work.Analysis.IonescuWainger.Circle => (AddCircle.equivIco (1 : ℝ) 0 ξ).val) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have h1 : (fun p : ℝ × Work.Analysis.IonescuWainger.Circle => periodize (φ p.1) p.2)
      = fun p => ∑' m : ℤ, φ p.1 ((AddCircle.equivIco (1 : ℝ) 0 p.2).val + (m : ℝ)) := by
    funext p
    rw [periodize]
  rw [h1]
  refine Measurable.tsum (fun m => ?_)
  exact hφ.comp (measurable_fst.prodMk ((hx.comp measurable_snd).add measurable_const))

/-- **The IW symbol of a jointly measurable family is jointly measurable.** -/
private lemma measurable_iwSymbolSet_uncurry_varphiNt (A : Finset Work.Analysis.IonescuWainger.Circle) {φ : ℝ → ℝ → ℂ}
    (hφ : Measurable (fun q : ℝ × ℝ => φ q.1 q.2)) :
    Measurable (fun p : ℝ × Work.Analysis.IonescuWainger.Circle => iwSymbolSet A (periodize (φ p.1)) p.2) := by
  have h1 : (fun p : ℝ × Work.Analysis.IonescuWainger.Circle => iwSymbolSet A (periodize (φ p.1)) p.2)
      = fun p => ∑ α ∈ A, periodize (φ p.1) (p.2 - α) := by
    funext p; simp only [iwSymbolSet]
  rw [h1]
  refine Finset.measurable_sum _ (fun α _ => ?_)
  exact (measurable_periodize_uncurry_varphiNt hφ).comp
    (measurable_fst.prodMk (measurable_snd.sub measurable_const))

/-- **The Fourier coefficients of the IW symbol depend measurably on the parameter.**  For a
finite set `A` of arithmetic frequencies and a jointly measurable `φ : ℝ → ℝ → ℂ`, the map
`t ↦ fourierCoeff (iwSymbolSet A (periodize (φ t))) j` is measurable. -/
private lemma measurable_fourierCoeff_iwSymbolSet_varphiNt (A : Finset Work.Analysis.IonescuWainger.Circle) (j : ℤ)
    {φ : ℝ → ℝ → ℂ} (hφ : Measurable (fun q : ℝ × ℝ => φ q.1 q.2)) :
    Measurable (fun t : ℝ => fourierCoeff (iwSymbolSet A (periodize (φ t))) j) := by
  have hsym := measurable_iwSymbolSet_uncurry_varphiNt A hφ
  have hprod : Measurable (fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
      fourier (-j) p.2 • iwSymbolSet A (periodize (φ p.1)) p.2) :=
    ((map_continuous (fourier (-j))).measurable.comp measurable_snd).smul hsym
  have hker : (fun t : ℝ => fourierCoeff (iwSymbolSet A (periodize (φ t))) j)
      = fun t : ℝ => ∫ z : Work.Analysis.IonescuWainger.Circle, fourier (-j) z • iwSymbolSet A (periodize (φ t)) z
          ∂circleMeasure := by
    funext t; rw [fourierCoeff, circleMeasure]
  rw [hker]
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := circleMeasure) hprod.stronglyMeasurable).measurable

/-- **Joint measurability of the modulated bump** `(t, ξ) ↦ φ_{N,t}(ξ)`, where
`φ_{N,t}(ξ) = φ_N(ξ)·e(Ntξ)`. -/
private lemma measurable_varphiNt_uncurry' (N k : ℕ) :
    Measurable (fun q : ℝ × ℝ => varphiNt N k q.1 q.2) := by
  have hk : Measurable Work.KMTContract.kmtEta := by
    have h : Work.KMTContract.kmtEta
        = fun x : ℝ => ((Work.KMTContract.kmtBump : ℝ → ℝ) x : ℂ) := rfl
    rw [h]
    exact Complex.continuous_ofReal.measurable.comp
      Work.KMTContract.kmtBump.continuous.measurable
  have hvp : Measurable (varphiN N k) := by
    unfold varphiN
    split_ifs with h0
    · exact hk.comp (measurable_const_mul _)
    · exact (hk.comp (measurable_const_mul _)).sub (hk.comp (measurable_const_mul _))
  have hee : Measurable ee := by unfold ee; fun_prop
  unfold varphiNt
  exact (hvp.comp measurable_snd).mul
    (hee.comp (((measurable_const.mul measurable_fst).mul measurable_snd)))

/-- **Measurability in `t` of the IW kernel of the modulated bump `φ_{N,t}`, for an arbitrary
finite set `A` of arithmetic frequencies.**  This is the general form (in `A`) of
`Work.KMTAreas.A7.measurable_iwKernel_varphiNt`. -/
theorem measurable_iwKernel_varphiNt_general (A : Finset Work.Analysis.IonescuWainger.Circle) (N k : ℕ) (j : ℤ) :
    Measurable (fun t : ℝ => iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j) := by
  have h := measurable_fourierCoeff_iwSymbolSet_varphiNt A j
    (φ := fun t ξ => varphiNt N k t ξ) (measurable_varphiNt_uncurry' N k)
  simpa only [iwKernel] using h

/-! ## The uniform-in-`t` pointwise bound -/

/-- **The `ℓ^∞` bound for `iwConv A (periodize φ_{N,t})`, uniform in `t ∈ [1/2,1]`.**  For an
arbitrary finite set `A` of circle frequencies, the convolution operator with the kernel of the
IW symbol of `φ_{N,t}` maps the bounded sequence `f` to a sequence bounded by a constant
independent of `t ∈ [1/2,1]` and of the position. -/
theorem iwConv_varphiNt_bounded (A : Finset Work.Analysis.IonescuWainger.Circle) (N k : ℕ) (f : ℤ → ℂ) (Cf : ℝ)
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖iwConv A (periodize (varphiNt N k t)) f y‖ ≤ C := by
  classical
  obtain ⟨R, S, hSnn, hB⟩ := varphiNt_bounds N k
  set C₀ : ℝ := 4 * ((A.card : ℝ) * S) + 1 with hC₀def
  have hC₀nn : 0 ≤ C₀ := by rw [hC₀def]; positivity
  -- the quadratic kernel decay, uniformly in `t`
  have hdec : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ j : ℤ,
      ‖iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j‖
        ≤ C₀ * ‖kmtKernWeight j‖ := by
    intro t ht j
    exact iwKernel_decay_of_bump A (hB t ht).2.1 (hB t ht).2.2.1 hSnn
      (hB t ht).2.2.2.1 (hB t ht).2.2.2.2 j
  refine ⟨(∑' j : ℤ, C₀ * ‖kmtKernWeight j‖ * Cf) + 1, ?_⟩
  intro t ht y
  have hκ : Summable (fun j : ℤ =>
      ‖iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hdec t ht j)
      (summable_kmtKernWeight.mul_left C₀)
  have hsum : Summable (fun j : ℤ =>
      iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j * f (y - j)) :=
    summable_mul_of_bounded hκ (fun j => hf _)
  have hsum2 : Summable (fun j : ℤ =>
      ‖iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j‖ * ‖f (y - j)‖) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun j => mul_le_mul_of_nonneg_left ((hf (y - j)).trans (le_max_left _ _)) (norm_nonneg _))
      (hκ.mul_right (max Cf 0))
  rw [iwConv_eq_tsum_mul]
  calc ‖∑' j : ℤ, iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j * f (y - j)‖
      ≤ ∑' j : ℤ,
          ‖iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j * f (y - j)‖ :=
        norm_tsum_le_tsum_norm hsum.norm
    _ = ∑' j : ℤ,
          ‖iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j‖ * ‖f (y - j)‖ :=
        tsum_congr (fun j => norm_mul _ _)
    _ ≤ ∑' j : ℤ, C₀ * ‖kmtKernWeight j‖ * Cf := by
        refine Summable.tsum_le_tsum (fun j => ?_) hsum2
          ((summable_kmtKernWeight.mul_left C₀).mul_right Cf)
        exact mul_le_mul (hdec t ht j) (hf (y - j)) (norm_nonneg _)
          (mul_nonneg hC₀nn (norm_nonneg _))
    _ ≤ (∑' j : ℤ, C₀ * ‖kmtKernWeight j‖ * Cf) + 1 := le_add_of_nonneg_right zero_le_one

/-! ## Measurability in `t` of `iwConv A (periodize φ_{N,t}) f y` -/

/-- **Measurability in `t` of the IW projection of the modulated bump**, for an arbitrary finite
set `A` of arithmetic frequencies: `t ↦ iwConv A (periodize (φ_{N,t})) f y` is measurable. -/
theorem measurable_iwConv_varphiNt (A : Finset Work.Analysis.IonescuWainger.Circle) (N k : ℕ) (f : ℤ → ℂ) (y : ℤ) :
    Measurable (fun t : ℝ => iwConv A (periodize (varphiNt N k t)) f y) := by
  have hterm : ∀ j : ℤ, Measurable (fun t : ℝ =>
      iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j * f (y - j)) :=
    fun j => (measurable_iwKernel_varphiNt_general A N k j).mul_const _
  have h := Measurable.tsum (L := SummationFilter.unconditional ℤ) hterm
  have hfun : (fun t : ℝ => iwConv A (periodize (varphiNt N k t)) f y)
      = fun t : ℝ => ∑' j : ℤ,
          iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j * f (y - j) :=
    funext fun t => iwConv_eq_tsum_mul A _ f y
  rw [hfun]
  exact h

/-! ## The target -/

theorem iwConv_varphiNt_bounded_measurable (A : Finset Work.Analysis.IonescuWainger.Circle)
    (N k : ℕ) (f : ℤ → ℂ) (Cf : ℝ) (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) :
    (∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖Work.Analysis.IWMultiplier.iwConv A
        (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k t)) f y‖ ≤ C)
    ∧ (∀ y : ℤ, Measurable (fun t : ℝ => Work.Analysis.IWMultiplier.iwConv A
        (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k t)) f y)) := by
  exact ⟨iwConv_varphiNt_bounded A N k f Cf hf, fun y => measurable_iwConv_varphiNt A N k f y⟩

end

end Work.KMTAreas.A7
