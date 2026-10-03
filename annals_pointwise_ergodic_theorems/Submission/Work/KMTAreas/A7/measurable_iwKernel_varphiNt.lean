/-
# Measurability of the IW kernel of the modulated bump `φ_{N,t}`

The `j`-th kernel coefficient of the Ionescu–Wainger projection applied to the modulated bump

  `φ_{N,t}(ξ) = φ_N(ξ) · e(N t ξ)`

is a function of the modulation parameter `t ∈ ℝ`; this file proves that it is measurable, i.e.
that `t ↦ (T^{≤l}_{φ_{N,t}})^^(j)` is a measurable function.  This is the measurability needed to
apply Fubini/dominated convergence to the `t`-integral in which the model tuple of
`Work.KMTAreas.A7.ModelLargeBound` is defined (the paper's §8).

The argument is a joint-measurability one:

* `(t,ξ) ↦ φ_{N,t}(ξ)` is jointly measurable on `ℝ × ℝ/ℤ`;
* hence so is its periodisation `(t,ξ) ↦ periodize (φ_{N,t}) ξ = ∑'_m φ_{N,t}(x(ξ) + m)`
  (a pointwise countable sum of jointly measurable functions, `Measurable.tsum`);
* hence so is the IW symbol `(t,ξ) ↦ ∑_{α ∈ (ℚ/ℤ)_{≤l}} periodize (φ_{N,t})(ξ - α)`;
* the kernel coefficient is the integral over `ℝ/ℤ` of this times `e(-j ξ)`, and an integral of a
  jointly strongly measurable function with respect to a finite measure is strongly measurable in
  the remaining variable (`StronglyMeasurable.integral_prod_right`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory

/-- The cutoff `η` is continuous. -/
private lemma continuous_kmtEta : Continuous Work.KMTContract.kmtEta :=
  Complex.continuous_ofReal.comp (ContDiffBump.continuous _)

/-- The bump `φ_N` at the scale `k` is continuous. -/
private lemma continuous_varphiN (N k : ℕ) : Continuous (varphiN N k) := by
  unfold varphiN
  split
  · exact continuous_kmtEta.comp (continuous_const.mul continuous_id)
  · exact (continuous_kmtEta.comp (continuous_const.mul continuous_id)).sub
      (continuous_kmtEta.comp (continuous_const.mul continuous_id))

/-- The character `e(x) = exp(2πix)` is continuous. -/
private lemma continuous_ee : Continuous ee := by
  unfold ee; fun_prop

/-- The canonical representative `ℝ/ℤ → [0,1)` is measurable. -/
private lemma measurable_equivIco_val :
    Measurable fun ξ : Work.Analysis.IonescuWainger.Circle =>
      (AddCircle.equivIco (1 : ℝ) 0 ξ).val :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

/-- **The periodisation of a jointly measurable family of symbols is jointly measurable.** -/
private lemma measurable_periodize_uncurry (φ : ℝ → ℝ → ℂ)
    (hφ : Measurable (Function.uncurry φ)) :
    Measurable fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
      Work.Analysis.IonescuWainger.periodize (φ p.1) p.2 := by
  have hterm : ∀ m : ℤ, Measurable fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
      φ p.1 ((AddCircle.equivIco (1 : ℝ) 0 p.2).val + (m : ℝ)) := fun m =>
    hφ.comp (measurable_fst.prodMk
      ((measurable_equivIco_val.comp measurable_snd).add_const (m : ℝ)))
  have h := Measurable.tsum (L := SummationFilter.unconditional ℤ) hterm
  simpa only [Work.Analysis.IonescuWainger.periodize] using h

/-- **Joint measurability of the modulated bump.** -/
private lemma measurable_varphiNt_uncurry (N k : ℕ) :
    Measurable fun p : ℝ × ℝ => varphiNt N k p.1 p.2 := by
  have h1 : Measurable fun p : ℝ × ℝ => varphiN N k p.2 :=
    (continuous_varphiN N k).measurable.comp measurable_snd
  have h2 : Measurable fun p : ℝ × ℝ => ee ((N : ℝ) * p.1 * p.2) :=
    continuous_ee.measurable.comp ((measurable_fst.const_mul (N : ℝ)).mul measurable_snd)
  unfold varphiNt
  exact h1.mul h2

/-- **Measurability in `t` of the IW kernel of the modulated bump `φ_{N,t}`.** -/
theorem measurable_iwKernel_varphiNt (ρ : ℝ) (l : ℕ) (N k : ℕ) (j : ℤ) :
    Measurable (fun t : ℝ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k t))) j) := by
  -- joint measurability of the periodisation and of the IW symbol
  have hper : Measurable fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
      Work.Analysis.IonescuWainger.periodize (varphiNt N k p.1) p.2 :=
    measurable_periodize_uncurry (varphiNt N k) (measurable_varphiNt_uncurry N k)
  have hsym : Measurable fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
      Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (varphiNt N k p.1)) p.2 := by
    simp only [Work.Analysis.IonescuWainger.iwSymbolSet]
    refine Finset.measurable_sum _ fun α _ => ?_
    exact hper.comp (measurable_fst.prodMk (measurable_snd.sub measurable_const))
  -- the kernel coefficient is the integral of the joint symbol against the character `e(-j·)`
  have hint : Measurable fun t : ℝ => ∫ ξ : Work.Analysis.IonescuWainger.Circle,
      fourier (T := 1) (-j) ξ • Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (varphiNt N k t)) ξ
      ∂Work.Analysis.IonescuWainger.circleMeasure := by
    have hf : StronglyMeasurable (Function.uncurry fun t : ℝ =>
        fun ξ : Work.Analysis.IonescuWainger.Circle =>
          fourier (T := 1) (-j) ξ • Work.Analysis.IonescuWainger.iwSymbolSet
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize (varphiNt N k t)) ξ) := by
      apply Measurable.stronglyMeasurable
      exact ((fourier (T := 1) (-j)).continuous.measurable.comp measurable_snd).mul hsym
    exact (hf.integral_prod_right (ν := Work.Analysis.IonescuWainger.circleMeasure)).measurable
  -- the kernel is that integral, by definition
  have hker : (fun t : ℝ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (varphiNt N k t))) j)
      = fun t : ℝ => ∫ ξ : Work.Analysis.IonescuWainger.Circle,
          fourier (T := 1) (-j) ξ • Work.Analysis.IonescuWainger.iwSymbolSet
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize (varphiNt N k t)) ξ
          ∂Work.Analysis.IonescuWainger.circleMeasure := by
    funext t
    rfl
  rw [hker]
  exact hint

end Work.KMTAreas.A7
