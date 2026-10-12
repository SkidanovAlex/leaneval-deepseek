import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Kinetic.momForm_le_box
import Submission.Work.OneBodyKin.kinFT_sub_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Polar.momForm_parallelogram` — `momForm` is a quadratic form

The large-momentum kinetic word of FS `eq:DefT`'s third term,

    `momForm ℓ d u ψ = (2π)⁻³ ∫_p 1_{(d²ℓ)⁻¹<‖p‖} · ‖kinFT (θ_u · Q_uψ) p‖²`,

is a **quadratic form** in the one-body state `ψ`: it satisfies the parallelogram
identity

    `momForm (f+g) + momForm (f−g) = 2 momForm f + 2 momForm g`.

This is exactly the "off-diagonal" information needed to polarise the word (the
`Sector.Polar` route: `4·polB Φ Ψ = wordB (Φ+Ψ) − wordB (Φ−Ψ)`), here at the level of
the one-body kinetic piece.

## Proof

`θ_u = indU ℓ u` does not depend on the state and `Q_u = Qfree ℓ u` is **linear**
(the box mean `bsMean` is linear, `bsMean_add`/`bsMean_sub`), the Fourier transform
`kinFT` is linear on integrable states (`kinFT_sub_smul` of the corpus, used here as
`kinFT_add`/`kinFT_sub`), and the inner product identity
`‖a+b‖² + ‖a−b‖² = 2‖a‖² + 2‖b‖²` (`parallelogram_law_with_norm`) is integrated against
the common nonnegative cut-off `momProj ≥ 0`.

The only analytic work is that the four `p`-integrands are integrable: the localised
mean-free state `boxState ℓ u ψ = ↑(θ_u·Q_uψ)` lies in `L¹ ∩ L²` for smooth `ψ`
(`boxState_memLp`), so `‖kinFT (boxState ℓ u ψ)‖²` is integrable (`kinFT_sq_of_memLp`,
Plancherel), and multiplying by the bounded measurable cut-off `momProj ≤ 1` preserves
integrability.  With every integral finite, the identities `∫ (F+G) = ∫F + ∫G`,
`∫ c·F = c·∫F` and `∫ F = ∫ G` (for pointwise equal integrands) assemble the result.
-/

open MeasureTheory

namespace Work.BoseFixB2.Polar

set_option maxHeartbeats 1000000

/-! ## 1. Linearity of the box mean and of the mean-free projection -/

/-- The moving-box mean `m_u(ψ) = (ℓ³)⁻¹∫_{Λ(u)}ψ` is additive in the state. -/
private lemma bsMean_add {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {f g : ℝ³ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Work.BSKinetic.bsMean ℓ u (fun z => f z + g z)
      = Work.BSKinetic.bsMean ℓ u f + Work.BSKinetic.bsMean ℓ u g := by
  simp only [Work.BSKinetic.bsMean]
  rw [MeasureTheory.integral_add]
  · ring
  · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      (hf.comp (by fun_prop)).continuousOn
  · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      (hg.comp (by fun_prop)).continuousOn

/-- The moving-box mean `m_u(ψ) = (ℓ³)⁻¹∫_{Λ(u)}ψ` is subtractive in the state. -/
private lemma bsMean_sub {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {f g : ℝ³ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Work.BSKinetic.bsMean ℓ u (fun z => f z - g z)
      = Work.BSKinetic.bsMean ℓ u f - Work.BSKinetic.bsMean ℓ u g := by
  simp only [Work.BSKinetic.bsMean]
  rw [MeasureTheory.integral_sub]
  · ring
  · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      (hf.comp (by fun_prop)).continuousOn
  · exact ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      (hg.comp (by fun_prop)).continuousOn

/-- The mean-free projection `Q_uψ = ψ − m_u(ψ)` is additive in the state. -/
private lemma Qfree_add {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {f g : ℝ³ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Work.BoseKinLoc.Qfree ℓ u (fun z => f z + g z)
      = fun z => Work.BoseKinLoc.Qfree ℓ u f z + Work.BoseKinLoc.Qfree ℓ u g z := by
  funext z
  simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ]
  rw [bsMean_add hℓ u hf hg]
  ring

/-- The mean-free projection `Q_uψ = ψ − m_u(ψ)` is subtractive in the state. -/
private lemma Qfree_sub {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {f g : ℝ³ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Work.BoseKinLoc.Qfree ℓ u (fun z => f z - g z)
      = fun z => Work.BoseKinLoc.Qfree ℓ u f z - Work.BoseKinLoc.Qfree ℓ u g z := by
  funext z
  simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ]
  rw [bsMean_sub hℓ u hf hg]
  ring

/-! ## 2. Linearity of the localised (windowed) state -/

/-- The localised complex state `↑(θ_u·Q_uψ)` is additive in `ψ`. -/
private lemma boxState_add (ℓ : ℝ) (u : ℝ³) {f g : ℝ³ → ℝ}
    (hQ : Work.BoseKinLoc.Qfree ℓ u (fun z => f z + g z)
      = fun z => Work.BoseKinLoc.Qfree ℓ u f z + Work.BoseKinLoc.Qfree ℓ u g z) :
    Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z + g z)
      = fun z => Work.BoseKinLoc.Kinetic.boxState ℓ u f z
          + Work.BoseKinLoc.Kinetic.boxState ℓ u g z := by
  funext z
  simp only [Work.BoseKinLoc.Kinetic.boxState]
  rw [congrFun hQ z]
  push_cast
  ring

/-- The localised complex state `↑(θ_u·Q_uψ)` is subtractive in `ψ`. -/
private lemma boxState_sub (ℓ : ℝ) (u : ℝ³) {f g : ℝ³ → ℝ}
    (hQ : Work.BoseKinLoc.Qfree ℓ u (fun z => f z - g z)
      = fun z => Work.BoseKinLoc.Qfree ℓ u f z - Work.BoseKinLoc.Qfree ℓ u g z) :
    Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z - g z)
      = fun z => Work.BoseKinLoc.Kinetic.boxState ℓ u f z
          - Work.BoseKinLoc.Kinetic.boxState ℓ u g z := by
  funext z
  simp only [Work.BoseKinLoc.Kinetic.boxState]
  rw [congrFun hQ z]
  push_cast
  ring

/-! ## 3. Linearity of the `p`-convention Fourier transform -/

/-- `kinFT` is additive in its (integrable) argument. -/
private lemma kinFT_add {g h : ℝ³ → ℂ} (hg : Integrable g) (hh : Integrable h) (p : ℝ³) :
    Submission.BoseGases.kinFT (fun z => g z + h z) p
      = Submission.BoseGases.kinFT g p + Submission.BoseGases.kinFT h p := by
  have hfun : (fun z : ℝ³ => g z + h z) = g - (-1 : ℂ) • h := by
    funext z; simp
  rw [hfun]
  simpa using Work.OneBodyKin.kinFT_sub_smul hg hh (-1 : ℂ) p

/-- `kinFT` is subtractive in its (integrable) argument. -/
private lemma kinFT_sub {g h : ℝ³ → ℂ} (hg : Integrable g) (hh : Integrable h) (p : ℝ³) :
    Submission.BoseGases.kinFT (fun z => g z - h z) p
      = Submission.BoseGases.kinFT g p - Submission.BoseGases.kinFT h p := by
  have hfun : (fun z : ℝ³ => g z - h z) = g - (1 : ℂ) • h := by
    funext z; simp
  rw [hfun]
  simpa using Work.OneBodyKin.kinFT_sub_smul hg hh (1 : ℂ) p

/-! ## 4. Integrability of the cut-off integrand -/

/-- For a smooth one-body state `ψ` the `momForm` integrand
`p ↦ momProj ℓ d p · ‖kinFT (boxState ℓ u ψ) p‖²` is integrable: the localised state is in
`L¹ ∩ L²` (`boxState_memLp`), so its squared Fourier transform is integrable
(`kinFT_sq_of_memLp`), and `momProj ≤ 1` is a bounded measurable multiplier. -/
private lemma integrable_momProj_kinFT_boxState {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : ℝ³)
    {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Integrable (fun p : ℝ³ => Work.BoseKinLoc.momProj ℓ d p *
      ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u ψ) p‖ ^ 2) := by
  have hml := Work.BoseKinLoc.Kinetic.boxState_memLp (ℓ := ℓ) hℓ u hψ
  have hbase : Integrable (fun p : ℝ³ =>
      ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u ψ) p‖ ^ 2) :=
    (Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp hml.1 hml.2).1
  refine Integrable.mono' hbase ?_ ?_
  · have hm : Measurable (fun p : ℝ³ => Work.BoseKinLoc.momProj ℓ d p) := by
      unfold Work.BoseKinLoc.momProj
      exact Measurable.ite
        (measurableSet_lt measurable_const continuous_norm.measurable)
        measurable_const measurable_const
    exact hm.aestronglyMeasurable.mul hbase.aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Work.BoseKinLoc.Kinetic.momProj_nonneg ℓ d p) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (Work.BoseKinLoc.Kinetic.momProj_le_one ℓ d p)

/-! ## 5. The parallelogram identity -/

theorem momForm_parallelogram {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Work.BoseKinLoc.momForm ℓ d u (fun z => f z + g z) + Work.BoseKinLoc.momForm ℓ d u (fun z => f z - g z) = 2 * Work.BoseKinLoc.momForm ℓ d u f + 2 * Work.BoseKinLoc.momForm ℓ d u g := by
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous g := hg.continuous
  have hQadd := Qfree_add hℓ u hfc hgc
  have hQsub := Qfree_sub hℓ u hfc hgc
  have hBSadd := boxState_add ℓ u hQadd
  have hBSsub := boxState_sub ℓ u hQsub
  have hmlF := Work.BoseKinLoc.Kinetic.boxState_memLp (ℓ := ℓ) hℓ u hf
  have hmlG := Work.BoseKinLoc.Kinetic.boxState_memLp (ℓ := ℓ) hℓ u hg
  have hintF : Integrable (Work.BoseKinLoc.Kinetic.boxState ℓ u f) :=
    memLp_one_iff_integrable.mp hmlF.1
  have hintG : Integrable (Work.BoseKinLoc.Kinetic.boxState ℓ u g) :=
    memLp_one_iff_integrable.mp hmlG.1
  have hKadd : ∀ p : ℝ³,
      Submission.BoseGases.kinFT
          (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z + g z)) p
        = Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u f) p
          + Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u g) p := by
    intro p
    rw [hBSadd]
    exact kinFT_add hintF hintG p
  have hKsub : ∀ p : ℝ³,
      Submission.BoseGases.kinFT
          (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z - g z)) p
        = Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u f) p
          - Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u g) p := by
    intro p
    rw [hBSsub]
    exact kinFT_sub hintF hintG p
  have hInt1 : Integrable (fun p : ℝ³ => Work.BoseKinLoc.momProj ℓ d p *
      ‖Submission.BoseGases.kinFT
        (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z + g z)) p‖ ^ 2) :=
    integrable_momProj_kinFT_boxState hℓ u (hf.add hg)
  have hInt2 : Integrable (fun p : ℝ³ => Work.BoseKinLoc.momProj ℓ d p *
      ‖Submission.BoseGases.kinFT
        (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z - g z)) p‖ ^ 2) :=
    integrable_momProj_kinFT_boxState hℓ u (hf.sub hg)
  have hInt3 : Integrable (fun p : ℝ³ => Work.BoseKinLoc.momProj ℓ d p *
      ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u f) p‖ ^ 2) :=
    integrable_momProj_kinFT_boxState hℓ u hf
  have hInt4 : Integrable (fun p : ℝ³ => Work.BoseKinLoc.momProj ℓ d p *
      ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u g) p‖ ^ 2) :=
    integrable_momProj_kinFT_boxState hℓ u hg
  -- the integrands satisfy the parallelogram identity pointwise
  have hpoint : ∀ p : ℝ³,
      Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT
            (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z + g z)) p‖ ^ 2
        + Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT
            (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z - g z)) p‖ ^ 2
      = 2 * (Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u f) p‖ ^ 2)
        + 2 * (Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u g) p‖ ^ 2) := by
    intro p
    rw [hKadd p, hKsub p, ← mul_add, parallelogram_law_with_norm ℂ]
    ring
  -- the four `p`-integrals
  have hI :
      (∫ p : ℝ³, Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT
            (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z + g z)) p‖ ^ 2)
        + (∫ p : ℝ³, Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT
            (Work.BoseKinLoc.Kinetic.boxState ℓ u (fun z => f z - g z)) p‖ ^ 2)
      = 2 * (∫ p : ℝ³, Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u f) p‖ ^ 2)
        + 2 * (∫ p : ℝ³, Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ u g) p‖ ^ 2) := by
    rw [(MeasureTheory.integral_add hInt1 hInt2).symm]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [MeasureTheory.integral_add (hInt3.const_mul 2) (hInt4.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [Work.BoseKinLoc.Kinetic.momForm_eq_boxState ℓ d u (fun z => f z + g z),
    Work.BoseKinLoc.Kinetic.momForm_eq_boxState ℓ d u (fun z => f z - g z),
    Work.BoseKinLoc.Kinetic.momForm_eq_boxState ℓ d u f,
    Work.BoseKinLoc.Kinetic.momForm_eq_boxState ℓ d u g]
  rw [← mul_add, hI]
  ring

end Work.BoseFixB2.Polar
