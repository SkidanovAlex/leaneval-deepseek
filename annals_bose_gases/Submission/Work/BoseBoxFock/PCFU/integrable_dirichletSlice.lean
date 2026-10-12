import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Fourier.T0Form_slot_eq_dirichlet
import Submission.Work.SmallBoxBridge.Fourier.peel_slot_abox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the one-slot Dirichlet slice

The `i`-th slot windowed Dirichlet integrand of a smooth state `Φ`,

    p ↦ ∑_k ‖∂_k (χ_ℓ · Φ ∘ kcInsN n i) (p.1)‖²,

is integrable for the product of the (restricted) Lebesgue measures on the one-particle cube
`acube ℓ` and the `n`-particle box `abox n ℓ`.

The two inputs are the two halves of `Work.SmallBoxBridge.Fourier.exists_bound_dirichlet_integrand`
and `Work.SmallBoxBridge.Fourier.fderiv_slot_eq_fibre`:

* the integrand is jointly continuous, hence a.e. strongly measurable (it is the composition of
  the continuous map `p ↦ fderiv ℝ (χ_ℓ (· i) Φ) (kcInsN n i p)` with `kcInsN`), and
* on the box it is bounded by the uniform constant `C` supplied by the compactness of
  `abox (n+1) ℓ` (`kcInsN n i` maps `acube ℓ × abox n ℓ` into `abox (n+1) ℓ`).

Since the product of the two restricted measures is a finite measure, `Integrable.mono'` applies.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

set_option linter.style.haveILetI false

theorem integrable_dirichletSlice {n : ℕ} (i : Fin (n + 1)) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      ∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, p.2))) p.1
        (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) := by
  classical
  -- the product of the two restricted measures is a finite measure
  haveI : IsFiniteMeasure
      (((MeasureTheory.volume :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) := by
    rw [MeasureTheory.isFiniteMeasure_iff, MeasureTheory.Measure.prod_apply MeasurableSet.univ]
    simp only [Set.preimage_univ]
    rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
      MeasureTheory.Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (Submission.BoseGases.abox_lt_top n ℓ (le_of_lt hℓ))
      (Submission.BoseGases.acube_lt_top ℓ (le_of_lt hℓ))
  -- the uniform bound on the windowed slot Dirichlet integrand over the `(n+1)`-box
  obtain ⟨C, hC⟩ :=
    Work.SmallBoxBridge.Fourier.exists_bound_dirichlet_integrand (n := n) (s := ℓ) hℓ hΦ i
  -- joint continuity of the `kcDir`-form of the integrand
  have hslot : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X (n + 1) =>
      Submission.BoseGases.chiScale ℓ (x i) * Φ x) :=
    ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).comp (by fun_prop)).mul hΦ
  have hfdcont : Continuous (fun x : Submission.BoseGases.X (n + 1) =>
      fderiv ℝ (fun x : Submission.BoseGases.X (n + 1) =>
        Submission.BoseGases.chiScale ℓ (x i) * Φ x) x) :=
    hslot.continuous_fderiv (by simp)
  have hφcont : Continuous (fun x : Submission.BoseGases.X (n + 1) => ∑ k : Fin 3,
      (fderiv ℝ (fun x : Submission.BoseGases.X (n + 1) =>
        Submission.BoseGases.chiScale ℓ (x i) * Φ x) x
        (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2) :=
    continuous_finsetSum _ (fun k _ => ((hfdcont.clm_apply continuous_const).pow 2))
  have hGcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      ∑ k : Fin 3, (fderiv ℝ (fun x : Submission.BoseGases.X (n + 1) =>
          Submission.BoseGases.chiScale ℓ (x i) * Φ x)
        (Submission.BoseGases.kcInsN n i (p.1, p.2))
        (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2) :=
    hφcont.comp (Submission.BoseGases.kcInsN_cont i)
  -- the pointwise identification of the two forms of the integrand
  have hpt : ∀ p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
      (∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, p.2))) p.1
        (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
      = ∑ k : Fin 3,
      (fderiv ℝ (fun x : Submission.BoseGases.X (n + 1) =>
          Submission.BoseGases.chiScale ℓ (x i) * Φ x)
        (Submission.BoseGases.kcInsN n i (p.1, p.2))
        (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2 := by
    intro p
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Work.SmallBoxBridge.Fourier.fderiv_slot_eq_fibre (n := n) (s := ℓ) hℓ hΦ i p.2 p.1 k,
      Submission.BoseGases.kcStdBasis, Real.norm_eq_abs, sq_abs]
  -- `kcInsN` maps the pair of boxes into the `(n+1)`-box
  have hmem : ∀ p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
      p.1 ∈ Submission.BoseGases.acube ℓ → p.2 ∈ Submission.BoseGases.abox n ℓ →
      Submission.BoseGases.kcInsN n i (p.1, p.2) ∈ Submission.BoseGases.abox (n + 1) ℓ := by
    intro p hy hr j
    by_cases hj : j = i
    · subst hj
      rw [Submission.BoseGases.kc_insN_apply_same]
      exact hy
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      rw [Submission.BoseGases.kc_insN_apply_succ]
      exact hr j'
  -- the a.e. bound of the integrand by the constant `max C 0`
  have hbnd : ∀ᵐ p ∂(((MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))),
      ‖(∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, p.2))) p.1
        (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)‖ ≤ max C 0 := by
    rw [MeasureTheory.Measure.prod_restrict,
      MeasureTheory.ae_restrict_iff' (MeasurableSet.prod (Submission.BoseGases.acube_measurable ℓ)
        (Submission.BoseGases.abox_measurable n ℓ))]
    refine Filter.Eventually.of_forall (fun p hp => ?_)
    rw [hpt p, Real.norm_of_nonneg (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
    exact le_trans (hC _ (hmem p hp.1 hp.2)) (le_max_left _ _)
  exact Integrable.mono' (integrable_const (max C 0))
    (hGcont.stronglyMeasurable.aestronglyMeasurable.congr
      (Filter.Eventually.of_forall (fun p => (hpt p).symm)))
    hbnd

end Work.BoseBoxFock.PCFU
