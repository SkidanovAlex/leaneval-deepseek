import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.fderiv_dirichletSlice_eq_zero_of_notMem_acube
import Submission.Work.BoseBoxFock.PCFU.taperSlotOne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
open scoped ContDiff Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.style.haveILetI false

theorem chAimg_dirBounded {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i : Fin (m + 1)}
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ∃ E : ℝ, 0 ≤ E ∧
      (∀ r ∈ Submission.BoseGases.abox m ℓ,
        Work.BoseBoxFock.PCFU.slotDir (fun w : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiScale ℓ w * Φ (Submission.BoseGases.kcInsN m i (w, r))) ≤ E) ∧
      MeasureTheory.AEStronglyMeasurable (fun r : Submission.BoseGases.X m =>
        Work.BoseBoxFock.PCFU.slotDir (fun w : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiScale ℓ w * Φ (Submission.BoseGases.kcInsN m i (w, r))))
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
          (Submission.BoseGases.abox m ℓ)) := by
  classical
  -- The slot-`i` windowed state on the `(m+1)`-particle box.
  set A : Submission.BoseGases.X (m + 1) → ℝ :=
    fun z => Submission.BoseGases.chiScale ℓ (z i) * Φ z with hA
  have hAcd : ContDiff ℝ ∞ A := by
    rw [hA]
    exact ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).comp (by fun_prop)).mul hΦ
  -- the uniform bound of `exists_bound_dirichlet_integrand` on the `(m+1)`-box
  obtain ⟨C, hC⟩ :=
    Work.SmallBoxBridge.Fourier.exists_bound_dirichlet_integrand (n := m) (s := ℓ) hℓ hΦ i
  -- the fibre derivative in the `i`-th slot equals the `kcDir`-directional derivative
  have hkey : ∀ (r : Submission.BoseGases.X m) (y : E3) (k : Fin 3),
      fderiv ℝ (fun w : E3 => Submission.BoseGases.chiScale ℓ w *
        Φ (Submission.BoseGases.kcInsN m i (w, r))) y (EuclideanSpace.single k (1 : ℝ))
      = fderiv ℝ A (Submission.BoseGases.kcInsN m i (y, r))
          (Submission.BoseGases.kcDir (m + 1) i k) := by
    intro r y k
    rw [hA]
    rw [Work.SmallBoxBridge.Fourier.fderiv_slot_eq_fibre (n := m) (s := ℓ) hℓ hΦ i r y k,
      Submission.BoseGases.kcStdBasis]
  -- inserting a cube point into a box configuration stays in the box
  have hmem : ∀ (r : Submission.BoseGases.X m) (y : E3),
      r ∈ Submission.BoseGases.abox m ℓ → y ∈ Submission.BoseGases.acube ℓ →
      Submission.BoseGases.kcInsN m i (y, r) ∈ Submission.BoseGases.abox (m + 1) ℓ := by
    intro r y hr hy j
    by_cases hj : j = i
    · subst hj
      rw [Submission.BoseGases.kc_insN_apply_same]; exact hy
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      rw [Submission.BoseGases.kc_insN_apply_succ]; exact hr j'
  refine ⟨max C 0 * (MeasureTheory.volume (Submission.BoseGases.acube ℓ)).toReal,
    mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg, ?_, ?_⟩
  · -- ## the uniform bound on `abox m ℓ`
    intro r hr
    have hbound : ∀ y : E3,
        (∑ k : Fin 3, ‖fderiv ℝ (fun w : E3 => Submission.BoseGases.chiScale ℓ w *
          Φ (Submission.BoseGases.kcInsN m i (w, r))) y
            (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) ≤ max C 0 := by
      intro y
      by_cases hy : y ∈ Submission.BoseGases.acube ℓ
      · calc (∑ k : Fin 3, ‖fderiv ℝ (fun w : E3 => Submission.BoseGases.chiScale ℓ w *
              Φ (Submission.BoseGases.kcInsN m i (w, r))) y
                (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
            = ∑ k : Fin 3, (fderiv ℝ A (Submission.BoseGases.kcInsN m i (y, r))
                (Submission.BoseGases.kcDir (m + 1) i k)) ^ 2 := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [hkey r y k, Real.norm_eq_abs, sq_abs]
          _ ≤ max C 0 :=
              le_trans (by simpa only [hA] using hC _ (hmem r y hr hy)) (le_max_left _ _)
      · have hz := fderiv_dirichletSlice_eq_zero_of_notMem_acube (n := m) (Φ := Φ) i hℓ hy r
        rw [hz]; simp
    have hsupp : ∀ y : E3, y ∉ Submission.BoseGases.acube ℓ →
        (∑ k : Fin 3, ‖fderiv ℝ (fun w : E3 => Submission.BoseGases.chiScale ℓ w *
          Φ (Submission.BoseGases.kcInsN m i (w, r))) y
            (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) = 0 := by
      intro y hy
      have hz := fderiv_dirichletSlice_eq_zero_of_notMem_acube (n := m) (Φ := Φ) i hℓ hy r
      rw [hz]; simp
    haveI : IsFiniteMeasure
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ)) :=
      ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]
          exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
    have haesm : AEStronglyMeasurable (fun y : E3 =>
        ∑ k : Fin 3, ‖fderiv ℝ (fun w : E3 => Submission.BoseGases.chiScale ℓ w *
          Φ (Submission.BoseGases.kcInsN m i (w, r))) y
            (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ)) := by
      have hfib : ContDiff ℝ ∞ (fun y : E3 => Submission.BoseGases.chiScale ℓ y *
          Φ (Submission.BoseGases.kcInsN m i (y, r))) :=
        (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).mul
          (hΦ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r))
      have hc : Continuous (fun y : E3 => ∑ k : Fin 3,
          ‖fderiv ℝ (fun w : E3 => Submission.BoseGases.chiScale ℓ w *
            Φ (Submission.BoseGases.kcInsN m i (w, r))) y
              (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) :=
        continuous_finsetSum _ (fun k _ =>
          (((hfib.continuous_fderiv (by simp)).clm_apply continuous_const).norm).pow 2)
      exact hc.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self
    have hint : Integrable (fun y : E3 =>
        ∑ k : Fin 3, ‖fderiv ℝ (fun w : E3 => Submission.BoseGases.chiScale ℓ w *
          Φ (Submission.BoseGases.kcInsN m i (w, r))) y
            (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ)) :=
      Integrable.mono' (integrable_const (max C 0)) haesm
        (Filter.Eventually.of_forall (fun y => by
          rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
          exact hbound y))
    calc Work.BoseBoxFock.PCFU.slotDir (fun w : E3 => Submission.BoseGases.chiScale ℓ w *
          Φ (Submission.BoseGases.kcInsN m i (w, r)))
        = ∫ y : E3, (∑ k : Fin 3, ‖fderiv ℝ (fun w : E3 => Submission.BoseGases.chiScale ℓ w *
            Φ (Submission.BoseGases.kcInsN m i (w, r))) y
              (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) := rfl
      _ = ∫ y in Submission.BoseGases.acube ℓ,
            (∑ k : Fin 3, ‖fderiv ℝ (fun w : E3 => Submission.BoseGases.chiScale ℓ w *
              Φ (Submission.BoseGases.kcInsN m i (w, r))) y
                (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
      _ ≤ ∫ _y, max C 0 ∂((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
            (Submission.BoseGases.acube ℓ)) :=
            integral_mono_ae hint (integrable_const _) (Filter.Eventually.of_forall hbound)
      _ = (MeasureTheory.volume (Submission.BoseGases.acube ℓ)).toReal * max C 0 := by
            rw [integral_const, MeasureTheory.Measure.real_def,
              MeasureTheory.Measure.restrict_apply_univ]
            simp
      _ = max C 0 * (MeasureTheory.volume (Submission.BoseGases.acube ℓ)).toReal :=
            mul_comm _ _
  · -- ## a.e. strong measurability
    have hkc : Continuous (fun p : Submission.BoseGases.X m × E3 =>
        Submission.BoseGases.kcInsN m i (p.2, p.1)) :=
      (Submission.BoseGases.kcInsN_cont (n := m) i).comp continuous_swap
    have hfdcont : Continuous (fun z : Submission.BoseGases.X (m + 1) => fderiv ℝ A z) :=
      hAcd.continuous_fderiv (by simp)
    have hGcont : Continuous (fun p : Submission.BoseGases.X m × E3 =>
        ∑ k : Fin 3, (fderiv ℝ A (Submission.BoseGases.kcInsN m i (p.2, p.1))
          (Submission.BoseGases.kcDir (m + 1) i k)) ^ 2) :=
      continuous_finsetSum Finset.univ
        (fun k _ => (((hfdcont.comp hkc).clm_apply continuous_const)).pow 2)
    have hFub := AEStronglyMeasurable.integral_prod_right'
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m ℓ))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3))
      (f := fun p : Submission.BoseGases.X m × E3 =>
        ∑ k : Fin 3, (fderiv ℝ A (Submission.BoseGases.kcInsN m i (p.2, p.1))
          (Submission.BoseGases.kcDir (m + 1) i k)) ^ 2)
      (Continuous.aestronglyMeasurable
        (μ := ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
          (Submission.BoseGases.abox m ℓ)).prod (MeasureTheory.volume : MeasureTheory.Measure E3))
        hGcont)
    refine hFub.congr (Filter.Eventually.of_forall (fun r => ?_))
    simp only [Work.BoseBoxFock.PCFU.slotDir]
    apply integral_congr_ae
    filter_upwards with y
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hkey r y k, Real.norm_eq_abs, sq_abs]

end Work.BoseBoxFock.PCFU
