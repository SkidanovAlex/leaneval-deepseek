import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.dirichletPeel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- The `i`-th slot windowed state `x ↦ χ_ℓ(x i)·Φ x`. -/
private noncomputable abbrev slotFun {n : ℕ} (ℓ : ℝ) (i : Fin (n + 1))
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) : Submission.BoseGases.X (n + 1) → ℝ :=
  fun x => Submission.BoseGases.chiScale ℓ (x i) * Φ x

/-- For a real-valued functional, `‖L (e_k)‖² = (L (kcStdBasis k))²`. -/
private lemma kcStdBasis_sq_eq (L : E3 →L[ℝ] ℝ) (k : Fin 3) :
    (L (Submission.BoseGases.kcStdBasis k)) ^ 2
      = ‖L (EuclideanSpace.single k (1 : ℝ))‖ ^ 2 := by
  rw [show Submission.BoseGases.kcStdBasis k = EuclideanSpace.single k (1 : ℝ) from rfl,
    Real.norm_eq_abs, sq_abs]

/-- The support shrink in the exact `‖·‖²`/`single` shape of the target. -/
private lemma shrink {s : ℝ} (hs : 0 < s) {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (∫ y : E3, ∑ k : Fin 3,
        ‖fderiv ℝ (fun z : E3 => Submission.BoseGases.chiScale s z * ψ z) y
          (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
      = ∫ z in Submission.BoseGases.acube s, ∑ k : Fin 3,
          (fderiv ℝ (fun w : E3 => Submission.BoseGases.chiScale s w * ψ w) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  rw [← Work.SmallBoxBridge.Fourier.energy_support_shrink hs ψ hψ]
  apply integral_congr_ae
  filter_upwards with y
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact (kcStdBasis_sq_eq (fderiv ℝ (fun w : E3 => Submission.BoseGases.chiScale s w * ψ w) y) k).symm

theorem dirichletSliceBound {n : ℕ} (i : Fin (n + 1)) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ r ∈ Submission.BoseGases.abox n ℓ,
        (∫ y : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3,
          ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) y
            (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) ≤ C) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun r : Submission.BoseGases.X n =>
          ∫ y : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3,
            ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
              Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) y
              (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) := by
  classical
  -- the uniform bound on the `acube`-integral
  obtain ⟨C₀, hC₀⟩ := Work.SmallBoxBridge.Fourier.fibre_energy_bound (n := n) (s := ℓ) hℓ hΦ i
  -- the pointwise identification of the whole-space integral with the `acube` integral
  have hkey : ∀ r : Submission.BoseGases.X n,
      (∫ y : E3, ∑ k : Fin 3,
        ‖fderiv ℝ (fun z : E3 =>
          Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) y
          (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
      = ∫ z in Submission.BoseGases.acube ℓ, ∑ k : Fin 3,
          (fderiv ℝ (fun w : E3 =>
            Submission.BoseGases.chiScale ℓ w * Φ (Submission.BoseGases.kcInsN n i (w, r))) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
    intro r
    have hψ : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : E3 => Φ (Submission.BoseGases.kcInsN n i (z, r))) :=
      hΦ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r)
    have h := shrink (s := ℓ) hℓ
      (ψ := fun z : E3 => Φ (Submission.BoseGases.kcInsN n i (z, r))) hψ
    simpa using h
  have hbound : ∀ r ∈ Submission.BoseGases.abox n ℓ,
      (∫ y : E3, ∑ k : Fin 3,
        ‖fderiv ℝ (fun z : E3 =>
          Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) y
          (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) ≤ max C₀ 0 := by
    intro r hr
    rw [hkey r]
    exact le_trans (hC₀ r hr) (le_max_left _ _)
  -- joint continuity of the fibre Dirichlet integrand
  have hslot : ContDiff ℝ (⊤ : ℕ∞) (slotFun ℓ i Φ) :=
    ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).comp (by fun_prop)).mul hΦ
  have hfdcont : Continuous (fun x : Submission.BoseGases.X (n + 1) =>
      fderiv ℝ (slotFun ℓ i Φ) x) := hslot.continuous_fderiv (by simp)
  have hφcont : Continuous (fun x : Submission.BoseGases.X (n + 1) => ∑ k : Fin 3,
      (fderiv ℝ (slotFun ℓ i Φ) x (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2) :=
    continuous_finsetSum _ (fun k _ => ((hfdcont.clm_apply continuous_const).pow 2))
  have hjoint : Continuous (fun q : Submission.BoseGases.X n × E3 => ∑ k : Fin 3,
      (fderiv ℝ (slotFun ℓ i Φ) (Submission.BoseGases.kcInsN n i (q.2, q.1))
        (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2) :=
    hφcont.comp ((Submission.BoseGases.kcInsN_cont i).comp continuous_swap)
  -- the joint integrand in the target's shape is a.e. strongly measurable
  have hGAE : AEStronglyMeasurable (fun q : Submission.BoseGases.X n × E3 => ∑ k : Fin 3,
      ‖fderiv ℝ (fun z : E3 => Submission.BoseGases.chiScale ℓ z *
          Φ (Submission.BoseGases.kcInsN n i (z, q.1))) q.2
        (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
      (((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)).prod MeasureTheory.volume) := by
    refine hjoint.aestronglyMeasurable.congr ?_
    filter_upwards with q
    obtain ⟨r, y⟩ := q
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← kcStdBasis_sq_eq (fderiv ℝ (fun z : E3 => Submission.BoseGases.chiScale ℓ z *
      Φ (Submission.BoseGases.kcInsN n i (z, r))) y) k]
    exact congrArg (fun t : ℝ => t ^ 2)
      (Work.SmallBoxBridge.Fourier.fderiv_slot_eq_fibre hℓ hΦ i r y k)
  refine ⟨max C₀ 0, le_max_right _ _, hbound, ?_⟩
  exact hGAE.integral_prod_right'

end Work.BoseBoxFock.PCFU
