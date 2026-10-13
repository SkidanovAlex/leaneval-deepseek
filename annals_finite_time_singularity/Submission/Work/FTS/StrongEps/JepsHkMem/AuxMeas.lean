/-
Copyright: work module for the Elgindi finite-time singularity project.

# `JepsHkMem/AuxMeas` — measurability helpers for `HkMem_Jeps`

The measure-theoretic plumbing of `Work.FTS.StrongEps.HkMem_Jeps`: the two restricted measures
`volume.restrict Iz` and `volume.restrict Iθ` agree with the ones on the open half-line and the
open interval, the open quadrant is conull for their product, the two weights of `HkIntegrand`
are continuous there, and the (finitely many) slots of `HkIntegrand α k (Jeps ρ ε f)` are a.e.
strongly measurable on the product — both jointly and slicewise.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.HkSqAux.Chain
import Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

namespace JepsHkMem

theorem restrict_Iz_eq : (MeasureTheory.volume.restrict Work.Spaces.Iz)
    = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show (Work.Spaces.Iz : Set ℝ) = Set.Ici 0 from rfl, Set.Ici_sdiff_Ioi, Set.Icc_self]
    exact measure_singleton 0
  · rw [show (Work.Spaces.Iz : Set ℝ) = Set.Ici 0 from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioi_subset_Ici_self, measure_empty]

theorem restrict_Iθ_eq : (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    = MeasureTheory.volume.restrict (Set.Ioo 0 (π/2)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show (Work.Spaces.Iθ : Set ℝ) = Set.Icc 0 (π/2) from rfl,
      Set.Icc_sdiff_Ioo_same (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π/2)]
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton 0) (measure_singleton _)
  · rw [show (Work.Spaces.Iθ : Set ℝ) = Set.Icc 0 (π/2) from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]

/-- The complement of the open quadrant is null for the product of the two restricted
(closed) measures. -/
theorem measure_quad_compl :
    ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
      (MeasureTheory.volume.restrict (Set.Ioo 0 (π/2)))) Quadᶜ = 0 := by
  rw [Measure.prod_restrict, Measure.restrict_apply isOpen_Quad.measurableSet.compl]
  change (MeasureTheory.volume.prod MeasureTheory.volume) (Quadᶜ ∩ Quad) = 0
  rw [Set.compl_inter_self, measure_empty]

theorem ae_mem_Quad_prod' :
    ∀ᵐ q ∂((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
      (MeasureTheory.volume.restrict (Set.Ioo 0 (π/2)))), q ∈ Quad := by
  simpa using compl_mem_ae_iff.mpr measure_quad_compl

theorem ae_mem_Quad_prod :
    ∀ᵐ q ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), q ∈ Quad := by
  rw [restrict_Iz_eq, restrict_Iθ_eq]
  exact ae_mem_Quad_prod'

/-! ## Continuity of the two weights on the quadrant -/

theorem continuousOn_wdiv :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.w q.1
      / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2)) Quad := by
  have hsinpos : ∀ p ∈ Quad, 0 < Real.sin (2 * p.2) := fun p hp =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Quad := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Quad :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  exact hw.div hsinpow (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))

theorem continuousOn_Wt (α : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2) Quad := by
  have hsinpos : ∀ p ∈ Quad, 0 < Real.sin (2 * p.2) := fun p hp =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Quad := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) Quad :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2)
      = fun q : ℝ × ℝ => Work.Spaces.w q.1 * (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext q; rfl
  rw [hfun]
  exact hw.mul hsinpow

/-! ## Almost-everywhere strong measurability of the mollified slots -/

theorem aestronglyMeasurable_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (fun q : ℝ × ℝ => g q.1 q.2) Quad) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => Jeps ρ ε g q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [restrict_Iz_eq, restrict_Iθ_eq, ← Measure.restrict_eq_self_of_ae_mem ae_mem_Quad_prod']
  exact (JepsHkMem.continuousOn_Jeps hρ hε hg).aestronglyMeasurable isOpen_Quad.measurableSet

theorem aestronglyMeasurable_Jeps_slice' {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (fun q : ℝ × ℝ => g q.1 q.2) Quad)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => Jeps ρ ε g z θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (π/2))) := by
  have hmap : ContinuousOn (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (π/2)) := by fun_prop
  have hcomp : ContinuousOn (fun θ : ℝ => Jeps ρ ε g z θ) (Set.Ioo 0 (π/2)) :=
    (JepsHkMem.continuousOn_Jeps hρ hε hg).comp hmap (fun θ hθ => ⟨hz, hθ⟩)
  exact hcomp.aestronglyMeasurable isOpen_Ioo.measurableSet

theorem aestronglyMeasurable_Jeps_slice {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (fun q : ℝ × ℝ => g q.1 q.2) Quad)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => Jeps ρ ε g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq]
  exact aestronglyMeasurable_Jeps_slice' hρ hε hg hz

/-- The continuity on the quadrant of the mixed derivatives of a profile that is `C^n` there for
every `n`. -/
theorem continuousOn_mixed_of_smooth {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (j i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2) Quad :=
  (Work.FTS.LocData.contDiffOn_mixed isOpen_Quad (contDiffOn_infty.mpr hsm) j i).continuousOn

theorem continuousOn_DzIter_of_smooth {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.DzIter i f q.1 q.2) Quad :=
  (Work.FTS.LocData.contDiffOn_DzIter isOpen_Quad (contDiffOn_infty.mpr hsm) i).continuousOn

/-- The mollified mixed slots are a.e. strongly measurable on the product of the two closed
intervals. -/
theorem aestronglyMeasurable_mixed_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (j i : ℕ) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => Work.Spaces.mixed j i (Jeps ρ ε f) q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine (aestronglyMeasurable_Jeps hρ hε (continuousOn_mixed_of_smooth hsm j i)).congr ?_
  filter_upwards [ae_mem_Quad_prod] with q hq
  exact (mixed_Jeps ρ hρ hε hsm hq.1 hq.2 j i).symm

theorem aestronglyMeasurable_DzIter_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (i : ℕ) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => Work.Spaces.DzIter i (Jeps ρ ε f) q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have h := aestronglyMeasurable_mixed_Jeps hρ hε hsm i 0
  simpa only [Work.Spaces.mixed_zero_right] using h

theorem aestronglyMeasurable_mixed_Jeps_slice {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z : ℝ} (hz : 0 < z) (j i : ℕ) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.mixed j i (Jeps ρ ε f) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq]
  refine (aestronglyMeasurable_Jeps_slice' hρ hε (continuousOn_mixed_of_smooth hsm j i) hz).congr ?_
  filter_upwards [self_mem_ae_restrict isOpen_Ioo.measurableSet] with θ hθ
  exact (mixed_Jeps ρ hρ hε hsm hz hθ j i).symm

theorem aestronglyMeasurable_DzIter_Jeps_slice {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z : ℝ} (hz : 0 < z) (i : ℕ) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter i (Jeps ρ ε f) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h := aestronglyMeasurable_mixed_Jeps_slice hρ hε hsm hz i 0
  simpa only [Work.Spaces.mixed_zero_right] using h

/-! ## Almost-everywhere strong measurability of the mollified `H^k`-integrand -/

theorem aestronglyMeasurable_wdiv_slice (z : ℝ) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq]
  exact (continuousOn_const.div
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.StrongEps.sin_two_pos hθ))))
    (fun θ hθ => ne_of_gt (Real.rpow_pos_of_pos (Work.FTS.StrongEps.sin_two_pos hθ) _))
      |>.aestronglyMeasurable isOpen_Ioo.measurableSet)

theorem aestronglyMeasurable_Wt_slice (α z : ℝ) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.Wt α z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq]
  have hfun : (fun θ : ℝ => Work.Spaces.Wt α z θ)
      = fun θ : ℝ => Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext θ; rfl
  rw [hfun]
  exact (continuousOn_const.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.StrongEps.sin_two_pos hθ)))))
    |>.aestronglyMeasurable isOpen_Ioo.measurableSet

theorem aestronglyMeasurable_HkIntegrand_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ)
    {α : ℝ} {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k (Jeps ρ ε f) q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hDz : ∀ i : ℕ, AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.DzIter i (Jeps ρ ε f) q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    fun i => aestronglyMeasurable_DzIter_Jeps hρ hε hsm i
  have hMx : ∀ j i : ℕ, AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.mixed j i (Jeps ρ ε f) q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    fun j i => aestronglyMeasurable_mixed_Jeps hρ hε hsm j i
  have hW : AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.w q.1 / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [restrict_Iz_eq, restrict_Iθ_eq]
    rw [← Measure.restrict_eq_self_of_ae_mem ae_mem_Quad_prod',
      ← Measure.restrict_eq_self_of_ae_mem ae_mem_Quad_prod']
    exact continuousOn_wdiv.aestronglyMeasurable isOpen_Quad.measurableSet
  have hWt : AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [restrict_Iz_eq, restrict_Iθ_eq]
    rw [← Measure.restrict_eq_self_of_ae_mem ae_mem_Quad_prod',
      ← Measure.restrict_eq_self_of_ae_mem ae_mem_Quad_prod']
    exact (continuousOn_Wt α).aestronglyMeasurable isOpen_Quad.measurableSet
  have hfun : (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k (Jeps ρ ε f) q.1 q.2)
      = (∑ i ∈ Finset.range (k + 1), fun q : ℝ × ℝ =>
            (Work.Spaces.DzIter i (Jeps ρ ε f) q.1 q.2
              * (Work.Spaces.w q.1 / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), fun q : ℝ × ℝ =>
              (if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i (Jeps ρ ε f) q.1 q.2 * Work.Spaces.Wt α q.1 q.2) ^ 2
                else 0) := by
    funext q
    simp only [Work.Spaces.HkIntegrand, Finset.sum_apply, Pi.add_apply]
  rw [hfun]
  refine AEStronglyMeasurable.add ?_ ?_
  · exact Finset.aestronglyMeasurable_sum _ (fun i _ => ((hDz i).mul hW).pow 2)
  · refine Finset.aestronglyMeasurable_sum _ (fun i _ => ?_)
    refine Finset.aestronglyMeasurable_sum _ (fun j _ => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      exact ((hMx j i).mul hWt).pow 2
    · simp only [if_neg hc]
      exact aestronglyMeasurable_const

theorem aestronglyMeasurable_HkIntegrand_Jeps_slice {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ)
    {α : ℝ} {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hDz : ∀ i : ℕ, AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.DzIter i (Jeps ρ ε f) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun i => aestronglyMeasurable_DzIter_Jeps_slice hρ hε hsm hz i
  have hMx : ∀ j i : ℕ, AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.mixed j i (Jeps ρ ε f) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun j i => aestronglyMeasurable_mixed_Jeps_slice hρ hε hsm hz j i
  have hfun : (fun θ : ℝ => Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)
      = (∑ i ∈ Finset.range (k + 1), fun θ : ℝ =>
            (Work.Spaces.DzIter i (Jeps ρ ε f) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), fun θ : ℝ =>
              (if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i (Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
                else 0) := by
    funext θ
    simp only [Work.Spaces.HkIntegrand, Finset.sum_apply, Pi.add_apply]
  rw [hfun]
  refine AEStronglyMeasurable.add ?_ ?_
  · exact Finset.aestronglyMeasurable_sum _
      (fun i _ => ((hDz i).mul (aestronglyMeasurable_wdiv_slice z)).pow 2)
  · refine Finset.aestronglyMeasurable_sum _ (fun i _ => ?_)
    refine Finset.aestronglyMeasurable_sum _ (fun j _ => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      exact ((hMx j i).mul (aestronglyMeasurable_Wt_slice α z)).pow 2
    · simp only [if_neg hc]
      exact aestronglyMeasurable_const


/-! ## Measurability of the shifted joint integrand -/

theorem aemeasurable_shift_z_pair {H : ℝ → ℝ → ℝ}
    (hH : ContinuousOn (fun q : ℝ × ℝ => H q.1 q.2) Quad) {z : ℝ} (hz : 0 < z) :
    AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (H (z * Real.exp (-q.1)) q.2))
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  classical
  set S : Set (ℝ × ℝ) := {q | q.2 ∈ Set.Ioo 0 (π/2)} with hSdef
  have hSmeas : MeasurableSet S := (isOpen_Ioo.preimage continuous_snd).measurableSet
  have hnull : (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) Sᶜ = 0 := by
    have hScompl : Sᶜ = (Set.univ : Set ℝ) ×ˢ (Set.Ioo 0 (π/2))ᶜ := by
      ext q; simp [hSdef]
    have hIc : (MeasureTheory.volume.restrict Work.Spaces.Iθ) (Set.Ioo (0 : ℝ) (π/2))ᶜ = 0 := by
      rw [restrict_Iθ_eq, Measure.restrict_apply measurableSet_Ioo.compl,
        Set.compl_inter_self, measure_empty]
    rw [hScompl, Measure.prod_prod, hIc, mul_zero]
  have hmaps : MapsTo (fun q : ℝ × ℝ => (z * Real.exp (-q.1), q.2)) S Quad := by
    intro q hq
    exact ⟨mul_pos hz (Real.exp_pos _), hq⟩
  have hmap : ContinuousOn (fun q : ℝ × ℝ => (z * Real.exp (-q.1), q.2)) S := by
    refine ContinuousOn.prodMk ?_ continuousOn_snd
    exact continuousOn_const.mul
      ((Real.continuous_exp.comp (continuous_neg.comp continuous_fst)).continuousOn)
  have hcont : ContinuousOn (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2) S :=
    hH.comp hmap hmaps
  have hA : AEMeasurable (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2)
      (Measure.restrict ((MeasureTheory.volume.prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) S) :=
    hcont.aemeasurable hSmeas
  have hind : AEMeasurable (S.indicator (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2))
      ((MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
    (aemeasurable_indicator_iff hSmeas).mpr hA
  have hcongr : (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2)
      =ᵐ[((MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)))]
      S.indicator (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2) := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq
    simp only [Set.mem_compl_iff, not_not] at hq
    exact (Set.indicator_of_mem hq (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2)).symm
  have hGae : AEMeasurable (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2)
      ((MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
    hind.congr hcongr.symm
  exact ENNReal.measurable_ofReal.comp_aemeasurable hGae

end JepsHkMem

end Work.FTS.StrongEps
