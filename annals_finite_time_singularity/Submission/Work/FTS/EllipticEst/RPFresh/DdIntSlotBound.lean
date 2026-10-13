import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.EllipticEst.Core.i0Aux.Basic
import Submission.Work.EllipticEst.Core.i0Aux.Honest
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RPFresh

/-- `SmoothNbhd` (smoothness on a neighbourhood of the closed quadrant) implies `SmoothOpen`
(smoothness on the open quadrant), which is the class needed by the slice identities. -/
private theorem smoothOpen_of_smoothNbhd_local {V : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd V) : Work.FTS.EllipticEst.SmoothOpen V := by
  have h' : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (Function.uncurry V)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := hsm
  show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry V)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
  refine (h'.of_le le_top).mono (Set.prod_mono ?_ ?_)
  · exact Set.Ioi_subset_Ioi (by norm_num)
  · exact Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])

/-- **The `ddIntS`-slot bound for `D_z^r V`.**

Under the pointwise Euler split `D_z^r(D_z²V) = D_z^r(z²∂_z²V) + D_z^r(D_zV)` on the closed
quadrant, the radial functional `∫_z ddIntS (D_z^r V) z` is honest (integrable) and is bounded
by twice the `ℋ^k`-squares of `z²∂_z²V` and of `D_zV`, for `r ≤ k`.

(`ddIntS u z = w(z)² ∫_θ (D_z(D_z u) z θ)² σ_η(θ)`, so
`ddIntS (D_z^r V) z = ∫_θ (D_z^r(D_z²V) z θ · w z / sin(2θ)^{η/2})²`.) -/
theorem DdIntSlotBound {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd V)
    (hsplit : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ
        = Work.Spaces.DzIter r (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) z θ
          + Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ)
    (hmemQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ))
    (hmemD : Work.Spaces.HkMem α k (Work.Spaces.Dz V)) (hr : r ≤ k) :
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ddIntS (Work.Spaces.DzIter r V) z)
        Work.Spaces.Iz
      ∧ (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS (Work.Spaces.DzIter r V) z)
          ≤ 2 * Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
            + 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) := by
  have hV : Work.FTS.EllipticEst.SmoothOpen V := smoothOpen_of_smoothNbhd_local hsm
  set Q : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ
  have hsplitQ : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ
        = Work.Spaces.DzIter r Q z θ + Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ :=
    fun z hz θ hθ => hsplit z hz θ hθ
  have hQ1 : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k Q z θ) Work.Spaces.Iθ := hmemQ.1
  have hQ2 : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Q z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmemQ.2
  have hD1 : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ) Work.Spaces.Iθ := hmemD.1
  have hD2 : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmemD.2
  -- ## Step 1: the pointwise comparison on the closed quadrant
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.thEta θ
        ≤ 2 * Work.Spaces.HkIntegrand α k Q z θ
          + 2 * Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ := by
    intro z hz θ hθ
    have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_nonneg hθ
    have e1 : (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ
        = ((Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      rw [Work.FTS.EllipticEst.thEta,
        Work.EllipticEst.Core.i0Aux.mul_div_rpow_sq_eq _ _ _ hs Work.Spaces.eta_pos.ne']
    rw [e1, hsplitQ z hz θ hθ]
    have h12 := Work.Spaces.sq_le_HkIntegrand_z α k Q z θ r hr
    have h22 := Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.Dz V) z θ r hr
    nlinarith [sq_nonneg ((Work.Spaces.DzIter r Q z θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        - (Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))), h12, h22]
  -- ## Step 2: the slice bound
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Q z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ) := by
    intro z hz
    have hgint : MeasureTheory.Integrable (fun θ : ℝ =>
        2 * Work.Spaces.HkIntegrand α k Q z θ
          + 2 * Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((hQ1 z hz).const_mul 2).add ((hD1 z hz).const_mul 2)
    have hmono : (∫ θ, (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ (∫ θ, (2 * Work.Spaces.HkIntegrand α k Q z θ
            + 2 * Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      MeasureTheory.integral_mono_of_nonneg
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
          mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ))
        hgint
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt z hz θ hθ)
    have hsplit_int : (∫ θ, (2 * Work.Spaces.HkIntegrand α k Q z θ
          + 2 * Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Q z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ) := by
      rw [MeasureTheory.integral_add ((hQ1 z hz).const_mul 2) ((hD1 z hz).const_mul 2)]
      simp only [MeasureTheory.integral_const_mul]
    exact le_trans hmono (le_of_eq hsplit_int)
  -- ## Step 3: the same bound integrated in `z`
  have hGint : MeasureTheory.Integrable (fun z : ℝ =>
      2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Q z θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (hQ2.const_mul 2).add (hD2.const_mul 2)
  have hFnn : ∀ z : ℝ, 0 ≤ Work.EllipticEst.Core.ddIntS (Work.Spaces.DzIter r V) z := by
    intro z
    rw [Work.EllipticEst.Core.ddIntS]
    refine mul_nonneg (sq_nonneg _) ?_
    refine MeasureTheory.integral_nonneg_of_ae ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ)
  have hFle : ∀ z ∈ Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS (Work.Spaces.DzIter r V) z
      ≤ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Q z θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ) := by
    intro z hz
    rw [Work.EllipticEst.Core.i0Aux.ddIntS_slice_eq hV r z]
    exact hslice z hz
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => Work.EllipticEst.Core.ddIntS (Work.Spaces.DzIter r V) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) p.1 p.2) ^ 2
          * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
        Work.FTS.EllipticEst.Q0 :=
      Work.EllipticEst.Core.i0Aux.continuousOn_dzIter_weight (g := Work.Spaces.DzIter 2 V)
        (hV.DzIter 2) r
    have h1 : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => ∫ θ,
        (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
    refine h1.congr ?_
    filter_upwards with z
    exact (Work.EllipticEst.Core.i0Aux.ddIntS_slice_eq hV r z).symm
  have hsum : (∫ z in Work.Spaces.Iz, (2 * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k Q z θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ)))
      = 2 * Work.Spaces.HkSq α k Q + 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) := by
    rw [MeasureTheory.integral_add (hQ2.const_mul 2) (hD2.const_mul 2)]
    simp only [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hGint haesm ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn z)]
    exact hFle z hz
  · refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z : ℝ => Work.EllipticEst.Core.ddIntS (Work.Spaces.DzIter r V) z)
      (g := fun z : ℝ => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Q z θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z _ => hFnn z) hGint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hFle)) (le_of_eq hsum)

end Work.FTS.EllipticEst.RPFresh
