/-
Copyright: work module for the Elgindi finite-time singularity project.

# Honesty of the three right-hand side functionals of the `i0`-family

For `u_r = D_z^r V` with `V` smooth on the open quadrant and the appropriate `ℋ^k`-membership,
the slice functions `dIntS u_r`, `ddIntS u_r`, `ttIntS u_r` are integrable over the radial
half-line `Iz`.  This is what allows the single-function interpolation estimate
(`Work.EllipticEst.Core.i0Aux.interpS_open`) to be applied to each `u_r`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.EllipticEst.Core.i0Aux.Basic
import Submission.Work.EllipticEst.Core.i0Aux.InterpDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux

set_option autoImplicit false

/-! ## Auxiliary facts -/

/-- The slice integrand `(D_z^m g)² w² σ_η` is continuous on the open quadrant. -/
theorem continuousOn_dzIter_weight {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter m g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2) (Work.FTS.EllipticEst.Q0) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter m g p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    ((hg.DzIter m).continuousOn).pow 2
  have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have h1 : ContinuousOn (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := by
      refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
      · exact (((continuous_const (y := (1 : ℝ))).add
          (continuous_id : Continuous (fun z : ℝ => z))).pow 2).continuousOn
      · exact (((continuous_id : Continuous (fun z : ℝ => z)).pow 2)).continuousOn
      · intro z hz
        exact pow_ne_zero 2 (ne_of_gt hz)
    refine h1.congr ?_
    intro z _
    simp only [Work.Spaces.w]
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    hw.comp (continuous_fst.continuousOn) (fun p hp => hp.1)
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
      Work.FTS.EllipticEst.Q0 := by
    simp only [Work.FTS.EllipticEst.thEta]
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    · intro p hp
      exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos])))
  exact (h1.mul h2).mul h3

/-- `σ_η = sin(2θ)^{-η}` is nonnegative on `Iθ`. -/
theorem thEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.thEta θ := by
  rcases eq_or_lt_of_le (Work.FTS.EllipticEst.sin_two_nonneg hθ) with h | h
  · simp only [Work.FTS.EllipticEst.thEta]
    rw [← h, Real.zero_rpow (neg_ne_zero.mpr Work.Spaces.eta_pos.ne')]
  · exact (Real.rpow_pos_of_pos h _).le

/-- The integrand `D² w² σ_η` is nonnegative on `Iθ`. -/
theorem slice_nonneg (D wz : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ D ^ 2 * wz ^ 2 * Work.FTS.EllipticEst.thEta θ :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (thEta_nonneg_Iθ hθ)

/-- For a.e. `z ∈ Iz` one has `0 < z`. -/
theorem ae_pos_Iz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
    ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-! ## The slice identities for `dIntS` and `ddIntS` -/

/-- `dIntS (D_z^r V) z` is the weighted `L²`-square of `D_z^{r+1}V` on the angular slice. -/
theorem dIntS_slice_eq {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    (z : ℝ) :
    dIntS (Work.Spaces.DzIter r V) z
      = ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.thEta θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hfun : ∀ θ : ℝ, Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ
      = Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ := by
    intro θ
    have h2 : Work.Spaces.DzIter (r + 1) V = Work.Spaces.DzIter r (Work.Spaces.Dz V) :=
      Work.Spaces.DzIter_add_right r 1 V
    exact congrFun (congrFun h2 z) θ
  rw [dIntS, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
    rw [hfun θ]; ring)

/-- `dIntS (D_z^r V) z`, written with the weighted quantity of `HkIntegrand`. -/
theorem dIntS_slice_eq' {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    (z : ℝ) :
    dIntS (Work.Spaces.DzIter r V) z
      = ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [dIntS_slice_eq hV r z]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  simp only [Work.FTS.EllipticEst.thEta]
  rw [mul_div_rpow_sq_eq (Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ) (Work.Spaces.w z)
      (Real.sin (2 * θ)) (Work.FTS.EllipticEst.sin_two_nonneg hθ) Work.Spaces.eta_pos.ne']

/-- `ddIntS (D_z^r V) z` is the weighted `L²`-square of `D_z^{r+2}V` on the angular slice. -/
theorem ddIntS_slice_eq {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    (z : ℝ) :
    ddIntS (Work.Spaces.DzIter r V) z
      = ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.thEta θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hfun : ∀ θ : ℝ, Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ := by
    intro θ
    have h2 : Work.Spaces.DzIter (r + 2) V = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) :=
      Work.Spaces.DzIter_add_right r 2 V
    exact congrFun (congrFun h2 z) θ
  rw [ddIntS, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
    rw [hfun θ]; ring)

/-- `ddIntS (D_z^r V) z`, written with the weighted quantity of `HkIntegrand`. -/
theorem ddIntS_slice_eq' {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    (z : ℝ) :
    ddIntS (Work.Spaces.DzIter r V) z
      = ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [ddIntS_slice_eq hV r z]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  simp only [Work.FTS.EllipticEst.thEta]
  rw [mul_div_rpow_sq_eq (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ) (Work.Spaces.w z)
      (Real.sin (2 * θ)) (Work.FTS.EllipticEst.sin_two_nonneg hθ) Work.Spaces.eta_pos.ne']

/-- `ttIntS (D_z^r V) z` is the weighted `L²`-square of `D_z^r ∂_θ²V` on the angular slice
(for `z > 0`). -/
theorem ttIntS_slice_eq {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    {z : ℝ} (hz : 0 < z) :
    ttIntS (Work.Spaces.DzIter r V) z
      = ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.thEta θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [ttIntS, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
    ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [show Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ from
        pthIter2_DzIter_comm hV hz hθ.1 hθ.2 r]
  ring

/-- `ttIntS (D_z^r V) z`, written with the weighted quantity of `HkIntegrand` (for `z > 0`). -/
theorem ttIntS_slice_eq' {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    {z : ℝ} (hz : 0 < z) :
    ttIntS (Work.Spaces.DzIter r V) z
      = ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [ttIntS_slice_eq hV r hz]
  refine MeasureTheory.integral_congr_ae ?_
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
    ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  show (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * Work.FTS.EllipticEst.thEta θ
    = (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
  simp only [Work.FTS.EllipticEst.thEta]
  rw [mul_div_rpow_sq_eq (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ) (Work.Spaces.w z)
      (Real.sin (2 * θ)) hpos.le Work.Spaces.eta_pos.ne']

/-! ## The three integrability statements -/

/-- A generic honesty step: a nonnegative slice functional dominated by the `ℋ^k`-integrand of
`g` is integrable over `Iz`. -/
theorem integrableOn_of_slice_le {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ} {G : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k g) (hGnn : ∀ z : ℝ, 0 ≤ G z)
    (haesm : MeasureTheory.AEStronglyMeasurable G
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      G z ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) :
    MeasureTheory.IntegrableOn G Work.Spaces.Iz := by
  refine MeasureTheory.Integrable.mono' hmem.2 haesm ?_
  filter_upwards [hbound] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (hGnn z)]
  exact hz

/-- `dIntS (D_z^r V)` is integrable on `Iz`. -/
theorem dIntS_integrableOn {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.Dz V)) (hr : r ≤ k) :
    MeasureTheory.IntegrableOn (fun z : ℝ => dIntS (Work.Spaces.DzIter r V) z)
      Work.Spaces.Iz := by
  refine integrableOn_of_slice_le hmem ?_ ?_ ?_
  · intro z
    rw [dIntS_slice_eq' hV r z]
    exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  · have h1 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _
        (continuousOn_dzIter_weight (g := Work.Spaces.Dz V) hV.Dz r)).integral_prod_right'
    refine h1.congr ?_
    filter_upwards with z
    exact (dIntS_slice_eq hV r z).symm
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [dIntS_slice_eq' hV r z]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hmem.1 z hz)
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.Dz V) z θ r hr)

/-- `ddIntS (D_z^r V)` is integrable on `Iz`. -/
theorem ddIntS_integrableOn {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V)) (hr : r ≤ k) :
    MeasureTheory.IntegrableOn (fun z : ℝ => ddIntS (Work.Spaces.DzIter r V) z)
      Work.Spaces.Iz := by
  refine integrableOn_of_slice_le hmem ?_ ?_ ?_
  · intro z
    rw [ddIntS_slice_eq' hV r z]
    exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  · have h1 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _
        (continuousOn_dzIter_weight (g := Work.Spaces.DzIter 2 V) (hV.DzIter 2) r)).integral_prod_right'
    refine h1.congr ?_
    filter_upwards with z
    exact (ddIntS_slice_eq hV r z).symm
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [ddIntS_slice_eq' hV r z]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hmem.1 z hz)
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.DzIter 2 V) z θ r hr)

/-- `ttIntS (D_z^r V)` is integrable on `Iz`. -/
theorem ttIntS_integrableOn {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V)) (hr : r ≤ k) :
    MeasureTheory.IntegrableOn (fun z : ℝ => ttIntS (Work.Spaces.DzIter r V) z)
      Work.Spaces.Iz := by
  refine integrableOn_of_slice_le hmem ?_ ?_ ?_
  · intro z
    by_cases hz : 0 < z
    · rw [ttIntS_slice_eq' hV r hz]
      exact MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => sq_nonneg _))
    · rw [ttIntS]
      exact mul_nonneg (sq_nonneg _)
        (MeasureTheory.integral_nonneg_of_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg_Iθ hθ))))
  · have h1 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ, (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _
        (continuousOn_dzIter_weight (g := Work.Spaces.pthIter 2 V) hV.pth.pth r)).integral_prod_right'
    refine h1.congr ?_
    filter_upwards [ae_pos_Iz] with z hz
    exact (ttIntS_slice_eq hV r hz).symm
  · filter_upwards [ae_pos_Iz] with z hz
    rw [ttIntS_slice_eq' hV r hz]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hmem.1 z (le_of_lt hz))
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 V) z θ r hr)


/-! ## Slicewise honesty of a single `HkIntegrand` summand -/

/-- A single `D_z`-summand of `HkIntegrand α k g`, written with the unweighted angular weight,
is integrable on the angular slice for every `z > 0` as soon as the whole integrand is. -/
theorem integrableOn_slice_summand {k i : ℕ} {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α k g) (hi : i ≤ k) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter i g z θ) ^ 2
      * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.DzIter i g z θ) ^ 2
      * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _
      (continuousOn_dzIter_weight (g := g) hg i) hz)
  refine MeasureTheory.Integrable.mono' (hmem.1 z (le_of_lt hz)) haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (thEta_nonneg_Iθ hθ))]
  have h := Work.Spaces.sq_le_HkIntegrand_z α k g z θ i hi
  have h2 : (Work.Spaces.DzIter i g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ := by
    rw [mul_div_rpow_sq_eq _ _ _ (Work.FTS.EllipticEst.sin_two_nonneg hθ)
      Work.Spaces.eta_pos.ne']
    simp only [Work.FTS.EllipticEst.thEta]
  rwa [h2] at h

/-! ## Slicewise honesty of the three functionals of `u_r = D_z^r V` -/

/-- **The slicewise honesty hypothesis of `InterpOpen` for `u_r = D_z^r V`**, derived from the
`ℋ^k`-membership of `D_zV`, `D_z²V` and `∂_θ²V`. -/
theorem sliceHonestOpen_dzIter {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hdd : Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V))
    (htt : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V))
    (hd : Work.Spaces.HkMem α k (Work.Spaces.Dz V)) (hr : r ≤ k) :
    SliceHonestOpen (Work.Spaces.DzIter r V) := by
  have hfunD : ∀ z θ : ℝ, Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ
      = Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ := by
    intro z θ
    have h2 : Work.Spaces.DzIter (r + 1) V = Work.Spaces.DzIter r (Work.Spaces.Dz V) :=
      Work.Spaces.DzIter_add_right r 1 V
    exact congrFun (congrFun h2 z) θ
  have hfunDD : ∀ z θ : ℝ, Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ := by
    intro z θ
    have h2 : Work.Spaces.DzIter (r + 2) V = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) :=
      Work.Spaces.DzIter_add_right r 2 V
    exact congrFun (congrFun h2 z) θ
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have h1 := integrableOn_slice_summand (g := Work.Spaces.pthIter 2 V) hV.pth.pth htt hr hz
    refine h1.congr ?_
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
      ← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2))]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [show Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ
        = Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ from
          pthIter2_DzIter_comm hV hz hθ.1 hθ.2 r]
  · intro z hz
    have h1 := integrableOn_slice_summand (g := Work.Spaces.DzIter 2 V) (hV.DzIter 2) hdd hr hz
    refine h1.congr ?_
    filter_upwards with θ
    rw [hfunDD z θ]
  · intro z hz
    have h1 := integrableOn_slice_summand (g := Work.Spaces.Dz V) hV.Dz hd hr hz
    refine h1.congr ?_
    filter_upwards with θ
    rw [hfunD z θ]

end Work.EllipticEst.Core.i0Aux
