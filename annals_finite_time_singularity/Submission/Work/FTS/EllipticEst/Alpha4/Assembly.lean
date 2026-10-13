import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.Alpha4.Cut
import Submission.Work.FTS.EllipticEst.Alpha4.slice_key
import Submission.Work.FTS.EllipticEst.Alpha4.radial_ibp_weight
import Submission.Work.FTS.EllipticEst.ThetaU.K1Aux
import Submission.Work.FTS.EllipticEst.ThetaU.OpenAux
import Submission.Work.FTS.EllipticEst.ThetaU.Defs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.ZCuts.zCut_exists
import Submission.Work.FTS.EllipticEst.ZCuts.zCut_props
import Submission.Work.FTS.EllipticEst.interpol_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Alpha4

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem continuousOn_box_mixed {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) (j i : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (Function.uncurry (Work.Spaces.mixed j i G))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) :=
  (hG.mixed j i 1).continuousOn.mono (fun p hp =>
    ⟨lt_of_lt_of_le ha hp.1.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩)

/-- The mixed iterate `D_z^j D_θ^i G` is jointly continuous on the open quadrant. -/
theorem continuousOn_quad_mixed {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) (j i : ℕ) :
    ContinuousOn (Function.uncurry (Work.Spaces.mixed j i G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  (hG.mixed j i 1).continuousOn.mono (fun p hp =>
    ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩)

/-- The z-outer integrability of `ζ w² ∫_θ (mixed j i G)² σ` for the logarithmic cut-off. -/
theorem integrable_outer_cut_mixed {k : ℕ} (hk2 : 2 ≤ k) {φ : ℝ → ℝ} {K : ℝ}
    (hφK : Work.FTS.EllipticEst.IsZCut φ K) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) (j i : ℕ) :
    MeasureTheory.Integrable
      (fun z => (zc φ k z) * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  obtain ⟨hζcd, hζzero, -, -, -⟩ := ZCuts.zCut_props hφK k hk2
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk2
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hkRpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk4 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [hkR]
  have hab : (1 : ℝ) / (k : ℝ) ^ 2 < (k : ℝ) ^ 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hk4]
  have hζsupp : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) → zc φ k z = 0 :=
    fun z hz => zc_eq_zero_of_notMem hk1 (fun z' hz' hz'' => hζzero z' hz' hz'') hz
  have hcdζ : ContDiffOn ℝ 1 (zc φ k) (Set.Ioi 0) := zc_contDiffOn hζcd
  have hbox : ContinuousOn (Function.uncurry (fun z θ =>
      zc φ k z * (Work.Spaces.mixed j i G z θ) ^ 2))
      (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
    ContinuousOn.mul
      ((hcdζ.continuousOn).comp continuousOn_fst (fun p hp => lt_of_lt_of_le (by positivity) hp.1.1))
      ((continuousOn_box_mixed (a := 1 / (k : ℝ) ^ 2) (b := (k : ℝ) ^ 2) hG j i
        (by positivity)).pow 2)
  have hcont : ContinuousOn (Function.uncurry (fun z θ =>
      zc φ k z * (Work.Spaces.mixed j i G z θ) ^ 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ContinuousOn.mul
      ((hcdζ.continuousOn).comp continuousOn_fst (fun p hp => hp.1))
      ((continuousOn_quad_mixed hG j i).pow 2)
  obtain ⟨Mb, -, hMb⟩ := Work.FTS.EllipticEst.ThetaU.exists_bound_box (δ := 1 / (k : ℝ) ^ 2)
    (R := (k : ℝ) ^ 2) (by positivity) hab hbox
  have h := Work.FTS.EllipticEst.ThetaU.integrable_outer_of_bound (δ := 1 / (k : ℝ) ^ 2)
    (R := (k : ℝ) ^ 2) (by positivity)
    (F := fun z θ => zc φ k z * (Work.Spaces.mixed j i G z θ) ^ 2) hcont
    (fun z hz θ => by rw [hζsupp z hz]; ring)
    ⟨Mb, fun z hz θ hθ => hMb z hz θ hθ⟩
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
      (zc φ k z * (Work.Spaces.mixed j i G z θ) ^ 2) * Work.FTS.EllipticEst.thEta θ)
    = (zc φ k z) * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j i G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
  rw [show (∫ θ in Work.Spaces.Iθ,
        (zc φ k z * (Work.Spaces.mixed j i G z θ) ^ 2) * Work.FTS.EllipticEst.thEta θ)
      = (zc φ k z) * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j i G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) from by
    rw [show (fun θ => (zc φ k z * (Work.Spaces.mixed j i G z θ) ^ 2)
          * Work.FTS.EllipticEst.thEta θ)
        = fun θ => ((Work.Spaces.mixed j i G z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) * (zc φ k z) from by funext θ; ring,
      MeasureTheory.integral_mul_const]
    ring]
  ring

/-- The iterate `D_z^j ∂_θ^i G` is jointly continuous on the closed box. -/
theorem continuousOn_box_pthDz {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) (j i : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (Function.uncurry (fun z θ =>
        Work.Spaces.DzIter j (Work.Spaces.pthIter i G) z θ))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) :=
  (((hG.pthIter i).DzIter j) 1).continuousOn.mono (fun p hp =>
    ⟨lt_of_lt_of_le ha hp.1.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩)

/-- The iterate `D_z^j ∂_θ^i G` is jointly continuous on the open quadrant. -/
theorem continuousOn_quad_pthDz {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) (j i : ℕ) :
    ContinuousOn (Function.uncurry (fun z θ =>
        Work.Spaces.DzIter j (Work.Spaces.pthIter i G) z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  (((hG.pthIter i).DzIter j) 1).continuousOn.mono (fun p hp =>
    ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩)

theorem pull_out_w (F : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, F z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.EllipticEst.thEta θ) := by
  rw [show (fun θ => F z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = fun θ => (F z θ * Work.FTS.EllipticEst.thEta θ) * (Work.Spaces.w z) ^ 2 from by
    funext θ; ring,
    MeasureTheory.integral_mul_const]
  ring

theorem mixInt_eq (G : ℝ → ℝ → ℝ) : Work.FTS.EllipticEst.mixInt G
    = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  rw [Work.FTS.EllipticEst.mixInt]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z =>
    pull_out_w (fun z θ => (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2) z)

theorem ddInt_eq (G : ℝ → ℝ → ℝ) : Work.FTS.EllipticEst.ddInt G
    = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  rw [Work.FTS.EllipticEst.ddInt]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z =>
    pull_out_w (fun z θ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2) z)

theorem ttInt_eq (G : ℝ → ℝ → ℝ) : Work.FTS.EllipticEst.ttInt G
    = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  rw [Work.FTS.EllipticEst.ttInt]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z =>
    pull_out_w (fun z θ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2) z)

theorem dInt_eq (G : ℝ → ℝ → ℝ) : Work.FTS.EllipticEst.dInt G
    = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  rw [Work.FTS.EllipticEst.dInt]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z =>
    pull_out_w (fun z θ => (Work.Spaces.Dz G z θ) ^ 2) z)


theorem iterated_swap_of_integrable {F : ℝ → ℝ → ℝ}
    (hFnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ F z θ)
    (haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry F)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hinner : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => F z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (houter : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ, F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, F z θ := by
  have hnorm : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, ‖F z θ‖) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine houter.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact (Real.norm_of_nonneg (hFnn z hz θ hθ)).symm
  have hInt : MeasureTheory.Integrable (Function.uncurry F)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integrable_prod_iff haesm).mpr ⟨hinner, hnorm⟩
  exact MeasureTheory.integral_integral_swap hInt

/-- The `θ`-outer form of `dInt`. -/
theorem dInt_theta (G : ℝ → ℝ → ℝ)
    (hF : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hinner : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    Work.FTS.EllipticEst.dInt G = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  have h1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.thEta θ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
    rw [show (fun θ => (Work.Spaces.Dz G z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        = fun θ => ((Work.Spaces.Dz G z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) * (Work.Spaces.w z) ^ 2 from by funext θ; ring,
      MeasureTheory.integral_mul_const]
    ring
  rw [dInt_eq G, h1]
  exact iterated_swap_of_integrable
    (F := fun z θ => (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * Work.FTS.EllipticEst.thEta θ)
    (fun z hz θ hθ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (sin_nonneg_of_mem_Iθ hθ) _)) haesm hinner hF

/-- The `θ`-outer form of `ttInt`. -/
theorem ttInt_theta (G : ℝ → ℝ → ℝ)
    (hF : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hinner : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    Work.FTS.EllipticEst.ttInt G = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
      (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ := by
  have h1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.thEta θ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
    rw [show (fun θ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        = fun θ => ((Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) * (Work.Spaces.w z) ^ 2 from by funext θ; ring,
      MeasureTheory.integral_mul_const]
    ring
  rw [ttInt_eq G, h1]
  exact iterated_swap_of_integrable
    (F := fun z θ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * Work.FTS.EllipticEst.thEta θ)
    (fun z hz θ hθ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (sin_nonneg_of_mem_Iθ hθ) _)) haesm hinner hF

/-- The `θ`-outer form of `ddInt`. -/
theorem ddInt_theta (G : ℝ → ℝ → ℝ)
    (hF : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hinner : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    Work.FTS.EllipticEst.ddInt G = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ := by
  have h1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.thEta θ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
    rw [show (fun θ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        = fun θ => ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) * (Work.Spaces.w z) ^ 2 from by funext θ; ring,
      MeasureTheory.integral_mul_const]
    ring
  rw [ddInt_eq G, h1]
  exact iterated_swap_of_integrable
    (F := fun z θ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * Work.FTS.EllipticEst.thEta θ)
    (fun z hz θ hθ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (sin_nonneg_of_mem_Iθ hθ) _)) haesm hinner hF



/-! ## Auxiliary continuity and integrability facts -/

theorem continuousOn_quad_thEta :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  exact hsin.rpow_const (fun p hp =>
    Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos]))))

theorem aesm_of_quad {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry F)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ hF

/-- The `θ`-slices of `(D_zG)²` and `(∂_θ²G)²` are integrable against `σ` for a.e. `z`. -/
theorem integrable_slice_of_smooth {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) (j i : ℕ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (Work.Spaces.mixed j i G z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ)))]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  have hcont : ContinuousOn (fun θ => Work.Spaces.mixed j i G z θ) Work.Spaces.Iθ :=
    ((hG.mixed j i).sliceSmoothO hz).continuousOn_Iθ
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hslice : MeasureTheory.IntegrableOn
      (fun θ => M ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul _)
  have hcont' : ContinuousOn (fun θ => (Work.Spaces.mixed j i G z θ) ^ 2
      * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hth : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      refine hsin.rpow_const (fun θ hθ => ?_)
      have h1 : (0 : ℝ) < θ := hθ.1
      have h2 : θ < Real.pi / 2 := hθ.2
      exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
        (by linarith [Real.pi_pos])))
    exact ContinuousOn.mul (ContinuousOn.mul
      ((hcont.mono (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩)).pow 2) continuousOn_const) hth
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => (Work.Spaces.mixed j i G z θ) ^ 2
      * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    rw [← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0:ℝ)) (b := Real.pi / 2))]
    exact hcont'.aestronglyMeasurable measurableSet_Ioo
  refine MeasureTheory.Integrable.mono' hslice haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hθ' : |Work.Spaces.mixed j i G z θ| ≤ M := hM θ hθ
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) hθ'
  have h1 : (Work.Spaces.mixed j i G z θ) ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hθ' 2
  have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ :=
    Real.rpow_nonneg (sin_nonneg_of_mem_Iθ hθ) _
  have hnn : 0 ≤ (Work.Spaces.mixed j i G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * Work.FTS.EllipticEst.thEta θ := mul_nonneg (mul_nonneg (sq_nonneg _) hw) hσ
  calc ‖(Work.Spaces.mixed j i G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ‖
      = (Work.Spaces.mixed j i G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    _ ≤ M ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hw) hσ


/-! ## The one-dimensional slice inequality applied to the slices `θ ↦ D_zG(z,θ)` -/

theorem slice_z {c₁ : ℝ} {G : ℝ → ℝ → ℝ}
    (hslice : ∀ (f : ℝ → ℝ), ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
          * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
          + c₁ * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    (h0 : ∀ z : ℝ, G z 0 = 0) (h1 : ∀ z : ℝ, G z (Real.pi / 2) = 0)
    {z : ℝ} (hz : 0 < z) :
    (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
        * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ - (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
              * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
              * Work.FTS.EllipticEst.thEta θ)
        + c₁ * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  have hcd : ContDiffOn ℝ 2 (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
    have hcomp : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ))
        (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmaps : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))
        Work.FTS.EllipticEst.ThetaU.OStrip := fun θ hθ => ⟨hz, hθ⟩
    have h := (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 2) (hsm 3)).comp
      hcomp hmaps
    simpa [Function.comp_def] using h
  have hz0 : (fun θ : ℝ => Work.Spaces.Dz G z θ) 0 = 0 := by
    show z * Work.Spaces.pz G z 0 = 0
    rw [show Work.Spaces.pz G z 0 = deriv (fun z' : ℝ => G z' 0) z from rfl,
      (funext fun z' => h0 z'), deriv_const, mul_zero]
  have hzpi : (fun θ : ℝ => Work.Spaces.Dz G z θ) (Real.pi / 2) = 0 := by
    show z * Work.Spaces.pz G z (Real.pi / 2) = 0
    rw [show Work.Spaces.pz G z (Real.pi / 2) = deriv (fun z' : ℝ => G z' (Real.pi / 2)) z
        from rfl, (funext fun z' => h1 z'), deriv_const, mul_zero]
  have h := hslice (fun θ : ℝ => Work.Spaces.Dz G z θ) hcd hz0 hzpi
  have hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffAt ℝ 2 (Function.uncurry G) (z, θ) := by
    intro θ hθ
    refine (hsm 2).contDiffAt ?_
    refine (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ?_
    exact ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have e1 : (∫ θ in Work.Spaces.Iθ,
        (deriv (fun θ' => Work.Spaces.Dz G z θ') θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [show deriv (fun θ' => Work.Spaces.Dz G z θ') θ
        = Work.Spaces.pth (Work.Spaces.Dz G) z θ from rfl,
      Work.FTS.EllipticEst.ThetaU.pth_Dz_eq (hcont θ hθ)]
  have e2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
        * deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
          * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
          * Work.FTS.EllipticEst.thEta θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [show deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ
        = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz G)) z θ from rfl,
      Work.FTS.EllipticEst.ThetaU.pth_pth_Dz_eq (hsm 3) hz
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩]
  rw [e1, e2] at h
  exact h

/-! ## The integration-by-parts identity for the `B`-term -/

theorem ibp_B_eq {φ : ℝ → ℝ} {K : ℝ} (hφK : Work.FTS.EllipticEst.IsZCut φ K)
    {k : ℕ} (hk2 : 2 ≤ k) (G : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))) :
    - (∫ z in Work.Spaces.Iz, (zc φ k z) * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ))
      = ∫ θ in Work.Spaces.Iθ,
          ((∫ z in Work.Spaces.Iz, deriv (zc φ k) z
              * (Work.Spaces.w z) ^ 2 * z * (Work.Spaces.Dz G z θ)
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
            + (∫ z in Work.Spaces.Iz, (zc φ k z) * (Work.Spaces.w z) ^ 2
              * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ)))
          * Work.FTS.EllipticEst.thEta θ := by
  obtain ⟨hζcd, hζzero, -, -, -⟩ := ZCuts.zCut_props hφK k hk2
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk2
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk4 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [hkR]
  have hab : (1 : ℝ) / (k : ℝ) ^ 2 < (k : ℝ) ^ 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hk4]
  have hζsupp : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) → zc φ k z = 0 :=
    fun z hz => zc_eq_zero_of_notMem hk1 (fun z' hz' hz'' => hζzero z' hz' hz'') hz
  have hζcd1 : ContDiffOn ℝ 1 (zc φ k) (Set.Ioi 0) := zc_contDiffOn hζcd
  have hstep1 : (∫ z in Work.Spaces.Iz, (zc φ k z) * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ))
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (zc φ k z) * (Work.Spaces.Dz G z θ)
              * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
              * Work.FTS.EllipticEst.thEta θ) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (zc φ k z) * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ)
      = (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (zc φ k z) * (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ)
    rw [show (∫ θ in Work.Spaces.Iθ, (zc φ k z) * (Work.Spaces.Dz G z θ)
          * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
          * Work.FTS.EllipticEst.thEta θ)
        = (zc φ k z) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ) from by
      rw [show (fun θ => (zc φ k z) * (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ)
          = fun θ => ((Work.Spaces.Dz G z θ)
              * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
              * Work.FTS.EllipticEst.thEta θ) * (zc φ k z) from by funext θ; ring,
        MeasureTheory.integral_mul_const]
      ring]
    ring
  have hcontF : ContinuousOn (Function.uncurry (fun z θ => (zc φ k z) * (Work.Spaces.Dz G z θ)
      * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ContinuousOn.mul (ContinuousOn.mul
      ((hζcd1.continuousOn).comp continuousOn_fst (fun p hp => hp.1))
      (continuousOn_quad_mixed (G := G) hsm 1 0))
      (continuousOn_quad_pthDz (G := G) hsm 1 2)
  have hboxF : ContinuousOn (Function.uncurry (fun z θ => (zc φ k z) * (Work.Spaces.Dz G z θ)
      * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)))
      (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
    ContinuousOn.mul (ContinuousOn.mul
      ((hζcd1.continuousOn).comp continuousOn_fst (fun p hp =>
        lt_of_lt_of_le (by positivity) hp.1.1))
      (continuousOn_box_mixed (G := G) hsm 1 0 (by positivity)))
      (continuousOn_box_pthDz (G := G) hsm 1 2 (by positivity))
  obtain ⟨Mb, -, hMb⟩ := Work.FTS.EllipticEst.ThetaU.exists_bound_box (δ := 1 / (k : ℝ) ^ 2)
    (R := (k : ℝ) ^ 2) (by positivity) hab hboxF
  have hstep2 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (zc φ k z) * (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ))
      = ∫ θ in Work.Spaces.Iθ,
          (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ((zc φ k z) * (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)))
          * Work.FTS.EllipticEst.thEta θ :=
    Work.FTS.EllipticEst.ThetaU.fubini_w_thEta (δ := 1 / (k : ℝ) ^ 2)
      (R := (k : ℝ) ^ 2) (by positivity) hcontF (fun z hz θ => by rw [hζsupp z hz]; ring)
      ⟨Mb, fun z hz θ hθ => hMb z hz θ hθ⟩
  have hslice : ∀ θ ∈ Work.Spaces.Iθ,
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ((zc φ k z) * (Work.Spaces.Dz G z θ)
          * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)))
      = - (∫ z in Work.Spaces.Iz, deriv (zc φ k) z * (Work.Spaces.w z) ^ 2 * z
            * (Work.Spaces.Dz G z θ) * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
        - (∫ z in Work.Spaces.Iz, (zc φ k z) * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
              + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
            * (Work.Spaces.pth (Work.Spaces.pth G) z θ)) := by
    intro θ hθ
    have hθmem : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hφ : ContDiffOn ℝ 1 (fun z : ℝ => Work.Spaces.Dz G z θ) (Set.Ioi 0) := by
      have hcomp : ContDiffOn ℝ 1 (fun z : ℝ => (z, θ)) (Set.Ioi 0) :=
        contDiffOn_id.prodMk contDiffOn_const
      have hmaps : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi 0)
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := fun z hz => ⟨hz, hθmem⟩
      exact ((Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 1) (hsm 2)).comp
        hcomp hmaps)
    have hψ : ContDiffOn ℝ 1 (fun z : ℝ => Work.Spaces.pth (Work.Spaces.pth G) z θ)
        (Set.Ioi 0) := by
      have hcomp : ContDiffOn ℝ 1 (fun z : ℝ => (z, θ)) (Set.Ioi 0) :=
        contDiffOn_id.prodMk contDiffOn_const
      have hmaps : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi 0)
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := fun z hz => ⟨hz, hθmem⟩
      exact ((Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (n := 1)
        (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (n := 2) (hsm 3))).comp
        hcomp hmaps)
    have hs : ∀ z, (0 < z ∧ z < 1 / (k : ℝ) ^ 2) ∨ (k : ℝ) ^ 2 < z → zc φ k z = 0 :=
      fun z hz => hζsupp z (by
        rcases hz with ⟨h1, h2⟩ | h2
        · exact fun h => absurd h.1 (not_le_of_gt h2)
        · exact fun h => absurd h.2 (not_le_of_gt h2))
    have hB := radial_ibp_weight (a := 1 / (k : ℝ) ^ 2) (b := (k : ℝ) ^ 2)
      (by positivity) hab hφ hψ hζcd1 hs
    have hIz : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ((zc φ k z) * (Work.Spaces.Dz G z θ)
          * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)))
        = ∫ z in Set.Ioi (0 : ℝ), (zc φ k z) * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz G z θ)
            * (z * deriv (fun z' => Work.Spaces.pth (Work.Spaces.pth G) z' θ) z) := by
      rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
        MeasureTheory.integral_Ici_eq_integral_Ioi]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      ring
    have hE : (∫ z in Set.Ioi (0 : ℝ), deriv (zc φ k) z * (Work.Spaces.w z) ^ 2 * z
          * (Work.Spaces.Dz G z θ) * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
        = ∫ z in Work.Spaces.Iz, deriv (zc φ k) z * (Work.Spaces.w z) ^ 2 * z
            * (Work.Spaces.Dz G z θ) * (Work.Spaces.pth (Work.Spaces.pth G) z θ) := by
      rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
        MeasureTheory.integral_Ici_eq_integral_Ioi]
    have hF : (∫ z in Set.Ioi (0 : ℝ), (zc φ k z) * (Work.Spaces.w z) ^ 2
          * (z * deriv (fun z' => Work.Spaces.Dz G z' θ) z
            + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
        = ∫ z in Work.Spaces.Iz, (zc φ k z) * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
              + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
            * (Work.Spaces.pth (Work.Spaces.pth G) z θ) := by
      rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
        MeasureTheory.integral_Ici_eq_integral_Ioi]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [hIz, hB, hE, hF]
  have hslice' : ∀ θ ∈ Work.Spaces.Iθ,
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ((zc φ k z) * (Work.Spaces.Dz G z θ)
          * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)))
      = - ((∫ z in Work.Spaces.Iz, deriv (zc φ k) z * (Work.Spaces.w z) ^ 2 * z
            * (Work.Spaces.Dz G z θ) * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
          + (∫ z in Work.Spaces.Iz, (zc φ k z) * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
              + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
            * (Work.Spaces.pth (Work.Spaces.pth G) z θ))) := by
    intro θ hθ
    rw [hslice θ hθ]
    ring
  calc - (∫ z in Work.Spaces.Iz, (zc φ k z) * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ))
      = - (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (zc φ k z) * (Work.Spaces.Dz G z θ)
              * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
              * Work.FTS.EllipticEst.thEta θ)) := by rw [hstep1]
    _ = - (∫ θ in Work.Spaces.Iθ,
          (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ((zc φ k z) * (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)))
          * Work.FTS.EllipticEst.thEta θ) := by rw [hstep2]
    _ = - (∫ θ in Work.Spaces.Iθ,
          - ((∫ z in Work.Spaces.Iz, deriv (zc φ k) z * (Work.Spaces.w z) ^ 2 * z
                * (Work.Spaces.Dz G z θ) * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
            + (∫ z in Work.Spaces.Iz, (zc φ k z) * (Work.Spaces.w z) ^ 2
              * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ)))
          * Work.FTS.EllipticEst.thEta θ) := by
        congr 1
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [hslice' θ hθ]
    _ = ∫ θ in Work.Spaces.Iθ,
          ((∫ z in Work.Spaces.Iz, deriv (zc φ k) z * (Work.Spaces.w z) ^ 2 * z
              * (Work.Spaces.Dz G z θ) * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
            + (∫ z in Work.Spaces.Iz, (zc φ k z) * (Work.Spaces.w z) ^ 2
              * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ)))
          * Work.FTS.EllipticEst.thEta θ := by
        rw [show (fun θ => - ((∫ z in Work.Spaces.Iz, deriv (zc φ k) z
                * (Work.Spaces.w z) ^ 2 * z * (Work.Spaces.Dz G z θ)
                * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
              + (∫ z in Work.Spaces.Iz, (zc φ k z) * (Work.Spaces.w z) ^ 2
                * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                  + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
                * (Work.Spaces.pth (Work.Spaces.pth G) z θ)))
            * Work.FTS.EllipticEst.thEta θ)
            = fun θ => - (((∫ z in Work.Spaces.Iz, deriv (zc φ k) z
                * (Work.Spaces.w z) ^ 2 * z * (Work.Spaces.Dz G z θ)
                * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
              + (∫ z in Work.Spaces.Iz, (zc φ k z) * (Work.Spaces.w z) ^ 2
                * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                  + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
                * (Work.Spaces.pth (Work.Spaces.pth G) z θ)))
              * Work.FTS.EllipticEst.thEta θ) from by funext θ; ring,
          MeasureTheory.integral_neg, neg_neg]
end Work.FTS.EllipticEst.Alpha4
