/-
Copyright: work module for the Elgindi finite-time singularity project.

# The truncated `w²`-energy inequality in the a.e. class: the profile bounds

The auxiliary bounds needed by the final assembly `aeCutEnergyProp`:

* the cut-off derivative bounds `hC1`, `hC2` for a compactly supported `C²` function vanishing
  near `0`;
* the a.e. continuity of the angular slices on `[0,π/2]`, from the two endpoint limits;
* the a.e. angular square-integrability of `∂_θu`;
* the finiteness of the untruncated `w²`-mass, of the truncated radial slot and of the truncated
  source slot.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Prop.CutEnergyAux.main
import Submission.Work.FTS.EllipticEst.Prop.CutEnergyAux.lzeroProfInt
import Submission.Work.FTS.EllipticEst.AeS1.aeSliceConds
import Submission.Work.FTS.EllipticEst.H2W.Ae.AngSliceBound
import Submission.Work.FTS.EllipticEst.Dispatch.ceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.CutEnergyAux

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 3200000

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "sg" => Work.FTS.EllipticEst.sEta

/-- **The cut-off derivative bounds.**  For a `C²` function `φ` with compact support, vanishing
on `(-∞,δ]` for some `δ > 0`, the products `|φ'|·z` and `|φ''|·z²` are bounded. -/
theorem deriv_mul_bdd (φ : ℝ → ℝ) (hφsm : ContDiff ℝ 2 φ)
    (hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → φ z = 0)
    (hcpt : HasCompactSupport φ) :
    (∃ C : ℝ, ∀ z : ℝ, |deriv φ z| * z ≤ C) ∧
      (∃ C : ℝ, ∀ z : ℝ, |deriv (deriv φ) z| * z ^ 2 ≤ C) := by
  obtain ⟨δ, hδpos, hδ0⟩ := hδ
  have hts : tsupport φ ⊆ Set.Ici δ := by
    refine closure_minimal (fun z hz => ?_) isClosed_Ici
    exact le_of_not_gt fun h => hz (hδ0 z (le_of_lt h))
  have hts' : tsupport φ ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le hδpos (hts hz)
  refine ⟨?_, ?_⟩
  · -- the first derivative
    have h1c : Continuous (fun z : ℝ => |deriv φ z| * z) :=
      (hφsm.continuous_deriv (by norm_num)).abs.mul continuous_id
    have h1s : HasCompactSupport (fun z : ℝ => |deriv φ z| * z) := by
      refine IsCompact.of_isClosed_subset hcpt.isCompact (isClosed_tsupport _) ?_
      refine closure_minimal (fun z hz => ?_) (isClosed_tsupport φ)
      by_contra hz'
      exact hz (by
        show |deriv φ z| * z = 0
        rw [(HasDerivAt.of_notMem_tsupport hz').deriv]
        simp)
    obtain ⟨C1, hC1⟩ := h1s.exists_bound_of_continuous h1c
    refine ⟨max C1 0, fun z => ?_⟩
    have hC10 : 0 ≤ C1 := le_trans (norm_nonneg _) (hC1 0)
    rcases le_or_gt 0 z with hz | hz
    · have h2 : 0 ≤ |deriv φ z| * z := mul_nonneg (abs_nonneg _) hz
      have h3 := hC1 z
      rw [Real.norm_eq_abs, abs_of_nonneg h2] at h3
      exact le_trans h3 (le_max_left _ _)
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) (le_of_lt hz))
        (le_max_right _ _)
  · -- the second derivative
    have hd1 : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) :=
      (hφsm.contDiffOn.mono (Set.subset_univ _)).deriv_of_isOpen isOpen_Ioi (by norm_num)
    have hd2 : ContDiffOn ℝ 0 (deriv (deriv φ)) (Set.Ioi 0) :=
      hd1.deriv_of_isOpen isOpen_Ioi (by norm_num)
    have hcont : ContinuousOn (fun z : ℝ => |deriv (deriv φ) z| * z ^ 2) (tsupport φ) :=
      (hd2.continuousOn.mono hts').abs.mul (continuousOn_id.pow 2)
    obtain ⟨C2, hC2⟩ := hcpt.isCompact.exists_bound_of_continuousOn hcont
    refine ⟨max C2 0, fun z => ?_⟩
    by_cases hz : z ∈ tsupport φ
    · have h3 := hC2 z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))] at h3
      exact le_trans h3 (le_max_left _ _)
    · have hz0 : deriv (deriv φ) z = 0 := by
        have h1 : (fun w : ℝ => deriv φ w) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
          have hmem : (tsupport φ)ᶜ ∈ 𝓝 z :=
            (isClosed_tsupport (f := φ)).isOpen_compl.mem_nhds hz
          filter_upwards [hmem] with w hw
          exact (HasDerivAt.of_notMem_tsupport hw).deriv
        rw [h1.deriv_eq]
        simp
      rw [hz0]
      simp only [abs_zero, zero_mul]
      exact le_max_right _ _

/-- **A.e. continuity of the angular slices on `[0,π/2]`**, from the two one-sided endpoint
limits. -/
theorem ae_continuousOn_slice (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hL0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hLπ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2)) := by
  filter_upwards [hL0, hLπ, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
    with z hl0 hlp hz
  exact Work.FTS.EllipticEst.H2W.AeProof.continuousOn_Icc_of_tendsto
    (by linarith [Real.pi_pos])
    (Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz 1).continuousOn
    (by simpa only [h.dirZero z] using hl0) (by simpa only [h.dirPi z] using hlp)

/-- **A.e. angular square-integrability of `∂_θu`.** -/
theorem ae_slice_pth_sq_finite (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2))) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Iθ := by
  have hIoi : MeasureTheory.volume.restrict Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  rw [hIoi]
  filter_upwards [hC, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hCz hz
  have hsm : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz 2
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv (fun θ' => u z θ') t) θ) ^ 2 * sg θ) Iθ := by
    have h0 := Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma h.memAng2 hz
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using h0
  have hbdd := Work.FTS.EllipticEst.H2W.Ae.slice_pth_sq_le_pointwise (fun θ => u z θ)
    hsm hCz (h.dirZero z) (h.dirPi z) hint
  have hC0 : (0 : ℝ) ≤ Real.pi / 2 * ∫ θ in Iθ, (deriv (fun t : ℝ => deriv
      (fun θ' => u z θ') t) θ) ^ 2 * sg θ :=
    mul_nonneg (by positivity) (MeasureTheory.integral_nonneg_of_ae (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
        (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ) _)))
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (deriv (fun θ' => u z θ') θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    ((hsm.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).pow 2)
      |>.aestronglyMeasurable measurableSet_Ioo
  have h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => u z θ') θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ haesm
      (Real.pi / 2 * ∫ θ in Iθ, (deriv (fun t : ℝ => deriv (fun θ' => u z θ') t) θ) ^ 2
        * sg θ) ?_
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hbdd θ hθ
  have h3 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => u z θ') θ) ^ 2) Iθ := by
    have hmeas : MeasureTheory.volume.restrict Iθ
        = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
      (MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
          (b := Real.pi / 2))).symm
    change MeasureTheory.Integrable (fun θ => (deriv (fun θ' => u z θ') θ) ^ 2)
      (MeasureTheory.volume.restrict Iθ)
    rw [hmeas]
    exact h2
  have h4 : (fun θ : ℝ => (Work.Spaces.pth u z θ) ^ 2)
      = fun θ : ℝ => (deriv (fun θ' => u z θ') θ) ^ 2 := by
    funext θ
    simp only [Work.Spaces.pth]
  rw [h4]
  exact h3

/-- The untruncated `w²`-mass profile is integrable (this is `HkMem α 0 u`). -/
theorem integrableOn_mass_unt (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (u z θ) ^ 2)) Iz := by
  have hmem := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h
  obtain ⟨hint, -⟩ := Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral hmem
  refine hint.mono' ?_ ?_
  · exact ((Work.FTS.EllipticEst.Honest.measurable_wSq).aestronglyMeasurable).mul
      (aesm_P2 α u G h)
  · filter_upwards [ae_pos_Iz] with z hz
    have hle := slice_sq_le_sigma hmem hz
      (Work.Spaces.aesm_slice_of_continuousOn_Qd _
        ((smoothOpen_u α u G h).forall 0 |>.continuousOn.pow 2) hz)
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ∫ θ in Iθ, (u z θ) ^ 2 := integral_nonneg fun θ => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw2 h2)]
    exact mul_le_mul_of_nonneg_left hle hw2

/-- The truncated radial slot `∫_z φw²z²∫_θ (∂_zu)²` is integrable. -/
theorem integrableOn_radialProf (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (φ : ℝ → ℝ)
    (hφm : Measurable φ) (hφ0 : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1) :
    MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
      * (∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2)) Iz := by
  have hmem := Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  obtain ⟨hint, -⟩ := Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral hmem
  have hint' : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ)) Iz := hint
  refine hint'.mono' ?_ ?_
  · have haesm : AEStronglyMeasurable
        (fun z => ∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2) (MeasureTheory.volume.restrict Iz) :=
      aesm_profile_of_cont ((smoothOpen_u α u G h).pz.forall 0 |>.continuousOn.pow 2)
    exact (((hφm.mul Work.FTS.EllipticEst.Honest.measurable_wSq).mul
      (measurable_id.pow_const 2)).aestronglyMeasurable).mul haesm
  · filter_upwards [ae_pos_Iz] with z hz
    have haesm : AEStronglyMeasurable (fun θ => (Work.Spaces.pz u z θ) ^ 2)
        (MeasureTheory.volume.restrict Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _
        (((smoothOpen_u α u G h).pz.forall 0).continuousOn.pow 2) hz
    have hle := slice_sq_le_sigma (α := α) (f := fun z θ => z * Work.Spaces.pz u z θ)
      hmem hz (Work.Spaces.aesm_slice_of_continuousOn_Qd _
        ((continuousOn_fst.mul ((smoothOpen_u α u G h).pz.forall 0).continuousOn).pow 2) hz)
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2 := integral_nonneg fun θ => sq_nonneg _
    have hinner : (∫ θ in Iθ, (z * Work.Spaces.pz u z θ) ^ 2)
        = z ^ 2 * (∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2) := by
      rw [show (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
          = fun θ => z ^ 2 * (Work.Spaces.pz u z θ) ^ 2 from by funext θ; ring]
      rw [integral_const_mul]
    rw [show φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
        * (∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2)
        = φ z * (Work.Spaces.w z) ^ 2
          * (z ^ 2 * (∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2)) from by ring]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hφ0 z) hw2) (mul_nonneg
      (sq_nonneg _) h2))]
    calc φ z * (Work.Spaces.w z) ^ 2 * (z ^ 2 * (∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2))
        = φ z * ((Work.Spaces.w z) ^ 2 * (z ^ 2
            * (∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2))) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (z ^ 2
            * (∫ θ in Iθ, (Work.Spaces.pz u z θ) ^ 2)) := by
          simpa using mul_le_mul_of_nonneg_right (hφ1 z)
            (mul_nonneg hw2 (mul_nonneg (sq_nonneg z) h2))
      _ = (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (z * Work.Spaces.pz u z θ) ^ 2) := by
          rw [hinner]
      _ ≤ (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (z * Work.Spaces.pz u z θ) ^ 2 * sg θ) :=
          mul_le_mul_of_nonneg_left hle hw2

/-- The truncated source slot `∫_z φw²∫_θ G²σ` is integrable. -/
theorem integrableOn_srcProf (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (φ : ℝ → ℝ)
    (hφm : Measurable φ) (hφ0 : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1) :
    MeasureTheory.IntegrableOn (fun z => φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ)) Iz := by
  obtain ⟨hint, -⟩ := Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral h.memG
  refine hint.mono' ?_ ?_
  · have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
      intro p hp
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos])
    have hsig : ContinuousOn (fun p : ℝ × ℝ => sg p.2) Q0 :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
    have haesm : AEStronglyMeasurable (fun z => ∫ θ in Iθ, (G z θ) ^ 2 * sg θ)
        (MeasureTheory.volume.restrict Iz) :=
      aesm_profile_of_cont (((continuousOn_G α u G h).pow 2).mul hsig)
    exact (((hφm.mul Work.FTS.EllipticEst.Honest.measurable_wSq)).aestronglyMeasurable).mul haesm
  · filter_upwards with z
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ∫ θ in Iθ, (G z θ) ^ 2 * sg θ :=
      MeasureTheory.integral_nonneg_of_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
          (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ) _))
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg (hφ0 z) hw2) h2)]
    calc φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ)
        = φ z * ((Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ)) := by ring
      _ ≤ 1 * ((Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ)) :=
          mul_le_mul_of_nonneg_right (hφ1 z) (mul_nonneg hw2 h2)
      _ = (Work.Spaces.w z) ^ 2 * (∫ θ in Iθ, (G z θ) ^ 2 * sg θ) := one_mul _

end Work.FTS.EllipticEst.Prop.CutEnergyAux
