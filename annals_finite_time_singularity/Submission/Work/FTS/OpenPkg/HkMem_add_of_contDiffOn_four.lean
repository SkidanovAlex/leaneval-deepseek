import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceKit
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.SrdFork.EllWeakPos_DzIter_one_shift_fork
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.H2W.sliceStep4Uniform
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueEnergy.integrableOn_sqrtSliceE_and_boundU_of_energy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueEnergy

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "sliceE" => Work.FTS.EllipticEst.AngAWeak.sliceE

/-- **Local integrability of `√ sliceE`.**  The `hint`-free form of
`AngAWeak.integrableOn_sqrtSliceE_of_hint`: local integrability of `sliceE u` on `Icc a b`
implies that of its square root, because `sliceE u ≥ 0` and `√x ≤ 1 + x` for `x ≥ 0`. -/
theorem integrableOn_sqrtSliceE_of_local {u : ℝ → ℝ → ℝ} {a b : ℝ}
    (hloc : MeasureTheory.IntegrableOn (sliceE u) (Set.Icc a b)) :
    MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt (sliceE u s)) (Set.Icc a b) := by
  have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
    MeasureTheory.integrableOn_const (s := Set.Icc a b) (C := (1 : ℝ))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  refine Integrable.mono' (hloc.add hone) ?_ ?_
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable hloc.1
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with s hs
    have h0 : 0 ≤ sliceE u s := Work.FTS.EllipticEst.AngAWeak.sliceE_nonneg u s
    have hle : Real.sqrt (sliceE u s) ≤ 1 + sliceE u s :=
      Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [h0, sq_nonneg (sliceE u s)]⟩
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    simp only [Pi.add_apply]
    linarith [hle]

/-- **Local integrability of the dominating function `boundU`.**  The `hint`-free form of
`AngAWeak.integrableOn_boundU`: from `SmoothOpen u` (which makes `z ↦ |∂_z u(z,1)|` continuous on
`(0,∞)`) and the local integrability of `sliceE u`, the function
`boundU u K s = |∂_z u(s,1)| + M √(sliceE u s)/s` is integrable on `Icc a b` for `0 < a ≤ b`.

The proof is the one of `AngAWeak.integrableOn_boundU`, with `integrableOn_sqrtSliceE_of_local`
in place of `integrableOn_sqrtSliceE_of_hint` (so the weighted hypothesis disappears). -/
theorem integrableOn_boundU_of_local {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {a b : ℝ} (hloc : MeasureTheory.IntegrableOn (sliceE u) (Set.Icc a b))
    {K : ℝ} (hK : 0 < K) (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngAWeak.boundU u K) (Set.Icc a b) := by
  have hθ1 : (1 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
  have hMnn : 0 ≤ Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)) := by
    have := Real.sqrt_nonneg K
    have := Real.sqrt_nonneg (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
    linarith
  have hsqrt := integrableOn_sqrtSliceE_of_local hloc
  have hboundcont : ContinuousOn (fun s : ℝ => |Work.Spaces.pz u s 1|) (Set.Icc a b) :=
    (((hS.pz).curry_z hθ1).continuousOn.abs).mono (fun s hs => lt_of_lt_of_le ha hs.1)
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hboundcont
  have hdom : ∀ s ∈ Set.Icc a b, Work.FTS.EllipticEst.AngAWeak.boundU u K s ≤ C₁
      + ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
        * Real.sqrt (sliceE u s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have h1 : |Work.Spaces.pz u s 1| ≤ C₁ := by
      simpa only [Real.norm_eq_abs, abs_abs] using hC₁ s hs
    have h2 : Real.sqrt (sliceE u s) / s ≤ Real.sqrt (sliceE u s) / a := by
      gcongr
      exact hs.1
    have h5 : 0 ≤ (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
        * (Real.sqrt (sliceE u s) / s) := mul_nonneg hMnn (by positivity)
    rw [Work.FTS.EllipticEst.AngAWeak.boundU]
    have h6 : (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
        * (Real.sqrt (sliceE u s) / s)
        ≤ ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
          * Real.sqrt (sliceE u s) := by
      rw [show ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
            * Real.sqrt (sliceE u s)
          = (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceE u s) / a) by ring]
      exact mul_le_mul_of_nonneg_left h2 hMnn
    linarith
  have haesm : AEStronglyMeasurable (Work.FTS.EllipticEst.AngAWeak.boundU u K)
      (MeasureTheory.volume.restrict (Set.Icc a b)) := by
    have h1 : AEStronglyMeasurable (fun s : ℝ => |Work.Spaces.pz u s 1|)
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      hboundcont.aestronglyMeasurable measurableSet_Icc
    have hsqrt_ae : AEStronglyMeasurable (fun s => Real.sqrt (sliceE u s))
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hloc.1
    have hinv : ContinuousOn (fun s : ℝ => s⁻¹) (Set.Icc a b) :=
      ContinuousOn.inv₀ continuousOn_id (fun s hs => ne_of_gt (lt_of_lt_of_le ha hs.1))
    have h2 : AEStronglyMeasurable (fun s : ℝ => Real.sqrt (sliceE u s) * s⁻¹)
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      hsqrt_ae.mul (hinv.aestronglyMeasurable measurableSet_Icc)
    have h3 : AEStronglyMeasurable (fun s : ℝ => (Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceE u s) * s⁻¹))
        (MeasureTheory.volume.restrict (Set.Icc a b)) := h2.const_mul _
    refine AEStronglyMeasurable.congr (h1.add h3) ?_
    filter_upwards with s
    simp only [Pi.add_apply, Work.FTS.EllipticEst.AngAWeak.boundU]
    ring
  refine Integrable.mono' (g := fun s : ℝ => C₁
      + ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
        * Real.sqrt (sliceE u s)) ?_ haesm ?_
  · have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
      MeasureTheory.integrableOn_const (s := Set.Icc a b) (C := (1 : ℝ))
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    simpa using (hone.const_mul C₁).add (hsqrt.const_mul
      ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a))
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with s hs
    have h2 : 0 ≤ Work.FTS.EllipticEst.AngAWeak.boundU u K s := by
      rw [Work.FTS.EllipticEst.AngAWeak.boundU]
      have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
      have : 0 ≤ (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceE u s) / s) :=
        mul_nonneg hMnn (div_nonneg (Real.sqrt_nonneg _) hs0.le)
      linarith [abs_nonneg (Work.Spaces.pz u s 1)]
    rw [Real.norm_of_nonneg h2]
    exact hdom s hs

theorem integrableOn_sqrtSliceE_and_boundU_of_energy {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hE : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngAWeak.sliceE u) Work.Spaces.Iz)
    {K : ℝ} (hK : 0 < K) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn
        (fun s : ℝ => Real.sqrt (Work.FTS.EllipticEst.AngAWeak.sliceE u s)) (Set.Icc a b) ∧
      MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngAWeak.boundU u K) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun s hs => le_trans ha.le hs.1
  have hloc : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngAWeak.sliceE u)
      (Set.Icc a b) := hE.mono_set hsub
  exact ⟨integrableOn_sqrtSliceE_of_local hloc,
    integrableOn_boundU_of_local hS hloc hK ha hab⟩

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueEnergy
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.StraightMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.DiagEstEllT

set_option autoImplicit false
set_option maxHeartbeats 1000000




end Work.FTS.EllipticEst.Cores.DiagEstEllT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

noncomputable section

local notation "Iθ" => Work.Spaces.Iθ
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-- `∂_θ²Ψ(z,·)` in the `deriv`-shape used by `weakSliceDerivBound`. -/
private theorem pthIter_two_eq (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 Ψ z θ = deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ := rfl


/-! ## Auxiliary slices

The three lemmas below are the slice inputs of the target, proved here so that the final
estimate depends on nothing unproved. -/

/-- The second `θ`-derivative of the slice `D_zΨ(z,·)` is `z·∂_z∂_θ²Ψ(z,·)`. -/
private theorem deriv_deriv_Dz {Ψ : ℝ → ℝ → ℝ} (hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => deriv (fun θ' => Work.Spaces.Dz Ψ z θ') t) θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ := by
  have h2 : ∀ t : ℝ, deriv (fun θ'' => z * Work.Spaces.pz Ψ z θ'') t
      = z * deriv (fun θ'' => Work.Spaces.pz Ψ z θ'') t := fun t => deriv_const_mul_field z
  have h3 : deriv (fun t => deriv (fun θ'' => z * Work.Spaces.pz Ψ z θ'') t) θ
      = deriv (fun t => z * deriv (fun θ'' => Work.Spaces.pz Ψ z θ'') t) θ := by
    congr 1 with t
    exact h2 t
  show deriv (fun t => deriv (fun θ'' => z * Work.Spaces.pz Ψ z θ'') t) θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
  rw [h3, deriv_const_mul_field z]
  rw [show Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ from
    Work.FTS.EllipticEst.remov.pz_pthIter_comm_open Ψ hSΨ 2 z θ hz hθ.1 hθ.2]
  rfl

/-- **The `D_zΨ`-slot.**  For a datum of the weak class and `z > 0`, `(∂_θ(D_zΨ))²σ_γ` is
integrable on `Iθ`. -/
private theorem sliceDzInt {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont := weakSliceContinuousKit α F Ψ hα hα4 h z hz
  have hslots :=
    Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
  have hPzSlot : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * sEta θ) Iθ :=
    hslots.2.2.2.1
  have hDsmooth : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Work.Spaces.Dz Ψ z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    fun n => contDiffOn_iff_forall_nat_le.mp ((hSΨ.DzIter 1).curry_θ hz) n le_top
  -- the second derivative of the slice is the `(j = 1)`-slot of `∂_θ²Ψ`
  have hD2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Work.Spaces.Dz Ψ z θ') t) θ) ^ 2 * sEta θ) Iθ := by
    have hscaled : MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * sEta θ) Iθ := by
      refine (hPzSlot.const_mul (z ^ 2)).congr ?_
      filter_upwards with θ
      ring
    refine hscaled.congr ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [deriv_deriv_Dz hSΨ hz hθ]
  obtain ⟨hbd1, -⟩ := Work.FTS.EllipticEst.H2W.weakSliceDerivBound
    (fun θ => Work.Spaces.Dz Ψ z θ) hDsmooth hcont.2 (dz_zero_at_zero h z)
    (dz_zero_at_pi_half h z) hD2
  have hσint : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ :=
    (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (p := 2 - Work.Spaces.gam α)
      (by rw [Work.Spaces.gam]; linarith)).1
  refine Integrable.mono'
    (hσint.const_mul ((∫ θ in Iθ,
          (deriv (fun t => deriv (fun θ' => Work.Spaces.Dz Ψ z θ') t) θ) ^ 2 * sEta θ)
        * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))) ?_ ?_
  · refine (((measurable_deriv (fun θ' => Work.Spaces.Dz Ψ z θ')).pow_const 2).mul
      ((Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)).pow_const _)
      ).aestronglyMeasurable
  · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    have hs : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
      sig_nonneg α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hs)]
    exact mul_le_mul_of_nonneg_right (hbd1 θ hθ) hs

/-- **The lower-order slices.**  For a datum of the weak class and `z > 0`, the slices `∂_θΨ`
and `Ψ` of `z` are square-integrable on `Iθ` and their squares are dominated by the
`η`-weighted square of `∂_θ²Ψ`. -/
private theorem sliceLowerOrder {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => Ψ z θ') θ) ^ 2) Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Iθ ∧
    (∫ θ in Iθ, (deriv (fun θ' => Ψ z θ') θ) ^ 2)
        ≤ 4 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) ∧
    (∫ θ in Iθ, (Ψ z θ) ^ 2) ≤ 4 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont := weakSliceContinuousKit α F Ψ hα hα4 h z hz
  have hslots :=
    Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
  have hT2s : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2 * sEta θ) Iθ := by
    have h := hslots.2.2.1
    simp only [pthIter_two_eq] at h
    exact h
  have hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun n => contDiffOn_iff_forall_nat_le.mp (hSΨ.curry_θ hz) n le_top
  obtain ⟨hbd1, hbd2⟩ := Work.FTS.EllipticEst.H2W.weakSliceDerivBound (fun θ => Ψ z θ) hsmooth
    hcont.1 (h.zero z) (h.pi_half z) hT2s
  -- the `η`-slot in the shape of the statement
  have hT2b : (∫ θ in Iθ, (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2 * sEta θ)
      = (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) := rfl
  have hT2nn : 0 ≤ (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  have hB0nn : 0 ≤ (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ' hθ) _)
  have hB0le : (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) ≤ Real.pi / 2 :=
    (Work.FTS.EllipticEst.integrableOn_sin_two_rpow Work.Spaces.eta_nonneg).2
  have hvol : (volume : Measure ℝ) Iθ ≠ ⊤ := Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top
  have hvolreal : (volume : Measure ℝ).real Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def,
      show (volume : Measure ℝ) Iθ = ENNReal.ofReal (Real.pi / 2) from by
        rw [show Iθ = Set.Icc 0 (Real.pi / 2) from rfl, Real.volume_Icc, sub_zero],
      ENNReal.toReal_ofReal (by positivity)]
  have hconstval (c : ℝ) : (∫ _ in Iθ, c) = (Real.pi / 2) * c := by
    rw [MeasureTheory.setIntegral_const, hvolreal, smul_eq_mul]
  -- ## the two pointwise bounds on `(0,π/2)`
  have hpt1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (deriv (fun θ' => Ψ z θ') θ) ^ 2
        ≤ (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := by
    intro θ hθ
    have h := hbd1 θ hθ
    rwa [hT2b] at h
  have hpt2 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Ψ z θ| ≤ (Real.pi / 4) * Real.sin (2 * θ)
        * Real.sqrt ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))) := by
    intro θ hθ
    have h := hbd2 θ hθ
    rwa [hT2b] at h
  -- ## `∫(u')²`
  have hC1int : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => Ψ z θ') θ) ^ 2) Iθ := by
    refine Integrable.mono'
      (g := fun _ : ℝ => |(∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))|)
      (integrableOn_const (C := |(∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))|) hvol) ?_ ?_
    · exact ((measurable_deriv (fun θ' => Ψ z θ')).pow_const 2).aestronglyMeasurable
    · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact le_trans (hpt1 θ hθ) (le_abs_self _)
  have hC1le : (∫ θ in Iθ, (deriv (fun θ' => Ψ z θ') θ) ^ 2)
      ≤ 4 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) := by
    have hle : (∫ θ in Iθ, (deriv (fun θ' => Ψ z θ') θ) ^ 2)
        ≤ (Real.pi / 2) * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))) := by
      rw [← hconstval ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))]
      refine integral_mono_ae hC1int
        (integrableOn_const (C := ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))) hvol) ?_
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      exact hpt1 θ hθ
    have h2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
    have hπ : (Real.pi / 2) ^ 2 ≤ 4 := by nlinarith [h2]
    have hstep1 : (Real.pi / 2) * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))
        ≤ (Real.pi / 2) * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (Real.pi / 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hB0le hT2nn) (by positivity)
    have hstep2 : (Real.pi / 2) * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (Real.pi / 2))
        = (Real.pi / 2) ^ 2 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) := by
      ring
    have hstep3 : (Real.pi / 2) ^ 2 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        ≤ 4 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) :=
      mul_le_mul_of_nonneg_right hπ hT2nn
    linarith [hle, hstep1, hstep2, hstep3]
  -- ## `∫u²`
  have hpt3 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Ψ z θ) ^ 2
        ≤ ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
    intro θ hθ
    have hsI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ' hsI
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hnn : 0 ≤ (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := mul_nonneg hT2nn hB0nn
    have h1 : (Ψ z θ) ^ 2
        ≤ ((Real.pi / 4) * Real.sin (2 * θ)
            * Real.sqrt ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
              * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (Ψ z θ)) (hpt2 θ hθ) 2
      simpa only [sq_abs] using h
    have h2 : ((Real.pi / 4) * Real.sin (2 * θ)
          * Real.sqrt ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)))) ^ 2
        = ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (Real.sin (2 * θ)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hnn]
      ring
    have heta0 : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h3 : Real.sin (2 * θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
      have hz : (2 : ℝ) - Work.Spaces.eta ≤ 2 := by linarith [heta0]
      rw [← Real.rpow_natCast (Real.sin (2 * θ)) 2]
      exact Real.rpow_le_rpow_of_exponent_ge hspos hs1 hz
    have h4 : 0 ≤ (Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))) :=
      mul_nonneg (by positivity) (mul_nonneg hT2nn hB0nn)
    calc (Ψ z θ) ^ 2
        ≤ ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (Real.sin (2 * θ)) ^ 2 := by
          rw [h2] at h1
          exact h1
      _ ≤ ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) :=
          mul_le_mul_of_nonneg_left h3 h4
  have hsint : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)) Iθ :=
    (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (p := 2 - Work.Spaces.eta)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hC0int : MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Iθ := by
    refine Integrable.mono'
      (g := fun θ => ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
      (hsint.const_mul ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))) ?_ ?_
    · exact AEStronglyMeasurable.pow (hcont.1.aestronglyMeasurable measurableSet_Icc) 2
    · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpt3 θ hθ
  have hC0le : (∫ θ in Iθ, (Ψ z θ) ^ 2)
      ≤ 4 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) := by
    have hsle : (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)) ≤ Real.pi / 2 :=
      (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (p := 2 - Work.Spaces.eta)
        (by rw [Work.Spaces.eta]; norm_num)).2
    have hmono : (∫ θ in Iθ, (Ψ z θ) ^ 2)
        ≤ ∫ θ in Iθ, ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
      refine integral_mono_ae hC0int (hsint.const_mul _) ?_
      filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      exact hpt3 θ hθ
    rw [MeasureTheory.integral_const_mul] at hmono
    have h2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
    have h4 : Real.pi ^ 4 ≤ 256 := by nlinarith [h2, Real.pi_pos]
    have hπ : (Real.pi / 4) ^ 2 * (Real.pi / 2) * (Real.pi / 2) ≤ 4 := by
      have hval : (Real.pi / 4) ^ 2 * (Real.pi / 2) * (Real.pi / 2) = Real.pi ^ 4 / 64 := by ring
      rw [hval]
      linarith
    have hstep1 : ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))))
          * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        ≤ ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (Real.pi / 2)))
          * (Real.pi / 2) := by
      have hsnn : 0 ≤ (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)) :=
        setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
          Real.rpow_nonneg (sin_two_nonneg_Iθ' hθ) _)
      refine mul_le_mul ?_ hsle hsnn (by positivity)
      have h4 : 0 ≤ (Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (Real.pi / 2)) := by
        have hb : 0 ≤ (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            * (Real.pi / 2) := mul_nonneg hT2nn (by positivity)
        positivity
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB0le hT2nn) (by positivity)
    have hstep2 : ((Real.pi / 4) ^ 2 * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          * (Real.pi / 2))) * (Real.pi / 2)
        = ((Real.pi / 4) ^ 2 * (Real.pi / 2) * (Real.pi / 2))
          * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) := by
      ring
    have hstep3 : ((Real.pi / 4) ^ 2 * (Real.pi / 2) * (Real.pi / 2))
          * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        ≤ 4 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) :=
      mul_le_mul_of_nonneg_right hπ hT2nn
    linarith [hmono, hstep1, hstep2, hstep3]
  exact ⟨hC1int, hC0int, hC1le, hC0le⟩

/-- **The source slot.**  `∂_θ(Lzero1 u)` for the slice `u = Ψ(z,·)` is dominated by the three
source slots, `(a+b+c)² ≤ 3(a²+b²+c²)` with `Lzero1 u = F + α²z²∂_z²Ψ + α(5+α)D_zΨ`. -/
private theorem slot01SourceBound {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z)
    (hF : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth F z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ)
    (hA : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ)
    (hB : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1
        (fun t => Ψ z t) θ') θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ ∧
      (∫ θ in Iθ, (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ 3 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + α ^ 4 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the slice equation `Lzero1 u = F + α²z²∂_z²Ψ + α(5+α)D_zΨ` on the open interval
  have hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
        = F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α)) * Work.Spaces.Dz Ψ z θ := by
    intro θ hθ
    have hlt := Work.H2W.Lzero1_slice_eq (α := α) (G := F) (Φ := Ψ) (z := z) (θ := θ)
      (fun θ' h1 h2 => h.eq z hz θ' h1 h2) hθ
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hlt
  -- differentiability on the open interval of the three summands
  have hsm (G : ℝ → ℝ → ℝ) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
      ContDiffOn ℝ 2 (fun θ => G z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_iff_forall_nat_le.mp (hG.curry_θ hz) 2 le_top
  have hdF : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      DifferentiableAt ℝ (fun θ' => F z θ') θ := by
    intro θ hθ
    exact ((hsm F (smoothOpen_source h)).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hdA : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      DifferentiableAt ℝ (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ := by
    intro θ hθ
    have hcd : ContDiffOn ℝ 2 (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ')
        (Set.Ioo 0 (Real.pi / 2)) :=
      ContDiffOn.mul contDiffOn_const
        (contDiffOn_iff_forall_nat_le.mp ((hSΨ.pzIter 2).curry_θ hz) 2 le_top)
    exact (hcd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hdB : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      DifferentiableAt ℝ (fun θ' => Work.Spaces.Dz Ψ z θ') θ := by
    intro θ hθ
    exact (((hSΨ.DzIter 1).curry_θ hz).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  -- the derivative of the slice source
  have hderiv_eq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ
        = Work.Spaces.pth F z θ + α ^ 2 * deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
          + (α * (5 + α)) * deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ := by
    intro θ hθ
    have hfun : (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ')
        =ᶠ[𝓝 θ] (fun θ' => F z θ' + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ')
            + (α * (5 + α)) * Work.Spaces.Dz Ψ z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
      exact hode x hx
    have hder : HasDerivAt (fun θ' => F z θ' + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ')
        + (α * (5 + α)) * Work.Spaces.Dz Ψ z θ')
        (Work.Spaces.pth F z θ + α ^ 2 * deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
          + (α * (5 + α)) * deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) θ :=
      ((((hdF θ hθ).hasDerivAt).add (((hdA θ hθ).hasDerivAt).const_mul (α ^ 2))).add
        (((hdB θ hθ).hasDerivAt).const_mul (α * (5 + α))))
    rw [hfun.deriv_eq, hder.deriv]
  -- the pointwise bound
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        ≤ 3 * ((Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
    intro θ hθ
    have hs : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
      sig_nonneg α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsq := sq_add_three_le (Work.Spaces.pth F z θ)
      (α ^ 2 * deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ)
      ((α * (5 + α)) * deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ)
    rw [hderiv_eq θ hθ]
    calc (Work.Spaces.pth F z θ + α ^ 2 * deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
            + (α * (5 + α)) * deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        ≤ 3 * ((Work.Spaces.pth F z θ) ^ 2
              + (α ^ 2 * deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
              + ((α * (5 + α)) * deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
          mul_le_mul_of_nonneg_right hsq hs
      _ = 3 * ((Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by ring
  -- integrability and the integral bound
  have hdom : MeasureTheory.IntegrableOn
      (fun θ => 3 * ((Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))) Iθ :=
    (((hF.add (hA.const_mul (α ^ 4))).add (hB.const_mul ((α * (5 + α)) ^ 2)))).const_mul 3
  constructor
  · refine Integrable.mono' hdom ?_ ?_
    · refine ((measurable_deriv (fun θ' => Work.FTS.EllipticEst.Lzero1
          (fun t => Ψ z t) θ')).pow_const 2).mul
        ((Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)).pow_const _)
        |>.aestronglyMeasurable
    · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
      have hnn : 0 ≤ 3 * ((Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
        have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
          sig_nonneg α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
        positivity
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
        (sig_nonneg α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))]
      exact hpt θ hθ
  · have hmono : (∫ θ in Iθ, (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ ∫ θ in Iθ, 3 * ((Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
      refine integral_mono_of_nonneg ?_ hdom ?_
      · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
        exact mul_nonneg (sq_nonneg _) (sig_nonneg α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      · filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
        exact hpt θ hθ
    -- decompose the integral of the dominating function
    have hAint : MeasureTheory.IntegrableOn
        (fun θ => α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) Iθ := hA.const_mul (α ^ 4)
    have hBint : MeasureTheory.IntegrableOn
        (fun θ => (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) Iθ := hB.const_mul ((α * (5 + α)) ^ 2)
    have hABint : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) Iθ :=
      hF.add hAint
    have hIntDom : (∫ θ in Iθ, 3 * ((Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))))
        = 3 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + α ^ 4 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
      have hAB : (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
          = (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
            + (∫ θ in Iθ, (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) :=
        MeasureTheory.integral_add
          (f := fun θ => (Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
          (g := fun θ => (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) hABint hBint
      have hAsplit : (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
          = (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + α ^ 4 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
        have h := MeasureTheory.integral_add
          (f := fun θ => (Work.Spaces.pth F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          (g := fun θ => α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) hF hAint
        rw [MeasureTheory.integral_const_mul] at h
        exact h
      have hCsplit : (∫ θ in Iθ, (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
          = (α * (5 + α)) ^ 2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
        MeasureTheory.integral_const_mul ((α * (5 + α)) ^ 2) _
      calc (∫ θ in Iθ, 3 * ((Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))))
          = 3 * (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) :=
            MeasureTheory.integral_const_mul 3 _
        _ = 3 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
            + α ^ 4 * ((deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
            + (∫ θ in Iθ, (α * (5 + α)) ^ 2 * ((deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))) := by rw [hAB]
        _ = 3 * (((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + α ^ 4 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
            + (α * (5 + α)) ^ 2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by rw [hAsplit, hCsplit]
        _ = 3 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + α ^ 4 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (α * (5 + α)) ^ 2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by ring
    exact le_trans hmono (le_of_eq hIntDom)

theorem slot01SliceBound : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ → ∀ z, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ K * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ,
                (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Work.Spaces.Iθ,
                (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
  obtain ⟨Cs, hCs0, hCs⟩ := sliceStep4Uniform
  refine ⟨Cs * 16, by positivity, fun α F Ψ hα hα4 h z hz => ?_⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  -- ## the range of `γ`
  have hgam1 : 1 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hgam32 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  -- ## the slice data
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont := weakSliceContinuousKit α F Ψ hα hα4 h z hz
  have hsliceSmooth : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun n => contDiffOn_iff_forall_nat_le.mp (hSΨ.curry_θ hz) n le_top
  have hslots :=
    Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (α := α) (k := 2) le_rfl h z hz
  -- ## the five integrability inputs of `sliceStep4Uniform`
  -- (1) the left-hand side
  have hL : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ := by
    have hh := integrableOn_pth_mixed01 (f := Work.Spaces.pthIter 2 Ψ) hα hα4 h.memB hz
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hh
  -- (2) the `η`-slot `∫(u'')²sEta`
  have hT2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
      * sEta θ) Iθ := hslots.2.2.1
  -- (3), (4) the lower-order terms `u'`, `u`
  obtain ⟨hC1int, hC0int, hC1le, hC0le⟩ := sliceLowerOrder hα hα4 h hz
  -- (5) the three source slots and the source itself
  have hT1 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth F z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ :=
    integrableOn_pth_mixed01 hα hα4 h.memF hz
  have hT3 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ :=
    integrableOn_pth_mixed01 (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hα hα4
      h.memA hz
  have hT4 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Iθ := sliceDzInt hα hα4 h hz
  obtain ⟨hDint, hDle⟩ := slot01SourceBound hα hα4 h hz hT1 hT3 hT4
  -- ## the one-dimensional Step 4 on the slice
  have hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
        = (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ := fun _ _ => rfl
  have hmain := hCs (Work.Spaces.gam α) (fun θ => Ψ z θ)
    (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ')
    hgam1 hgam32 (hsliceSmooth 3) hcont.1 (h.zero z) (h.pi_half z) hode hL hT2 hC1int hC0int hDint
  -- ## nonnegativity of the four slots
  have hT1nn : 0 ≤ (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (sig_nonneg α hθ))
  have hT2nn : 0 ≤ (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  have hT3nn : 0 ≤ (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (sig_nonneg α hθ))
  have hT4nn : 0 ≤ (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (sig_nonneg α hθ))
  -- ## absorption of the coefficients
  have hα4le : α ^ 4 ≤ 1 := by nlinarith [hα, hα4]
  have hcoefle : (α * (5 + α)) ^ 2 ≤ 2 := by
    have h5 : 5 + α ≤ 21 / 4 := by linarith
    have hb : α * (5 + α) ≤ 1 / 4 * (21 / 4) :=
      mul_le_mul hα4 h5 (by linarith) (by norm_num)
    have hnn : 0 ≤ α * (5 + α) := by positivity
    calc (α * (5 + α)) ^ 2 ≤ (1 / 4 * (21 / 4)) ^ 2 := pow_le_pow_left₀ hnn hb 2
      _ ≤ 2 := by norm_num
  have hD' : (∫ θ in Iθ, (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ 3 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + 2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
    have h1 : α ^ 4 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) ≤
        (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
      mul_le_of_le_one_left hT3nn hα4le
    have h2 : (α * (5 + α)) ^ 2 * (∫ θ in Iθ,
          (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) ≤
        2 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
      mul_le_mul_of_nonneg_right hcoefle hT4nn
    linarith [hDle, h1, h2]
  -- ## assembly
  have hstep : (∫ θ in Iθ, (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
        + (∫ θ in Iθ, (deriv (fun θ' => Ψ z θ') θ) ^ 2)
        + (∫ θ in Iθ, (Ψ z θ) ^ 2)
      ≤ 3 * (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + 9 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          + 3 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + 6 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
    linarith [hD', hC1le, hC0le]
  have hfactor : 3 * (∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + 9 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          + 3 * (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + 6 * (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ 16 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            + (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
    linarith [hT1nn, hT2nn, hT3nn, hT4nn]
  have hfinal : (∫ θ in Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ Cs * (16 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            + (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))) := by
    have h1 : Cs * ((∫ θ in Iθ, (deriv (fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
          + (∫ θ in Iθ, (deriv (fun θ' => Ψ z θ') θ) ^ 2)
          + (∫ θ in Iθ, (Ψ z θ) ^ 2))
        ≤ Cs * (16 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            + (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))) :=
      mul_le_mul_of_nonneg_left (le_trans hstep hfactor) (le_of_lt hCs0)
    exact le_trans hmain h1
  calc (∫ θ in Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ Cs * (16 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            + (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))) := hfinal
    _ = Cs * 16 * ((∫ θ in Iθ, (Work.Spaces.pth F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * sEta θ)
            + (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by ring

end

end Work.H2W
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rl1.L12densN1Sum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.Rl1

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)

/-! ## The `N₁`-analogue of `N2_split` / `n3split` -/


/-! ## Slices: a.e. strong measurability and integrability of `K·f(s,·)/s` -/

/-- `SmoothQuad` data are continuous on the open quadrant `(0,∞) × (0,π/2)`. -/
theorem continuousOn_uncurry_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h := hsm
  rw [Work.FTS.LocData.SmoothQuad] at h
  refine h.continuousOn.mono (fun p hp => ⟨?_, hp.2⟩)
  exact Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0) hp.1

/-- The angular slice `θ ↦ f(s,θ)` of a `SmoothQuad` datum is a.e. strongly measurable on
`Iθ` for `s > 0`. -/
theorem aesm_slice_of_smoothQuad {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    {s : ℝ} (hs : 0 < s) :
    MeasureTheory.AEStronglyMeasurable (fun θ => f s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  simpa only [Function.uncurry] using
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f)
      (continuousOn_uncurry_of_smoothQuad hsm) hs



/-! ## The target -/


end Work.FTS.Nonlinear.Pieces.Rl1
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.envPth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

set_option maxHeartbeats 1600000

/-! ## The two auxiliary estimates -/

/-- The angular Cauchy–Schwarz partner of `∂_θ g`: with `γ = 1 + α/10`,

  `√(∫_θ sin(2θ)^{γ-2}) ≤ 10 √(10/α)`  (the sharp value of the integral is `≈ 10/α`).

`Work.Spaces.integral_sin_rpow` gives `∫_θ sin(2θ)^{γ-2} ≤ 100/(γ-1) = 1000/α`, and
`√(1000/α) = √100 · √(10/α) = 10 √(10/α)`. -/
theorem sqrt_integral_sin_rpow {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2))
      ≤ 10 * Real.sqrt (10 / α) := by
  have h := Work.Spaces.integral_sin_rpow α hα hα1
  have hg1 : Work.Spaces.gam α - 1 = α / 10 := by rw [Work.Spaces.gam]; ring
  rw [hg1] at h
  have h100 : (100 : ℝ) / (α / 10) = 1000 / α := by ring
  rw [h100] at h
  refine le_trans (Real.sqrt_le_sqrt h) ?_
  rw [show (1000 : ℝ) / α = 100 * (10 / α) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 100)]
  have h10 : Real.sqrt (100 : ℝ) = 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h10]

/-- The `θ`-slice of `∂_θ g` is integrable on `Iθ` for `r > 0`, for admissible data.

This is the only integrability fact the envelope needs: it lets the `∫⁻`-statement be
converted into one about the ordinary integral.  The bound is the AM–GM inequality
`|∂_θ g| = (|D_θg| sin^{-γ/2})·(sin^{γ/2-1}) ≤ ((D_θg)² sin^{-γ} + sin^{γ-2})/2`,
whose two terms are integrable because `(D_θg)² sin^{-γ} ≤ HkIntegrand α 4 g`
(`Dth_sq_le_HkIntegrand`) resp. `-1 < γ-2 ≤ 0` (`Work.Spaces.sin_two_rpow`). -/
theorem integrableOn_pth_slice {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) {r : ℝ}
    (hr : 0 < r) :
    MeasureTheory.IntegrableOn (fun θ => |Work.Spaces.pth g r θ|) Work.Spaces.Iθ := by
  -- the `D_θ`-slice, with its `sin(2θ)^{-γ}` weight, is dominated by the `ℋ⁴`-integrand
  have hDint : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ := by
    change Integrable
      (fun θ => (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (volume.restrict Work.Spaces.Iθ)
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
    refine Integrable.mono'
      ((hmem.1 r hr.le).mono_set (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩)) ?_ ?_
    · have hcont : ContinuousOn
          (fun θ => (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Set.Ioo (0 : ℝ) (π / 2)) :=
        ((Work.FTS.Nonlinear.Pieces.rl1Tools.continuousOn_Dth_slice hsm hr).pow 2).mul
          (((Real.continuous_sin.comp
            (continuous_const.mul continuous_id)).continuousOn).rpow_const
              (fun θ hθ => Or.inl
                (ne_of_gt (Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ))))
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hpt := Work.FTS.Nonlinear.Pieces.rl1Tools.Dth_sq_le_HkIntegrand α hα (g := g) hr hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ)) _))]
      exact hpt
  have hSint : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2)
      (by rw [Work.Spaces.gam]; linarith) (by rw [Work.Spaces.gam]; linarith)).1
  -- the AM–GM majorant
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ => ((Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) / 2) Work.Spaces.Iθ :=
    (hDint.add hSint).div_const 2
  refine Integrable.mono' hmaj ?_ ?_
  · -- a.e. strong measurability, from the identity `|∂_θg| = |D_θg|/sin(2θ)` on `(0,π/2)`
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
    have hQ : ContinuousOn
        (fun θ => |Work.Spaces.Dth g r θ| * (Real.sin (2 * θ))⁻¹) (Set.Ioo (0 : ℝ) (π / 2)) :=
      (Work.FTS.Nonlinear.Pieces.rl1Tools.continuousOn_Dth_slice hsm hr).abs.mul
        (ContinuousOn.inv₀
          ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
          (fun θ hθ => ne_of_gt (Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ)))
    have hQaesm : AEStronglyMeasurable
        (fun θ => |Work.Spaces.Dth g r θ| * (Real.sin (2 * θ))⁻¹)
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
      hQ.aestronglyMeasurable measurableSet_Ioo
    refine hQaesm.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    show |Work.Spaces.Dth g r θ| * (Real.sin (2 * θ))⁻¹ = |Work.Spaces.pth g r θ|
    have hs := Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.abs_Dth_eq hθ]
    rw [mul_assoc, mul_comm (|Work.Spaces.pth g r θ|) ((Real.sin (2 * θ))⁻¹), ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hs), one_mul]
  · -- the pointwise AM–GM bound
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hs := Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ
    set A : ℝ := |Work.Spaces.Dth g r θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
      with hA
    set B : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1) with hB
    have hpow : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
      congr 1
      ring
    have hA2 : A ^ 2
        = (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [hA, mul_pow, sq_abs, hpow]
    have hpowB : ((Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1)) ^ 2
        = (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
      congr 1
      ring
    have hB2 : B ^ 2 = (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2) := by
      rw [hB, hpowB]
    have hab : |Work.Spaces.pth g r θ| = A * B := by
      have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
            * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1)
          = (Real.sin (2 * θ)) ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hs]
        congr 1
        ring
      rw [hA, hB, mul_assoc, h1, Work.FTS.Nonlinear.Pieces.rl1Tools.abs_Dth_eq hθ,
        Real.rpow_neg_one]
      rw [mul_comm (Real.sin (2 * θ)) (|Work.Spaces.pth g r θ|), mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hs), mul_one]
    rw [Real.norm_eq_abs, abs_abs, hab]
    calc A * B ≤ (A ^ 2 + B ^ 2) / 2 := by nlinarith [sq_nonneg (A - B)]
      _ = ((Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            + (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) / 2 := by
          rw [hA2, hB2]

/-! ## The target -/

theorem envPth {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.pth g r θ|))
      ≤ ENNReal.ofReal (10 * Real.sqrt (10 / α) * Work.Spaces.HkNorm α 4 g) := by
  set cc : ℝ := 10 * Real.sqrt (10 / α) with hcc
  have hcc_nn : 0 ≤ cc := by rw [hcc]; positivity
  have hsqrtC := sqrt_integral_sin_rpow hα hα1
  have hsqrtC' : Real.sqrt (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) ≤ cc := by rw [hcc]; exact hsqrtC
  -- ## The per-slice estimate
  have key : ∀ r : ℝ, 0 < r →
      ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.pth g r θ|)
        ≤ ENNReal.ofReal (cc * (r / (1 + r) ^ 2) *
            Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)) := by
    intro r hr
    have hw : 0 < Work.Spaces.w r := Work.FTS.Nonlinear.Pieces.rl1Tools.w_pos_of_pos hr
    have hzw : r⁻¹ = Work.Spaces.w r * (r / (1 + r) ^ 2) := by
      rw [Work.Spaces.w, inv_eq_one_div]; field_simp
    have hint := integrableOn_pth_slice hα hα1 hsm hmem hr
    have hlin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.pth g r θ|)
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pth g r θ|) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun θ => abs_nonneg _)).symm
    -- Cauchy–Schwarz in `θ`, with the `D_θ`-slot of the `ℋ⁴`-integrand
    have hreal :=
      Work.FTS.Nonlinear.Pieces.rl1Tools.slice_pth_abs_le_sqrt α hα hα1 hsm hmem r hr
    have hslot : (Work.Spaces.w r) ^ 2 *
          (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 r hr.le) ?_
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        refine mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) ?_)
        refine Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
      · rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
        exact Work.FTS.Nonlinear.Pieces.rl1Tools.w2_Dth_sq_le_HkIntegrand α hα hr hθ
    -- the radial weight `r⁻¹ = w(r)·r/(1+r)²` and `w(r)√E ≤ √(∫_θ HkIntegrand)`
    have hwE : Work.Spaces.w r *
          Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) := by
      rw [show Work.Spaces.w r * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          = Real.sqrt ((Work.Spaces.w r) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
          by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hw)]]
      exact Real.sqrt_le_sqrt hslot
    have hinner : r⁻¹ * (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pth g r θ|)
        ≤ cc * (r / (1 + r) ^ 2) *
            Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) := by
      calc r⁻¹ * (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pth g r θ|)
          ≤ r⁻¹ * (Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
              * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2))) :=
            mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr hr.le)
        _ = (Work.Spaces.w r * (r / (1 + r) ^ 2)) *
              (Real.sqrt (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                  (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2))) := by rw [hzw]
        _ = (r / (1 + r) ^ 2) *
              ((Work.Spaces.w r * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.Dth g r θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
                * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                    (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2))) := by ring
        _ ≤ (r / (1 + r) ^ 2) *
              (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) * cc) := by
            refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hr.le (by positivity))
            exact mul_le_mul hwE hsqrtC' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = cc * (r / (1 + r) ^ 2) *
              Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) := by ring
    rw [hlin, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
    exact ENNReal.ofReal_le_ofReal hinner
  -- ## The radial Hölder step
  have hae : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.pth g r θ|)
        ≤ ENNReal.ofReal (cc * (r / (1 + r) ^ 2) *
            Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => key r hr)
  have hmain := Work.FTS.Nonlinear.Pieces.rl1Tools.radial_of_sqrt
    (J := fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
    (A := fun r => ENNReal.ofReal r⁻¹ *
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.pth g r θ|))
    (c := cc) hcc_nn (hmem.2.mono_set Set.Ioi_subset_Ici_self)
    (fun r => MeasureTheory.integral_nonneg
      fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g r θ) hae
  rw [← Work.FTS.Nonlinear.Pieces.rl1Tools.HkSq_eq_integral_Ioi α g] at hmain
  refine le_trans hmain ?_
  rw [hcc]
  exact le_of_eq rfl

end Work.FTS.Nonlinear.Pieces.rl1Pieces
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.FourFactors =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The open quadrant of the interior estimates: `(0,∞) × (0,π/2)`. -/
abbrev Q0 : Set (ℝ × ℝ) := Work.FTS.EllipticEst.Q0

/-- A radial function, as a function of the two self-similar variables. -/
abbrev Rad (R : ℝ → ℝ) : Fn := fun z (_ : ℝ) => R z

/-- **The `C⁴`-smoothness of the factors of the 27 pieces of the §8 assembly.** -/
structure FourFactors (α : ℝ) (g Φs Φg : Fn) : Prop where
  /-- the perturbation and its three first-order operators -/
  hg : ContDiffOn ℝ 4 (Function.uncurry g) Q0
  hpthg : ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.pth g)) Q0
  hDzg : ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.Dz g)) Q0
  hDthg : ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.Dth g)) Q0
  /-- the fixed profile `F_*` and its two operators -/
  hF : ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.Fstar α)) Q0
  hpthF : ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.pth (Work.Construction.Fstar α))) Q0
  hDzF : ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.Dz (Work.Construction.Fstar α))) Q0
  /-- the four radial functions -/
  hL12g : ContDiffOn ℝ 4 (Function.uncurry (Rad (Work.Construction.L12 g))) Q0
  hL12F : ContDiffOn ℝ 4
    (Function.uncurry (Rad (Work.Construction.L12 (Work.Construction.Fstar α)))) Q0
  hFKg : ContDiffOn ℝ 4 (Function.uncurry (Rad (Work.Construction.FK g))) Q0
  hFKF : ContDiffOn ℝ 4
    (Function.uncurry (Rad (Work.Construction.FK (Work.Construction.Fstar α)))) Q0
  /-- the residuals transported by `Rop`, `Uop`, `Vop` -/
  hRopTg : ContDiffOn ℝ 4
    (Function.uncurry (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))) Q0
  hUopTg : ContDiffOn ℝ 4
    (Function.uncurry (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg))) Q0
  hVopTg : ContDiffOn ℝ 4
    (Function.uncurry (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))) Q0
  hRopTs : ContDiffOn ℝ 4
    (Function.uncurry (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) Q0
  hUopTs : ContDiffOn ℝ 4
    (Function.uncurry (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) Q0
  hVopTs : ContDiffOn ℝ 4
    (Function.uncurry (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))) Q0

/-! ## Elementary closure facts used by the piece lemmas -/


/-- `cos 2θ - sin²θ` is smooth on the quadrant. -/
theorem contDiffOn_c2m_Q0 (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (fun (_ : ℝ) (θ : ℝ) =>
      Real.cos (2 * θ) - Real.sin θ ^ 2)) Q0 :=
  (((Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd)).sub
    ((Real.contDiff_sin.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top


end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## PRIVATE WORKSPACE — the finite-order subadditivity of `HkIntegrand`

The target of this module is the closure of `Work.Spaces.HkMem α 4` under addition for data which
are only `C^4` (not `C^∞`) on the open quadrant `Q0 = (0,∞) × (0,π/2)`.  Two ingredients:

* the `ℋ^4`-integrand of `f + g` is *continuous on the open quadrant* (for measurability, via
  `HkMem_of_majorant`).  Its summands are the weighted derivatives of `f+g`, which are continuous
  as long as `f+g` is `C^4` there, and the weights `w`, `sin(2θ)^{-η/2}`, `W` are continuous for
  `z > 0`, `0 < θ < π/2`;
* the *pointwise* subadditivity `HkIntegrand α k (f+g) ≤ 2 (HkIntegrand α k f + HkIntegrand α k g)`
  on all of `Iz × Iθ`, which only needs the additivity of the iterated operators on the open
  quadrant (for `C^k`-data) and vanishing of both sides on the two boundary lines.

Everything is stated for a general pair `(k, n)` with `k ≤ n` so that the `Finset.range (k+1)`
bookkeeping of `HkIntegrand` matches the definition verbatim; the target is the instance
`k = n = 4`. -/

/-! ### The weights on the open quadrant -/

private lemma sin_two_pos_Q0 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
  simp only [Work.Spaces.w]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

private lemma continuousOn_sinpow_Q0 (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.EllipticEst.Q0 :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_Q0 hp.2)))

private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  exact continuousOn_w_Q0.mul (continuousOn_sinpow_Q0 (-(Work.Spaces.gam α / 2)))

private lemma continuousOn_wdivsin_Q0 :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      Work.FTS.EllipticEst.Q0 :=
  continuousOn_w_Q0.div (continuousOn_sinpow_Q0 (Work.Spaces.eta / 2))
    (fun _p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_Q0 hp.2) _))

/-! ### Continuity of the integrand for finite-order data -/

/-- **The `ℋ^k`-integrand of a `C^n` function is continuous on the open quadrant** (`k ≤ n`).

Each `D_z`-slot `D_z^i f` with `i ≤ k` is `C^{n-i}` on `Q0` (`contDiffOn_DzIter_fin`), hence
continuous; each mixed slot `D_z^jD_θ^i f` with `i + j ≤ k` is obtained from the `C^{n-i}`
function `D_θ^i f` by `D_z^j` (`i + j ≤ n`), hence continuous as well.  The weights are the
previous lemmas. -/
theorem continuousOn_HkIntegrand_of_contDiffOn (α : ℝ) {n k : ℕ} (hkn : k ≤ n)
    {F : ℝ → ℝ → ℝ} (hF : ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hDz : ∀ i ≤ k, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    intro i hi
    exact (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin
      Work.FTS.EllipticEst.isOpen_Q0 hF i (by omega)).continuousOn
  have hMx : ∀ (j i : ℕ), i ≤ k → i + j ≤ k →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
    intro j i hik hij
    have hDth := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
      Work.FTS.EllipticEst.isOpen_Q0 hF i (by omega)
    have hz := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin
      Work.FTS.EllipticEst.isOpen_Q0 hDth j (by omega)
    exact hz.continuousOn
  simp only [Work.Spaces.HkIntegrand]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    exact ((hDz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).mul
      continuousOn_wdivsin_Q0).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1))
      (fun i hi => continuousOn_finsetSum (Finset.range (k + 1)) (fun j hj => ?_))
    split_ifs with hc
    · exact ((hMx j i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hc.2).mul
        (continuousOn_Wt_Q0 α)).pow 2
    · exact continuousOn_const

/-! ### Additivity of the iterated operators on the open quadrant

For `C^n`-data on `Q0` (with `n ≥ 1`) the operators `D_z^j` and `D_θ^i` are additive on `Q0`,
because `deriv` is additive at every point of the open set. -/

/-- Slices of a `C^k` (`k ≥ 1`) function on the open quadrant are differentiable in `z`. -/
private lemma slice_diffAt_fst {h : ℝ → ℝ → ℝ} {m n : ℕ}
    (hh : ContDiffOn ℝ (n - m) (Function.uncurry h) Work.FTS.EllipticEst.Q0) (hm : m < n)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun z' => h z' θ) z := by
  have hslice : ContDiffOn ℝ (n - m) (fun z' => h z' θ) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_z_fin (s := Set.Ioi 0)
      (t := Set.Ioo 0 (π / 2)) hh hθ
  have hne : ((n - m : ℕ) : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (show n - m ≠ 0 by omega)
  exact (hslice.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-- Slices of a `C^k` (`k ≥ 1`) function on the open quadrant are differentiable in `θ`. -/
private lemma slice_diffAt_snd {h : ℝ → ℝ → ℝ} {m n : ℕ}
    (hh : ContDiffOn ℝ (n - m) (Function.uncurry h) Work.FTS.EllipticEst.Q0) (hm : m < n)
    {z θ : ℝ} (hz : z ∈ Set.Ioi 0) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun θ' => h z θ') θ := by
  have hslice : ContDiffOn ℝ (n - m) (fun θ' => h z θ') (Set.Ioo 0 (π / 2)) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_θ_fin (s := Set.Ioi 0)
      (t := Set.Ioo 0 (π / 2)) hh hz
  have hne : ((n - m : ℕ) : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (show n - m ≠ 0 by omega)
  exact (hslice.differentiableOn hne).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-- Functions agreeing on the open quadrant have the same `D_z`-iterates there. -/
private lemma DzIter_congr_Q0 {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j F z θ = Work.Spaces.DzIter j G z θ := by
  induction j with
  | zero => exact h
  | succ m ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter m F z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter m G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq]

/-- The operators `D_z^j` are additive on the open quadrant for `C^n`-data. -/
private theorem DzIter_add_of_contDiffOn {n : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ j ≤ n, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DzIter j f z θ + Work.Spaces.DzIter j g z θ := by
  intro j
  induction j with
  | zero => intro _ z θ _ _ _; rfl
  | succ m ih =>
      intro hm z θ hz h1 h2
      have hm' : m ≤ n := by omega
      have hlt : m < n := by omega
      have heq : (fun z' => Work.Spaces.DzIter m (fun z θ => f z θ + g z θ) z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter m f z' θ + Work.Spaces.DzIter m g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih hm' z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter m f z' θ) z :=
        slice_diffAt_fst
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin
            Work.FTS.EllipticEst.isOpen_Q0 hf m hm') hlt hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter m g z' θ) z :=
        slice_diffAt_fst
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin
            Work.FTS.EllipticEst.isOpen_Q0 hg m hm') hlt hz ⟨h1, h2⟩
      have hd : deriv (fun z' => Work.Spaces.DzIter m f z' θ
            + Work.Spaces.DzIter m g z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter m f z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter m g z' θ) z := deriv_add hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- The operators `D_θ^i` are additive on the open quadrant for `C^n`-data. -/
private theorem DthIter_add_of_contDiffOn {n : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ i ≤ n, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ := by
  intro i
  induction i with
  | zero => intro _ z θ _ _ _; rfl
  | succ m ih =>
      intro hm z θ hz h1 h2
      have hm' : m ≤ n := by omega
      have hlt : m < n := by omega
      have heq : (fun θ' => Work.Spaces.DthIter m (fun z θ => f z θ + g z θ) z θ') =ᶠ[𝓝 θ]
          (fun θ' => Work.Spaces.DthIter m f z θ' + Work.Spaces.DthIter m g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)]
          with θ' hθ'
        exact ih hm' z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter m f z θ') θ :=
        slice_diffAt_snd
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
            Work.FTS.EllipticEst.isOpen_Q0 hf m hm') hlt hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter m g z θ') θ :=
        slice_diffAt_snd
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
            Work.FTS.EllipticEst.isOpen_Q0 hg m hm') hlt hz ⟨h1, h2⟩
      have hd : deriv (fun θ' => Work.Spaces.DthIter m f z θ'
            + Work.Spaces.DthIter m g z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter m f z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter m g z θ') θ := deriv_add hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

/-- The mixed operators `D_z^j D_θ^i` are additive on the open quadrant for `C^n`-data
(`i + j ≤ n`). -/
private theorem mixed_add_of_contDiffOn {n : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (j i : ℕ) (hij : i + j ≤ n) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := by
  intro z θ hz h1 h2
  have hDth : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ :=
    DthIter_add_of_contDiffOn hf hg i (by omega)
  have hstep : Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter j (fun z θ => Work.Spaces.DthIter i f z θ
          + Work.Spaces.DthIter i g z θ) z θ := by
    simp only [Work.Spaces.mixed]
    exact DzIter_congr_Q0 (F := Work.Spaces.DthIter i (fun z θ => f z θ + g z θ))
      (G := fun z θ => Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ)
      hDth j z θ hz h1 h2
  rw [hstep]
  have hadd := DzIter_add_of_contDiffOn (n := n - i)
    (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
      Work.FTS.EllipticEst.isOpen_Q0 hf i (by omega))
    (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
      Work.FTS.EllipticEst.isOpen_Q0 hg i (by omega))
    j (by omega)
  simpa only [Work.Spaces.mixed] using hadd z θ hz h1 h2

/-! ### Pointwise subadditivity of the integrand -/

/-- **Pointwise subadditivity of the `ℋ^k`-integrand for `C^n` (with `k ≤ n`) data on the open
quadrant.**  The two boundary lines contribute `0 ≤ 0`; in the interior every slot is split by
`(a+b)² ≤ 2a² + 2b²` using the additivity of the iterated operators. -/
private theorem HkIntegrand_add_le_of_contDiffOn {α : ℝ} {k n : ℕ} (hkn : k ≤ n)
    {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * (Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ) := by
  intro z hz θ hθ
  by_cases hz0 : z = 0
  · subst hz0
    have hz0' : ∀ X : ℝ → ℝ → ℝ, Work.Spaces.HkIntegrand α k X 0 θ = 0 :=
      fun X => Work.FTS.LocData.HkIntegrand_zero_fst α k X θ
    simp only [hz0']
    norm_num
  by_cases hs : Real.sin (2 * θ) = 0
  · have hs' : ∀ X : ℝ → ℝ → ℝ, Work.Spaces.HkIntegrand α k X z θ = 0 :=
      fun X => Work.FTS.EllipticEst.RegQ.HkIntegrand_zero_sin_fts α k X hs z
    simp only [hs']
    norm_num
  · have hzpos : 0 < z := lt_of_le_of_ne (show (0 : ℝ) ≤ z from hz) (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := Set.mem_Icc.mp hθ
    have hθ0 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h' | h'
      · exact absurd (by rw [← h']; simp) hs
      · exact h'
    have hθ1 : θ < Real.pi / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h' | h'
      · exact h'
      · exact absurd (by rw [h', show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring,
          Real.sin_pi]) hs
    have hDz : ∀ i : ℕ, i ≤ k → Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ :=
      fun i hi => DzIter_add_of_contDiffOn hf hg i (by omega) z θ hzpos hθ0 hθ1
    have hMixed : ∀ j i : ℕ, i + j ≤ k →
        Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
          = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ :=
      fun j i hij => mixed_add_of_contDiffOn hf hg j i (by omega) z θ hzpos hθ0 hθ1
    simp only [Work.Spaces.HkIntegrand]
    have hZ : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      calc (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ i ∈ Finset.range (k + 1),
              (2 * (Work.Spaces.DzIter i f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
                + 2 * (Work.Spaces.DzIter i g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            rw [hDz i hik, add_mul]
            nlinarith [sq_nonneg (Work.Spaces.DzIter i f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
              - Work.Spaces.DzIter i g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
        _ = 2 * (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + 2 * (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0)
          ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (2 * (if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
                + 2 * (if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ k
            · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left hc, hMixed j i hc.2, add_mul]
              nlinarith [sq_nonneg (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ
                - Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ)]
            · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc]
              norm_num
        _ = 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
            + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
            simp only [Finset.sum_add_distrib, Finset.mul_sum]
    linarith [hZ, hM]

/-- `HkMem` is closed under addition at order 4 for data that are `C^4` on the open quadrant `Q0 = (0,∞) × (0,π/2)` — the finite-order companion of `Work.FTS.EllipticEst.HkMem_add_smoothOpen`.

Proof recipe: `Work.FTS.LocData.HkMem_of_majorant` with `M := 2 * HkIntegrand α 4 f + 2 * HkIntegrand α 4 g` reduces to
(a) `ContinuousOn (fun p => HkIntegrand α 4 (f+g) p.1 p.2) Q0`, from `ContDiffOn ℝ 4 (uncurry (f+g)) Q0` via `RegQ.contDiffOn_DzIter_fin` / `RegQ.contDiffOn_DthIter_fin` (`Submission/Work/FTS/EllipticEst/RegQ/pthU_slot_alg.lean`) and the continuity of the weights `w`, `wTheta`, `Wt` on `Q0` (see `Submission/Work/Spaces/continuousOn_HkIntegrand_Qd.lean` for the pattern), and
(b) the pointwise bound `HkIntegrand α 4 (f+g) ≤ 2 * HkIntegrand α 4 f + 2 * HkIntegrand α 4 g` on `Iz × Iθ`, either by re-running the slot argument of `Work.FTS.EllipticEst.RegQ.HkIntegrand_slot_le` with coefficients `(1,1)`, or by instantiating `HkIntegrand_slot_le` (stated for `E = -3f - αg` and the *same* `α` as the weight exponent) at `E := f+g`, `f := fun z θ => -(f z θ)/3`, `g := fun z θ => -(g z θ)/α`: the identity `f+g = -3·(-f/3) - α·(-g/α)` holds for `α ≠ 0`, and `Work.FTS.LocData.HkIntegrand_const_mul` converts `18·I_{(-f/3)} + 2·I_{α·(-g/α)}` into `2·I_f + 2·I_g`. At `z = 0` and at `sin(2θ) = 0` both sides vanish (`Q2.HkIntegrand_zero_z_fts`, `Q2.HkIntegrand_zero_sin_fts`). -/
theorem HkMem_add_of_contDiffOn_four {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 4 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g) :
    Work.Spaces.HkMem α 4 (fun z θ => f z θ + g z θ) := by
  refine Work.FTS.LocData.HkMem_of_majorant α 4
    (f := fun z θ => f z θ + g z θ)
    (M := fun z θ => 2 * (Work.Spaces.HkIntegrand α 4 f z θ
      + Work.Spaces.HkIntegrand α 4 g z θ)) ?_ ?_ ?_ ?_
  · exact continuousOn_HkIntegrand_of_contDiffOn (n := 4) (k := 4) α le_rfl
      ((hf.add hg).congr (fun p _ => by simp only [Function.uncurry]))
  · intro z hz
    exact ((hmf.1 z hz).add (hmg.1 z hz)).const_mul 2
  · refine IntegrableOn.congr_fun ((hmf.2.add hmg.2).const_mul 2) ?_ measurableSet_Ici
    intro z hz
    show 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      = ∫ θ in Work.Spaces.Iθ, 2 * (Work.Spaces.HkIntegrand α 4 f z θ
          + Work.Spaces.HkIntegrand α 4 g z θ)
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hmf.1 z hz) (hmg.1 z hz)]
  · exact HkIntegrand_add_le_of_contDiffOn (k := 4) (n := 4) le_rfl hf hg

end Work.FTS.OpenPkg
end
