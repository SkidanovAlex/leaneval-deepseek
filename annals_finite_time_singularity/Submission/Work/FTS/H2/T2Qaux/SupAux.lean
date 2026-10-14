import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.wsSliceRight
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.AeMom.Repair.ShiftAeRepair =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeMom.Repair

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## §0 Two bookkeeping lemmas copied from `EllHyp_certificates.lean`
(`SmoothOpen.zsq_mul`, `HkMem_of_majorant_ae`; that module is currently unreachable because of the
`EllHyp` re-scope, but both lemmas are stated for the open quadrant and their proofs use nothing
from the re-scoped part). -/

/-- Multiplication of a `SmoothOpen` function by `z ^ 2` keeps it `SmoothOpen`. -/
theorem SmoothOpen.zsq_mul {Ψ : ℝ → ℝ → ℝ} (hu : SmoothOpen Ψ) : SmoothOpen (fun z θ => z ^ 2 * Ψ z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => z ^ 2 * Ψ z θ)) Q0
  rw [show Function.uncurry (fun z θ => z ^ 2 * Ψ z θ)
      = fun p : ℝ × ℝ => p.1 ^ 2 * Ψ p.1 p.2 from rfl]
  have hu' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Ψ p.1 p.2) Q0 := hu
  exact ((contDiffOn_fst (𝕜 := ℝ) (s := Q0)).pow 2).mul hu'


/-- **Membership in `ℋ^k` by an almost-everywhere majorant.**  The closed-quadrant version
`Work.FTS.LocData.HkMem_of_majorant` requires the domination at every point of
`[0,∞) × [0,π/2]`; here it is only required for almost every interior angle, which is what
the additivity of the `D`-operators on the open quadrant delivers. -/
theorem HkMem_of_majorant_ae (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2) Q0)
    (hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Set.Icc 0 (π / 2) := MeasureTheory.Ioo_ae_eq_Icc
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iθ := by
    intro z hz
    show IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) (Set.Icc 0 (π / 2))
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
      exact (Work.FTS.LocData.HkIntegrand_zero_fst α k f θ).symm
    · refine MeasureTheory.IntegrableOn.congr_set_ae ?_ hIoo.symm
      have hMioo : IntegrableOn (fun θ => M z θ) (Set.Ioo 0 (π / 2)) :=
        (hMslice z hz).congr_set_ae hIoo
      have hsl : ContinuousOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
          (Set.Ioo 0 (π / 2)) :=
        Work.FTS.LocData.continuousOn_slice_theta (G := Work.Spaces.HkIntegrand α k f) hcont hz0
      refine MeasureTheory.Integrable.mono' hMioo
        (hsl.aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [hle z hz] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
      exact hθ
  have houter : IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := by
    have hKnn : ∀ z ∈ Work.Spaces.Iz,
        0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
    have hKle : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
      intro z hz
      have hIθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (π / 2) := by
        show Set.Icc (0 : ℝ) (π / 2) =ᵐ[volume] Set.Ioo 0 (π / 2)
        exact hIoo.symm
      rw [MeasureTheory.setIntegral_congr_set hIθ,
        MeasureTheory.setIntegral_congr_set hIθ]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
        ((hMslice z hz).congr_set_ae hIoo) ?_
      filter_upwards [hle z hz] with θ hθ
      exact hθ
    refine MeasureTheory.Integrable.mono' hMz ?_ ?_
    · have hprod : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact hcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      have h1 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict (Set.Ioi 0)) :=
        hprod.integral_prod_right'
      have h2 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict Work.Spaces.Iz) := by
        rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
        exact h1
      have hfun : (fun z => ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.HkIntegrand α k f z θ)
          = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
        funext z
        exact MeasureTheory.setIntegral_congr_set hIoo
      rw [← hfun]
      exact h2
    · have hbnd : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
          ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ‖
            ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
        exact Filter.Eventually.of_forall fun z hz => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hKnn z hz)]
          exact hKle z hz
      exact hbnd
  exact ⟨hslice, houter⟩


/-! ## §1 The pointwise tools, copied from `Cores/Repair/DzShift.lean` -/


/-- **The source of the weak class is `C^∞` on the open quadrant.**  On `Q0` it agrees with
`bslOp α Ψ`, which is `C^∞` there by `SmoothOpen_bslOp_of_smoothOpen`. -/
theorem SmoothOpen_of_bslOp_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ) heq

/-- The shifted mixed slots: for `f` of class `C^∞` on the open quadrant and `(z,θ)` in the open
quadrant, `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`. -/
theorem mixed_Dz_shift_eq {j i : ℕ} (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Work.FTS.EllipticEst.remov.Step.Qd :=
    Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen f hg i
  have hpt : (z, θ) ∈ Work.FTS.EllipticEst.remov.Step.Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    Work.FTS.EllipticEst.remov.Step.DzIter_congr_of_isOpen Work.FTS.EllipticEst.remov.Step.isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, Work.FTS.EllipticEst.remov.Step.DzIter_Dz j (Work.Spaces.DthIter i f)]

/-- **The pointwise `D_z`-shift bound on the open quadrant.**  Every slot of
`HkIntegrand α (k-1) (D_z f)` is a slot of `HkIntegrand α k f` (up to the commutation of `D_z`
with `D_θ^i`), and each single slot is dominated by the whole integrand; counting `k` radial and
`k·k` mixed slots gives the factor `k + k²`. -/
theorem HkIntegrand_Dz_shift_le (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Work.FTS.EllipticEst.remov.Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [Work.FTS.EllipticEst.remov.Step.DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Work.FTS.EllipticEst.remov.Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2 := by
      unfold Work.FTS.EllipticEst.remov.Step.Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Work.FTS.EllipticEst.remov.Step.Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Work.FTS.EllipticEst.remov.Step.Msum_eq_rows, show k - 1 + 1 = k from by omega]
    have hterm : ∀ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hstep : (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _j ∈ Finset.range (k - i), Work.Spaces.HkIntegrand α k f z θ := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        by_cases hi1 : 1 ≤ i
        · rw [if_pos hi1]
          rw [mixed_Dz_shift_eq f hz hθ hg]
          have hj' : i + (j + 1) ≤ k := by
            have := Finset.mem_range.mp hj
            omega
          exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hi1 hj'
        · rw [if_neg hi1]
          exact hHnn
      refine le_trans hstep ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : k - i ≤ k := by omega
        exact_mod_cast this
      have hci : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) := by positivity
      nlinarith [hHnn, hcast, hci]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ _i ∈ Finset.range k, (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ)
        = ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hsum.le
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Zsum k f z θ + Work.FTS.EllipticEst.remov.Step.Msum α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]

/-- **Membership form of the `D_z`-shift**: if `f` is `C^∞` on the open quadrant and in
`ℋ^k` (`k ≥ 1`), then `D_z f ∈ ℋ^{k-1}`. -/
theorem HkMem_Dz_shift {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz f) := by
  refine HkMem_of_majorant_ae α (k - 1) (f := Work.Spaces.Dz f)
    (M := fun z θ => ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
    ?_ ?_ ?_ ?_
  · exact (Work.FTS.EllipticEst.SmoothOpen.Dz hf).continuousOn_HkIntegrand α (k - 1)
  · intro z hz
    exact (hmem.1 z hz).const_mul _
  · show MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
    simpa only [MeasureTheory.integral_const_mul] using hmem.2.const_mul _
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
    · subst h0
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ _ => by
        rw [Work.FTS.LocData.HkIntegrand_zero_fst α (k - 1) (Work.Spaces.Dz f) θ,
          Work.FTS.LocData.HkIntegrand_zero_fst α k f θ, mul_zero]
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ hθ =>
        HkIntegrand_Dz_shift_le α hk f hz0 hθ hf

/-- **`∂_z` commutes with `∂_θ²` on the open quadrant**: Clairaut's theorem applied twice. -/
theorem pz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) := by
  intro z θ hz hθ hlt
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      ContDiffAt ℝ 2 (Function.uncurry Ψ) (z', θ') := fun z' θ' hz' hθ' hlt' =>
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hΨ 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hlt'⟩))
  have hcd_pth : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) (z, θ) :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pth Ψ)).mp
      (Work.FTS.EllipticEst.SmoothOpen.pth hΨ) 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ :=
    Work.Spaces.pz_pth_comm (f := Work.Spaces.pth Ψ) hcd_pth
  have hagree : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pz (Work.Spaces.pth Ψ))
      (Work.Spaces.pth (Work.Spaces.pz Ψ)) :=
    fun z' θ' hz' hθ' hlt' => Work.Spaces.pz_pth_comm (f := Ψ) (hcd z' θ' hz' hθ' hlt')
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Ψ)) z θ :=
    Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
      (fun p hp => by
        obtain ⟨z', θ'⟩ := p
        exact hagree z' θ' hp.1 hp.2.1 hp.2.2) hmem
  show Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact h1.trans h2

/-- **`D_z` commutes with `∂_θ²` on the open quadrant.** -/
theorem Dz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)) := by
  have hplain := pz_pthIter_two_comm hΨ
  have hmul : Work.Spaces.pth (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ := by
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pz Ψ z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ
    rw [deriv_const_mul_field]
  have hstep : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ := by
    have h2 : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
        = Work.Spaces.pth (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ) := by
      rw [← hmul]
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
    rw [h2]
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
    rw [deriv_const_mul_field]
  intro z θ hz hθ hlt
  show z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ) z θ
  rw [hstep, hplain z θ hz hθ hlt]


/-! ## §2 Box integrability from a fibre bound, copied from `H2W/PsiSlices/PsiBox.lean` -/

/-! ## §5 Box integrability from a fibre bound -/

/-- **Integrability of a divided fibre bound.**  If the fibres `θ ↦ f r θ` are integrable with
`∫_θ |f r θ| ≤ B r` for `r ∈ (s,z]` and `B` is integrable there, then `(r,θ) ↦ f r θ / r` is
integrable on `(s,z] × Iθ`.  (This is the Tonelli step: the `θ`-integral of the absolute value
is dominated by `s⁻¹B`.) -/
theorem integrable_uncurry_div_of_fibre_bound {f : ℝ → ℝ → ℝ} {B : ℝ → ℝ} {s z : ℝ}
    (hs : 0 < s) (hsz : s ≤ z)
    (hae : AEStronglyMeasurable (Function.uncurry (fun r θ : ℝ => f r θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)))
    (hfib : ∀ r ∈ Set.Ioc s z, IntegrableOn (fun θ => f r θ) Work.Spaces.Iθ)
    (hle : ∀ r ∈ Set.Ioc s z, ∫ θ in Work.Spaces.Iθ, |f r θ| ≤ B r)
    (hB : IntegrableOn B (Set.Ioc s z)) :
    Integrable (Function.uncurry (fun r θ : ℝ => f r θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
  haveI : SFinite (volume.restrict (Set.Ioc s z)) := inferInstance
  haveI : SFinite (volume.restrict Work.Spaces.Iθ) := inferInstance
  have hG : Integrable (Function.uncurry (fun r θ : ℝ => |f r θ / r|))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine (Work.Spaces.integrable_prod_of_iterated (μ := volume.restrict (Set.Ioc s z))
      (ν := volume.restrict Work.Spaces.Iθ) (G := fun r θ => |f r θ / r|)
      (fun a b => abs_nonneg _) ?_ ?_ ?_).1
    · exact hae.norm.congr (Filter.Eventually.of_forall fun p => by
        simp only [Function.uncurry, Real.norm_eq_abs])
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
      have hr0 : 0 < r := lt_trans hs hr.1
      exact (((hfib r hr).norm.const_mul r⁻¹).congr
        (Filter.Eventually.of_forall fun θ => by
          simp only [Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr hr0)]
          ring))
    · refine (hB.const_mul s⁻¹).mono' ?_ ?_
      · exact (hae.norm.integral_prod_right'
          (μ := volume.restrict (Set.Ioc s z)) (ν := volume.restrict Work.Spaces.Iθ)).congr
          (Filter.Eventually.of_forall fun r => by
            simp only [Function.uncurry, Real.norm_eq_abs])
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
        have hr0 : 0 < r := lt_trans hs hr.1
        have hBnn : 0 ≤ B r := le_trans (integral_nonneg fun θ => abs_nonneg _) (hle r hr)
        rw [Real.norm_of_nonneg (integral_nonneg fun θ => abs_nonneg _)]
        have h1 : ∫ θ in Work.Spaces.Iθ, |f r θ / r| = (∫ θ in Work.Spaces.Iθ, |f r θ|) / r := by
          rw [← MeasureTheory.integral_div]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
          rw [abs_div, abs_of_pos hr0]
        rw [h1]
        have hstep1 : (∫ θ in Work.Spaces.Iθ, |f r θ|) / r ≤ B r / r :=
          div_le_div_of_nonneg_right (hle r hr) (le_of_lt hr0)
        have hstep2 : B r / r ≤ s⁻¹ * B r := by
          rw [div_eq_mul_inv, mul_comm (B r)]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ hs (le_of_lt hr.1)) hBnn
        exact le_trans hstep1 hstep2
  refine (MeasureTheory.integrable_norm_iff hae).mp ?_
  exact hG.congr (Filter.Eventually.of_forall fun p => by
    simp only [Function.uncurry, Real.norm_eq_abs])


/-! ## §3 The a.e. `Ψ`-moment, copied from `AeMom/FstarDzOnePsiAe.lean` -/


set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-! ## §1 Elementary angular facts -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Work.FTS.EllipticEst.H2W.sin_two_nonneg hθ


/-- `1 ≤ w u` for `u > 0`. -/
theorem one_le_w' {u : ℝ} (hu : 0 < u) : 1 ≤ Work.Spaces.w u := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith


/-- The angular weight `ρ θ = sin(2θ)^{-η}` is continuous on the open quadrant. -/
theorem continuousOn_rho_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.H2W.rho p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have h : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      Work.FTS.EllipticEst.Q0 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  simpa only [Work.FTS.EllipticEst.H2W.rho] using h


/-- The `θ`-slice of a function `C^∞` on the open quadrant is `C²` there. -/
theorem contDiffOn_slice_two {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {u : ℝ} (hu : 0 < u) :
    ContDiffOn ℝ 2 (fun θ : ℝ => f u θ) (Set.Ioo 0 (Real.pi / 2)) :=
  (hf.curry_θ hu).of_le (by simp [Work.Stability.smoothOrder])

/-! ## §2 The `ℋ¹`-level slice machinery -/

/-- **The weighted `θ`-energy of a `D_z`-slot is integrable.**  For `g` smooth on the open
quadrant with `g ∈ ℋ^k` and `i ≤ k`, the slice
`θ ↦ (D_z^i g(u,θ))² sin(2θ)^{-η}` is integrable on `Iθ` for every `u > 0`. -/
theorem slot_slice_integrableOn {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen g) (hm : Work.Spaces.HkMem α k g)
    (i : ℕ) (hi : i ≤ k) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ => (Work.Spaces.DzIter i g u θ) ^ 2
      * Work.FTS.EllipticEst.H2W.rho θ) Iθ := by
  have hI : IntegrableOn (fun θ => (Work.Spaces.DzIter i g u θ
      * Work.FTS.EllipticEst.H2W.Wf u θ) ^ 2) Iθ :=
    Work.FTS.EllipticEst.integrableOn_zSummand α k hs hm i hi (Set.mem_Ici.mpr hu.le)
  have hwu : Work.Spaces.w u ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_w' hu))
  have hWu : (Work.Spaces.w u) ^ 2 ≠ 0 := pow_ne_zero 2 hwu
  refine ((hI.mul_const ((Work.Spaces.w u) ^ 2)⁻¹).congr ?_)
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  rw [mul_pow, Work.FTS.EllipticEst.H2W.Wf_sq_eq (sin_two_nonneg_Iθ hθ),
    Work.FTS.EllipticEst.H2W.rho]
  field_simp [hWu]



/-! ## §3 The fibre bound for `D_z^iΨ`, `i ≤ 1` -/

/-- The majorant of `∫_θ |D_z^iΨ(u,θ)| sinθcos²θ` delivered by the slice moment/Taylor estimate,
built from the interior value and derivative at `π/4` and from the weighted `θ`-energy of
`∂_θ²(D_z^iΨ)`. -/
def Bnd2 (Ψ : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  4 + 4 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
    + 4 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
    + 2 * ∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
        * Work.FTS.EllipticEst.H2W.rho θ


/-- **The energy term of `Bnd2` is `z`-locally integrable.**  The proof replaces
`∂_θ²(D_z^iΨ)` by `D_z^i(∂_θ²Ψ)` (commuting the two derivatives), which is a slot of
`HkIntegrand α 1 (∂_θ²Ψ)`, and uses that the extra factor `w²` is bounded below by `1`. -/
theorem integrableOn_energy_level1 {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPosAe α k F Ψ) (i : ℕ) (hi : i ≤ 1) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => ∫ θ in Iθ,
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
          * Work.FTS.EllipticEst.H2W.rho θ) (Set.Ioc a b) := by
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hmemB : Work.Spaces.HkMem α 1 (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open hk
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp ((hso.pth).pth)) h.memB
  have hΨpth : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := (hso.pth).pth
  -- the two `θ`-integrands agree for `u > 0`
  have heq : ∀ u : ℝ, 0 < u →
      (∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
          * Work.FTS.EllipticEst.H2W.rho θ)
        = ∫ θ in Iθ, (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
            * Work.FTS.EllipticEst.H2W.rho θ := by
    intro u hu
    refine MeasureTheory.integral_congr_ae
      (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (p := fun θ =>
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
            * Work.FTS.EllipticEst.H2W.rho θ
          = (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
            * Work.FTS.EllipticEst.H2W.rho θ) ?_)
    intro θ hθ
    have hcomm := Work.EllipticEst.H2W.pthIter2_DzIter_comm hso i
      (show ((u, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hu, hθ⟩)
    simp only [Function.uncurry_apply_pair] at hcomm
    rw [hcomm]
  -- the slot integrability with the extra weight `w²`
  have hW : IntegrableOn (fun u : ℝ => (∫ θ in Iθ,
      (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
        * Work.FTS.EllipticEst.H2W.rho θ) * (Work.Spaces.w u) ^ 2) (Set.Ioc a b) := by
    have hIz := Work.FTS.EllipticEst.integrableOn_slice_Iz α 1 hΨpth hmemB i hi
    refine (hIz.mono_set ?_).congr ?_
    · intro u hu
      exact Set.mem_Ici.mpr (le_of_lt (lt_trans ha hu.1))
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u _
      rw [← MeasureTheory.integral_mul_const]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      show (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ
            * Work.FTS.EllipticEst.H2W.Wf u θ) ^ 2
          = ((Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
              * Work.FTS.EllipticEst.H2W.rho θ) * (Work.Spaces.w u) ^ 2
      rw [mul_pow, Work.FTS.EllipticEst.H2W.Wf_sq_eq (sin_two_nonneg_Iθ hθ)]
      ring
  -- a.e. strong measurability of the `z`-integral
  have haesm : AEStronglyMeasurable (fun u : ℝ =>
      ∫ θ in Iθ, (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
        * Work.FTS.EllipticEst.H2W.rho θ) (volume.restrict (Set.Ioc a b)) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.H2W.rho p.2) Work.FTS.EllipticEst.Q0 :=
      ((hΨpth.DzIter i).continuousOn.pow 2).mul continuousOn_rho_Q0
    have h := (Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont (le_of_lt ha))
      |>.integral_prod_right' (μ := volume.restrict (Set.Ioc a b))
        (ν := volume.restrict Iθ)
    simpa only [Function.uncurry_apply_pair] using h
  have hmono : IntegrableOn (fun u : ℝ => ∫ θ in Iθ,
      (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
        * Work.FTS.EllipticEst.H2W.rho θ) (Set.Ioc a b) := by
    refine hW.mono' haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u hu
    have hu0 : 0 < u := lt_trans ha hu.1
    have hnn : 0 ≤ ∫ θ in Iθ, (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
        * Work.FTS.EllipticEst.H2W.rho θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.rho_nonneg hθ)
    have hw : 1 ≤ (Work.Spaces.w u) ^ 2 := by
      have := one_le_w' hu0
      nlinarith
    show ‖∫ θ in Iθ, (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
        * Work.FTS.EllipticEst.H2W.rho θ‖ ≤ (∫ θ in Iθ,
          (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
            * Work.FTS.EllipticEst.H2W.rho θ) * (Work.Spaces.w u) ^ 2
    rw [Real.norm_of_nonneg hnn]
    have hstep := mul_le_mul_of_nonneg_left hw hnn
    rwa [mul_one] at hstep
  refine hmono.congr ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u hu
  exact (heq u (lt_trans ha hu.1)).symm

/-- `Bnd2 Ψ i` is integrable on `(a,b] ⊂ (0,∞)` for `i ≤ 1`. -/
theorem Bnd2_integrableOn {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPosAe α k F Ψ) (i : ℕ) (hi : i ≤ 1) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (Bnd2 Ψ i) (Set.Ioc a b) := by
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hpi : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun u hu => lt_of_lt_of_le ha hu.1
  have hraw1 : IntegrableOn (fun u : ℝ => Work.Spaces.DzIter i Ψ u (Real.pi / 4))
      (Set.Ioc a b) :=
    ((((hso.DzIter i).curry_z hpi).continuousOn.mono hsub).integrableOn_compact
      isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have h1 : IntegrableOn (fun u : ℝ => |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|)
      (Set.Ioc a b) :=
    ((((hso.DzIter i).curry_z hpi).continuousOn.mono hsub).abs.integrableOn_compact
      isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hraw2 : IntegrableOn (fun u : ℝ => Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4))
      (Set.Ioc a b) :=
    (((((hso.DzIter i).pth).curry_z hpi).continuousOn.mono hsub).integrableOn_compact
      isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun u : ℝ =>
      |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|) (Set.Ioc a b) :=
    (((((hso.DzIter i).pth).curry_z hpi).continuousOn.mono hsub).abs.integrableOn_compact
      isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have h3 : IntegrableOn (fun u : ℝ => ∫ θ in Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
        * Work.FTS.EllipticEst.H2W.rho θ) (Set.Ioc a b) :=
    integrableOn_energy_level1 hk h i hi ha
  have hone : IntegrableOn (fun _ : ℝ => (4 : ℝ)) (Set.Ioc a b) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hsum : IntegrableOn (fun u : ℝ => 4
      + 4 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
      + 4 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
      + 2 * ∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
          * Work.FTS.EllipticEst.H2W.rho θ) (Set.Ioc a b) :=
    ((hone.add (h1.const_mul 4)).add (h2.const_mul 4)).add (h3.const_mul 2)
  exact hsum.congr (Filter.Eventually.of_forall fun u => rfl)

/-! ## §4 Box integrability of `∂_zΨ·sinθcos²θ` -/

/-- A point of the box `(s,z] × Iθ` has first coordinate non-zero when `s > 0`. -/
theorem ae_fst_ne_zero {s z : ℝ} (hs : 0 < s) :
    ∀ᵐ p ∂((volume.restrict (Set.Ioc s z)).prod (volume.restrict Iθ)), p.1 ≠ 0 := by
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => p.1 ≠ 0)
    ((measurableSet_singleton 0).compl.preimage measurable_fst)]
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
  filter_upwards with θ
  exact ne_of_gt (lt_trans hs hr.1)


/-! ## §5 The integrated moment chain, and the conclusion -/



/-- `F_*(D_z f)(z) = z·F_*(∂_z f)(z)`. -/
theorem Fstar_Dz_eq (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Fstar (Work.Spaces.Dz f) z
      = z * Work.Elliptic.Fstar (Work.Spaces.pz f) z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => Work.Spaces.Dz f z θ * sg θ)
      = fun θ : ℝ => z * (Work.Spaces.pz f z θ * sg θ) from by
    funext θ; simp only [Work.Spaces.Dz]; ring]
  rw [MeasureTheory.integral_const_mul]



/-! ## §4 The a.e. radial shift, copied from `AeMom/shiftAe.lean` -/


open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Why this statement (it is the provable form of `Mine.ShiftLevel`):

`Work.FTS.EllipticEst.AeMom.EllWeakPosAe` (`AeMom/Defs.lean`) is `TT.EllWeakPos` with the two
angular-moment conditions required only **a.e.** on `(0,∞)`.  In that class the radial shift
holds at **every** `k ≥ 1`:

* the equation (`TT.bslOp_DzIter_eq`), the Dirichlet data (`TT.DzIter_zero_at_zero`,
  `TT.DzIter_zero_at_pi_half`), the smoothness (`EllWeakPos.smoothOpen_DzIter`) and the three
  `HkMem` descents (`TT.HkMem_descend_open`) are immediate;
* the two moment conditions of the shifted pair are the a.e. statements `Fstar (D_z F) ≡ 0` and
  `Fstar (D_z Ψ) ≡ 0`, i.e. exactly what the moment chain at `j = 0` yields from `HkMem α 1`-
  honesty (`Cert.GbarSin.FstarDzIter_chain_open` needs only `SmoothOpen`, `HkMem α k`, `1 ≤ k`):
  `Fstar f(z) - Fstar f(s) = ∫_s^z Fstar (D_z f)(r)/r dr`, whose left side is `0` a.e. when
  `Fstar f = 0` a.e., while its right side is continuous, so `Fstar (D_z f) = 0` a.e.
  No pointwise upgrade is needed — that is exactly what blocked the pointwise class at `k = 1`
  (`Mine.ShiftLevel`'s `k = 1` case is false as stated: the pointwise `Fstar (D_z F) ≡ 0` there
  needs `HkMem α 3 F`).

The nine-field bookkeeping is literally `Mine.ShiftLevel.shift_of_moments` (same fields,
`Fstar`-conditions replaced by their a.e. forms); the only new work is the two a.e. moment
arguments above (note that the existing `Mine.FstarDzOneF_ae` / `remov.Fstar_DzIter_one_Psi`
are stated for `TT.EllWeakPos`, so they must be re-derived, not applied as black boxes). -/

/-! ## The two a.e. moment conditions -/


/-! ## The nine-field assembly -/




end Work.FTS.EllipticEst.AeMom.Repair
end
end
-- ===== merged: Submission.Work.FTS.H2.T2Qaux.SupAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.T2Qaux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The radial Hardy inequality in `lintegral` form -/

/-- **The radial Hardy inequality in `lintegral` form.**  For a function `v` of class `C¹` on
`(0,∞)` with `v → 0` at `+∞`,

  `(v z)² ≤ ∫⁻_s (s · v'(s))² w(s)²`   for every `z > 0`,

where `w(s) = (1+s)²/s²`.  No integrability hypothesis is needed: if the `lintegral` is `⊤`
the claim is trivial, and otherwise the weighted square is integrable and the classical
(Hardy) inequality `Work.FTS.H2.HQ.HardyZQ` applies. -/
theorem hardyZQ_lintegral {v : ℝ → ℝ} (hcd : ContDiffOn ℝ 1 v (Set.Ioi (0 : ℝ)))
    (hdec : Tendsto v atTop (𝓝 0)) {z : ℝ} (hz : 0 < z) :
    ENNReal.ofReal ((v z) ^ 2) ≤ ∫⁻ s in Work.Spaces.Iz,
      ENNReal.ofReal ((s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2) := by
  -- continuity of `deriv v` on `(0,∞)`
  have hdvcont : ContinuousOn (deriv v) (Set.Ioi (0 : ℝ)) := by
    have h := hcd.continuousOn_derivWithin isOpen_Ioi.uniqueDiffOn le_rfl
    exact h.congr fun x hx => (derivWithin_of_isOpen isOpen_Ioi hx).symm
  have hcont : ContinuousOn (fun s : ℝ => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    have hw : ContinuousOn (fun s : ℝ => Work.Spaces.w s) (Set.Ioi (0 : ℝ)) := by
      unfold Work.Spaces.w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) fun x hx => ?_
      have hx0 : x ≠ 0 := ne_of_gt hx
      exact pow_ne_zero 2 hx0
    exact ((continuousOn_id.mul hdvcont).pow 2).mul (hw.pow 2)
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    have h1 : AEStronglyMeasurable
        (fun s : ℝ => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      hcont.aestronglyMeasurable measurableSet_Ioi
    have h2 : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
      rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
      exact (MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm
    rwa [h2]
  have hnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz]
      fun s : ℝ => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2 :=
    Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  by_cases htop : (∫⁻ s in Work.Spaces.Iz,
      ENNReal.ofReal ((s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)) = ⊤
  · rw [htop]; exact le_top
  · have hint : IntegrableOn (fun s : ℝ => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)
        Work.Spaces.Iz :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas hnn).mp htop
    have hH := Work.FTS.H2.HQ.HardyZQ v hcd hdec hint z (Set.mem_Ioi.mpr hz)
    calc ENNReal.ofReal ((v z) ^ 2)
        ≤ ENNReal.ofReal (∫ s, (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2
            ∂(volume.restrict Work.Spaces.Iz)) := ENNReal.ofReal_le_ofReal hH
      _ = ∫⁻ s in Work.Spaces.Iz,
            ENNReal.ofReal ((s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2) :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn

/-! ## A minimum below the average on the open interval -/



/-! ## The `ℋ⁴`-integrand and the iterated `lintegral` of `HkSq` -/

/-- `ofReal (HkSq α 4 f)` is the `z`-outer iterated `lintegral` of
`ofReal (HkIntegrand α 4 f · ·)`; only the two components of `HkMem` are used. -/
theorem ofReal_HkSq_eq_lintegral (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 f) :
    ENNReal.ofReal (Work.Spaces.HkSq α 4 f)
      = ∫⁻ s in Work.Spaces.Iz, ∫⁻ σ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f s σ) := by
  have hnn1 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz]
      fun s => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ :=
    Eventually.of_forall fun s =>
      integral_nonneg fun σ => Work.Spaces.HkIntegrand_nonneg α 4 f s σ
  have hstep : ENNReal.ofReal (Work.Spaces.HkSq α 4 f)
      = ∫⁻ s in Work.Spaces.Iz,
          ENNReal.ofReal (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2 hnn1
  rw [hstep]
  refine MeasureTheory.lintegral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ici ?_)
  intro s hs
  have hnn2 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      fun σ => Work.Spaces.HkIntegrand α 4 f s σ :=
    Eventually.of_forall fun σ => Work.Spaces.HkIntegrand_nonneg α 4 f s σ
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 s (Set.mem_Ici.mpr hs)) hnn2

/-- The closed rectangle `[0,∞) × [0,π/2]` agrees a.e. with the open quadrant
`(0,∞) × (0,π/2)` for the product of Lebesgue measure with itself; the two differences are
contained in the null sets `{0} × ℝ` and `ℝ × {0,π/2}`. -/
theorem ae_eq_quad : (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (π / 2) : Set (ℝ × ℝ))
    =ᵐ[volume.prod volume] (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
  have hnull2 : volume ({0, π / 2} : Set ℝ) = 0 := by
    rw [show ({0, π / 2} : Set ℝ) = {0} ∪ {π / 2} from rfl,
      measure_union_null_iff]
    exact ⟨measure_singleton 0, measure_singleton (π / 2)⟩
  have hnullA : (volume.prod volume) (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
    rw [MeasureTheory.Measure.prod_prod]; simp
  have hnullB : (volume.prod volume) ((Set.univ : Set ℝ) ×ˢ ({0, π / 2} : Set ℝ)) = 0 := by
    rw [MeasureTheory.Measure.prod_prod, hnull2, mul_zero]
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null (t := (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
        ∪ ((Set.univ : Set ℝ) ×ˢ ({0, π / 2} : Set ℝ))) ?_ ?_
    · rintro p ⟨hp, hnab⟩
      obtain ⟨a, b⟩ := p
      simp only [Set.mem_prod, Set.mem_Ici, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ioo] at hp hnab
      obtain ⟨ha, hb⟩ := hp
      obtain ⟨hb1, hb2⟩ := hb
      simp only [Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, Set.mem_union]
      rcases not_and_or.mp hnab with h | h
      · left
        exact ⟨le_antisymm (not_lt.mp h) ha, trivial⟩
      · right
        refine ⟨trivial, ?_⟩
        rcases eq_or_lt_of_le hb1 with h0 | h0
        · exact Or.inl (by simpa using h0.symm)
        · rcases eq_or_lt_of_le hb2 with hπ | hlt
          · exact Or.inr (by simpa using hπ)
          · exact absurd ⟨h0, hlt⟩ h
    · rw [measure_union_null_iff]; exact ⟨hnullA, hnullB⟩
  · have hsub : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))
        ⊆ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (π / 2)) := by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      simp only [Set.mem_prod, Set.mem_Ici, Set.mem_Icc, Set.mem_Ioo] at hb ⊢
      obtain ⟨hb1, hb2⟩ := hb
      exact ⟨le_of_lt ha, le_of_lt hb1, le_of_lt (by linarith [hb2, Real.pi_pos])⟩
    rw [Set.sdiff_eq_empty.mpr hsub]
    simp

/-- The uncurried `ℋ⁴`-integrand is a.e. strongly measurable for the product of the two
interval measures (taken in the `z`-first order). -/
theorem aesm_HkIntegrand_prod (α : ℝ) (f : ℝ → ℝ → ℝ) (hsq : Work.FTS.LocData.SmoothQuad f) :
    AEMeasurable (Function.uncurry fun s σ : ℝ =>
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f s σ))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 f hsq)
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2))
      ((volume.prod volume).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) :=
    hcont.aestronglyMeasurable (by measurability)
  have hmeq : (volume.prod volume).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact (MeasureTheory.Measure.restrict_congr_set (by
      rw [show ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)))
          = (Set.Ici 0 ×ˢ Set.Icc 0 (π / 2)) from rfl]
      exact ae_eq_quad)).symm
  rw [hmeq] at haesm
  exact haesm.aemeasurable


end Work.FTS.H2.T2Qaux
end
end
