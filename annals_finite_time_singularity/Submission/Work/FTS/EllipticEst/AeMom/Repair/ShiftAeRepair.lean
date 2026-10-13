/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AeMom/Repair/ShiftAeRepair` — the a.e.-class radial shift in a *buildable* module

This module provides, under the fresh namespace `Work.FTS.EllipticEst.AeMom.Repair` (so that it
can be imported *together* with the originals once the latter are repaired, without an
environment clash), the three declarations that the a.e.-class induction step of Proposition
`prop:Hk` needs and that are currently unreachable because of *broken transitive imports* of
their home modules:

* `AeMom.shiftAe` (`Submission/Work/FTS/EllipticEst/AeMom/shiftAe.lean`) — the radial shift in
  the a.e.-moment class, the whole point of `AeMom`;
* `AeMom.FstarDzOnePsiAe` (`Submission/Work/FTS/EllipticEst/AeMom/FstarDzOnePsiAe.lean`) — the
  `Ψ`-half of the shift, needed by `shiftAe`;
* `remov.Dz_pthIter_two_comm`, `remov.SmoothOpen_of_bslOp_eq`, `remov.HkMem_Dz_shift`
  (in `remov/EllWeakPos_DzIter_one_shift.lean`, and duplicated in `Cores/Repair/DzShift.lean`) —
  used by `shiftAe`'s assembly.

## Why a copy

The mathematical content of those modules is intact and `sorry`-free; they are unreachable for
purely *import-graph* reasons.  The offending import edges are

* `AeMom/shiftAe.lean → remov/EllWeakPos_DzIter_one_shift.lean → EllHyp_certificates` (whose
  consumers `Cert/HkMem_Gbar_sin.lean`, `Cert/HkMem_Fstar_sin.lean` currently fail), and
* `AeMom/FstarDzOnePsiAe.lean → H2W/PsiSlices/PsiBox.lean → AgmonSlice/zsq_pzIter2_mixed_open
  .lean → propHk_fts.lean → … → {ellHyp_L2Mem_fields, ellHyp_L2Mem_pz_weighted,
  Tools/ellHyp_pz_honesty_fts, RPFresh/excess_finite}` (all currently failing because of the
  `EllHyp.smooth : SmoothNbhd → SmoothInt` re-scope).

The declarations below are *faithful copies* of the proofs of those modules with those three
import edges replaced by their clean counterparts: the pointwise-`SmoothInt` tools from
`Cores/Repair/DzShift.lean` (which already performs exactly this repair for the pointwise class),
and `H2W.PsiSlices.integrable_uncurry_div_of_fibre_bound` copied out of `PsiBox.lean`.  Nothing
else is changed.  Once the offending modules build again, this file can be deleted and
`AeMom/EllEstUnifAe_step.lean` re-pointed at the originals.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.AeMom.Defs
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.TT.SliceDatum
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.integrable_prod_sq_restrict_open
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.H2W.SliceMomentLinear
import Submission.Work.FTS.EllipticEst.H2W.Norms
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.AeBasic
import Submission.Work.FTS.EllipticEst.Mine.SliceMomentTaylor
import Submission.Work.FTS.EllipticEst.Cert.radIter_Bmom_ae
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.integrable_prod_of_iterated

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

/-- `sinθcos²θ ≥ 0` on `Iθ`. -/
theorem sg_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ sg θ := by
  show 0 ≤ Real.sin θ * Real.cos θ ^ 2
  exact mul_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)

/-- `1 ≤ w u` for `u > 0`. -/
theorem one_le_w' {u : ℝ} (hu : 0 < u) : 1 ≤ Work.Spaces.w u := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith

/-- `sinθcos²θ` is continuous. -/
theorem continuous_sg : Continuous fun θ : ℝ => sg θ := by
  simp only [Work.Elliptic.sinCos2]
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

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

/-- The second angular derivative of a `z`-slice is the second iterate of `pth`. -/
theorem deriv_deriv_eq_pthIter2 {f : ℝ → ℝ → ℝ} (u : ℝ) :
    ∀ θ : ℝ, deriv (deriv (fun t : ℝ => f u t)) θ = Work.Spaces.pthIter 2 f u θ := by
  intro θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]

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

/-- **The weighted `θ`-energy of `∂_θ²(D_z^i Ψ)` is integrable, `i ≤ 1`.**  This is the only
place where the `ℋ¹`-honesty of `∂_θ²Ψ` (i.e. the hypothesis `1 ≤ k`, via `HkMem_descend_open`)
is used. -/
theorem sliceEnergy_level1 {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPosAe α k F Ψ) (i : ℕ) (hi : i ≤ 1) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
      * Work.FTS.EllipticEst.H2W.rho θ) Iθ := by
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hmemB : Work.Spaces.HkMem α 1 (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open hk
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp ((hso.pth).pth)) h.memB
  have h1 := slot_slice_integrableOn ((hso.pth).pth) hmemB i hi hu
  refine h1.congr ?_
  filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
    (p := fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
        * Work.FTS.EllipticEst.H2W.rho θ
      = (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
        * Work.FTS.EllipticEst.H2W.rho θ)
    (fun θ hθ => by
      have hcomm := Work.EllipticEst.H2W.pthIter2_DzIter_comm hso i
        (show ((u, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hu, hθ⟩)
      simp only [Function.uncurry_apply_pair] at hcomm
      rw [hcomm])] with θ hθ
  exact hθ.symm

/-- **The angular slice of `D_z^iΨ` against `sinθcos²θ` is integrable**, for `i ≤ 1`. -/
theorem sliceIntegrableOn_level1 {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPosAe α k F Ψ) (i : ℕ) (hi : i ≤ 1) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ => Work.Spaces.DzIter i Ψ u θ * sg θ) Iθ := by
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hen := sliceEnergy_level1 hk h i hi hu
  have hEn : IntegrableOn (fun θ => deriv (deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ)) θ ^ 2
      * Work.FTS.EllipticEst.H2W.rho θ) Iθ := by
    refine hen.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
    rw [deriv_deriv_eq_pthIter2 u θ]
  exact (Work.FTS.EllipticEst.H2W.sliceMomentLinear (contDiffOn_slice_two (hso.DzIter i) hu)
    hEn).1

/-! ## §3 The fibre bound for `D_z^iΨ`, `i ≤ 1` -/

/-- The majorant of `∫_θ |D_z^iΨ(u,θ)| sinθcos²θ` delivered by the slice moment/Taylor estimate,
built from the interior value and derivative at `π/4` and from the weighted `θ`-energy of
`∂_θ²(D_z^iΨ)`. -/
def Bnd2 (Ψ : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  4 + 4 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
    + 4 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
    + 2 * ∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
        * Work.FTS.EllipticEst.H2W.rho θ

/-- **The angular slice bound for `D_z^iΨ`, `i ≤ 1`.** -/
theorem sliceBound_level1 {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPosAe α k F Ψ) (i : ℕ) (hi : i ≤ 1) :
    ∀ u : ℝ, 0 < u →
      ∫ θ in Iθ, |Work.Spaces.DzIter i Ψ u θ| * sg θ ≤ Bnd2 Ψ i u := by
  intro u hu
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hen := sliceEnergy_level1 hk h i hi hu
  have hEn : IntegrableOn (fun θ => deriv (deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ)) θ ^ 2
      * Work.FTS.EllipticEst.H2W.rho θ) Iθ := by
    refine hen.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
    rw [deriv_deriv_eq_pthIter2 u θ]
  have hmain := (Work.FTS.EllipticEst.H2W.sliceMomentLinear
    (contDiffOn_slice_two (hso.DzIter i) hu) hEn).2
  have h1 : deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ) (Real.pi / 4)
      = Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4) := rfl
  have h2 : Work.FTS.EllipticEst.H2W.SliceEnergy (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ)
      = ∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
          * Work.FTS.EllipticEst.H2W.rho θ := by
    rw [Work.FTS.EllipticEst.H2W.SliceEnergy]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [deriv_deriv_eq_pthIter2 (f := Work.Spaces.DzIter i Ψ) u θ]
    rfl
  rw [h1, h2] at hmain
  rw [Bnd2]
  exact hmain

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

/-- **Box integrability of `∂_zΨ·sinθcos²θ` on `(s,z] × Iθ`**, at `ℋ¹`-honesty. -/
theorem boxIntegrable_pz_level1 {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPosAe α k F Ψ) {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z) :
    MeasureTheory.Integrable
      (Function.uncurry (fun r θ : ℝ => Work.Spaces.pz Ψ r θ * sg θ))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Iθ)) := by
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hr0 := ae_fst_ne_zero (s := s) (z := z) hs
  have hsm : ContinuousOn (Function.uncurry (fun r θ : ℝ => Work.Spaces.pz Ψ r θ * sg θ))
      Work.FTS.EllipticEst.Q0 :=
    (hso.pz.continuousOn).mul ((continuous_sg.comp continuous_snd).continuousOn)
  have hkey : ∀ p : ℝ × ℝ, p.1 ≠ 0 →
      Work.Spaces.Dz Ψ p.1 p.2 * sg p.2 / p.1 = Work.Spaces.pz Ψ p.1 p.2 * sg p.2 := by
    intro p hp
    simp only [Work.Spaces.Dz]
    field_simp
  have hae : AEStronglyMeasurable
      (Function.uncurry (fun r θ : ℝ => Work.Spaces.Dz Ψ r θ * sg θ / r))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Iθ)) :=
    (Work.FTS.EllipticEst.aesm_uncurry_restrict_open
      (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2 * sg p.2) hsm hs.le).congr (by
        filter_upwards [hr0] with p hp
        simp only [Function.uncurry]
        exact (hkey p hp).symm)
  have hfib : ∀ r ∈ Set.Ioc s z, IntegrableOn (fun θ : ℝ =>
      Work.Spaces.Dz Ψ r θ * sg θ) Iθ :=
    fun r hr => sliceIntegrableOn_level1 hk h 1 (by norm_num) (lt_trans hs hr.1)
  have hle : ∀ r ∈ Set.Ioc s z,
      ∫ θ in Iθ, |Work.Spaces.Dz Ψ r θ * sg θ| ≤ Bnd2 Ψ 1 r := by
    intro r hr
    have hsb := sliceBound_level1 hk h 1 (by norm_num) r (lt_trans hs hr.1)
    have heq : (∫ θ in Iθ, |Work.Spaces.Dz Ψ r θ * sg θ|)
        = ∫ θ in Iθ, |Work.Spaces.Dz Ψ r θ| * sg θ :=
      MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
          show |Work.Spaces.Dz Ψ r θ * sg θ| = |Work.Spaces.Dz Ψ r θ| * sg θ
          rw [abs_mul, abs_of_nonneg (sg_nonneg_Iθ hθ)]))
    rw [heq]
    exact hsb
  have hb := integrable_uncurry_div_of_fibre_bound
    hs hsz hae hfib hle (Bnd2_integrableOn hk h 1 (by norm_num) hs)
  refine hb.congr ?_
  filter_upwards [hr0] with p hp
  simp only [Function.uncurry]
  exact hkey p hp

/-! ## §5 The integrated moment chain, and the conclusion -/

/-- **The integrated moment chain for `Ψ`** in the a.e.-moment class: for `0 < s ≤ t`,
`F_* Ψ(t) - F_* Ψ(s) = ∫_s^t F_*(∂_zΨ)(r) dr`. -/
theorem chain_pz {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPosAe α k F Ψ) :
    ∀ s t : ℝ, 0 < s → s ≤ t →
      Work.Elliptic.Fstar Ψ t - Work.Elliptic.Fstar Ψ s
        = ∫ r in s..t, Work.Elliptic.Fstar (Work.Spaces.pz Ψ) r := by
  intro s t hs hst
  rcases eq_or_lt_of_le hst with heq | hlt
  · rw [← heq, sub_self, intervalIntegral.integral_same]
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  exact Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz hso hs hlt.le
    (sliceIntegrableOn_level1 hk h 0 (by norm_num) hs)
    (sliceIntegrableOn_level1 hk h 0 (by norm_num) (lt_of_lt_of_le hs hlt.le))
    (boxIntegrable_pz_level1 hk h hs hlt.le)

/-- The moment `F_*(∂_zΨ)` is interval integrable on every `(a,b) ⊂ (0,∞)`. -/
theorem intervalIntegrable_Fstar_pz {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPosAe α k F Ψ) :
    ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable (Work.Elliptic.Fstar (Work.Spaces.pz Ψ)) volume a b := by
  intro a b ha hab
  have hbox := boxIntegrable_pz_level1 hk h ha hab.le
  have hint : IntegrableOn (Work.Elliptic.Fstar (Work.Spaces.pz Ψ)) (Set.Ioc a b) := by
    have h1 := hbox.integral_prod_left
    refine h1.congr (Filter.Eventually.of_forall fun r => ?_)
    show (∫ θ, Function.uncurry (fun r θ : ℝ => Work.Spaces.pz Ψ r θ * sg θ) (r, θ)
        ∂(volume.restrict Iθ)) = Work.Elliptic.Fstar (Work.Spaces.pz Ψ) r
    rw [Work.Elliptic.Fstar]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => rfl)
  have hIcc : IntegrableOn (Work.Elliptic.Fstar (Work.Spaces.pz Ψ)) (Set.Icc a b) := by
    change Integrable (Work.Elliptic.Fstar (Work.Spaces.pz Ψ)) (volume.restrict (Set.Icc a b))
    rw [← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))]
    exact hint
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
  exact hIcc

/-- `F_*(D_z f)(z) = z·F_*(∂_z f)(z)`. -/
theorem Fstar_Dz_eq (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Fstar (Work.Spaces.Dz f) z
      = z * Work.Elliptic.Fstar (Work.Spaces.pz f) z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => Work.Spaces.Dz f z θ * sg θ)
      = fun θ : ℝ => z * (Work.Spaces.pz f z θ * sg θ) from by
    funext θ; simp only [Work.Spaces.Dz]; ring]
  rw [MeasureTheory.integral_const_mul]

/-- **The angular moment of `D_zΨ` vanishes almost everywhere** in the a.e.-moment weak class,
for every `k ≥ 1`. -/
theorem FstarDzOnePsiAe {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.AeMom.EllWeakPosAe α k F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0 := by
  have hV := Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_moment_chain
    (W := Work.Elliptic.Fstar Ψ)
    (V := Work.Elliptic.Fstar (Work.Spaces.pz Ψ))
    (chain_pz hk h) h.orthPsi (intervalIntegrable_Fstar_pz hk h)
  filter_upwards [hV, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz hzpos
  rw [show Work.Spaces.DzIter 1 Ψ = Work.Spaces.Dz Ψ from rfl, Fstar_Dz_eq, hz, mul_zero]


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

/-- **The `F`-half of the shift, almost everywhere.**  In the a.e.-moment class, the angular
moment of `D_z F` vanishes almost everywhere on `(0,∞)`.

This is `Mine.FstarDzOneF.FstarDzOneF_ae` with the pointwise vanishing of `F_*(F)` replaced by
the a.e. one.  The moment chain at `j = 0` (`Cert.GbarSin.FstarDzIter_chain_open`, whose
hypotheses are `SmoothOpen F`, `HkMem α 1 F` and `0 + 1 ≤ 1`) exhibits `z ↦ B_0(z) = F_*(F)(z)`
as a primitive of the locally integrable `r ↦ B_1(r)/r`, so `B_0` is continuous on `(0,∞)`
(`Cert.radIter_bmom_continuousOn`); since it is also a.e. zero, it is *identically* zero there
(`MeasureTheory.Measure.eqOn_of_ae_eq`).  The Lebesgue differentiation theorem
(`Cert.radIter_bmom_ae_hasDerivAt` at level `1`) then gives `0 = d/dz B_0 = B_1(z)/z` for almost
every `z`, i.e. `F_*(D_z F) = 0` a.e. -/
theorem FstarDzIter_one_F_ae {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPosAe α k F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0 := by
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    SmoothOpen_of_bslOp_eq
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mpr h.2.2.2.2.2.1)
      (fun z θ hz hθ hlt => h.1 z hz θ hθ hlt)
  have hmem1 : Work.Spaces.HkMem α 1 F :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open hk
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hSF) h.2.2.2.2.2.2.1
  -- `B_0 = F_*(F)` vanishes almost everywhere
  have hae0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.FTS.EllipticEst.Bmom F 0 z = 0 := by
    filter_upwards [h.2.2.2.1] with z hz
    rw [Work.FTS.EllipticEst.Bmom_zero]
    exact hz
  -- hence so does `B_1 = F_*(D_z F)`, since `B_0` is continuous and a.e. zero
  have hcont0 : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.Bmom F 0 z) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.radIter_bmom_continuousOn α 1 hSF hmem1 0 (by omega)
  have hzero : ∀ z : ℝ, 0 < z → Work.FTS.EllipticEst.Bmom F 0 z = 0 := by
    have hEq := MeasureTheory.Measure.eqOn_of_ae_eq hae0 hcont0 continuousOn_const
      (fun x hx => by rw [interior_Ioi]; exact subset_closure hx)
    intro z hz
    exact hEq hz
  have hd := Work.FTS.EllipticEst.Cert.radIter_bmom_ae_hasDerivAt α 1 hSF hmem1 (le_refl 1)
  rw [show (1 : ℕ) - 1 = 0 from rfl, MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hd
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hd] with z hzimp hzmem
  have hz0 : 0 < z := hzmem
  have hev : (fun w : ℝ => Work.FTS.EllipticEst.Bmom F 0 w) =ᶠ[𝓝 z]
      (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz0] with w hw
    exact hzero w hw
  have hder0 : HasDerivAt (fun _ : ℝ => (0 : ℝ))
      (Work.FTS.EllipticEst.Bmom F 1 z / z) z :=
    hev.hasDerivAt_iff.mp (hzimp hzmem)
  have hval : Work.FTS.EllipticEst.Bmom F 1 z / z = 0 :=
    hder0.unique (hasDerivAt_const z 0)
  rw [div_eq_zero_iff] at hval
  rcases hval with h' | h'
  · rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter] at h'
    exact h'
  · exact absurd h' hz0.ne'

/-! ## The nine-field assembly -/

/-- **The bookkeeping assembly of the radial shift in the a.e.-moment class**, with the two
moment conditions supplied as explicit hypotheses (in their a.e. form).

* the equation is preserved because `bslOp` commutes with `D_z`
  (`Work.FTS.EllipticEst.TT.bslOp_DzIter_eq`);
* the Dirichlet data are preserved (`TT.DzIter_zero_at_zero`, `..._pi_half`);
* the smoothness is preserved (`SmoothOpen.DzIter`);
* the `ℋ`-membership of the three fields follows from the pointwise domination
  `HkIntegrand α (k-1) (D_z g) ≤ ((k:ℝ)+(k:ℝ)*(k:ℝ)) * HkIntegrand α k g`
  (`Work.FTS.EllipticEst.remov.HkIntegrand_Dz_shift_le`, at the genuine `C^∞` order, via
  `HkMem_of_majorant_ae`) for `g ∈ {F, z²∂_zzΨ, ∂_θθΨ}`;
* the auxiliary identities are `pthIter 2 (D_z Ψ) = D_z (pthIter 2 Ψ)`
  (`remov.Dz_pthIter_two_comm`) and `z² ∂_zz(D_z Ψ) = D_z (z² ∂_zzΨ)`
  (`Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm`), both pointwise on the open quadrant. -/
theorem shiftAe_of_moments {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPosAe α k F Ψ)
    (hmomF : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0)
    (hmomΨ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0) :
    EllWeakPosAe α (k - 1) (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mpr h.2.2.2.2.2.1
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    SmoothOpen_of_bslOp_eq hSΨ
      (fun z θ hz hθ hlt => h.1 z hz θ hθ hlt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the equation commutes with `D_z`
    exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.2.2.2.2.2.1
      (fun z hz θ hθ hlt => h.1 z hz θ hθ hlt)
  · -- the Dirichlet data at `θ = 0`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ 1 h.2.1
  · -- the Dirichlet data at `θ = π/2`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ 1 h.2.2.1
  · -- the source moment condition
    exact hmomF
  · -- the solution moment condition
    exact hmomΨ
  · -- smoothness on the open quadrant is preserved by `D_z`
    intro n
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.DzIter 1 Ψ)).mp
      (hSΨ.DzIter 1) n
  · -- `D_z F ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz F) :=
      HkMem_Dz_shift hk hSF h.2.2.2.2.2.2.1
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hmem
  · -- `z² ∂_zz(D_z Ψ) ∈ ℋ^{k-1}`
    have hG : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      SmoothOpen.zsq_mul (hSΨ.pzIter 2)
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      HkMem_Dz_shift hk hG h.2.2.2.2.2.2.2.1
    have hEqOn := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hSΨ 1 0
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact (hEqOn (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
      from ⟨hz, hθ⟩)).symm
  · -- `∂_θθ(D_z Ψ) ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
      HkMem_Dz_shift hk
        (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2) h.2.2.2.2.2.2.2.2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact Dz_pthIter_two_comm hSΨ z θ hz hθ.1 hθ.2

/-- **The radially differentiated data are again of the a.e.-moment class, one level down**,
at every `k ≥ 1`.  The two a.e. moment conditions are `FstarDzIter_one_F_ae` (the `F`-half, by
the moment chain and the Lebesgue differentiation theorem) and `FstarDzOnePsiAe`
(`AeMom/FstarDzOnePsiAe.lean`, the `Ψ`-half). -/
theorem shiftAe (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.AeMom.EllWeakPosAe α k F Ψ) :
    Work.FTS.EllipticEst.AeMom.EllWeakPosAe α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
  shiftAe_of_moments hk h (FstarDzIter_one_F_ae hk h) (FstarDzOnePsiAe hk h)


end Work.FTS.EllipticEst.AeMom.Repair
