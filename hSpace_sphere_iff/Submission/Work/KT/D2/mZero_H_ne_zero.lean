import Mathlib
import Submission.Work.KT.D2.mZero
import Submission.Work.KT.D2.Basic
import Submission.Work.KT.D2.PAM_clutching_not_nullhomotopic
import Submission.Work.KT.Dim2.circle_log_facts
import Submission.Work.KT.D2.mZeroH_defs
import Submission.Work.KT.D2.mZeroH_wind_sum_zero
import Submission.Work.KT.D2.degNZ_eq_zero_homotopic_const_one

/-!
# `Work.KT.D2.mZero_H_ne_zero` — the Bott class has non-zero winding

`Work.KT.D2.mZero y0 hy0` is the integer winding invariant of an idempotent matrix over
`Kpair ℝ² = C(D²/S¹)`, computed on the boundary circle through a trivialising family of units.
The disc-model Bott class is `PA`, the Hopf idempotent, and

`Work.KT.D2.mZero y0 hy0 PA`

is the degree of the boundary loop of the chosen trivialisation `mZeroH_U y0` of `PA`
(`Work.KT.D2.mZeroH_mZero_eq`).

The argument is the `K`-theoretic form of the computation of `K̃(S²) = ℤ`:

* The companion inverse family `mZeroH_V y0` carries the constant rank-one projection `e0M` to the
  disc family of `PA` (`mZeroH_V_clutch`), so `Work.KT.D2.PAM_clutching_not_nullhomotopic` applies
  to it: the `(0,0)` entry of its boundary loop — which is exactly its block-determinant loop
  `psiV = wlmDet 2 e0M (mZeroH_V y0).comp inBallCM` — is not null-homotopic.  A loop of degree
  zero is null-homotopic (`degNZ_eq_zero_homotopic_const_one`), hence that winding is non-zero.
* On the boundary circle the two families are pointwise inverse to one another and diagonal with
  respect to `e0M`, so they commute with `e0M` there; additivity of the winding under the pointwise
  product (`mZeroH_wind_sum_zero`) then gives
  `windLoop (mZeroH_U) = - windLoop (mZeroH_V) = - degNZ psiV ≠ 0`.

Hence `mZero y0 hy0 PA ≠ 0`.
-/

namespace Work.KT.D2

open Matrix
open Classical

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The companion trivialisation of the Bott class -/

/-- The inverse trivialising family `mZeroH_V` conjugates the boundary value `e0M` of `PA` to the
disc family of `PA`: `mZeroH_V y0 y * e0M = PA(y) * mZeroH_V y0 y` for every `y` in the disc.

Route: `mZeroH_U y0 y * PA(y) = e0M * mZeroH_U y0 y` is `trivU_spec`, with `e0M` the boundary
value of `PA` at `y0 ∈ S¹`; bracketing with the two-sided inverse `mZeroH_V y0 y` gives
`PA(y) * mZeroH_V = mZeroH_V * e0M`. -/
lemma mZeroH_V_clutch (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) (y : Ball (Euc 2)) :
    mZeroH_V y0 y * e0M = (PAM.map (augPair (Euc 2) y)) * mZeroH_V y0 y := by
  have hU : mZeroH_U y0 y * (PAM.map (augPair (Euc 2) y)) = e0M * mZeroH_U y0 y := by
    have h : mZeroH_U y0 y * toCM 2 PAM y = bval 2 y0 PAM * mZeroH_U y0 y :=
      (trivU_spec y0 PA PA_idem).2.2 y
    rw [mZeroH_bval_eq_e0M y0 hy0] at h
    exact h
  have hvu := mZeroH_V_mul_U y0 y
  have huv := mZeroH_U_mul_V y0 y
  have key : (PAM.map (augPair (Euc 2) y)) * mZeroH_V y0 y = mZeroH_V y0 y * e0M := by
    calc (PAM.map (augPair (Euc 2) y)) * mZeroH_V y0 y
        = (mZeroH_V y0 y * mZeroH_U y0 y) * (PAM.map (augPair (Euc 2) y))
            * mZeroH_V y0 y := by rw [hvu, Matrix.one_mul]
      _ = mZeroH_V y0 y * (mZeroH_U y0 y * (PAM.map (augPair (Euc 2) y)))
            * mZeroH_V y0 y := by noncomm_ring
      _ = mZeroH_V y0 y * (e0M * mZeroH_U y0 y) * mZeroH_V y0 y := by rw [hU]
      _ = mZeroH_V y0 y * e0M * (mZeroH_U y0 y * mZeroH_V y0 y) := by noncomm_ring
      _ = mZeroH_V y0 y * e0M := by rw [huv, Matrix.mul_one]
  exact key.symm

/-- The disc family of `PA` at a boundary point is its boundary value `e0M`. -/
lemma mZeroH_PAM_inBall (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) (x : Sph (Euc 2)) :
    PAM.map (augPair (Euc 2) (inBall x)) = e0M := by
  rw [← mZeroH_bval_eq_e0M y0 hy0, ← toCM_inBall 2 PAM y0 hy0 x]
  rfl

/-! ## The boundary loop of the companion trivialisation -/

/-- The `(0,0)` entry of the boundary loop of `mZeroH_V` is nowhere zero: on the boundary circle
`mZeroH_V` is invertible and diagonal with respect to `e0M`, so the block determinant
`det (e0M * V * e0M + (1 - e0M)) = V 0 0` does not vanish. -/
lemma mZeroH_V_entry_ne (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) :
    ∀ x, mZeroH_V y0 (inBall x) 0 0 ≠ 0 := by
  intro x
  have h := blk_det_ne_zero (e := e0M) (u := mZeroH_V y0 (inBall x))
    (v := mZeroH_U y0 (inBall x)) e0M_idem (mZeroH_V_comm y0 hy0 x)
    (mZeroH_V_mul_U y0 (inBall x)) (mZeroH_U_mul_V y0 (inBall x))
  rwa [det_e0M_block] at h

/-- The block determinant of the boundary loop of `mZeroH_V` is nowhere zero. -/
lemma mZeroH_V_ne (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) :
    ∀ x, Matrix.det (e0M * ((mZeroH_V y0).comp inBallCM) x * e0M + (1 - e0M)) ≠ 0 := by
  intro x
  rw [det_e0M_block]
  exact mZeroH_V_entry_ne y0 hy0 x

/-- The `(0,0)` entry of the boundary loop of `mZeroH_V`, as a continuous complex loop. -/
def psiV (y0 : Ball (Euc 2)) : C(Sph (Euc 2), ℂ) :=
  ⟨fun x => mZeroH_V y0 (inBall x) 0 0,
    ((mZeroH_V y0).comp inBallCM).continuous.matrix_elem 0 0⟩

@[simp] lemma psiV_apply (y0 : Ball (Euc 2)) (x : Sph (Euc 2)) :
    psiV y0 x = mZeroH_V y0 (inBall x) 0 0 := rfl

/-- `psiV` is the block-determinant loop of `mZeroH_V`. -/
lemma wlmDet_V (y0 : Ball (Euc 2)) :
    wlmDet 2 e0M ((mZeroH_V y0).comp inBallCM) = psiV y0 := by
  apply ContinuousMap.ext
  intro x
  simp only [wlmDet_apply, psiV_apply, ContinuousMap.comp_apply, inBallCM_apply,
    det_e0M_block]

/-! ## The main theorem -/

theorem mZero_H_ne_zero (y0 : Work.KT.Ball (EuclideanSpace ℝ (Fin 2)))
    (hy0 : y0 ∈ Work.KT.bdry (EuclideanSpace ℝ (Fin 2))) :
    Work.KT.D2.mZero y0 hy0 Work.KT.D2.PA ≠ 0 := by
  -- `psiV` is nowhere zero, so it may be regarded as a loop of units.
  have hψV : ∀ x, psiV y0 x ≠ 0 := fun x => mZeroH_V_entry_ne y0 hy0 x
  -- `mZeroH_V` is a family of units carrying `e0M` to the disc family of `PA`.
  have hunit : ∀ y, IsUnit (mZeroH_V y0 y) := fun y =>
    isUnit_iff_exists.mpr ⟨mZeroH_U y0 y, mZeroH_V_mul_U y0 y, mZeroH_U_mul_V y0 y⟩
  -- hence its boundary loop is not null-homotopic ...
  have hnot := PAM_clutching_not_nullhomotopic (mZeroH_V y0) hunit
    (fun y => mZeroH_V_clutch y0 hy0 y) (toUnits (psiV y0) hψV)
    (fun x => toUnits_val (psiV y0) hψV x)
  -- ... so its winding number does not vanish.
  have hdegV : degNZ (psiV y0) hψV ≠ 0 := by
    intro h0
    exact hnot (degNZ_eq_zero_homotopic_const_one (psiV y0) hψV h0)
  -- The winding of `mZeroH_V` is that winding number.
  have hwindV : windLoop 2 e0M ((mZeroH_V y0).comp inBallCM) (mZeroH_V_ne y0 hy0)
      = degNZ (psiV y0) hψV := by
    rw [windLoop_eq_degNZ]
    exact wlmDegNZcongr (wlmDet_V y0) _ hψV
  -- The two trivialisations have opposite windings.
  have hsum := mZeroH_wind_sum_zero y0 hy0 (mZeroH_U_ne y0 hy0) (mZeroH_V_ne y0 hy0)
  -- The Bott class has the winding of `mZeroH_U`.
  rw [mZeroH_mZero_eq y0 hy0]
  intro hzero
  rw [hzero, zero_add] at hsum
  exact hdegV (by rw [← hwindV]; exact hsum)

end

end Work.KT.D2
