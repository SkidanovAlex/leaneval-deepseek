/-
# `Work.FTS.PressureOn.Connect.BoundaryTime.lambExt_timeDeriv_zero`

The retracted Lamb vector `lambExt ω T` agrees with the Lamb vector `lamb (physVel ω) ω` on the
closed strip `ℝ³ × [0,T/2]` and extends it to *negative* times by the affine continuation with
slope the right derivative `dtLamb ω T`.  Hence its two sided time derivative at the boundary time
`t = 0` exists and equals `dtLamb ω T`:

* on `Ici 0` we are inside the strip, so `lambExt ω T y t = lamb (physVel ω) ω y t`; the right
  derivative of the Lamb vector is `dtLamb ω T y` by the one sided product rule below, using the
  hypothesis `huc` (`∂ₜ⁺u = tblock ω T`) and `hder` (`∂ₜ⁺ω = timeDeriv ω · 0`);
* on `Iic 0` the function is the affine branch `lamb (physVel ω) ω y 0 + t • dtLamb ω T y`, whose
  slope is `dtLamb ω T y`;
* the two one sided derivatives agree, so `HasDerivWithinAt.union` over `Iic 0 ∪ Ici 0 = univ`
  gives the two sided derivative, i.e. the `deriv` appearing in `timeDeriv`.

The ingredients are

* `lamb_hasDerivWithinAt_Ici_zero` — the one sided product rule
  `∂ₜ(u × ω) = (∂ₜu) × ω + u × (∂ₜω)` within `Ici 0` at `0`, via the continuous bilinear form
  `Work.FTS.BSSwirl.crossBilin` and `HasFDerivWithinAt.clm_apply`;
* `lambExt_eq_lamb_of_nonneg` — the identification on `Ici 0` (at `t = 0` the affine branch is
  taken, but it differs from `lamb` only by the vanishing term `0 • dtLamb`).
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_lamb_time

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set
open Work.FTS.Physical (physVel)

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect.BoundaryTime

/-- **The one sided product rule for the Lamb vector at the boundary time.**  If the time slices
of `u` and `ω` are differentiable *within* `Ici 0` at `0`, with derivatives `u'` and `ω'`, then so
is the time slice of the Lamb vector `u × ω`, with derivative `u' × ω(·,0) + u(·,0) × ω'`. -/
theorem lamb_hasDerivWithinAt_Ici_zero {u ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {y : Work.FTS.PressureOn.R3} {u' ω' : Work.FTS.PressureOn.R3}
    (hu : HasDerivWithinAt (fun s => u y s) u' (Set.Ici 0) 0)
    (hω : HasDerivWithinAt (fun s => ω y s) ω' (Set.Ici 0) 0) :
    HasDerivWithinAt (fun s => Work.FTS.PressureOn.lamb u ω y s)
      (Work.FTS.PressureOn.crossVec u' (ω y 0) + Work.FTS.PressureOn.crossVec (u y 0) ω')
      (Set.Ici 0) 0 := by
  -- `lamb u ω y s` is the cross product `u y s × ω y s`, i.e. the continuous bilinear form
  -- `crossBilin` applied to the two time slices (definitionally).
  have hfeq : (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s) (ω y s))
      = fun s => Work.FTS.PressureOn.lamb u ω y s := by
    funext s
    rfl
  -- Compose the first factor with the curve `s ↦ u y s` (the cross product is linear).
  have hc : HasFDerivWithinAt (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s))
      (Work.FTS.BSSwirl.crossBilin.comp
        (ContinuousLinearMap.toSpanSingleton ℝ u')) (Set.Ici 0) 0 :=
    HasFDerivAt.comp_hasFDerivWithinAt (0 : ℝ)
      (Work.FTS.BSSwirl.crossBilin.hasFDerivAt) hu.hasFDerivWithinAt
  -- Product rule for a bilinear map (`HasFDerivWithinAt.clm_apply`).
  have hmain := hc.clm_apply hω.hasFDerivWithinAt
  -- Evaluation of the resulting continuous linear map at `1`.
  have hval : ((Work.FTS.BSSwirl.crossBilin (u y 0)).comp
        (ContinuousLinearMap.toSpanSingleton ℝ ω')
      + (Work.FTS.BSSwirl.crossBilin.comp
        (ContinuousLinearMap.toSpanSingleton ℝ u')).flip (ω y 0)) (1 : ℝ)
      = Work.FTS.PressureOn.crossVec u' (ω y 0)
        + Work.FTS.PressureOn.crossVec (u y 0) ω' := by
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    rw [add_comm]
    rfl
  rw [← hfeq]
  exact hmain.hasDerivWithinAt.congr_deriv hval

/-- On `Ici 0` the retracted Lamb vector agrees with the Lamb vector: for `t = 0` the affine
branch is taken, but it differs from `lamb` only by the vanishing term `0 • dtLamb`. -/
theorem lambExt_eq_lamb_of_nonneg {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {T : ℝ} (y : Work.FTS.PressureOn.R3) {t : ℝ} (ht : 0 ≤ t) :
    Work.FTS.PressureOn.Connect.lambExt ω T y t
      = Work.FTS.PressureOn.lamb (physVel ω) ω y t := by
  rw [Work.FTS.PressureOn.Connect.lambExt]
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    rw [ite_eq_left le_rfl, zero_smul, add_zero]
  · rw [ite_eq_right (not_le.mpr h)]

theorem lambExt_timeDeriv_zero {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {T : ℝ}
    (huc : ∀ x : Work.FTS.PressureOn.R3, HasDerivWithinAt
      (fun s => Work.FTS.Physical.physVel ω x s)
      (Work.FTS.PressureOn.Connect.tblock ω T x) (Set.Ici 0) 0)
    (hder : ∀ x : Work.FTS.PressureOn.R3, HasDerivWithinAt (ω x)
      (FiniteTimeSingularity.timeDeriv ω x 0) (Set.Ici 0) 0) :
    ∀ y : Work.FTS.PressureOn.R3,
      FiniteTimeSingularity.timeDeriv (Work.FTS.PressureOn.Connect.lambExt ω T) y 0
        = Work.FTS.PressureOn.Connect.dtLamb ω T y := by
  intro y
  -- The right hand derivative: the Lamb vector itself, whose right derivative is `dtLamb`.
  have hlamb : HasDerivWithinAt
      (fun t => Work.FTS.PressureOn.lamb (physVel ω) ω y t)
      (Work.FTS.PressureOn.Connect.dtLamb ω T y) (Set.Ici 0) 0 :=
    (lamb_hasDerivWithinAt_Ici_zero (u := physVel ω) (ω := ω) (y := y)
      (u' := Work.FTS.PressureOn.Connect.tblock ω T y)
      (ω' := FiniteTimeSingularity.timeDeriv ω y 0) (huc y) (hder y)).congr_deriv rfl
  have hright : HasDerivWithinAt (fun t => Work.FTS.PressureOn.Connect.lambExt ω T y t)
      (Work.FTS.PressureOn.Connect.dtLamb ω T y) (Set.Ici 0) 0 :=
    hlamb.congr_of_eventuallyEq
      (by filter_upwards [self_mem_nhdsWithin] with t ht
          exact lambExt_eq_lamb_of_nonneg y ht)
      (by rw [lambExt_eq_lamb_of_nonneg y le_rfl])
  -- The left hand derivative: the affine branch, whose slope is `dtLamb`.
  have hleft : HasDerivWithinAt (fun t => Work.FTS.PressureOn.Connect.lambExt ω T y t)
      (Work.FTS.PressureOn.Connect.dtLamb ω T y) (Set.Iic 0) 0 := by
    have hbase : HasDerivWithinAt
        (fun t : ℝ => Work.FTS.PressureOn.lamb (physVel ω) ω y 0
          + t • Work.FTS.PressureOn.Connect.dtLamb ω T y)
        (Work.FTS.PressureOn.Connect.dtLamb ω T y) (Set.Iic 0) 0 :=
      (HasDerivWithinAt.const_add (Work.FTS.PressureOn.lamb (physVel ω) ω y 0)
        ((hasDerivWithinAt_id (0 : ℝ) (Set.Iic 0)).smul_const
          (Work.FTS.PressureOn.Connect.dtLamb ω T y))).congr_deriv
        (one_smul ℝ (Work.FTS.PressureOn.Connect.dtLamb ω T y))
    exact hbase.congr_of_eventuallyEq
      (by filter_upwards [self_mem_nhdsWithin] with t ht
          have ht' : t ≤ 0 := ht
          rw [Work.FTS.PressureOn.Connect.lambExt, ite_eq_left ht'])
      (by rw [Work.FTS.PressureOn.Connect.lambExt, ite_eq_left le_rfl, zero_smul, add_zero])
  -- Gluing the two one sided derivatives along `Iic 0 ∪ Ici 0 = univ`.
  have hunion := hleft.union hright
  rw [Set.Iic_union_Ici] at hunion
  have hd : HasDerivAt (fun t => Work.FTS.PressureOn.Connect.lambExt ω T y t)
      (Work.FTS.PressureOn.Connect.dtLamb ω T y) 0 := hunion.hasDerivAt Filter.univ_mem
  simpa only [FiniteTimeSingularity.timeDeriv] using hd.deriv

end Work.FTS.PressureOn.Connect.BoundaryTime
