/-
# `Work.FTS.PressureOn.Connect.Data` — the clamped fields satisfy the windowed hypotheses

The helper lemmas `weakDiv_timeDeriv`, `weakCurl_pair`, `hasDerivAt_pressurePotential_time_of_continuous`
of this area are stated for fields whose time-dependence is under control on the *whole* window
`Ioo (t - 1) (t + 1)`, whereas the data of `PressureReconstructionOn` live on `[0, T)` only.  This
file collects the elementary consequences of clamping the time variable with `clampt S`
(`Connect/Clamp.lean`): the clamped fields agree with the originals near an interior time `t`, are
Lipschitz in time everywhere, keep their support, and their slices inherit the regularity of the
strip.  Together with `Connect/lipschitz_extendTime` and `Connect/omega_uniform_bound` these are
exactly the hypotheses the windowed helpers ask for.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Connect.Clamp
import Submission.Work.FTS.PressureOn.Connect.contDiff_slice_of_isContDiffHolderOn
import Submission.Work.FTS.PressureOn.vorticity_cross_eq
import Submission.Work.FTS.PressureOn.div_vorticity_mul_eq_zero
import Submission.Work.FTS.BSSwirl.CrossAux
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

noncomputable section

/-- The slice of a clamped field at time `s` is the slice of the original at the clamped time. -/
theorem extendTime_slice (v : R3 → ℝ → R3) (S : ℝ) (s : ℝ) :
    (extendTime v S · s) = fun x => v x (clampt S s) := rfl

/-- The clamped slice inherits the regularity of the strip. -/
theorem contDiff_extendTime_slice {α : NNReal} {v : R3 → ℝ → R3} {S : ℝ} (hS : 0 ≤ S)
    (hstrip : IsContDiffHolderOn ℝ α v.uncurry (Set.univ ×ˢ Set.Icc 0 S)) (s : ℝ) :
    ContDiff ℝ 1 (extendTime v S · s) := by
  have h := contDiff_slice_of_isContDiffHolderOn (τ := clampt S s) hstrip (clampt_mem_Icc hS s)
  show ContDiff ℝ 1 fun x => v x (clampt S s)
  exact h

/-- The clamped time lies in `[0,T)` as soon as `S < T`. -/
theorem clampt_mem_Ico_of_lt {S T s : ℝ} (hS : S < T) (h0 : 0 ≤ S) :
    clampt S s ∈ Set.Ico (0 : ℝ) T :=
  ⟨clampt_nonneg S s, lt_of_le_of_lt (clampt_mem_Icc h0 s).2 hS⟩

/-- **The clamped vorticity is the curl of the clamped velocity.** -/
theorem vorticity_extendTime {u ω : R3 → ℝ → R3} {S T : ℝ} (hS : S ∈ Set.Ioo 0 T)
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x, FiniteTimeSingularity.vorticity (u · s) x = ω x s) (s : ℝ) :
    FiniteTimeSingularity.vorticity (extendTime u S · s) = (extendTime ω S · s) := by
  funext x
  rw [extendTime_slice, extendTime_apply]
  exact hcurl (clampt S s) (clampt_mem_Ico_of_lt hS.2 hS.1.le) x

/-- **The clamped velocity is divergence-free.** -/
theorem div_extendTime {u : R3 → ℝ → R3} {S T : ℝ} (hS : S ∈ Set.Ioo 0 T)
    (hdiv : ∀ s ∈ Set.Ico 0 T, FiniteTimeSingularity.div (u · s) = 0) (s : ℝ) :
    FiniteTimeSingularity.div (extendTime u S · s) = 0 := by
  rw [extendTime_slice]
  exact hdiv (clampt S s) (clampt_mem_Ico_of_lt hS.2 hS.1.le)

/-- **The clamped vorticity keeps its support.** -/
theorem support_extendTime {ω : R3 → ℝ → R3} {S R : ℝ} (hS : 0 ≤ S)
    (hsupp : ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R) (s : ℝ) :
    ∀ x, extendTime ω S x s ≠ 0 → ‖x‖ ≤ R := by
  intro x hx
  rw [extendTime_apply] at hx
  exact hsupp (clampt S s) (clampt_mem_Icc hS s) x hx

/-- **The right derivative of a clamped field at an interior time.** -/
theorem hasDerivWithinAt_extendTime {v : R3 → ℝ → R3} {S t : ℝ} (ht : t ∈ Set.Ioo 0 S)
    (h : ∀ x, HasDerivWithinAt (v x) (FiniteTimeSingularity.timeDeriv v x t) (Set.Ici t) t)
    (x : R3) :
    HasDerivWithinAt (extendTime v S x) (FiniteTimeSingularity.timeDeriv (extendTime v S) x t)
      (Set.Ici t) t := by
  rw [timeDeriv_extendTime ht x]
  exact (h x).congr_of_eventuallyEq_of_mem (eventuallyEq_extendTime_Ici ht x) (le_refl t)

/-- A Lipschitz constant for a bound holding on all of `[0,S]` against an interior point is
nonnegative (for `t < S` the bound is applied at a point `s ≠ t`). -/
theorem nonneg_of_lipschitz {v : R3 → ℝ → R3} {t S C : ℝ} (ht0 : 0 ≤ t) (htS : t < S)
    (h : ∀ x, ∀ s ∈ Set.Icc 0 S, ‖v x s - v x t‖ ≤ C * |s - t|) : 0 ≤ C := by
  by_contra hC
  push_neg at hC
  have hpos : 0 < (S - t) / 2 := by linarith
  have hs : t + (S - t) / 2 ∈ Set.Icc (0 : ℝ) S := by constructor <;> linarith
  have habs : |t + (S - t) / 2 - t| = (S - t) / 2 := by
    rw [add_sub_cancel_left, abs_of_pos hpos]
  have hle := h 0 (t + (S - t) / 2) hs
  rw [habs] at hle
  nlinarith [norm_nonneg (v 0 (t + (S - t) / 2) - v 0 t)]

/-- **The vorticity slice is continuous**, being the curl of the `C¹` velocity slice. -/
theorem continuous_vorticity_slice {α : NNReal} {ω : R3 → ℝ → R3} {T S t : ℝ} (hST : S < T)
    (ht : t ∈ Set.Icc 0 S)
    (hstrip : IsContDiffHolderOn ℝ α (Work.FTS.Physical.physVel ω).uncurry
      (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s) :
    Continuous (fun x => ω x t) := by
  have htT : t ∈ Set.Ico 0 T := ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩
  have hcv : ContDiff ℝ 1 (Work.FTS.Physical.physVel ω · t) :=
    contDiff_slice_of_isContDiffHolderOn hstrip ht
  have hfun : (fun x => ω x t)
      = FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z t) :=
    funext fun x => (hcurl t htT x).symm
  rw [hfun]
  exact Work.FTS.BSSwirl.continuous_vorticity hcv

/-- The Lamb vector vanishes wherever the vorticity does. -/
theorem lamb_eq_zero_of_right_eq_zero {u ω : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : ω x t = 0) : Work.FTS.PressureOn.lamb u ω x t = 0 := by
  have h1 : ‖Work.FTS.PressureOn.lamb u ω x t‖ ≤ ‖u x t‖ * ‖ω x t‖ :=
    vorticityCross_norm_crossVec_le (u x t) (ω x t)
  rw [h, norm_zero, mul_zero] at h1
  exact norm_eq_zero.mp (le_antisymm h1 (norm_nonneg _))

/-- **The Lamb-vector slice is compactly supported** as soon as the vorticity slice is. -/
theorem hasCompactSupport_lamb_slice {u ω : R3 → ℝ → R3} {R t : ℝ}
    (hsupp : ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R) :
    HasCompactSupport (fun x => Work.FTS.PressureOn.lamb u ω x t) :=
  hasCompactSupport_of_norm_bound (fun x hx =>
    hsupp x (fun h => hx (lamb_eq_zero_of_right_eq_zero h)))

end

end Work.FTS.PressureOn.Connect
