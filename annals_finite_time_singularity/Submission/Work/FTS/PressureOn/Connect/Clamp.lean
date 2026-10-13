/-
# `Work.FTS.PressureOn.Connect` — the clamping of the time variable

The helper lemmas of this area (`weakDiv_timeDeriv`, `weakCurl_pair`,
`hasDerivAt_pressurePotential_time_of_continuous`, …) take their spatial/time-uniform hypotheses
on the *fixed* window `Ioo (t - 1) (t + 1)` around the time `t` at which the pressure is being
reconstructed, whereas the data of `PressureReconstructionOn` are only available on the half-open
strip `[0, T)` (through `Icc 0 S`, `S < T`).

`clampt S` is the `1`-Lipschitz retraction of `ℝ` onto `[0, S]`; clamping the time variable of
`u` and `ω` produces fields that agree with the originals near any interior time `t ∈ Ioo 0 S`,
are bounded and Lipschitz in time *everywhere*, and are still supported in the required ball.  This
is what lets the windowed helpers be applied verbatim.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

noncomputable section

/-- **Clamping of the time variable into `[0,S]`**: `clampt S s = max 0 (min s S)`. -/
noncomputable def clampt (S s : ℝ) : ℝ := max 0 (min s S)

theorem clampt_apply (S s : ℝ) : clampt S s = max 0 (min s S) := rfl

theorem clampt_nonneg (S s : ℝ) : 0 ≤ clampt S s := le_max_left _ _

theorem clampt_le_max (S s : ℝ) : clampt S s ≤ max S 0 := by
  rw [clampt]
  exact max_le (le_max_right S 0) (le_trans (min_le_right s S) (le_max_left S 0))

theorem clampt_mem_Icc {S : ℝ} (hS : 0 ≤ S) (s : ℝ) : clampt S s ∈ Set.Icc (0 : ℝ) S := by
  refine ⟨clampt_nonneg S s, ?_⟩
  have h := clampt_le_max S s
  rwa [max_eq_left hS] at h

theorem clampt_eq_self_of_mem {S s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) S) : clampt S s = s := by
  rw [clampt, min_eq_left hs.2, max_eq_right hs.1]

theorem clampt_eq_zero_of_nonpos {S s : ℝ} (hs : s ≤ 0) : clampt S s = 0 := by
  rw [clampt]
  exact max_eq_left (le_trans (min_le_left s S) hs)

/-- `clampt S` is `1`-Lipschitz. -/
theorem lipschitzWith_clampt (S : ℝ) : LipschitzWith 1 (clampt S) := by
  have h1 : LipschitzWith 1 fun s : ℝ => min s S := LipschitzWith.min_const LipschitzWith.id S
  have h2 : LipschitzWith 1 fun s : ℝ => max 0 (min s S) := LipschitzWith.const_max h1 0
  change LipschitzWith 1 fun s : ℝ => max 0 (min s S)
  exact h2

/-- `|clampt S s − clampt S t| ≤ |s − t|`. -/
theorem abs_clampt_sub_le (S s t : ℝ) : |clampt S s - clampt S t| ≤ |s - t| := by
  have h : dist (clampt S s) (clampt S t) ≤ 1 * dist s t :=
    (lipschitzWith_clampt S).dist_le_mul s t
  simpa [Real.dist_eq] using h

theorem clampt_sub_le (S s t : ℝ) : clampt S s - clampt S t ≤ |s - t| :=
  le_trans (le_abs_self _) (abs_clampt_sub_le S s t)

/-- Near an interior time the clamp is the identity, as an eventual equality. -/
theorem eventuallyEq_clampt {S t : ℝ} (ht : t ∈ Set.Ioo 0 S) :
    (fun s : ℝ => clampt S s) =ᶠ[𝓝 t] id := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact clampt_eq_self_of_mem (Set.Ioo_subset_Icc_self hs)

/-- Near an interior time the clamp is the identity, within the closed right filter. -/
theorem eventuallyEq_clampt_Ici {S t : ℝ} (ht : t ∈ Set.Ioo 0 S) :
    (fun s : ℝ => clampt S s) =ᶠ[𝓝[Set.Ici t] t] id := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ht)] with s hs
  exact clampt_eq_self_of_mem (Set.Ioo_subset_Icc_self hs)

/-- **The clamped time field**: `v x s` for `s ∈ [0,S]`, extended constantly outside. -/
noncomputable def extendTime (v : R3 → ℝ → R3) (S : ℝ) : R3 → ℝ → R3 :=
  fun x s => v x (clampt S s)

theorem extendTime_apply (v : R3 → ℝ → R3) (S : ℝ) (x : R3) (s : ℝ) :
    extendTime v S x s = v x (clampt S s) := rfl

theorem extendTime_eq_of_mem (v : R3 → ℝ → R3) (S : ℝ) (x : R3) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) S) : extendTime v S x s = v x s := by
  rw [extendTime_apply, clampt_eq_self_of_mem hs]

/-- The clamped field agrees with the original near every interior time. -/
theorem eventuallyEq_extendTime {v : R3 → ℝ → R3} {S t : ℝ} (ht : t ∈ Set.Ioo 0 S) (x : R3) :
    (fun s : ℝ => extendTime v S x s) =ᶠ[𝓝 t] (fun s => v x s) := by
  filter_upwards [eventuallyEq_clampt ht] with s hs
  rw [extendTime_apply, hs]; rfl

theorem eventuallyEq_extendTime_Ici {v : R3 → ℝ → R3} {S t : ℝ} (ht : t ∈ Set.Ioo 0 S) (x : R3) :
    (fun s : ℝ => extendTime v S x s) =ᶠ[𝓝[Set.Ici t] t] (fun s => v x s) := by
  filter_upwards [eventuallyEq_clampt_Ici ht] with s hs
  rw [extendTime_apply, hs]; rfl

/-- The time derivative of the clamped field is the time derivative of the original at an interior
time. -/
theorem timeDeriv_extendTime {v : R3 → ℝ → R3} {S t : ℝ} (ht : t ∈ Set.Ioo 0 S) (x : R3) :
    FiniteTimeSingularity.timeDeriv (extendTime v S) x t
      = FiniteTimeSingularity.timeDeriv v x t :=
  (eventuallyEq_extendTime ht x).deriv_eq

/-- The clamp is `1`-Lipschitz with respect to a fixed interior time. -/
theorem abs_clampt_sub_time_le {S t s : ℝ} (ht : clampt S t = t) :
    |clampt S s - t| ≤ |s - t| := by
  calc |clampt S s - t| = |clampt S s - clampt S t| := by rw [ht]
    _ ≤ |s - t| := abs_clampt_sub_le S s t

theorem clampt_sub_time_le {S t s : ℝ} (ht : clampt S t = t) : clampt S s - t ≤ |s - t| :=
  le_trans (le_abs_self _) (abs_clampt_sub_time_le ht)

end

end Work.FTS.PressureOn.Connect
