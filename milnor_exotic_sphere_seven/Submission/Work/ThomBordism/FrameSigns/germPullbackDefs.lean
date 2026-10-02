import Mathlib
import Submission.Work.ThomBordism.FrameSigns.germFDeriv
import Submission.Work.ThomBordism.FrameSigns.linearActionIsl
import Submission.Work.Thom.ATools
import Submission.Work.Cohomology.capRelAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.defProp false

open scoped unitInterval

/-!
# The objects of the proof of `germPullback`

This file sets up, in a self-contained way, the objects that the proof of
`Work.ThomBordism.FrameSigns.germPullback` uses.  The setting is a fixed open set
`W ∋ 0` of `E8 = ℝ⁸`, a positive radius `r` with `Metric.closedBall 0 r ⊆ W`, and:

* `gpU r W` — the open ball of radius `r` inside `W`, as a subset of `↥W`;
* `gpc r W` — the coercion `↥(gpU r W) → ↥W`;
* `gpiW`, `gpiU` — the inclusions of `↥W` and of `↥(gpU r W)` into `E8`;
* `gpBW`/`gpAU`/`gpB0`/`gpACl` — the punctured parts of `↥W`, `↥(gpU r W)`, `E8` and of the
  closed ball of radius `r/2`;
* `gpFW`, `gpFU`, `gpFCl` — the restrictions of `F` to `↥W`, `↥(gpU r W)` and the closed ball;
* `gpL8`, `gpLU`, `gpLCl` — the restrictions of the linear map `L`;
* `gpρ r W` — the radial retraction `z ↦ z/2` of the open ball of radius `r` onto the closed ball
  of radius `r/2`.
-/

namespace Work.ThomBordism.FrameSigns

noncomputable section

/-- The punctured model space `ℝ⁸ ∖ {0}`. -/
abbrev gpB0 : Set E8 := {v : E8 | v ≠ 0}

/-- The puncture, as a subset of `↥W`. -/
abbrev gpBW (W : Set E8) : Set ↥W := {z : ↥W | (z : E8) ≠ 0}

/-- The open ball of radius `r` around the origin, as a subset of `↥W`. -/
abbrev gpU (r : ℝ) (W : Set E8) : Set ↥W :=
  {z : ↥W | (z : E8) ∈ Metric.ball (0 : E8) r}

/-- The punctured part of `gpU`. -/
abbrev gpAU (r : ℝ) (W : Set E8) : Set ↥(gpU r W) :=
  {z : ↥(gpU r W) | ((z : ↥W) : E8) ≠ 0}

/-- The closed ball of radius `r/2` in `E8` (the target of the retraction `gpρ`). -/
abbrev gpCl (r : ℝ) : Set E8 := Metric.closedBall (0 : E8) (r / 2)

/-- The punctured part of `gpCl`. -/
abbrev gpACl (r : ℝ) : Set ↥(gpCl r) := {z : ↥(gpCl r) | (z : E8) ≠ 0}

/-- The coercion `↥(gpU r W) → ↥W`. -/
def gpc (r : ℝ) (W : Set E8) : C(↥(gpU r W), ↥W) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion `↥W → ℝ⁸`. -/
def gpiW (W : Set E8) : C(↥W, E8) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion `↥(gpU r W) → ℝ⁸`. -/
def gpiU (r : ℝ) (W : Set E8) : C(↥(gpU r W), E8) :=
  (gpiW W).comp (gpc r W)

/-- `F` restricted to `W`. -/
def gpFW (W : Set E8) (F : E8 → E8) (hFc : ContinuousOn F W) : C(↥W, E8) :=
  ⟨fun z => F (z : E8), continuousOn_iff_continuous_domRestrict.mp hFc⟩

/-- `F` restricted to the open ball `gpU`. -/
def gpFU (r : ℝ) (W : Set E8) (F : E8 → E8) (hFc : ContinuousOn F W) :
    C(↥(gpU r W), E8) :=
  (gpFW W F hFc).comp (gpc r W)

@[simp] theorem gpFU_apply (r : ℝ) (W : Set E8) (F : E8 → E8) (hFc : ContinuousOn F W)
    (z : ↥(gpU r W)) : gpFU r W F hFc z = F ((z : ↥W) : E8) := rfl

/-- `F` restricted to the closed ball `gpCl`, using that `closedBall 0 r ⊆ W`. -/
def gpFCl (r : ℝ) (hr : 0 < r) (W : Set E8) (F : E8 → E8) (hFc : ContinuousOn F W)
    (hrW : Metric.closedBall (0 : E8) r ⊆ W) : C(↥(gpCl r), E8) :=
  ⟨fun z => F (z : E8), hFc.comp_continuous continuous_subtype_val
    (fun z => hrW (Metric.closedBall_subset_closedBall (by linarith) z.2))⟩

@[simp] theorem gpFCl_apply (r : ℝ) (hr : 0 < r) (W : Set E8) (F : E8 → E8)
    (hFc : ContinuousOn F W) (hrW : Metric.closedBall (0 : E8) r ⊆ W) (z : ↥(gpCl r)) :
    gpFCl r hr W F hFc hrW z = F (z : E8) := rfl

/-- The pair condition for `gpFU`. -/
theorem gpFUmem (r : ℝ) (W : Set E8) (F : E8 → E8) (hFc : ContinuousOn F W)
    (hnz : ∀ z ∈ W, z ≠ 0 → F z ≠ 0) :
    ∀ z ∈ gpAU r W, gpFU r W F hFc z ∈ gpB0 :=
  fun z hz => hnz ((z : ↥W) : E8) ((z : ↥W).2) hz

/-- The pair condition for `gpFCl`. -/
theorem gpFClmem (r : ℝ) (hr : 0 < r) (W : Set E8) (F : E8 → E8) (hFc : ContinuousOn F W)
    (hnz : ∀ z ∈ W, z ≠ 0 → F z ≠ 0) (hrW : Metric.closedBall (0 : E8) r ⊆ W) :
    ∀ z ∈ gpACl r, gpFCl r hr W F hFc hrW z ∈ gpB0 :=
  fun z hz => hnz (z : E8)
    (hrW (Metric.closedBall_subset_closedBall (by linarith) z.2)) hz

/-- The pair condition for `gpiU`. -/
theorem gpiUmem (r : ℝ) (W : Set E8) :
    ∀ z ∈ gpAU r W, gpiU r W z ∈ gpB0 := fun z hz => hz

/-- The linear map `L` as a continuous map `ℝ⁸ → ℝ⁸`. -/
def gpL8 (L : E8 →L[ℝ] E8) : C(E8, E8) := ⟨fun z => L z, L.continuous⟩

/-- `L` restricted to the closed ball `gpCl`. -/
def gpLCl (r : ℝ) (L : E8 →L[ℝ] E8) : C(↥(gpCl r), E8) :=
  ⟨fun z => L (z : E8), L.continuous.comp continuous_subtype_val⟩

@[simp] theorem gpLCl_apply (r : ℝ) (L : E8 →L[ℝ] E8) (z : ↥(gpCl r)) :
    gpLCl r L z = L (z : E8) := rfl

/-- `L` restricted to the open ball `gpU`. -/
def gpLU (r : ℝ) (W : Set E8) (L : E8 →L[ℝ] E8) : C(↥(gpU r W), E8) :=
  (gpL8 L).comp (gpiU r W)

@[simp] theorem gpLU_apply (r : ℝ) (W : Set E8) (L : E8 →L[ℝ] E8) (z : ↥(gpU r W)) :
    gpLU r W L z = L ((z : ↥W) : E8) := rfl

/-- The pair condition for `gpLU`. -/
theorem gpLUmem (r : ℝ) (W : Set E8) (L : E8 →L[ℝ] E8) (hL : Function.Bijective L) :
    ∀ z ∈ gpAU r W, gpLU r W L z ∈ gpB0 := by
  intro z hz h
  exact hz (hL.1 (by rw [← gpLU_apply r W L z]; exact h.trans (map_zero L).symm))

/-- The pair condition for `gpLCl`. -/
theorem gpLClmem (r : ℝ) (L : E8 →L[ℝ] E8) (hL : Function.Bijective L) :
    ∀ z ∈ gpACl r, gpLCl r L z ∈ gpB0 := by
  intro z hz h
  exact hz (hL.1 (by rw [← gpLCl_apply r L z]; exact h.trans (map_zero L).symm))

/-- The membership of the retraction: `z ↦ z/2` maps the open ball of radius `r` into the closed
ball of radius `r/2`. -/
theorem gpρ_mem (r : ℝ) (W : Set E8) (z : ↥(gpU r W)) :
    (1 / 2 : ℝ) • ((z : ↥W) : E8) ∈ gpCl r := by
  have hz : ‖((z : ↥W) : E8)‖ < r := by
    have h : ((z : ↥W) : E8) ∈ Metric.ball (0 : E8) r := z.2
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hs : ‖(1 / 2 : ℝ) • ((z : ↥W) : E8)‖ = (1 / 2) * ‖((z : ↥W) : E8)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [Metric.mem_closedBall, dist_zero_right, hs]
  linarith

/-- The radial retraction of the open ball of radius `r` onto the closed ball of radius `r/2`,
`z ↦ z/2`. -/
def gpρ (r : ℝ) (W : Set E8) : C(↥(gpU r W), ↥(gpCl r)) :=
  ⟨fun z => ⟨(1 / 2 : ℝ) • ((z : ↥W) : E8), gpρ_mem r W z⟩,
    Continuous.subtype_mk
      (show Continuous fun z : ↥(gpU r W) => (1 / 2 : ℝ) • ((z : ↥W) : E8) from
        (continuous_const : Continuous fun _ : ↥(gpU r W) => (1 / 2 : ℝ)).smul
          (continuous_subtype_val.comp continuous_subtype_val))
      (gpρ_mem r W)⟩

@[simp] theorem gpρ_apply (r : ℝ) (W : Set E8) (z : ↥(gpU r W)) :
    ((gpρ r W z : ↥(gpCl r)) : E8) = (1 / 2 : ℝ) • ((z : ↥W) : E8) := rfl

/-- `gpFU` is by definition the composite `gpFW ∘ gpc`. -/
theorem gpFU_unfold (r : ℝ) (W : Set E8) (F : E8 → E8) (hFc : ContinuousOn F W) :
    gpFU r W F hFc = (gpFW W F hFc).comp (gpc r W) := rfl

/-- `gpiU` is by definition the composite `gpiW ∘ gpc`. -/
theorem gpiU_unfold (r : ℝ) (W : Set E8) :
    gpiU r W = (gpiW W).comp (gpc r W) := rfl

/-- `gpLU` is by definition the composite `gpL8 L ∘ gpiU`. -/
theorem gpLU_unfold (r : ℝ) (W : Set E8) (L : E8 →L[ℝ] E8) :
    gpLU r W L = (gpL8 L).comp (gpiU r W) := rfl

end

end Work.ThomBordism.FrameSigns
