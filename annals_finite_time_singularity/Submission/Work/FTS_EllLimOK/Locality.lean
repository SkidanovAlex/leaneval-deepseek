/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.Locality` — `mixed` is a local operator

`mixed j i f = D_z^j D_θ^i f` is an iterated (totalised) derivative followed by multiplication by
the smooth factors `z^j` and `sin(2θ)^i`; it is therefore a **local** operator: two functions that
agree on a neighbourhood of a point have the same mixed derivatives there.  This is the single
technical ingredient behind every `QdZero`-statement of the area, and hence behind the whole
`EllLimOK` analysis: the limits in `EllLimOK` are only tested on the open quadrant `Qd`, so a
direction that vanishes on a neighbourhood of `Qd` is invisible to the hypotheses while `E` may
still see it.

The proof is the congruence of `pz`/`pth` on an open set (`Work.Spaces.pz_congr_of_isOpen`,
`Work.Spaces.pth_congr_of_isOpen`) iterated through `D_z`, `D_θ`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_EllLimOK.Defs
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Congruence of the iterated operators on an open set -/

/-- Two functions that agree on an open set have the same `D_θ`-iterates there. -/
theorem DthIter_congr_eqOn {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i u))
      (Function.uncurry (Work.Spaces.DthIter i v)) V := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro p hp
      show Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter n u) p.1 p.2
        = Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter n v) p.1 p.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hp]

/-- Two functions that agree on an open set have the same `D_z`-iterates there. -/
theorem DzIter_congr_eqOn {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter i u))
      (Function.uncurry (Work.Spaces.DzIter i v)) V := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro p hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter n u) p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter n v) p.1 p.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]

/-- **Locality of `mixed`**: agreement on a neighbourhood of `(z,θ)` gives equality of every
mixed derivative there. -/
theorem mixed_congr_of_eventuallyEq {f g : ℝ → ℝ → ℝ} {z θ : ℝ} (a b : ℕ)
    (h : Function.uncurry f =ᶠ[𝓝 (z, θ)] Function.uncurry g) :
    Work.Spaces.mixed a b f z θ = Work.Spaces.mixed a b g z θ := by
  obtain ⟨s, hs, hssub⟩ := Filter.Eventually.exists_mem h
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.mp hs
  have heqW : Set.EqOn (Function.uncurry f) (Function.uncurry g) W := fun p hp => hssub p (hWsub hp)
  have hDth := DthIter_congr_eqOn hWopen heqW b
  have hfin := DzIter_congr_eqOn hWopen hDth a hWmem
  simpa only [Function.uncurry, Work.Spaces.mixed] using hfin

/-- The `EqOn`-form of the locality of `mixed` (on an open set). -/
theorem mixed_congr_of_eqOn_isOpen {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) {z θ : ℝ} (hz : (z, θ) ∈ V)
    (a b : ℕ) : Work.Spaces.mixed a b f z θ = Work.Spaces.mixed a b g z θ :=
  mixed_congr_of_eventuallyEq a b (h.eventuallyEq_of_mem (hV.mem_nhds hz))

/-! ## The consequences for `QdZero` -/

/-- A direction that vanishes on a neighbourhood of `Qd` has vanishing mixed derivatives on
`Qd` (of every order): it is invisible to the hypotheses of `EllLimOK`. -/
theorem QdZero.mixed_eq_zero {γ : Fn} (h : QdZero γ) (j i : ℕ) {z θ : ℝ}
    (hz : (z, θ) ∈ Work.Construction.Qd) : Work.Spaces.mixed j i γ z θ = 0 := by
  obtain ⟨V, hVopen, hQd, hzero⟩ := h
  have hEq : Set.EqOn (Function.uncurry γ) (Function.uncurry (0 : Fn)) V := by
    intro p hp
    show γ p.1 p.2 = (0 : Fn) p.1 p.2
    rw [hzero p.1 p.2 hp]
    simp
  rw [mixed_congr_of_eqOn_isOpen hVopen hEq (hQd hz) j i,
    Work.FTS.EllipticEst.mixed_zero_fun j i]
  rfl

/-- `QdZero` implies the jet-flatness `QdFlat`. -/
theorem QdZero.qdFlat {γ : Fn} (h : QdZero γ) : QdFlat γ :=
  fun j i _ z θ hz => h.mixed_eq_zero j i hz

/-- A `QdZero` direction is `C^∞` on `Qd` (it vanishes on a neighbourhood of `Qd`). -/
theorem QdZero.contDiffOn {γ : Fn} (h : QdZero γ) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry γ) Work.Construction.Qd := by
  obtain ⟨V, hVopen, hQd, hzero⟩ := h
  refine ContDiffOn.congr
    (contDiffOn_const (c := (0 : ℝ)) (s := Work.Construction.Qd)) ?_
  intro p hp
  show Function.uncurry γ p = (0 : ℝ)
  have hγ0 : γ p.1 p.2 = 0 := hzero p.1 p.2 (hQd hp)
  simpa only [Function.uncurry] using hγ0

/-- Adding a `QdZero` direction does not change the `uncurry`-germ at a point of `Qd`. -/
theorem QdZero.add_eventuallyEq {γ : Fn} (h : QdZero γ) (f : Fn) {z θ : ℝ}
    (hz : (z, θ) ∈ Work.Construction.Qd) :
    Function.uncurry (fun z θ => f z θ + γ z θ) =ᶠ[𝓝 (z, θ)] Function.uncurry f := by
  obtain ⟨V, hVopen, hQd, hzero⟩ := h
  filter_upwards [hVopen.mem_nhds (hQd hz)] with p hp
  have hγ : γ p.1 p.2 = 0 := hzero p.1 p.2 hp
  simp [Function.uncurry, hγ]

/-- Consequently, adding a `QdZero` direction does not change any mixed derivative at a point of
`Qd`. -/
theorem QdZero.add_mixed_eq {γ : Fn} (h : QdZero γ) (f : Fn) (j i : ℕ) {z θ : ℝ}
    (hz : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.mixed j i (fun z θ => f z θ + γ z θ) z θ = Work.Spaces.mixed j i f z θ :=
  mixed_congr_of_eventuallyEq j i (h.add_eventuallyEq f hz)

end Work.FTS_EllLimOK
