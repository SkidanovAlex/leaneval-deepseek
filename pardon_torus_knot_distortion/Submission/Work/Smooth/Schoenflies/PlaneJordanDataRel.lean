import Submission.Work.Smooth.Schoenflies.RelExtension
import Submission.Work.Smooth.Schoenflies.Unconditional
import Submission.Work.Smooth.Jordan.noFilling_of_mem_V
import Submission.Work.Smooth.Jordan.plane_schoenflies_openDisc_eq

/-!
# The corrected planar Jordan datum, and the hard direction of the Jordan curve theorem

This file completes the corrected form of the classical input of the planar innermost-disc chapter:
the datum `Work.Smooth.Schoenflies.PlaneJordanDataRel` — an embedded disc spanning the curve plus
the statement that no point of its interior can be contracted away *through loops based at `c 0`*
(the corrected form of `Work.Smooth.Plane.PlaneJordanData`, whose `NullHomotopicAvoiding` is
vacuous: `Work.Smooth.Schoenflies.not_planeJordanInput`).

## Main results

* `not_nullHomotopicRel_of_mem_V` — **the hard direction of the Jordan curve theorem** in the
  corrected form: for a point `x` of the bounded side of a simple closed plane curve
  (`h : PlaneSchoenflies γ`), there is no null-homotopy of `γ` relative to its base point avoiding
  `x`.  This is `Work.Smooth.Jordan.noFilling_of_mem_V` (no disc avoiding `x` spans `γ`) combined
  with `Work.Smooth.Schoenflies.exists_discExtension_of_nullHomotopicRel` (a relative null-homotopy
  produces such a disc);
* `PlaneJordanDataRel`, `PlaneJordanInputRel` — the corrected datum and input;
* `nonempty_planeJordanDataRel_of_planeSchoenflies` — a Schoenflies datum gives the corrected datum;
* `nonempty_planeJordanDataRel_of_smooth` — **unconditional** for `C¹` simple closed curves, via
  the planar Jordan–Schoenflies theorem `Work.Smooth.Schoenflies.nonempty_planeSchoenflies`.
-/

open Set

namespace Work.Smooth.Schoenflies

noncomputable section

/-- **The hard direction of the Jordan curve theorem** (corrected form).  If `x` lies on the bounded
side `h.V` of a simple closed plane curve presented as the boundary of an embedded disc, then the
loop `γ` is *essential* in `ℂ ∖ {x}`: there is no null-homotopy of the loop, through loops based at
`γ 0`, avoiding `x`.

Equivalently: `x` cannot be "contracted away" from the curve — the winding of `γ` around every
interior point of the disc it bounds is non-zero. -/
theorem not_nullHomotopicRel_of_mem_V {γ : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℂ} (hx : x ∈ h.V) :
    ¬ NullHomotopicRel γ.γ x := by
  rintro hnull
  obtain ⟨F, hFne, hFbd, _⟩ :=
    exists_discExtension_of_nullHomotopicRel γ.cont γ.periodic hnull
  exact Work.Smooth.Jordan.noFilling_of_mem_V h hx ⟨F, hFne, hFbd⟩

/-- **The corrected planar Jordan–Schoenflies datum for a simple closed curve `c`.**

It consists of an embedded disc `e : 𝔻 → ℂ` spanning `c` and the (corrected) hard direction of the
Jordan curve theorem: no interior point of the disc can be contracted away, through loops based at
`c 0` (see `NullHomotopicRel`; the notion `Work.Smooth.Plane.NullHomotopicAvoiding` used by the
sibling chapter is vacuous and must be replaced by this one). -/
structure PlaneJordanDataRel (c : ℝ → ℂ) where
  /-- the spanning embedded disc -/
  e : C(Work.InnermostDisk.Disc, ℂ)
  /-- the disc is embedded -/
  inj : Function.Injective e
  /-- its boundary is the curve -/
  boundary : ∀ θ : ℝ, e (Work.CoreTopology.circlePoint θ) = c θ
  /-- **Jordan's theorem, hard direction**: interior points cannot be contracted away -/
  inside_not_nullHomotopic : ∀ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 →
    ¬ NullHomotopicRel c (e z)

/-- **The corrected classical input of the planar chapter**: every simple closed plane curve has a
`PlaneJordanDataRel`.  This replaces the (false) `Work.Smooth.Plane.PlaneJordanInput`. -/
def PlaneJordanInputRel : Prop :=
  ∀ c : ℝ → ℂ, Continuous c → Function.Periodic c (2 * Real.pi) →
    Set.InjOn c (Set.Ico 0 (2 * Real.pi)) → Nonempty (PlaneJordanDataRel c)

/-- A Jordan–Schoenflies datum for a curve gives the corrected Jordan datum for it. -/
theorem nonempty_planeJordanDataRel_of_planeSchoenflies {γ : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSchoenflies γ) : Nonempty (PlaneJordanDataRel γ.γ) := by
  refine ⟨{ e := h.e, inj := h.inj, boundary := ?_, inside_not_nullHomotopic := ?_ }⟩
  · intro θ
    exact h.boundary θ
  · intro z hz
    have hmem : h.e z ∈ h.V := by
      have hopen := Work.Smooth.Jordan.plane_schoenflies_openDisc_eq h
      rw [← hopen]
      exact ⟨z, hz, rfl⟩
    exact not_nullHomotopicRel_of_mem_V h hmem

/-- **The corrected classical input holds unconditionally for `C¹` simple closed curves**, by the
planar Jordan–Schoenflies theorem of this chapter. -/
theorem nonempty_planeJordanDataRel_of_smooth {c : ℝ → ℂ} (hc : Continuous c)
    (hper : Function.Periodic c (2 * Real.pi)) (hinj : Set.InjOn c (Set.Ico 0 (2 * Real.pi)))
    (hdiff : ContDiff ℝ 1 c) : Nonempty (PlaneJordanDataRel c) := by
  let γ : Work.Smooth.Jordan.PlaneCurve := ⟨c, hc, hper⟩
  have hs : γ.IsSimple := hinj
  obtain ⟨h⟩ := nonempty_planeSchoenflies γ (by simpa [γ] using hdiff) hs
  have := nonempty_planeJordanDataRel_of_planeSchoenflies h
  simpa [γ] using this

end

end Work.Smooth.Schoenflies
