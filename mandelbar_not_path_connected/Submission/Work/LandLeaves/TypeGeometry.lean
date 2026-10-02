/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# The geometry of the *type* of a repelling periodic point

Definitions and elementary provable facts underlying the finiteness theorem for the type of a
repelling periodic point of the tricorn (`Work.LandLeaves.finite_landingAngles`):

* `Work.LandLeaves.ccBet a b x` — **cyclic** betweenness: `x` lies on the counterclockwise arc
  from `a` to `b` (angles modulo `1`); the angle-mod-`1` companion of
  `Work.LandLeaves.ccBetween`.
* `Work.LandLeaves.typeSet c φ y` — the type of `y`.
* `Work.LandLeaves.image_dynRay_eq`, `dynRay_iterate_eq` — `(T_c)^[n]` maps the dynamic ray at
  angle `θ` **onto** the dynamic ray at angle `(angDouble)^[n] θ`.
-/
import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher
import Submission.Work.Landing.Rays.image_dynRay_subset
import Submission.Work.Landing.Rays.preimage_mem_dynRay
import Submission.Work.Landing.Rays.rayAccum_image_homeo

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Classical
open scoped Topology

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Cyclic betweenness on the circle of angles -/

/-- **Strict cyclic betweenness**: `x` lies on the counterclockwise arc from `a` to `b`, with
`x` distinct from both endpoints.  Angles are taken modulo `1`, so this is the correct notion for
arcs that wrap around. -/
def ccBet (a b x : ℝ) : Prop :=
  0 < Int.fract (x - a) ∧ Int.fract (x - a) < Int.fract (b - a)

/-- `a` is not strictly counterclockwise between `a` and `b`. -/
theorem not_ccBet_left (a b : ℝ) : ¬ ccBet a b a := by simp [ccBet]

/-- `b` is not strictly counterclockwise between `a` and `b`. -/
theorem not_ccBet_right (a b : ℝ) : ¬ ccBet a b b := by
  intro h
  exact absurd h.2 (lt_irrefl _)

/-- `ccBet` is invariant under translating all three angles by an integer. -/
theorem ccBet_add_int (a b x : ℝ) (m : ℤ) :
    ccBet (a + m) (b + m) (x + m) ↔ ccBet a b x := by
  have h1 : x + (m : ℝ) - (a + (m : ℝ)) = x - a := by ring
  have h2 : b + (m : ℝ) - (a + (m : ℝ)) = b - a := by ring
  simp only [ccBet, h1, h2]

/-- In the *non-wrapping* case the cyclic betweenness is the ordinary one. -/
theorem ccBet_of_lt {a b x : ℝ} (ha : 0 ≤ a) (hx : a < x) (hxb : x < b) (hb : b < a + 1) :
    ccBet a b x := by
  have h1 : Int.fract (x - a) = x - a := by
    rw [Int.fract_eq_self]; exact ⟨by linarith, by linarith⟩
  have h2 : Int.fract (b - a) = b - a := by
    rw [Int.fract_eq_self]; exact ⟨by linarith, by linarith⟩
  rw [ccBet, h1, h2]
  constructor <;> linarith

/-! ## The type of a point -/

/-- The **type** of the point `y` for the Böttcher coordinate `φ`: the angles of the dynamic rays
whose accumulation set is the singleton `{y}`. -/
def typeSet (c : ℂ) (φ : ℂ → ℂ) (y : ℂ) : Set ℝ := {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}}

theorem mem_typeSet {c : ℂ} {φ : ℂ → ℂ} {y : ℂ} {ψ : ℝ} :
    ψ ∈ typeSet c φ y ↔ Work.Landing.rayAccum c φ ψ = {y} := Iff.rfl

/-! ## The dynamic ray is mapped onto the ray of the doubled angle -/

/-- The dynamic ray at angle `θ` is mapped **onto** the dynamic ray at angle `angDouble θ` by
`T_c`. -/
theorem image_dynRay_eq {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) (θ : ℝ) :
    Tantibar c '' Work.Landing.dynRay c φ θ = Work.Landing.dynRay c φ (Work.Landing.angDouble θ) := by
  have hH := Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher hφ
  refine Set.Subset.antisymm (Work.Landing.Rays.image_dynRay_subset hφ θ) ?_
  rintro w hw
  obtain ⟨z, hzT, hz⟩ := Work.Landing.Rays.exists_preimage_mem_dynRay_homeo hH hw
  exact ⟨z, hz, hzT⟩

/-- Iterating `image_dynRay_eq`. -/
theorem dynRay_iterate_eq {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) (θ : ℝ)
    (n : ℕ) :
    (Tantibar c)^[n] '' Work.Landing.dynRay c φ θ
      = Work.Landing.dynRay c φ ((Work.Landing.angDouble)^[n] θ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ', Set.image_comp, ih,
        Function.iterate_succ_apply' (f := Work.Landing.angDouble), image_dynRay_eq hφ]

end Work.LandLeaves
