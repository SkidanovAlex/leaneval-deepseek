import Mathlib
import Submission.Work.Drive.CappingSpace
import Submission.Work.Drive.stripConfigInterface
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.planeChartDefs

/-!
# The **midpoint coordinate** of the capping space

The capping space `Y = (0,∞) × L` is the quotient of the configuration piece
`ConfigPiece = {q : ℝ × ℂ × UnitAddCircle // 0 < q.1 ∧ ‖q.2.1‖ ≤ 1}` and the cap piece
`CapPiece = {q : ℝ × UnitAddCircle × ℂ // 0 < q.1 ∧ ‖q.2.2‖ ≤ 1}` by the gluing
`cappingRel`, which identifies the configuration boundary point `(r, circleOf φ, θ + 2φ)` with the cap
boundary point `(r, θ, circleOf φ)`.

On the configuration piece the quantities `r` and `z` are the *capping radius* and the *normalised
midpoint* of a chord of `γ`, so that `r · z` is the **midpoint of the chord** (a complex number).  The
key observation of this file is that this expression is *also* glued correctly: on the gluing circle the
configuration coordinate `z` equals the cap coordinate `circleOf φ` of the cap point it is glued to, so
that `r · z` is well defined on the **whole** capping space:

> `cappingMid : CappingSpace → ℂ`,  `cappingMid ⟨(r, z, η)⟩ = r * z`  (configuration piece),
> `cappingMid ⟨(r, θ, w)⟩ = r * w`  (cap piece).

It is continuous (`continuous_cappingMid`), and on a plane chart `Q` of `γ` the composite
`z ↦ cappingMid (Q z)` is the midpoint of the chord that `Q z` encodes
(`cappingMid_stripChart`).  This is the bridge that makes the *curve* `γ` accessible from the *chart*
`Q` alone:  the midpoints of its chords are continuous (smooth) functions of the chart, and the
midpoint of the chord through two points determines the curve (`Continuous γ`).

The main consumer is `Submission/Work/Drive/planeChartCurve.lean`.
-/

namespace Work.Drive

open scoped Topology

noncomputable section

/-- **The midpoint coordinate on the two pieces.**  On the configuration piece `(r, z, η)` and on the
cap piece `(r, θ, w)` it is `r * z` respectively `r * w`. -/
def midPiece : ConfigPiece ⊕ CapPiece → ℂ
  | Sum.inl q => (q.1.1 : ℂ) * q.1.2.1
  | Sum.inr q => (q.1.1 : ℂ) * q.1.2.2

@[simp] lemma midPiece_inl (q : ConfigPiece) : midPiece (Sum.inl q) = (q.1.1 : ℂ) * q.1.2.1 := rfl

@[simp] lemma midPiece_inr (q : CapPiece) : midPiece (Sum.inr q) = (q.1.1 : ℂ) * q.1.2.2 := rfl

/-- **The midpoint coordinate respects the gluing.**  The two boundary points glued by `cappingRel`
carry the same value: the configuration point `(r, circleOf φ, θ + 2φ)` has `r * circleOf φ` and the
cap point `(r, θ, circleOf φ)` has the same. -/
lemma midPiece_compat {x y : ConfigPiece ⊕ CapPiece} (h : cappingRel x y) :
    midPiece x = midPiece y := by
  rcases h with h | ⟨r, hr, θ, φ, h | h⟩
  · rw [h]
  · obtain ⟨hx, hy⟩ := h
    rw [hx, hy]
    simp
  · obtain ⟨hy, hx⟩ := h
    rw [hx, hy]
    simp

/-- **The midpoint coordinate of the capping space**: well defined on the whole capping space. -/
def cappingMid (p : CappingSpace) : ℂ :=
  Quotient.lift midPiece (fun _ _ h => midPiece_compat h) p

@[simp] lemma cappingMid_mk (x : ConfigPiece ⊕ CapPiece) :
    cappingMid (Quotient.mk'' x) = midPiece x := rfl

@[simp] lemma cappingMid_confPiece (q : ConfigPiece) :
    cappingMid (Quotient.mk'' (Sum.inl q)) = (q.1.1 : ℂ) * q.1.2.1 := rfl

@[simp] lemma cappingMid_capPiece (q : CapPiece) :
    cappingMid (Quotient.mk'' (Sum.inr q)) = (q.1.1 : ℂ) * q.1.2.2 := rfl

/-- The midpoint coordinate is invariant under the rotation of the configuration piece (which only
changes the doubled direction `η`). -/
@[simp] lemma cappingMid_rotConfig (v : UnitAddCircle) (q : ConfigPiece) :
    cappingMid (Quotient.mk'' (Sum.inl (rotConfig v q))) = cappingMid (Quotient.mk'' (Sum.inl q)) := by
  rw [cappingMid_confPiece, cappingMid_confPiece]
  rfl

/-- **The midpoint coordinate is continuous.** -/
theorem continuous_cappingMid : Continuous cappingMid := by
  refine (isQuotientMap_quotient_mk').continuous_iff.mpr ?_
  have hcont : Continuous (fun x : ConfigPiece ⊕ CapPiece => midPiece x) := by
    rw [show (fun x : ConfigPiece ⊕ CapPiece => midPiece x)
        = Sum.elim (fun q : ConfigPiece => (q.1.1 : ℂ) * q.1.2.1)
            (fun q : CapPiece => (q.1.1 : ℂ) * q.1.2.2) from by
      funext x
      cases x <;> rfl]
    exact Continuous.sumElim
      ((Complex.continuous_ofReal.comp continuous_subtype_val.fst).mul
        (continuous_subtype_val.snd.fst))
      ((Complex.continuous_ofReal.comp continuous_subtype_val.fst).mul
        (continuous_subtype_val.snd.snd))
  exact hcont

end

end Work.Drive
