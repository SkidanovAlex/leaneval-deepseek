import Mathlib
import Submission.Work.Drive.Mono.NoGrazeDefs
import Submission.Work.Drive.Mono.OneEventNDDefs

/-!
# The one-event slice nullity at the cutting level, on a countable family of directions

Definitions (and two elementary bricks) of the interface through which the single-level producer of
`Work.Drive.Mono.Geom3Data` obtains the clause "one event per level" of `Work.Drive.Mono.G3Extra`.

The clause is produced by `Work.Drive.Mono.oneEventPerLevel_of_nd` from two facts about the datum:

* every event of the datum is *non-degenerate* (`Work.Drive.Mono.NDEvent`, supplied by
  `Work.Drive.Mono.ndEvent_of_datum` applied to the datum the producer itself builds), and
* the datum's `(h, τ)` avoids the bad set `Work.Drive.Mono.OneEvBad ψ s c σ v a₀ b₀ u · ·` of the
  direction triple `(v, a₀, b₀)` of the datum.

The latter is a null set of `(h, τ)` **at the cutting level `u` of the datum**; the only available
nullity (`Work.Drive.Mono.ae_oneEvBad_slice_null`) is the `∀ᵐ u` one, so the direction triple must be
drawn from a countable family fixed independently of `u`.  The family delivered by
`Work.Drive.Mono.g3_exists_dense_heightGood_noVanishing` is exactly right: it is countable,
`HeightGood`, dense and has no vanishing sweep coordinate, so it is *also* the family from which the
witness's tilt direction is drawn (`Work.Drive.Mono.noGraze_witness_arcs_Q`); the direction of the
datum then has the bad-`(h,τ)`-set nullity at `u`, because that nullity holds for *every* member of
the family simultaneously (a countable intersection of conull sets).

The pointwise-in-`u` strengthening (the same for **all** direction triples at a fixed `u`) is
FALSE: for the surface mirror-symmetric about the cutting plane, with `v` the axis of that symmetry
and `u` the symmetry level, the bad slice is fat.  This is why the a.e. quantifier and the countable
family are not removable.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set
open scoped RealInnerProductSpace

noncomputable section

/-- **The frame attached to a height direction `ng`.**  `unitDir ng` is the height direction (of unit
norm), `orthDir e (unitDir ng)` the associated sweep direction, and `(a, b)` an orthonormal basis of
the orthogonal complement of that sweep direction, adapted to the height direction
(`unitDir ng = (√2)⁻¹ • (a + b)`) — the configuration of the level functional
`ℓ_τ = ⟪dirOf τ a b, ·⟫` at `τ = 0`. -/
def G3Frame (e ng a b : R3) : Prop :=
  ‖unitDir ng‖ = 1 ∧
  ‖orthDir e (unitDir ng)‖ = 1 ∧
  inner ℝ (orthDir e (unitDir ng)) (unitDir ng) = 0 ∧
  ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ inner ℝ a b = 0 ∧
  inner ℝ (orthDir e (unitDir ng)) a = 0 ∧
  inner ℝ (orthDir e (unitDir ng)) b = 0 ∧
  unitDir ng = (Real.sqrt 2)⁻¹ • (a + b)

/-- **The one-event slice nullity at the cutting level `u`, on a countable family of directions.**
There is a countable, `HeightGood`, dense set `Q` of height directions, no member of which has a
vanishing sweep coordinate, together with an adapted frame `(af ng, bf ng)` for every `ng ∈ Q`, such
that at the level `u` the `(h, τ)`-slice of the bad set `Work.Drive.Mono.OneEvBad` of the direction
triple `(orthDir (shiftVσ σ 1) (unitDir ng), af ng, bf ng)` is null. -/
def G3OneEv (ψ : Submission.Diffeo) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∃ (Q : Set R3) (af bf : R3 → R3),
    Q.Countable ∧
    (∀ ng ∈ Q, Work.Drive.Mono.Band.HeightGood ψ ng) ∧
    (∀ U : Set R3, IsOpen U → U.Nonempty → (U ∩ Q).Nonempty) ∧
    (∀ ng ∈ Q, ∀ j : Fin 3,
      (orthDir (Work.BoxShrink.shiftVσ σ 1) (unitDir ng)) j ≠ 0) ∧
    (∀ ng ∈ Q, G3Frame (Work.BoxShrink.shiftVσ σ 1) ng (af ng) (bf ng)) ∧
    (∀ ng ∈ Q, MeasureTheory.volume {y : ℝ × ℝ |
      Work.Drive.Mono.OneEvBad ψ s c σ (orthDir (Work.BoxShrink.shiftVσ σ 1) (unitDir ng))
        (af ng) (bf ng) u y.1 y.2} = 0)

/-- **The normalised orthogonal projection is orthogonal to the direction it projects away from.** -/
theorem g3_inner_orthDir_eq_zero {e m : R3} (hm : ‖m‖ = 1) :
    inner ℝ (orthDir e m) m = 0 := by
  rw [orthDir, real_inner_smul_left, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hm]
  ring

/-- **The normalised orthogonal projection is a unit vector** as soon as the vector it normalises
does not vanish. -/
theorem g3_norm_orthDir_eq_one {e m : R3} (h : e - inner ℝ e m • m ≠ 0) :
    ‖orthDir e m‖ = 1 := by
  rw [orthDir, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

end

end Work.Drive.Mono
