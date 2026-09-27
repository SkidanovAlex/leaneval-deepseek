import Mathlib
import Submission.Work.Drive.Neutral.HalfDir

/-!
# (Neutral copy) `WindingEqTwoMulDegreeHalfDir`

Verbatim copy of the module `Work.Surf.ChordN.winding_eq_two_mul_degree_halfDir` in the namespace `Work.Surf.ChordN`, with:

* every import of a module whose closure contains the declaration `Work.Drive.toC` of
  `Submission/Work/Drive/winding_eq_crossing_sum.lean` redirected to the neutral copy of that module
  (the only such channel is the import of `Submission/Work/Drive/line_crossings_even.lean`, replaced
  by `Submission/Work/Drive/Neutral/HalfDir.lean`);
* every qualified reference to the declarations of the neutral half-direction file
  (`halfDir`, `continuous_halfDir`, `halfDir_apply`, `halfDir_add_self`, `rescaleAngle`,
  `twoPiNeZero`, `toC`) redirected to `Work.Drive.NH`.

Reason: `Work.Drive.toC` is declared both in `Submission/Work/Drive/winding_eq_crossing_sum.lean` (in
the chord-parity world) and in `Submission/Work/Drive/UmlaufSetup.lean` (in the capping world), so the
two worlds cannot be imported together.  With these copies,
`Work.Surf.ChordN.chord_crossing_parity` — the strict base case of the mod-2 intersection form of
`ℝP²` — is importable next to `Work.Drive.CappingSpace`; see
`Submission/Work/Drive/cutTransportStrict.lean`.
-/
namespace Work.Surf.ChordN

open Work.Drive.NH

/-!
# The winding number is twice the degree of the half-direction

For a closed plane curve `γ : ℝ/ℤ → ℝ²` and a point `p` off it, the winding number of `γ` about `p`
is the degree of the *doubled* direction map `dirCurve γ hγ p hp` (`Submission.Collision.dirC v =
arg v / π`).  That map has a continuous square root, the **half-direction**
`halfDir γ p t = arg (γ t - p) / (2π)` (`Work.Drive.NH.halfDir`), because `halfDir + halfDir = dirCurve`
(`Work.Drive.NH.halfDir_add_self`).  Since `t ↦ 2 * liftOf (halfDir γ p) _ t` is a continuous lift of
`dirCurve γ hγ p hp` with monodromy `2 * degree (halfDir γ p) _`, the intrinsic description of the
degree (`Work.Drive.degree_eq_of_lift`) gives

`winding γ hγ hp = 2 * degree (halfDir γ p) (continuous_halfDir γ hγ hp)`.

Consequently `halfWinding γ hγ hp = degree (halfDir γ p) _`, and the winding number of any closed
curve about a point off it is even.
-/

theorem winding_eq_two_mul_degree_halfDir (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ)
    {p : ℝ × ℝ} (hp : p ∉ Set.range γ) :
    Work.Drive.winding γ hγ hp =
      2 * Work.Drive.degree (Work.Drive.NH.halfDir γ p)
        (Work.Drive.NH.continuous_halfDir γ hγ hp) := by
  have hHc : Continuous (Work.Drive.NH.halfDir γ p) := Work.Drive.NH.continuous_halfDir γ hγ hp
  have hGcont : Continuous fun t : ℝ =>
      2 * Work.Drive.liftOf (Work.Drive.NH.halfDir γ p) hHc t :=
    continuous_const.mul (Work.Drive.liftOf_continuous (Work.Drive.NH.halfDir γ p) hHc)
  have hlift : ∀ t : ℝ,
      ((2 * Work.Drive.liftOf (Work.Drive.NH.halfDir γ p) hHc t : ℝ) : UnitAddCircle)
        = Work.Drive.dirCurve γ hγ p hp (t : UnitAddCircle) := by
    intro t
    have h1 : (2 * Work.Drive.liftOf (Work.Drive.NH.halfDir γ p) hHc t : ℝ) =
        Work.Drive.liftOf (Work.Drive.NH.halfDir γ p) hHc t
          + Work.Drive.liftOf (Work.Drive.NH.halfDir γ p) hHc t := by ring
    rw [h1, AddCircle.coe_add, Work.Drive.liftOf_lifts]
    exact Work.Drive.NH.halfDir_add_self γ hγ hp (t : UnitAddCircle)
  have hmono : ∀ t : ℝ,
      (fun t : ℝ => 2 * Work.Drive.liftOf (Work.Drive.NH.halfDir γ p) hHc t) (t + 1)
        = (fun t : ℝ => 2 * Work.Drive.liftOf (Work.Drive.NH.halfDir γ p) hHc t) t
          + ((2 * Work.Drive.degree (Work.Drive.NH.halfDir γ p) hHc : ℤ) : ℝ) := by
    intro t
    show 2 * Work.Drive.liftOf (Work.Drive.NH.halfDir γ p) hHc (t + 1)
        = 2 * Work.Drive.liftOf (Work.Drive.NH.halfDir γ p) hHc t
          + ((2 * Work.Drive.degree (Work.Drive.NH.halfDir γ p) hHc : ℤ) : ℝ)
    rw [Work.Drive.liftOf_add_one (Work.Drive.NH.halfDir γ p) hHc t]
    push_cast
    ring
  rw [Work.Drive.winding]
  exact (Work.Drive.degree_eq_of_lift (Work.Drive.continuous_dirCurve γ hγ p hp)
    hGcont hlift hmono).symm

/-- The honest (halved) winding number of a closed curve about a point off it is the degree of the
half-direction map. -/
theorem winding_div_two_eq_degree_halfDir (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ)
    {p : ℝ × ℝ} (hp : p ∉ Set.range γ) :
    Work.Drive.winding γ hγ hp / 2 =
      Work.Drive.degree (Work.Drive.NH.halfDir γ p)
        (Work.Drive.NH.continuous_halfDir γ hγ hp) := by
  rw [winding_eq_two_mul_degree_halfDir γ hγ hp]
  exact Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)

end Work.Surf.ChordN
