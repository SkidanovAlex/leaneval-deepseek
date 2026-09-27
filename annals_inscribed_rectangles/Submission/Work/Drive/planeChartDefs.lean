import Mathlib
import Submission.Work.Drive.planeProfiles
import Submission.Work.Drive.planePt
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.cone_chain
import Submission.Work.Drive.cappingCharted

/-!
# The predicate "`Q` is the plane chart of `γ`"

The chain route needs **one** concrete object: a `C^∞` map `Q : ℂ → CappingSpace` of the closed disk
whose

* **strip clause** reproduces the strip chart of the configuration Möbius band on the outer annulus
  `1/2 < ‖z‖ ≤ 1` (this is what makes the counts the paper's `n_P`);
* **seam clause** `Q (-z) = Q z` holds on the boundary circle `‖z‖ = 1` (the disk model of `ℝP²`);
* **cap clause** puts the inner disk `‖z‖ < 1/2` in the *cap* solid torus, i.e. makes `[P]` the
  generator of `H₂(Y) ≅ ℤ/2` — the homological nontriviality of the plane.

**WARNING (the meridian input) — the unconditional existence statement is FALSE.**
`Submission/Work/Drive/PLANE_MERIDIAN_NOTES.md` proves (and
`Work.Drive.wrapData_of_planeChart` has been delegated to make it machine-checked) that
`∃ Q, IsPlaneChart γ hγne Q` **forces** the origin to be enclosed by `γ` with the same sign as the
turning of its tangent, i.e. `Work.Drive.WrapData γ` (`Submission/Work/Drive/planeWrapData.lean`); the
obstruction is that the cap coordinate `θ` of the chart is a continuous `S¹`-valued function on a
*disk*, so its boundary degree is `0` (`Work.Drive.degree_circle_boundary_eq_zero`), while the strip
clause forces that degree to be `2ε - 2m` (`ε` the Umlauf sign, `m` the position winding).  A concrete
counterexample is the unit circle centred at `(2,0)` (`m = 0`, `ε = 1`): it admits **no** plane chart.
The correct statement is `Work.Drive.wrapData_of_planeChart`'s converse,
`UmlaufProp → WrapData γ → ∃ Q, IsPlaneChart γ hγne Q` (delegated as `Work.Drive.exists_planeChart`);
since `GoodC`/`Zc` (and hence the wall) are translation invariant
(`Work.Drive.goodC_translate`), the route may use a translate `γ + c` with `WrapData`
(`Work.Drive.exists_wrapData_translate`).

**WARNING (the meridian input).**  The **cap clause is not unconditional**: the boundary circle
`‖z‖ = 1/2` has its image in the gluing torus *forced* by the strip clause, and for a disk filling to
exist that curve must be a **meridian** of the cap solid torus — equivalently (with
`∂M : x ↦ (arg (γ x), arg² (γ' x))` and `m = winding (γ, 0)`) the position winding must equal the
Umlauf sign, `m = ±1`.  So the *existence* statement `∃ Q, IsPlaneChart γ hγne Q` must be stated either
with that input as a hypothesis or after translating `γ` by a point of winding `±1`
(`Work.Drive.goodC_translate`, `Work.Drive.exists_winding_ne_zero`).  See
`Submission/Work/Drive/PLANE_CAP_CONSTRUCTION.md` §5.

**The cap clause: the sharp mechanism, and the working design (session of `orderSplit_model`).**
Read `Submission/Work/Drive/CAP_MARK_OBSTRUCTION.md` first; it records that the cap clause is equivalent
to the lift of `Q` being *cap side* (`Work.Drive.IsCapVec`, in `Submission/Work/Drive/capSideLift.lean`),
that the "cap mark" of `Submission/Work/Drive/wrapData_of_planeChart.lean` can vanish only at the
configuration pole `[c₁ : 0]`, and that this winding obstruction is what forces `WrapData` (so no
pointwise patching of the projective lift, and no linear blend, can produce the clause: the cap-side
cone is not convex — `Work.Drive.not_forall_convex_isCapVec`).  §3bis of that note contains the working
design, with explicit formulas, and verifies its inputs against the workspace: the periodic lift of the
seam's cap coordinate is *proved* (`Work.Drive.exists_periodic_cap_angle_polar`), the cap side in a
collar of the seam is *proved* for the honest descent (`Work.Drive.collar_isCapVec`,
`Work.Drive.one_sub_normSq_dataD_ge`), and the construction is carried out in the coordinates
`(r, θ, φ)` of `CapPiece` (convex disk coordinate `φ`, `θ` through a real lift), where the pole is never
attained and the centre `z = 0` is smooth (there `φ = z` or `z̄`).

`Work.Drive.IsPlaneChart γ hγne Q` bundles exactly these three clauses together with smoothness, so
that the construction can be delegated as one statement.  The *existence* of such a `Q` is the last
missing stone of the counting half; the construction is written up in
`Submission/Work/Drive/PLANE_CAP_CONSTRUCTION.md` (band continuation `τ ↦ M(τ), W(τ)` of the chord
data, the radial profiles `Work.Drive.wCollapse` / `Work.Drive.tauComp` of `planeProfiles.lean`, and
the collar lemma `Work.Drive.exists_collar_ne_pos`).
-/

namespace Work.Drive

noncomputable section

open Manifold
open scoped Manifold ContDiff

/-- **The plane chart of `γ`**: a smooth disk model of the capped plane, with the strip values on the
outer annulus, the antipodal identification of the boundary circle, and the cap on the inner disk. -/
def IsPlaneChart (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (Q : ℂ → CappingSpace) : Prop :=
  (letI := cappingCharted;
   ContMDiff (modelWithCornersSelf ℝ ℂ)
     (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q) ∧
  (∀ z : ℂ, 1 / 2 < ‖z‖ → ‖z‖ ≤ 1 →
    Q z = stripChart γ hγne 0
      (mk2 (Complex.arg z + Real.sqrt (Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2))
        (Complex.arg z - Real.sqrt (Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2)))) ∧
  (∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) ∧
  (∀ z : ℂ, ‖z‖ < 1 / 2 → ∃ c : CapPiece, Q z = Quotient.mk'' (Sum.inr c))

end

end Work.Drive
