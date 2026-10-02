import Mathlib
import Submission.Work.Thom.localThom_full
import Submission.Work.Thom.subsingleton_PieceCoh_genFibre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The Thom isomorphism theorem for an oriented bundle with an arbitrary finite-dimensional fibre

`Work.Thom.nonempty_thomClass_of_oriented` (`Submission/Work/Thom/localThom_full.lean`) proves the
Thom isomorphism theorem for a real bundle `Z → B` trivial over a two-piece open cover, with the
orientation `Work.Thom.IsOrientedOver Z n U V` and the low-degree vanishing
`Subsingleton (PieceCoh Z (U ∩ V) (n - 1))` as its two hypotheses.  For the model fibre
`EuclideanSpace ℝ (Fin n)` the second hypothesis is automatic over a chart
(`Work.Thom.subsingleton_PieceCoh_of_lt_rankA`).

This module supplies the same for an **arbitrary finite-dimensional real normed fibre** `F`, using
`Work.Thom.subsingleton_PieceCoh_genFibre` for the vanishing.  This is the form in which the
*realification* of a complex bundle (whose fibre is a complex, hence real, vector space) is
covered: the fibre of `Work.Thom.realification Z` is the complex normed space `F`, of real
dimension `2 * Module.finrank ℂ F`.
-/

open Work.TangentClasses

namespace Work.Thom

open CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **The Thom isomorphism theorem for an oriented bundle of arbitrary finite-dimensional real
fibre**, trivial over a two-piece open cover.  The orientation `IsOrientedOver` is the only
bundle-theoretic input: the low-degree vanishing is supplied by
`Work.Thom.subsingleton_PieceCoh_genFibre` from the chart hypothesis `U ∩ V ⊆ Z.baseSet k`. -/
theorem nonempty_thomClass_of_oriented_genFibre [Inhabited ι] {n : ℕ} (hn : 1 ≤ n)
    [FiniteDimensional ℝ F] (hF : Module.finrank ℝ F = n)
    (Z : RealBundle B F ι) {U V : Set B} (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (hori : IsOrientedOver Z n U V)
    {k : ι} (hUVk : U ∩ V ⊆ Z.baseSet k) :
    Nonempty (ThomClass Z n) :=
  nonempty_thomClass_of_oriented hn Z hU hV hcov hori
    (subsingleton_PieceCoh_genFibre Z k hUVk (m := n - 1) (by omega))

end

end Work.Thom
