import Mathlib
import Submission.Work.Mostow.dirichletSet_isFundamentalDomain
import Submission.Work.Mostow.exists_closest_orbit
import Submission.Work.Mostow.volH_null_linear
import Submission.Work.Mostow.thinTubeDefs
import Submission.Work.Mostow.haarBridge

/-!
# A fundamental domain for a discrete subgroup of `PO 3 1`

**Gap A closure.**  A discrete subgroup `H ≤ PO 3 1` admits a `volH`-fundamental domain in
`ℍ³ = E 3`.

The construction is the **Dirichlet domain** at a base point `o` whose `H`-stabiliser is trivial:

`D = {x | ∀ γ : H, hdist x o ≤ hdist x (γ • o)}`.

Three ingredients, all available in the workspace:

* `Work.Mostow.countable_of_isDiscrete` — a discrete subset of the second countable group
  `PO 3 1` is countable, so `H` is a countable group;
* `Work.Mostow.exists_trivial_stabiliser` — the union of the fixed point sets of the elements
  `γ ≠ 1` is `volH`-null (each is contained in a hyperplane zero set, `fix_subset_hyperplane`
  + `volH_null_linear`), hence there is a point outside it, i.e. with trivial stabiliser;
* `Work.Mostow.exists_closest_orbit` — properness of the action: every orbit has a point closest
  to a given point (a near-stabiliser argument).

Then `Work.Mostow.dirichletSet_isFundamentalDomain` (Dirichlet domains are fundamental domains,
with a.e. disjointness of translates coming from nullity of bisectors) gives the result.

No lattice hypothesis (finite covolume) is used: the statement holds for every discrete subgroup.
-/

set_option linter.style.haveILetI false

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem exists_fundamentalDomain (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) (H : Subgroup (LeanEval.Geometry.MostowRigidity.PO 3 1))
    (hdisc : IsDiscrete (SetLike.coe H)) :
    ∃ D : Set (Submission.Mostow.E 3),
      MeasureTheory.IsFundamentalDomain ↥H D (Submission.Mostow.volH 3) := by
  -- a discrete subgroup of `PO 3 1` is countable
  haveI : Countable ↥H :=
    Work.Mostow.countable_of_isDiscrete (LeanEval.Geometry.MostowRigidity.PO 3 1) hdisc
  -- a base point with trivial stabiliser
  obtain ⟨o, ho⟩ := Work.Mostow.exists_trivial_stabiliser 3 hA hI H hdisc
  -- the Dirichlet domain at `o` is a fundamental domain
  exact ⟨Work.Mostow.dirichletSet H o,
    Work.Mostow.dirichletSet_isFundamentalDomain 3 hA hI H o ho
      (fun x => Work.Mostow.exists_closest_orbit 3 hA hI hdisc o x)⟩

end Work.Mostow.gapA
