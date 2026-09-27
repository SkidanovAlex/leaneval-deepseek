import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.fermi_measurePreserving

/-!
# Vocabulary for `Work.Mostow.gapA.tubeIneq3`

The target theorem `Work.Mostow.gapA.tubeIneq3` needs a "coordinate along the axis"
`X = geodSet a b` that is *equivariant* under the centraliser `C` of the rotation `b₀`
about `X`.  Namely

`sig a b u = (β_b u − β_a u) / 2`

where `β` is the Busemann function (`Submission.Mostow.busemann`).  On the axis `sig` is an
arc-length coordinate, and for `c ∈ C` one has `sig a b (c • u) = ± sig a b u + sig a b (c • 0)`
(the Busemann cocycle together with `bd c a, bd c b ∈ {a,b}`).

Delegated pieces:
* `tubeSubsetTb` : `{distGeod a b ≤ ρ+1} ⊆ Tb b₀ η₁`;
* `sig_isometry_on_geodSet` : on `geodSet a b`, `sig` is the arc-length coordinate;
* `bd_fixed_rotation` : the fixed set of `bd b₀` on the sphere is `{a,b}`;
* `orderOf_rotAbout` : `orderOf b₀ = M`;
* `sourceSlab_vol` : the Fermi-chart volume of a slab.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- The Busemann coordinate along the axis with endpoints `a b`: `(β_b u − β_a u)/2`. -/
def sig (a b u : E 3) : ℝ := (busemann b u - busemann a u) / 2

/-- The centraliser of `b₀` inside `Γ`. -/
def cent (Γ : Subgroup (PO 3 1)) (b₀ : PO 3 1) : Subgroup (PO 3 1) :=
  Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ

/-- The sign by which `c` acts on the coordinate `sig`: `+1` if `bd c a = a`, else `−1`. -/
def eps (a : E 3) (c : PO 3 1) : ℝ := if bd c a = a then 1 else -1

/-- The translation of the coordinate: `sig a b (c • 0)`. -/
def psi (a b : E 3) (c : PO 3 1) : ℝ := sig a b (c • (0 : E 3))

end

end Work.Mostow.gapA
