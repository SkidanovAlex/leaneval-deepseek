import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs

/-!
# Margulis thin regions at a parabolic fixed point

For a subgroup `Γ ≤ PO(n,1)`, a boundary point `ξ` and a level `ε > 0`, the *Margulis thin
region* at `ξ` is the set of points of `ℍⁿ` that are moved by less than `ε` by some **parabolic**
element of `Γ` fixing `ξ`:

`cuspThinRegion Γ ξ ε = {u | ∃ q : Γ, IsParabolic q ∧ bd q ξ = ξ ∧ hdist u (q • u) < ε}`.

These are the regions that the Margulis lemma controls.  The two facts proved elsewhere and used
in `Submission/Work/Mostow/cuspHoroballsPairwise.lean` are

* for `ε` below a Margulis threshold, thin regions of *distinct* parabolic fixed points are
  disjoint (`cuspThinRegion_separation`, proved from `Work.Mostow.cuspMargulisCommon` and
  `Work.Mostow.parabolicCommuteFix`), and
* every thin region contains a horoball at its cusp (`Work.Mostow.cuspThinHoroball`).

The `Γ`-action sends the thin region at `ξ` to the thin region at `bd γ ξ`
(`cuspThinRegion_smul`), which is what makes the associated height `Γ`-equivariant.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- The Margulis thin region at the boundary point `ξ` of level `ε`: points moved by less than
`ε` by some parabolic element of `Γ` fixing `ξ`. -/
def cuspThinRegion (Γ : Subgroup (PO n 1)) (ξ : E n) (ε : ℝ) : Set (E n) :=
  {u | ∃ q : Γ, IsParabolic (q : PO n 1) ∧ bd (q : PO n 1) ξ = ξ ∧
        hdist u ((q : PO n 1) • u) < ε}

/-- The thin region is monotone in the level. -/
lemma cuspThinRegion_mono {Γ : Subgroup (PO n 1)} {ξ : E n} {ε ε' : ℝ} (h : ε ≤ ε') :
    cuspThinRegion Γ ξ ε ⊆ cuspThinRegion Γ ξ ε' :=
  fun u hu => let ⟨q, hq, hfix, hd⟩ := hu; ⟨q, hq, hfix, lt_of_lt_of_le hd h⟩

end

end Work.Mostow
