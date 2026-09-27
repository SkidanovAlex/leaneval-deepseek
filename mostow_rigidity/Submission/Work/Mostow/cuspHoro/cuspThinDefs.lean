import Mathlib
import Submission.Work.Mostow.cuspHoroDefs

/-!
# The Margulis cusp regions `cuspThin`

For a subgroup `Γ ≤ PO(n,1)` and a boundary point `ξ`, the *cusp region* of `ξ` at level `ε` is
the set of points of `ℍⁿ` that are moved by less than `ε` by some **parabolic** element of `Γ`
which **fixes** `ξ`:

`cuspThin Γ ξ ε = {u | ∃ γ ∈ Γ, IsParabolic γ ∧ bd γ ξ = ξ ∧ hdist u (γ • u) < ε}`.

These are the regions on which the Margulis lemma controls the group: two such regions belonging
to *distinct* parabolic fixed points `ξ ≠ η` are disjoint for small `ε`
(`Work.Mostow.cuspHoro.cuspThinSeparation`), while for small `ε` the Margulis horoball
`horoball ξ (htEps Γ ε ξ)` of `cuspHoroDefs` is contained in `cuspThin Γ ξ δ` for every fixed
`δ > 0` (`Work.Mostow.cuspHoro.horoballSubCuspThin`). Together these two facts give the pairwise
disjointness of the Margulis horoballs, `Work.Mostow.cuspHoro.cuspHoroballDisjoint`.
-/

namespace Work.Mostow.cuspHoro

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The `ε`-neighbourhood-of-`ξ`-cusp region: points moved by less than `ε` by a parabolic
element of `Γ` fixing `ξ`. -/
def cuspThin (Γ : Subgroup (PO n 1)) (ξ : E n) (ε : ℝ) : Set (E n) :=
  {u | ∃ γ : Γ, IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ ∧
        hdist u ((γ : PO n 1) • u) < ε}

/-- `cuspThin` is monotone in the level. -/
lemma cuspThin_mono {Γ : Subgroup (PO n 1)} {ξ : E n} {ε ε' : ℝ} (h : ε ≤ ε')
    {u : E n} (hu : u ∈ cuspThin Γ ξ ε) : u ∈ cuspThin Γ ξ ε' := by
  obtain ⟨γ, hγ, hfix, hd⟩ := hu
  exact ⟨γ, hγ, hfix, lt_of_lt_of_le hd h⟩

end

end Work.Mostow.cuspHoro
