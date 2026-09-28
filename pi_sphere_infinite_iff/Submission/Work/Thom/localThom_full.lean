import Mathlib
import Submission.Work.Thom.localThom_line
import Submission.Work.Thom.thomClassTrivialEuclideanA
import Submission.Work.Thom.subsingleton_PieceCohA
import Submission.Work.Thom.nonempty_thomClass_of_compatible_local

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The Thom isomorphism theorem for a bundle trivial over a two-chart cover

This module assembles the two halves delivered by `Submission/Work/Thom/`:

* **the local step** (`Work.Thom.nonempty_localThom_of_subset_baseSet`, below): over a set `U ⊆ B`
  contained in a chart of a real bundle `Z` of rank `n`, the restricted Thom pair carries a *local
  Thom class* `Work.Thom.LocalThom Z n U` — a class for which `x ↦ π^*(x) ⌣ τ` is bijective in
  every degree.  This is `Work.Thom.nonempty_localThom_of_subset_baseSet_of_trivial` with the Thom
  class of the trivial bundle supplied by `Work.Thom.thomClassTrivialEuclideanA`, and it is
  **unconditional**;
* **the global step** (`Work.Thom.nonempty_thomClass_of_oriented`): compatible local data over the
  two pieces of an open cover, plus the vanishing of the relative cohomology of the overlap in
  degree `n - 1`, give a Thom class of the whole bundle
  (`Work.Thom.nonempty_thomClass_of_compatible_local`).

`Work.Thom.IsOrientedOver Z n U V` records the compatibility of the local data — the chapter's
formalisation of an **orientation** of the bundle over the cover (the classical condition on the
transition functions: they preserve the model Thom class).  The orientation is the only remaining
input: for a bundle trivialised over the cover, `Work.Thom.nonempty_localThom_of_subset_baseSet`
supplies local data over `U`, `V` and over the overlap `U ∩ V` (whenever each of the three sets lies
in a chart, `Work.Thom.nonempty_thomClass_of_charts`), and the local data over the overlap of the
two pieces differ from the local data over the overlap by a unit of
`H^0(X|_{U∩V}, X|_{U∩V}∖0)`; compatibility says the unit is `1`.

The low-degree vanishing `Work.Thom.subsingleton_PieceCoh_of_lt_rankA`
(`Submission/Work/Thom/subsingleton_PieceCohA.lean`) is also unconditional.
-/

open Work.TangentClasses

namespace Work.Thom

open CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **The local step of the Thom isomorphism theorem: local Thom data over a chart.**  For a real
bundle `Z → B` of rank `n ≥ 1` with model fibre `EuclideanSpace ℝ (Fin n)` and a set `U ⊆ B`
contained in a chart `Z.baseSet i`, the restricted Thom pair carries a local Thom class. -/
theorem nonempty_localThom_of_subset_baseSet {ι : Type}
    (n : ℕ) (hn : 1 ≤ n) (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι) (i : ι) (U : Set B)
    (hU : U ⊆ Z.baseSet i) : Nonempty (LocalThom Z n U) :=
  nonempty_localThom_of_subset_baseSet_of_trivial Z i U hU
    (thomClassTrivialEuclideanA n ↥U hn)

/-- **An orientation of a real bundle over a two-piece cover**: a choice of local Thom data over
`U`, over `V` and over the overlap `U ∩ V` which is *compatible*, i.e. such that the local data over
`U` and over `V` restrict to the local data over `U ∩ V`.  This is the compatibility input of
`Work.Thom.nonempty_thomClass_of_compatible_local`, and it is the honest algebraic shadow of the
classical condition that the transition functions of the bundle preserve the model Thom class (a
bundle carries such data iff it is orientable over the cover, and then the data are unique up to a
unit of `H^0(X|_{U∩V}, X|_{U∩V}∖0)`). -/
def IsOrientedOver (Z : RealBundle B F ι) (n : ℕ) (U V : Set B) : Prop :=
  ∃ (hUloc : LocalThom Z n U) (hVloc : LocalThom Z n V) (hUVloc : LocalThom Z n (U ∩ V)),
    (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' (U ∩ V)) (Set.preimage_mono Set.inter_subset_left) n).hom
      hUloc.τ = hUVloc.τ ∧
    (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' V) (Z.proj ⁻¹' (U ∩ V)) (Set.preimage_mono Set.inter_subset_right) n).hom
      hVloc.τ = hUVloc.τ

/-- **The Thom isomorphism theorem for an oriented bundle trivial over a two-piece open cover.**
The only bundle-theoretic input besides the cover is the orientation
`Work.Thom.IsOrientedOver Z n U V`; the vanishing of the relative cohomology of the overlap in
degree `n - 1` is the other hypothesis. -/
theorem nonempty_thomClass_of_oriented {n : ℕ} (hn : 1 ≤ n) (Z : RealBundle B F ι)
    {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hori : IsOrientedOver Z n U V)
    (hlow : Subsingleton (PieceCoh Z (U ∩ V) (n - 1))) :
    Nonempty (ThomClass Z n) := by
  obtain ⟨hUloc, hVloc, hUVloc, h1, h2⟩ := hori
  exact nonempty_thomClass_of_compatible_local Z n hn hU hV hcov hUloc hVloc hUVloc h1 h2 hlow

/-- **The Thom isomorphism theorem for an oriented bundle trivial over a cover by two charts.**
Here the sets `U`, `V` and the overlap `U ∩ V` each lie in a chart of `Z` (indices `i`, `j`, `k`),
so the low-degree vanishing `Subsingleton (PieceCoh Z (U ∩ V) (n - 1))` of
`Work.Thom.subsingleton_PieceCoh_of_lt_rankA` is automatic and the only hypothesis left is the
orientation. -/
theorem nonempty_thomClass_of_charts {n : ℕ} (hn : 1 ≤ n) (ι : Type) [Inhabited ι]
    (Z : RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    {i j k : ι} (hUi : U ⊆ Z.baseSet i) (hVj : V ⊆ Z.baseSet j) (hUVk : U ∩ V ⊆ Z.baseSet k)
    (hori : IsOrientedOver Z n U V) :
    Nonempty (ThomClass Z n) :=
  nonempty_thomClass_of_oriented hn Z hU hV hcov hori
    (subsingleton_PieceCoh_of_lt_rankA n ι Z k hUVk (m := n - 1) (by omega))

end

end Work.Thom
