import Mathlib
import Submission.Work.Serre.ratPairBasic
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.B1Rel.Model
import Submission.Work.Serre.B1Rel.Assembly
import Submission.Work.Serre.ratPairComparisonOneBoundary

/-!
# The rational Serre pair comparison for a path connected base (`b = 1`)

For a Serre fibration `p : E → B` over a path connected base whose fibre over `b₀` is path connected
and rationally acyclic in degrees `0 < j < f`, the map of pairs `(E, p⁻¹{b₀}) → (B, {b₀})` is an
isomorphism on rational homology in every degree `i < 1 + f` and surjective in degree `1 + f`.

This is the `b = 1` case of the rational Serre pair comparison (the base is *not* assumed simply
connected), in the form needed by the cellular model of `B`: the isomorphism part is the sharp
`b = 1` model computation `Work.Serre.B1Rel.relPairMapRat_isIso` (built from the sharp rational
`1`-cell step `Work.Serre.B1Rel.oneCellStepSharp`, the `2`-cells killing `π₁` and the
generator/killing tower of `Work.Serre.E3aModel`), and the boundary surjectivity is
`Work.Serre.ratPairComparisonOneBoundary`.
-/

set_option linter.style.haveILetI false

namespace Work.Serre

open CategoryTheory

theorem ratPairComparisonBOneGeneral {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (f : ℕ) (hf : 1 ≤ f)
    (hB : PathConnectedSpace B)
    (hfib0 : PathConnectedSpace (Work.StemsB.fibre p b₀))
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) j)) :
    (∀ i : ℕ, i < 1 + f → Nonempty
      (((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology i) ≅
        ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology i))) ∧
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.relPairMapRat p b₀) (1 + f)).hom := by
  haveI hB' : PathConnectedSpace B := hB
  haveI hfib0' : PathConnectedSpace (Work.StemsB.fibre p b₀) := hfib0
  -- the fibre data at every point of the base, from the data at `b₀`
  have h0b₀ : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) 0
      ≅ ModuleCat.of ℚ ℚ) :=
    Work.Serre.ratH_zero_of_pathConnected (Work.StemsB.fibre p b₀)
  obtain ⟨hfib_all, h0_all⟩ := Work.Serre.B1Rel.fibreDataBelow_all p hp b₀ f hfib h0b₀
  refine ⟨fun i hi => ?_,
    Work.Serre.ratPairComparisonOneBoundary p hp b₀ f hf hB hfib0 hfib⟩
  -- the sharp `b = 1` model comparison is an isomorphism below `1 + f`
  haveI : CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b₀) i) :=
    Work.Serre.B1Rel.relPairMapRat_isIso p hp b₀ (1 + f) f (by omega) hfib_all h0_all i hi
  exact ⟨CategoryTheory.asIso
      (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b₀) i)⟩

end Work.Serre
