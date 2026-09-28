import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.relCoh_concentrated_of_ratAcyclic
import Submission.Work.Stems.product_ratH_vanishing
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.ThomCylDefs

/-!
# The rational relative cohomology of the mapping-cylinder pair is concentrated

`Work.Serre.DiscPair.cylPair_concentrated`: for a map `q : C(X,B)` with `B` rationally acyclic and
`X` rationally a rational sphere in degree `r` (through degree `N`), the pair
`(cyl q, range (cylIncl q))` has rational *relative* cohomology concentrated in degree `r+1`
(through degree `N+1`), where it is a line.

The mathematical content is the "geometric input" of subproject SERRE, and it is a direct
application of `Work.Serre.relCoh_concentrated_of_ratAcyclic` to the pair
`P := cyl q`, `Q := Set.range (cylIncl q)`:

* the mapping cylinder `cyl q` is homotopy equivalent to `B` (`cylHomotopyEquiv`), hence rationally
  acyclic;
* the bottom copy `range (cylIncl q)` is homeomorphic to `X` (`cylHomeo`), so its rational homology
  and its path connectedness transfer to `X`.
-/

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option linter.style.haveILetI false

noncomputable section

/-! ## Transport of rational homology along a homeomorphism -/

/-- A homeomorphism induces an isomorphism on rational homology in every degree. -/
private theorem isIso_ratHomologyMap_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (k : ℕ) : IsIso (Work.Serre.ratHomologyMap (e : C(X, Y)) k) :=
  Work.Serre.IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv k

/-! ## The main statement -/

theorem cylPair_concentrated {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (r N : ℕ) (hr : 1 ≤ r)
    (hBacyc : Work.Serre.RatAcyclic B)
    (hX : PathConnectedSpace X)
    (hXvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) t))
    (hXgen : Nonempty (Work.Serre.ratH (TopCat.of X) r ≅ ModuleCat.of ℚ ℚ)) :
    (∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j (Work.Serre.cyl q)
        (Set.range (Work.Serre.cylIncl q)))) ∧
    Nonempty (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q)
      (Set.range (Work.Serre.cylIncl q)) ≅ ModuleCat.of ℚ ℚ) := by
  classical
  -- The bottom copy `range (cylIncl q)` of the mapping cylinder.
  set Q : Set (Work.Serre.cyl q) := Set.range (Work.Serre.cylIncl q) with hQdef
  -- (1) `cyl q` is homotopy equivalent to `B`, hence rationally acyclic.
  have hP : Work.Serre.RatAcyclic (Work.Serre.cyl q) := by
    obtain ⟨he⟩ := Work.Serre.cylHomotopyEquiv q
    exact Work.Serre.ratAcyclic_of_homotopyEquiv he hBacyc
  -- (2) `Q` is homeomorphic to `X` (via the explicit homeomorphism of `cylHomeo`).
  obtain ⟨eH⟩ := Work.Serre.cylHomeo q
  -- (3) transport the fibre data across the homeomorphism.
  have hQ : PathConnectedSpace ↥Q := by
    haveI := hX
    refine eH.surjective.pathConnectedSpace eH.continuous
  have hvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      IsZero (Work.Serre.ratH (TopCat.of ↥Q) t) := by
    intro t ht htr htN
    haveI := isIso_ratHomologyMap_homeo eH t
    exact IsZero.of_iso (hXvan t ht htr htN)
      (asIso (Work.Serre.ratHomologyMap (eH : C(X, ↥Q)) t)).symm
  have hgen : Nonempty (Work.Serre.ratH (TopCat.of ↥Q) r ≅ ModuleCat.of ℚ ℚ) := by
    haveI := isIso_ratHomologyMap_homeo eH r
    obtain ⟨e'⟩ := hXgen
    exact ⟨(asIso (Work.Serre.ratHomologyMap (eH : C(X, ↥Q)) r)).symm ≪≫ e'⟩
  exact Work.Serre.relCoh_concentrated_of_ratAcyclic Q r N hr hP hQ hvan hgen

end

end Work.Serre.DiscPair
