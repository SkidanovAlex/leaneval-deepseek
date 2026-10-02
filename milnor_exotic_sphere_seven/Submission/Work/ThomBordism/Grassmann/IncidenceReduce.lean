import Mathlib
import Submission.Work.ThomBordism.Grassmann.IncidenceKernel
import Submission.Work.ThomBordism.Grassmann.SphereCover
import Submission.Work.ThomBordism.Grassmann.Model

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

/-!
# Reduction of the incidence fibre statement to two geometric inputs

The target `incidenceFibreCohomology` is a statement about the cohomology of the incidence space
`E = zeroComplement (tautologicalBundle k m)` and of the fibre `OG (k-1) m`.  This module reduces it
to the two geometric inputs that the local triviality of the incidence fibration provides:

* the restrictions `H^i(upSet) ⟶ H^i(upSet ∩ downSet)` and `H^i(downSet) ⟶ H^i(upSet ∩ downSet)`
  are bijections for `i ≤ k + m - 3` (this is where the ball/annulus computation of the bundle over
  the two hemispheres is used);
* `H^j(upSet) ≅ H^j(OG (k-1) m)` (the upper hemisphere is cohomologically the fibre).

Everything else — the two-set cover, the Mayer–Vietoris short exact sequence, the identification of
its maps with the honest restrictions, the five-term extraction and the passage from the small-chain
complex to the singular cochain complex — is proved in this workspace
(`Work.Cohomology.mvCochainSES`, `Work.Cohomology.cohSmallIso`,
`Work.ThomBordism.Grassmann.mvExtractEquiv`) and assembled here.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.ThomBordism.Grassmann

noncomputable section

open Work.Cohomology

/-- **The incidence fibre statement, from the two geometric inputs** (in the form in which the
Mayer–Vietoris pieces are stated). -/
theorem incidenceFibreCohomology_singular (k m j : ℕ) (hk : 1 ≤ k) (hj1 : 1 ≤ j)
    (hj : j ≤ k + m - 3)
    (hU : ∀ i, i + 2 ≤ k + m - 1 →
      Function.Bijective (restU (X := TopCat.of ↥(zeroComp k m)) (upSet k m) (downSet k m) i))
    (hV : ∀ i, i + 2 ≤ k + m - 1 →
      Function.Bijective (restV (X := TopCat.of ↥(zeroComp k m)) (upSet k m) (downSet k m) i))
    (hup : Nonempty (singularCohomology ℤ j (TopCat.of ↥(upSet k m)) ≅
      singularCohomology ℤ j (TopCat.of (OG (k - 1) m)))) :
    Nonempty (singularCohomology ℤ j (TopCat.of ↥(zeroComp k m)) ≃ₗ[ℤ]
      singularCohomology ℤ j (TopCat.of (OG (k - 1) m))) := by
  classical
  obtain ⟨e₁⟩ := cohSmallIso (X := TopCat.of ↥(zeroComp k m)) (upSet k m) (downSet k m)
    (isOpen_upSet k m) (isOpen_downSet k m) (upSet_union_downSet k m) j
  have e₂ := mvExtractEquiv (X := TopCat.of ↥(zeroComp k m)) (upSet k m) (downSet k m) j hj1
    (hU j (by omega)) (hU (j - 1) (by omega)) (hV j (by omega))
  obtain ⟨e₃⟩ := hup
  exact ⟨e₁.toLinearEquiv.trans (e₂.trans e₃.toLinearEquiv)⟩

/-- **The incidence fibre statement, from the two geometric inputs**, in the form of the target
statement of this chapter. -/
theorem incidenceFibreCohomology_of_geometry (k m j : ℕ) (hk : 1 ≤ k) (hj1 : 1 ≤ j)
    (hj : j ≤ k + m - 3)
    (hU : ∀ i, i + 2 ≤ k + m - 1 →
      Function.Bijective (restU (X := TopCat.of ↥(zeroComp k m)) (upSet k m) (downSet k m) i))
    (hV : ∀ i, i + 2 ≤ k + m - 1 →
      Function.Bijective (restV (X := TopCat.of ↥(zeroComp k m)) (upSet k m) (downSet k m) i))
    (hup : Nonempty (singularCohomology ℤ j (TopCat.of ↥(upSet k m)) ≅
      singularCohomology ℤ j (TopCat.of (OG (k - 1) m)))) :
    Nonempty ((cochainC ℤ (sset ↥(zeroComp k m))).homology j ≃ₗ[ℤ]
      (cochainC ℤ (sset (OG (k - 1) m))).homology j) := by
  obtain ⟨e⟩ := incidenceFibreCohomology_singular k m j hk hj1 hj hU hV hup
  exact ⟨e⟩

end

end Work.ThomBordism.Grassmann
