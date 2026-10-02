import Mathlib
import Submission.Work.Serre.cubePairDefs
import Submission.Work.StemsB.CubePairHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative homology of the cube pair `(I^D, ∂I^D)` vanishes away from degree `D`

The pair `(I^D, ∂I^D)` is the pair of the closed `D`-disc with its boundary sphere; consequently its
relative homology is `ℤ` in degree `D` and vanishes in every other degree.  This file proves the
vanishing part, in the `PUnit`-parametrised model of area STEMS-B:

* `Work.StemsB.cubePair_iso` computes the relative homology of `(I^k × Y, ∂I^k × Y)` as `H_{j}(Y)`
  in degree `j + k` for *every* `j`, and
* `Work.StemsB.cubePair_isZero` gives the vanishing below the cube dimension;

the two together with the vanishing of the positive-degree homology of a point
(`Work.Cohomology.homologyContractible`) give the vanishing in *all* degrees `≠ D`.  The transport
from the `PUnit`-parametrised model `I^D × pt` to the cube `I^D` itself is the homeomorphism of
pairs `Work.StemsB.nonempty_relChains_homology_iso_of_homeomorph` along `I^D × pt ≃ₜ I^D`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- The homeomorphism `I^D × pt ≃ₜ I^D` forgetting the (unique) point of the parameter space.  It
carries the boundary `∂I^D × pt` onto the boundary `∂I^D`. -/
def cubePUnitHomeoIC (D : ℕ) :
    Work.StemsB.CubeP PUnit D ≃ₜ Work.Stems.Cubical.IC D where
  toFun p := p.1
  invFun v := (v, ⟨⟩)
  left_inv p := by obtain ⟨v, u⟩ := p; cases u; rfl
  right_inv v := rfl
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prodMk continuous_const

/-- The homeomorphism `I^D × pt ≃ₜ I^D` matches the two boundaries. -/
theorem cubePUnitHomeoIC_mem (D : ℕ) (p : Work.StemsB.CubeP PUnit D) :
    p ∈ Work.StemsB.cubeBdryK PUnit D ↔ cubePUnitHomeoIC D p ∈ cubeBdryS D :=
  Iff.rfl

/-- **The relative homology of the `PUnit`-parametrised cube pair vanishes away from degree `D`.**
This is the model computation `I^D × pt`: below degree `D` the relative homology vanishes because
the cube is `D`-dimensional (`Work.StemsB.cubePair_isZero`), and above degree `D` it is the homology
of the point in a positive degree (`Work.StemsB.cubePair_iso` +
`Work.Cohomology.homologyContractible`). -/
theorem cubePairPUnit_isZero (D m : ℕ) (hm : m ≠ D) :
    IsZero ((Work.Cohomology.relChains (Work.StemsB.CubeSpace (Y := PUnit) D)
      (Work.StemsB.cubeBdryK PUnit D)).homology m) := by
  by_cases hlt : m < D
  · exact Work.StemsB.cubePair_isZero D PUnit m hlt
  · have hle : D ≤ m := Nat.le_of_not_lt hlt
    have hgt : D < m := lt_of_le_of_ne hle (Ne.symm hm)
    have hj : 0 < m - D := Nat.sub_pos_of_lt hgt
    obtain ⟨e⟩ := Work.StemsB.cubePair_iso D PUnit (m - D)
    have h := IsZero.of_iso (Work.Cohomology.homologyContractible (m - D) hj) e
    rwa [show (m - D) + D = m from Nat.sub_add_cancel hle] at h

/-- **The relative homology of the cube pair `(I^D, ∂I^D)` vanishes in every degree `m ≠ D`.**

`(I^D, ∂I^D)` is the pair of the `D`-disc with its boundary sphere, so its relative homology is `ℤ`
in degree `D` and zero elsewhere.  The proof transports `cubePairPUnit_isZero` from the model
`I^D × pt` to `I^D` along the homeomorphism of pairs `I^D × pt ≃ₜ I^D`. -/
theorem cubeBdry_isZero (D m : ℕ) (hm : m ≠ D) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains (TopCat.of (Work.Stems.Cubical.IC D))
      (Work.Serre.cubeBdryS D)).homology m) := by
  obtain ⟨e⟩ := Work.StemsB.nonempty_relChains_homology_iso_of_homeomorph
    (X := Work.StemsB.CubeSpace (Y := PUnit) D) (Y := TopCat.of (Work.Stems.Cubical.IC D))
    (cubePUnitHomeoIC D) (Work.StemsB.cubeBdryK PUnit D) (cubeBdryS D)
    (cubePUnitHomeoIC_mem D) m
  exact IsZero.of_iso (cubePairPUnit_isZero D m hm) e.symm

end

end Work.Serre
