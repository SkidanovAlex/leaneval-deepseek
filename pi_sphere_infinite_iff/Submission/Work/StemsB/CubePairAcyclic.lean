import Submission.Work.StemsB.CubePairGeom

/-!
# The two halves of the cover of `I^{n+1} × Y` are acyclic relative to the boundary

`Submission/Work/StemsB/CubePairGeom.lean` proves that the zero face `{last = 0} × Y` is a homotopy
retract of the first slab `U = {last < 3/4}` of the cube `I^{n+1} × Y`, and the one face
`{last = 1} × Y` of the second slab `V = {last > 1/4}`.  This file draws the homological
consequences, which are the vanishing hypotheses of the relative Mayer–Vietoris sequence used in
`Submission/Work/StemsB/CubePairHomology.lean`:

* `Work.StemsB.isZero_relChains_slabA` / `..._slabB` : the relative homology of the pair
  `(U, U ∩ ∂I^{n+1})` vanishes in **every** degree (including degree `0`);
* `Work.StemsB.isZero_relSmallChains_slabA` / `..._slabB` : the same for the *small* chains of the
  cover, which are the terms appearing in the relative Mayer–Vietoris sequence.
-/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

namespace Work.StemsB

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-- **The inclusion of the boundary part of the first slab is a homology isomorphism.** -/
theorem isIso_inclSlabA (n : ℕ) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (slabAi (Y := Y) n))
        (TopCat.of ↥(slabA (Y := Y) n)) (inclSlabA n)) j) :=
  Work.Cohomology.homologyEquiv ℤ (TopCat.of (slabAi (Y := Y) n))
    (TopCat.of ↥(slabA (Y := Y) n)) (inclSlabA n) (pushSlabA n)
    (homSlabAi n) (homSlabA n) j

/-- **The inclusion of the boundary part of the second slab is a homology isomorphism.** -/
theorem isIso_inclSlabB (n : ℕ) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (slabBi (Y := Y) n))
        (TopCat.of ↥(slabB (Y := Y) n)) (inclSlabB n)) j) :=
  Work.Cohomology.homologyEquiv ℤ (TopCat.of (slabBi (Y := Y) n))
    (TopCat.of ↥(slabB (Y := Y) n)) (inclSlabB n) (pushSlabB n)
    (homSlabBi n) (homSlabB n) j

/-- **The relative homology of `(U, U ∩ ∂I^{n+1})` vanishes in positive degrees.** -/
theorem isZero_relChains_slabA_succ (n : ℕ) (j : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(slabA (Y := Y) n))
      (slabAi (Y := Y) n)).homology (j + 1)) :=
  isZero_relChainsR_homology_succ_of_isIso ℤ (TopCat.of ↥(slabA (Y := Y) n))
    (slabAi (Y := Y) n) j (isIso_inclSlabA n (j + 1)) (isIso_inclSlabA n j)

/-- **The relative homology of `(V, V ∩ ∂I^{n+1})` vanishes in positive degrees.** -/
theorem isZero_relChains_slabB_succ (n : ℕ) (j : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(slabB (Y := Y) n))
      (slabBi (Y := Y) n)).homology (j + 1)) :=
  isZero_relChainsR_homology_succ_of_isIso ℤ (TopCat.of ↥(slabB (Y := Y) n))
    (slabBi (Y := Y) n) j (isIso_inclSlabB n (j + 1)) (isIso_inclSlabB n j)

/-- **The relative homology of `(U, U ∩ ∂I^{n+1})` vanishes in degree zero.** -/
theorem isZero_relChains_slabA_zero (n : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(slabA (Y := Y) n))
      (slabAi (Y := Y) n)).homology 0) :=
  Work.ThreeConnected.Excision.isZero_homology_zero_of_cokernel_pi_eq_zero
    (Work.Cohomology.inclChains (TopCat.of ↥(slabA (Y := Y) n)) (slabAi (Y := Y) n))
    (Work.ThreeConnected.Excision.homologyMap_cokernel_pi_eq_zero
      (inclSlabA n) (pushSlabA n) ⟨homSlabA n⟩ 0)

/-- **The relative homology of `(V, V ∩ ∂I^{n+1})` vanishes in degree zero.** -/
theorem isZero_relChains_slabB_zero (n : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(slabB (Y := Y) n))
      (slabBi (Y := Y) n)).homology 0) :=
  Work.ThreeConnected.Excision.isZero_homology_zero_of_cokernel_pi_eq_zero
    (Work.Cohomology.inclChains (TopCat.of ↥(slabB (Y := Y) n)) (slabBi (Y := Y) n))
    (Work.ThreeConnected.Excision.homologyMap_cokernel_pi_eq_zero
      (inclSlabB n) (pushSlabB n) ⟨homSlabB n⟩ 0)

/-- **The relative homology of `(U, U ∩ ∂I^{n+1})` vanishes in every degree.** -/
theorem isZero_relChains_slabA (n : ℕ) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(slabA (Y := Y) n))
      (slabAi (Y := Y) n)).homology m) := by
  cases m with
  | zero => exact isZero_relChains_slabA_zero n
  | succ j => exact isZero_relChains_slabA_succ n j

/-- **The relative homology of `(V, V ∩ ∂I^{n+1})` vanishes in every degree.** -/
theorem isZero_relChains_slabB (n : ℕ) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(slabB (Y := Y) n))
      (slabBi (Y := Y) n)).homology m) := by
  cases m with
  | zero => exact isZero_relChains_slabB_zero n
  | succ j => exact isZero_relChains_slabB_succ n j

/-- **The first small-chains term of the relative Mayer–Vietoris sequence vanishes in every
degree.** -/
theorem isZero_relSmallChains_slabA (n : ℕ) (m : ℕ) :
    IsZero ((Work.Cohomology.relSmallChains (X := CubeSpace (Y := Y) (n+1))
      (slabA (Y := Y) n) (slabB (Y := Y) n) (slabA (Y := Y) n) (slabA (Y := Y) n ∩ cubeBdry (Y := Y) n)
      (Set.inter_subset_left : slabA (Y := Y) n ∩ cubeBdry (Y := Y) n ⊆ slabA (Y := Y) n)).homology m) := by
  obtain ⟨e⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains
    (X := CubeSpace (Y := Y) (n+1)) (slabA (Y := Y) n) (slabB (Y := Y) n)
    (slabA (Y := Y) n) (slabA (Y := Y) n ∩ cubeBdry (Y := Y) n)
    (Set.inter_subset_left : slabA (Y := Y) n ∩ cubeBdry (Y := Y) n ⊆ slabA (Y := Y) n)
    (Or.inl subset_rfl)
  exact IsZero.of_iso (isZero_relChains_slabA (Y := Y) n m)
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso e)

/-- **The second small-chains term of the relative Mayer–Vietoris sequence vanishes in every
degree.** -/
theorem isZero_relSmallChains_slabB (n : ℕ) (m : ℕ) :
    IsZero ((Work.Cohomology.relSmallChains (X := CubeSpace (Y := Y) (n+1))
      (slabA (Y := Y) n) (slabB (Y := Y) n) (slabB (Y := Y) n) (slabB (Y := Y) n ∩ cubeBdry (Y := Y) n)
      (Set.inter_subset_left : slabB (Y := Y) n ∩ cubeBdry (Y := Y) n ⊆ slabB (Y := Y) n)).homology m) := by
  obtain ⟨e⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains
    (X := CubeSpace (Y := Y) (n+1)) (slabA (Y := Y) n) (slabB (Y := Y) n)
    (slabB (Y := Y) n) (slabB (Y := Y) n ∩ cubeBdry (Y := Y) n)
    (Set.inter_subset_left : slabB (Y := Y) n ∩ cubeBdry (Y := Y) n ⊆ slabB (Y := Y) n)
    (Or.inr subset_rfl)
  exact IsZero.of_iso (isZero_relChains_slabB (Y := Y) n m)
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso e)

end

end Work.StemsB
