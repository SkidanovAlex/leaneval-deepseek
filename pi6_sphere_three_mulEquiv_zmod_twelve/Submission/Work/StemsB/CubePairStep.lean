import Submission.Work.StemsB.CubePairAcyclic
import Submission.Work.ThreeConnected.Excision.relMV_iso_of_acyclic

/-!
# The Mayer–Vietoris step for the disc pair `(Iⁿ, ∂Iⁿ)` times a parameter space

Since the two halves `U = {last < 3/4}` and `V = {last > 1/4}` of the cover of `I^{n+1} × Y` are
acyclic relative to the boundary (`Submission/Work/StemsB/CubePairAcyclic.lean`), the connecting map
of the relative Mayer–Vietoris sequence is an isomorphism, and the relative homology of the pair
`(I^{n+1} × Y, ∂I^{n+1} × Y)` is that of the middle slab:

  `H_{m+1}(I^{n+1} × Y, ∂I^{n+1} × Y) ≅ H_m((1/4,3/4) × Iⁿ × Y, (1/4,3/4) × ∂Iⁿ × Y)`.

The middle slab is `Iⁿ × ((1/4,3/4) × Y)` with relative part `∂Iⁿ × ((1/4,3/4) × Y)`, so this is
the induction step of `Submission/Work/StemsB/CubePairHomology.lean`.

* `Work.StemsB.slabMid` — the middle slab;
* `Work.StemsB.isZero_relMVH₂_cube` — the middle term of the relative Mayer–Vietoris sequence
  vanishes in every degree;
* `Work.StemsB.isIso_relMVδ_cube` — the connecting map `relMVδ` is an isomorphism in every degree;
* `Work.StemsB.relMVH₁_iso_slabMid`, `Work.StemsB.cubePairStep_iso` — the resulting isomorphism of
  relative homology groups.
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

namespace Work.StemsB

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-- The middle slab `{1/4 < last < 3/4}` of the cover of `I^{n+1} × Y`. -/
def slabMid (n : ℕ) : Set (CubeP Y (n+1)) := slabA (Y := Y) n ∩ slabB (Y := Y) n

/-- The boundary part of the middle slab, as a subset of the middle slab. -/
def slabMidi (n : ℕ) : Set ↥(slabMid (Y := Y) n) :=
  (Subtype.val) ⁻¹' (slabMid (Y := Y) n ∩ cubeBdry (Y := Y) n)

/-- **The middle term of the relative Mayer–Vietoris sequence of the cube cover vanishes in every
degree.** -/
theorem isZero_relMVH₂_cube (n : ℕ) :
    ∀ m : ℕ, IsZero (Work.Cohomology.relMVH₂ (CubeSpace (Y := Y) (n+1)) (cubeBdry (Y := Y) n)
      (slabA (Y := Y) n) (slabB (Y := Y) n) m) := fun m =>
  Work.ThreeConnected.Excision.isZero_homology_biprod
    (isZero_relSmallChains_slabA (Y := Y) n m) (isZero_relSmallChains_slabB (Y := Y) n m)

/-- **The connecting map of the relative Mayer–Vietoris sequence of the cube cover is an
isomorphism in every degree.** -/
theorem isIso_relMVδ_cube (n : ℕ) (m : ℕ) :
    IsIso (Work.Cohomology.relMVδ (CubeSpace (Y := Y) (n+1)) (cubeBdry (Y := Y) n)
      (slabA (Y := Y) n) (slabB (Y := Y) n) m) :=
  Work.ThreeConnected.Excision.relMV_iso_of_acyclic (X := CubeSpace (Y := Y) (n+1))
    (cubeBdry (Y := Y) n) (slabA (Y := Y) n) (slabB (Y := Y) n)
    (isZero_relMVH₂_cube (Y := Y) n) m

/-- **The identification of the first term of the relative Mayer–Vietoris sequence with the
relative homology of the middle slab.** -/
theorem relMVH₁_iso_slabMid (n : ℕ) (m : ℕ) :
    Nonempty (Work.Cohomology.relMVH₁ (CubeSpace (Y := Y) (n+1)) (cubeBdry (Y := Y) n)
        (slabA (Y := Y) n) (slabB (Y := Y) n) m ≅
      ((Work.Cohomology.relChains (TopCat.of ↥(slabMid (Y := Y) n))
        (slabMidi (Y := Y) n)).homology m)) := by
  obtain ⟨e⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains
    (X := CubeSpace (Y := Y) (n+1)) (slabA (Y := Y) n) (slabB (Y := Y) n)
    (slabMid (Y := Y) n) (slabMid (Y := Y) n ∩ cubeBdry (Y := Y) n)
    (Set.inter_subset_left : slabMid (Y := Y) n ∩ cubeBdry (Y := Y) n ⊆ slabMid (Y := Y) n)
    (Or.inl (by intro x hx; exact hx.1))
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso e⟩

/-- **The Mayer–Vietoris step.**  The relative homology of the pair `(I^{n+1} × Y, ∂I^{n+1} × Y)`
in degree `m+1` is that of the middle slab `(1/4,3/4) × Iⁿ × Y` in degree `m`. -/
theorem cubePairStep_iso (n : ℕ) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (CubeSpace (Y := Y) (n+1))
        (cubeBdry (Y := Y) n)).homology (m + 1)) ≅
      ((Work.Cohomology.relChains (TopCat.of ↥(slabMid (Y := Y) n))
        (slabMidi (Y := Y) n)).homology m)) := by
  haveI := isIso_relMVδ_cube (Y := Y) n m
  obtain ⟨e⟩ := relMVH₁_iso_slabMid (Y := Y) n m
  exact ⟨(Work.Cohomology.relMVSmallIso (CubeSpace (Y := Y) (n+1)) (cubeBdry (Y := Y) n)
      (slabA (Y := Y) n) (slabB (Y := Y) n) (isOpen_slabA (Y := Y) n) (isOpen_slabB (Y := Y) n)
      (slabA_union_slabB (Y := Y) n) (m + 1)).symm
    ≪≫ asIso (Work.Cohomology.relMVδ (CubeSpace (Y := Y) (n+1)) (cubeBdry (Y := Y) n)
      (slabA (Y := Y) n) (slabB (Y := Y) n) m) ≪≫ e⟩

end

end Work.StemsB
