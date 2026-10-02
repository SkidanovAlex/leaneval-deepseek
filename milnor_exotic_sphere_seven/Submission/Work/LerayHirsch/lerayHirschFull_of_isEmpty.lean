import Mathlib
import Submission.Work.LerayHirsch.LH
import Submission.Work.Cohomology.pd_middleDegree_of_good
import Submission.Work.Thom.thomClass_of_finite_cover

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Leray–Hirsch for a bundle over the empty base

If the base `B` of a complex gluing-data bundle `Z` is empty, then so are the projectivisation
`P(E) = ProjSpace Z` (its points are classes of nonzero vectors of the total space of the
realification, and there are none) and, consequently, every cohomology group appearing in the
Leray–Hirsch statement.  Both the domain and the codomain of the Leray–Hirsch maps are therefore
subsingletons, and the domain is inhabited (a function into the cohomology of `B`); hence every
`lhMap Z k` and every `lhMapOdd Z k` is a bijection and `LerayHirschFull Z` holds.

This is the base case ("the bundle over the empty base") of the Mayer–Vietoris induction proving
Leray–Hirsch, and it is also what makes the statement meaningful for every `m` (including `m = 0`,
where the projectivisation is empty for every `B`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.LerayHirsch

/-- **The `n`-th singular cohomology of an empty space is the zero module**: the singular cochain
complex vanishes in every degree, hence so does its `n`-th homology. -/
theorem isZero_cohomology_of_isEmpty {X : Type} [TopologicalSpace X] [IsEmpty X] (n : ℕ) :
    CategoryTheory.Limits.IsZero (Work.Thom.Coh ℤ n X) := by
  rw [Work.Thom.Coh, Work.Cohomology.singularCohomology]
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact CategoryTheory.ShortComplex.exact_of_isZero_X₂ _
    (Work.Cohomology.isZero_singularCochainComplex_of_isEmpty (TopCat.of X) n)

/-- The singular cohomology of an empty space is a subsingleton (indeed the zero module). -/
theorem subsingleton_cohomology_of_isEmpty {X : Type} [TopologicalSpace X] [IsEmpty X] (n : ℕ) :
    Subsingleton (Work.Thom.Coh ℤ n X) :=
  ModuleCat.subsingleton_of_isZero (isZero_cohomology_of_isEmpty n)

/-- **The projectivisation of a complex gluing-data bundle over an empty base is empty**: its
points are `ℂˣ`-classes of points of the punctured total space `E∖0`, and the total space of `Z`,
being the total space of a bundle over `B = ∅`, is empty. -/
theorem isEmpty_projSpace_of_isEmpty {B : Type} [TopologicalSpace B] [IsEmpty B] {ι : Type}
    {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    IsEmpty (ProjSpace Z) :=
  letI : IsEmpty ↥(Work.Thom.zeroComplement (Work.Thom.realification Z)) :=
    ⟨fun p => isEmptyElim p.1.1⟩
  ⟨fun q => Quotient.inductionOn q (fun p => isEmptyElim p)⟩

/-- **Leray–Hirsch holds for a bundle over the empty base.**  Every cohomology group involved is a
subsingleton, the domains of the Leray–Hirsch maps are inhabited, so both the even and the odd part
of the theorem are immediate. -/
theorem lerayHirschFull_of_isEmpty {B : Type} [TopologicalSpace B] [IsEmpty B] {ι : Type} {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] :
    Work.LerayHirsch.LerayHirschFull Z := by
  haveI hProj : IsEmpty (ProjSpace Z) := isEmpty_projSpace_of_isEmpty Z
  haveI subsB : ∀ n, Subsingleton (Work.Thom.Coh ℤ n B) :=
    fun n => subsingleton_cohomology_of_isEmpty n
  haveI subsP : ∀ n, Subsingleton (Work.Thom.Coh ℤ n (ProjSpace Z)) :=
    fun n => subsingleton_cohomology_of_isEmpty n
  refine ⟨fun k => ?_, fun k => ?_⟩
  · refine ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨fun i => 0, ?_⟩⟩
    exact Subsingleton.elim _ _
  · refine ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨fun i => 0, ?_⟩⟩
    exact Subsingleton.elim _ _

end Work.LerayHirsch
