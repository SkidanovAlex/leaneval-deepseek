import Mathlib
import Submission.Work.Thom.Glue
import Submission.Work.Cohomology.relCohMV_honest_les

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-!
# The glueing of local classes into a global class

The middle exactness of the honest relative Mayer--Vietoris sequence
(`Work.Cohomology.honest_exact₂`) says that the two restrictions
`Work.Cohomology.honestF` of the pair `(Z.TotalSpace, Z.zeroComplement)` to the pieces over an open
cover `U ∪ V = B` have range exactly the pairs agreeing on the overlap.  This is the step that
turns compatible local Thom data into a global candidate class.
-/

open Work.TangentClasses

namespace Work.Thom

open Bundle CategoryTheory AlgebraicTopology Limits

open scoped Simplicial

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **The glueing of local classes over the two pieces of a cover.**  A pair of relative classes of
the Thom pair over `U` and over `V` whose restrictions to the overlap agree is the pair of
restrictions of a *global* class of the Thom pair. -/
theorem exists_glue (Z : RealBundle B F ι) (n : ℕ) {U V : Set B} (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ)
    (w : Work.Cohomology.pdCohBiprod (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n)
    (h : (Work.Cohomology.honestG (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n).hom w = 0) :
    ∃ τ : OpenThom Z n, (Work.Cohomology.honestF (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n).hom τ = w := by
  have hcov' : Z.proj ⁻¹' U ∪ Z.proj ⁻¹' V = Set.univ := by
    rw [← Set.preimage_union, hcov, Set.preimage_univ]
  have hex := Work.Cohomology.honest_exact₂ (TopCat.of Z.TotalSpace) (zeroComplement Z)
    (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj)
    (hV.preimage Z.continuous_proj) hcov' n
  have hker : w ∈ LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.honestG (TopCat.of Z.TotalSpace)
      (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n)) := h
  have hrange : LinearMap.range (ModuleCat.Hom.hom (Work.Cohomology.honestF
        (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n))
      = LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.honestG (TopCat.of Z.TotalSpace)
        (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n)) :=
    ShortComplex.Exact.moduleCat_range_eq_ker hex
  rw [← hrange] at hker
  exact hker

end

end Work.Thom
