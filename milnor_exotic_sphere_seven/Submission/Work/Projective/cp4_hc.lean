import Mathlib
import Submission.Work.Projective.CP4Concrete
import Submission.Work.Projective.cp2_hc
import Submission.Work.Projective.cp_compl_homeo
import Submission.Work.Projective.cpnV_homotopyEquiv
import Submission.Work.Projective.cpn_homology
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.PairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fundamental class of `ℂP⁴` has local degree `±1`

`Work.Projective.cp4_hc`: the image of `cp4C` (the chosen generator of `H₈(ℂP⁴;ℤ)`) in each local
relative group `H₈(ℂP⁴, ℂP⁴∖{x})` is a generator — the fundamental-class condition `hc` of the
workspace's Poincaré–Lefschetz duality project (`Work.Cohomology.pd_good_univ`).

The proof is the degree-shifted copy of `Work.Projective.cp2_hc`
(`Submission/Work/Projective/cp2_hc.lean`): the complement of a point in `ℂP⁴` is homotopy
equivalent to `ℂP³` (`cp_compl_homeo`, `cpnV_homotopyEquiv`), whose `H₇` vanishes
(`cpn_homology`); hence the connecting map `H₈(ℂP⁴, ℂP⁴∖{x}) → H₇(ℂP⁴∖{x})` of the pair is zero,
so `H₈(ℂP⁴) → H₈(ℂP⁴, ℂP⁴∖{x})` is surjective, and the image of the generator `cp4C`
(`cp4C_span`) under a surjection generates.
-/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology
open scoped Manifold ContDiff Topology

noncomputable section

/-- `H₇(ℂP³;ℤ) = 0` (odd degree, `cpn_homology`). -/
theorem isZero_homology_seven_cpThree :
    IsZero ((singularChains ℤ (CPSpace 3)).homology 7) := by
  have e : (chainC ℤ (TopCat.toSSet.obj (CPSpace 3))).homology 7 ≅
      ModuleCat.of ℤ (Fin (if Even 7 ∧ 7 ≤ 2 * 3 then 1 else 0) → ℤ) :=
    Classical.choice (cpn_homology 3 7)
  haveI hA : IsZero (ModuleCat.of ℤ (Fin (if Even 7 ∧ 7 ≤ 2 * 3 then 1 else 0) → ℤ)) := by
    rw [if_neg (by rintro ⟨k, hk⟩; omega : ¬(Even 7 ∧ 7 ≤ 2 * 3))]
    exact ModuleCat.isZero_of_subsingleton _
  exact IsZero.of_iso hA e

/-- **The seventh homology of the complement of a point in `ℂP⁴` vanishes**: the complement is
homeomorphic to `cpV 4`, which is homotopy equivalent to `ℂP³`. -/
theorem isZero_homology_seven_compl_point (x : CPSpace 4) :
    IsZero ((singularChains ℤ (TopCat.of ↥({y : CPSpace 4 | y ≠ x}))).homology 7) := by
  have hh1 : ↥({y : CPSpace 4 | y ≠ x}) ≃ₜ ↥(cpV 4 : Set (CPSpace 4)) :=
    (cp_compl_homeo 4 x).some.symm.trans (Homeomorph.setCongr (cpV_eq_compl_cpOrigin 4)).symm
  obtain ⟨e1⟩ := homologyIso_of_homotopyEquiv hh1.toHomotopyEquiv 7
  obtain ⟨e2⟩ := homologyIso_of_homotopyEquiv (cpnV_homotopyEquiv 3).some 7
  exact IsZero.of_iso (IsZero.of_iso isZero_homology_seven_cpThree e2) e1

/-- The fundamental class of `ℂP⁴`: the image of `cp4C` in each local relative group
`H₈(ℂP⁴, ℂP⁴∖{x})` is a generator (local degree `±1` at every point). -/
theorem cp4_hc (x : Work.Projective.CPSpace 4) :
    Submodule.span ℤ
      {(((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
            (Work.Projective.CPSpace 4)
            {y : Work.Projective.CPSpace 4 | y ≠ x}))) 8) Work.Projective.cp4C)} = ⊤ := by
  have hzero : IsZero ((singularChains ℤ
      (TopCat.of ↥({y : CPSpace 4 | y ≠ x}))).homology 7) :=
    isZero_homology_seven_compl_point x
  have hδ : hPairδ (CPSpace 4) {y : CPSpace 4 | y ≠ x} 7 = 0 :=
    IsZero.eq_zero_of_tgt hzero _
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap
        (cokernel.π (inclChains (CPSpace 4) {y : CPSpace 4 | y ≠ x})) 8).hom := by
    have hex := hPair_exact₃ (CPSpace 4) {y : CPSpace 4 | y ≠ x} 7
    have hker : LinearMap.ker (hPairδ (CPSpace 4) {y : CPSpace 4 | y ≠ x} 7).hom = ⊤ := by
      rw [hδ, ModuleCat.hom_zero, LinearMap.ker_zero]
    have hrange : LinearMap.range (HomologicalComplex.homologyMap
        (cokernel.π (inclChains (CPSpace 4) {y : CPSpace 4 | y ≠ x})) (7 + 1)).hom = ⊤ := by
      rw [ShortComplex.Exact.moduleCat_range_eq_ker hex, hker]
    rw [show (8 : ℕ) = 7 + 1 from rfl]
    exact LinearMap.range_eq_top.mp hrange
  exact span_singleton_map_eq_top'
    (HomologicalComplex.homologyMap
      (cokernel.π (inclChains (CPSpace 4) {y : CPSpace 4 | y ≠ x})) 8).hom
    hsurj cp4C cp4C_span

end

end Work.Projective
