import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.localCohomology
import Submission.Work.Cohomology.relComplex_vanishing_of_homology_free
import Submission.Work.ThomBordism.relH_localisation_injective_normalTotal
import Submission.Work.Tubular.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.ThomBordism

/-- **Vanishing of the local cohomology of the normal bundle one degree above the top.**

For an embedded closed oriented smooth `8`-manifold `V ⊆ ℝ^{8+k}` (`k ≥ 1`), a point `x : V` and
the normal bundle model `ν = NormalTotal E`, the relative cohomology
`H^{8+k+1}(ν, ν ∖ {0_x}; ℤ)` vanishes.

The pair `(ν, ν ∖ {0_x})` is locally `(ℝ^{8+k}, ℝ^{8+k} ∖ 0)`: the normal total space carries a
`ChartedSpace` structure modelled on `ℝ^{8+k}` (transported along
`Work.Tubular.eucNormalHomeomorph` from `Work.ThomBordism.chartedSpaceTotalSpace`), and then
`Work.Cohomology.localHomology_charted` computes the *homology* of the pair: it is `ℤ` in degree
`8+k` (hence free) and vanishes in every other degree.  The universal coefficient theorem in the one
degree where both of its terms vanish, `Work.Cohomology.relComplex_vanishing_of_homology_free`,
converts this into the vanishing of the cohomology one degree up. -/
theorem normalTotal_locCoh_succ_subsingleton {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Subsingleton (Work.Thom.RelCoh ℤ (8 + k + 1) (TopCat.of (Work.Tubular.NormalTotal E))
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})) := by
  classical
  -- the charted-space structure of the normal total space, modelled on `ℝ^{8+k}`
  obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion E.e
    (E.smooth.of_le (by simp)) E.injective_mfderiv
  obtain ⟨hChb⟩ := Work.ThomBordism.chartedSpaceTotalSpace hk (Work.Tubular.normalBundle E ND)
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + k)))
      (Work.Tubular.normalBundle E ND).TotalSpace := hChb
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + k))) (Work.Tubular.NormalTotal E) :=
    Homeomorph.chartedSpace (Work.Tubular.eucNormalHomeomorph E ND)
  -- the local homology of the pair `(ν, ν ∖ {0_x})` is `ℤ` in degree `8 + k` ...
  have h0 : Module.Free ℤ
      ↥((Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})).homology
        (8 + k)) := by
    obtain ⟨e⟩ := (Work.Cohomology.localHomology_charted (8 + k) (by omega)
      (Work.Tubular.NormalTotal E) (Work.Tubular.zeroSectionNormal E x) (8 + k)).1 rfl
    exact Module.Free.of_equiv' (inferInstance : Module.Free ℤ ℤ) e.toLinearEquiv.symm
  -- ... and vanishes one degree higher
  have h1 : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})).homology
        (8 + k + 1)) :=
    (Work.Cohomology.localHomology_charted (8 + k) (by omega) (Work.Tubular.NormalTotal E)
      (Work.Tubular.zeroSectionNormal E x) (8 + k + 1)).2 (by omega)
  -- universal coefficients: `H^{n+1} = 0` when `H_{n+1} = 0` and `H_n` is free
  exact Work.Cohomology.relComplex_vanishing_of_homology_free
    (X := TopCat.of (Work.Tubular.NormalTotal E))
    (A := {p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
    (8 + k) h1 h0

end Work.ThomBordism
