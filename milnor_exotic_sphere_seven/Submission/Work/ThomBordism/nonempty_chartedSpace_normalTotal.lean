import Mathlib
import Submission.Work.Tubular.Defs
import Submission.Work.Tubular.normalTotalIso
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.ThomBordism.chartedSpaceTotalSpace

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# The normal total space is a charted space modelled on `ℝ^{8+k}`

`Work.Tubular.NormalTotal E` is the concrete model of the normal bundle of an embedding
`E : V ↪ ℝ^{8+k}` of a closed oriented smooth `8`-manifold `V`.  It is homeomorphic to the total
space of the gluing-data bundle `Work.Tubular.normalBundle E ND` (`Work.Tubular.eucNormalHomeomorph`,
`Submission/Work/Tubular/normalTotalIso.lean`), and the total space of a rank-`k` real bundle over a
base charted on `ℝ⁸` is a charted space modelled on `ℝ^{8+k}`
(`Work.ThomBordism.chartedSpaceTotalSpace`).

## Route

* `obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion E.e
    (E.smooth.of_le (by simp)) E.injective_mfderiv`
  (the same extraction as in `Work.Tubular.exists_euclidean_normalBundle`);
* `nu := Work.Tubular.normalBundle E ND : RealBundle V.pt (Euc k) (CoverIdx V k)`, and
  `Φ := Work.Tubular.eucNormalHomeomorph E ND : nu.TotalSpace ≃ₜ NormalTotal E`;
* `obtain ⟨c⟩ := Work.ThomBordism.chartedSpaceTotalSpace (k := k) hk nu`;
* transport `c` along the homeomorphism `Φ` (`Homeomorph.chartedSpace`).

This instance is needed by the local (co)homology computations of
`Submission/Work/ThomBordism/localisation_injective_zeroSection.lean`
(`Work.Cohomology.localHomology_charted`, `Work.Cohomology.localCohomology`) and by the homology
localisation statement `Work.ThomBordism.relH_normalNonzero_localisation_injective`.
-/

namespace Work.ThomBordism

/-- **The normal total space is a charted space** modelled on `ℝ^{8+k}`: it is homeomorphic to the
total space of the gluing-data normal bundle `Work.Tubular.normalBundle E ND`, which is charted by
`Work.ThomBordism.chartedSpaceTotalSpace`. -/
theorem nonempty_chartedSpace_normalTotal {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin (8 + k))) (Work.Tubular.NormalTotal E)) := by
  sorry

end Work.ThomBordism
