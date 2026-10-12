import ChallengeDeps
import Submission.Work.BoseBox.paramsAtSmall
import Submission.Work.BoseBox.potAmbIntegrable
import Submission.Work.BoseBox.sideAt_large
import Submission.Work.BoseBox.tKinAmbIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.cWordIntegrable` — the `C` node's integrability side condition, assembled

`Work.BoseBox.CWordIntegrable v h` (`CNodeDefs.lean`) is the *technical* input of the `C`
node: eventually in `μ`, at FS's parameters, the two localised words `tKinAmb` and
`potAmb` are integrable as functions of the translation parameter `u` on the localisation
region `coverU (sideAt μ (a v)) L`.  It is what lets the `u`-averages of the node be added
(`∫_u (tKinAmb + potAmb) = ∫_u tKinAmb + ∫_u potAmb`) and what the inner
`IntegrableOn`-hypothesis of `CKinAmb` consumes.

Both halves are proved independently, at *general* parameters:

* `Work.BoseBox.tKinAmbIntegrable` — `IntegrableOn (fun u ↦ tKinAmb N L ℓ d s eT b u Ψ)
  (coverU ℓ L)` for `0 < L`, `0 < ℓ`, smooth `Ψ` supported in the corner box;
* `Work.BoseBox.potAmbIntegrable` — `IntegrableOn (fun u ↦ potAmb N L ℓ μ v h u Ψ)
  (coverU ℓ L)` in the potential regime `R ≤ ℓ r₀` (`potAmb_integral`'s hypotheses);

and this module puts them together along the eventual set
`{0 < μ} ∩ {R ≤ sideAt μ (a v) · r₀}` (`sideAt_large`), which is a neighbourhood of
`0⁺` because `ℓ = sideAt μ (a v) → ∞`. -/

noncomputable section

open MeasureTheory
open scoped Topology

namespace Work.BoseBox

set_option linter.unusedVariables false
set_option autoImplicit false

/-- `sideAt μ a = K_ℓ(μa)^{-1/2} > 0` for `μ, a > 0` (FS's box side is positive). -/
lemma sideAt_pos {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) : 0 < sideAt μ a :=
  boxSide_pos hμ ha (by
    rw [paramsAt]
    exact fsXp_pos (by positivity))

/-- **`CWordIntegrable` from the two integrability halves.**  On the eventual set
`{μ > 0} ∩ {R ≤ sideAt μ (a v)·r₀}` (a right-neighbourhood of `0` by `sideAt_large`),
each of the two conjuncts of `CWordIntegrable` is the corresponding half. -/
theorem cWordIntegrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hv_nonneg : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (hC : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₀ →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseBox.CWordIntegrable v h := by
  filter_upwards [self_mem_nhdsWithin,
    sideAt_large hav R r₀ hr₀] with μ hμpos hside
  intro N L hL1 Ψ hΨ hsupp
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hℓpos : 0 < sideAt μ (_root_.BoseGases.a v) := sideAt_pos hμpos hav
  refine ⟨?_, ?_⟩
  · exact tKinAmbIntegrable (L := L) (ℓ := sideAt μ (_root_.BoseGases.a v)) hLpos hℓpos hΨ hsupp
  · exact potAmbIntegrable hR hr₀ hv_supp hv_nonneg hvrad hv1 hC hℓpos hLpos hside Ψ hΨ hsupp

end Work.BoseBox
