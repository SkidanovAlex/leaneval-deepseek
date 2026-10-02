import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Thom.realSumStable
import Submission.Work.Gen.EulerToolkit
import Submission.Work.ThomBordism.Grassmann.InclDefs
import Submission.Work.ThomBordism.Grassmann.InclGauge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
# The stabilisation inclusion pulls the tautological bundle back to itself

Appending a last zero coordinate gives the continuous map `ogInclCM k m : OG k m → OG k (m+1)` of
oriented Grassmannians (`Submission/Work/ThomBordism/Grassmann/InclDefs.lean`), and the chart
bookkeeping of that module (`chartDown`, `chartPerm`, `frameMatrix_inclFrame`) shows that the
pulled-back tautological bundle `ogInclCM k m ^* γ_{k,m+1}` is isomorphic to `γ_{k,m}`.

The isomorphism is the gauge `Work.ThomBordism.Grassmann.inclPhi` of
`Submission/Work/ThomBordism/Grassmann/InclGauge.lean`: on the chart `(i,t)` it is the geometric
identification of the two trivialisations, `coordChangeO (cd i) t b ∘ T i b` with
`T i b = D_{i^ρ} Q_i^{-1} D_i`, whose intertwining property `inclT_comp_coordChangeO` — the frame
computation `frameMatrix_inclFrame` transported to the transition functions — is what makes all six
hypotheses of `Work.Thom.nonempty_bundleIso_of_gauge` hold.
-/

namespace Work.ThomBordism.Grassmann

theorem inclusionBundleIso (k m : ℕ) :
    ∃ φ : C(Work.ThomBordism.Grassmann.OG k m, Work.ThomBordism.Grassmann.OG k (m+1)),
      Nonempty (Work.Thom.BundleIso
        (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k (m+1)) φ)
        (Work.ThomBordism.Grassmann.tautologicalBundle k m)) := by
  refine ⟨ogInclCM k m, ?_⟩
  refine Work.Thom.nonempty_bundleIso_of_gauge
    (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m))
    (tautologicalBundle k m) (inclPhi k m) (inclPhiInv k m) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i t
    exact continuousOn_inclPhi i t
  · intro i t
    exact continuousOn_inclPhiInv i t
  · intro i t t' b hb1 hb2 hb3
    exact inclPhi_htgt i t t' b hb1 hb2 hb3
  · intro i t i' b hb1 hb2 hb3
    exact inclPhi_hsrc i i' t b hb1 hb2 hb3
  · intro i t t' b hb1 hb2 hb3
    exact inclPhi_htgtinv i t t' b hb1 hb2 hb3
  · intro i t i' b hb1 hb2 hb3
    exact inclPhi_hsrcinv i i' t b hb1 hb2 hb3
  · intro i i' b x hb
    exact inclPhi_hleft i i' b hb x
  · intro i i' b y hb
    exact inclPhi_hright i i' b hb y

end Work.ThomBordism.Grassmann
