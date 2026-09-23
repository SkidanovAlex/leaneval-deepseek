import Mathlib
import Submission.Work.OddBound.PolygonModel
import Submission.Work.OddBound.polygon.polygon_energy_aux
import Submission.Work.OddBound.polygonValue.balancing.distLeCurveLengthOfContMDiffOn
import Submission.Work.OddBound.longHomotopy.curveLength_toolkit
import Submission.Work.OddBound.IndexBound
import Submission.Work.OddBound.LiftKit
import Submission.EnergyGeoGlobal
import Submission.EnergyGeoSmooth
import Submission.EnergyRaySmooth
import Submission.DerivShorten
import Submission.IndexScale

/-!
# Re-export module for the index-transfer lemmas

Purely an aggregation of imports: it collects (for the delegated lemmas of
`Work.OddBound.indexTransfer.hasNegDefPlane_of_negativeDirichletIndex`) the modules defining
`gonEnergy`, the polygon energy bounds, the distance/length comparison for `ContMDiffOn` curves,
the `C^∞` smoothness of the geodesic variation, the unscaled second variation of the energy,
and the calculus modules used by the chain rule.
-/
