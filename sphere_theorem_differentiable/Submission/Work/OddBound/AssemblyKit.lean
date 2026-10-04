import Submission.RauchK
import Submission.Geodesic
import Submission.GeodesicSpeed
import Submission.Length
import Submission.Distance
import Submission.InjRadius
import Submission.UniformInj
import Submission.KlingenbergLemma
import Submission.PinchUniform
import Submission.MetricScale
import Submission.KlingenbergXu
import Submission.Work.OddBound.PolygonModel
import Submission.Work.OddBound.PolygonChart
import Submission.Work.OddBound.PiExtChart
import Submission.Work.OddBound.isManifold_piChartedSpaceExt
import Submission.Work.OddBound.exists_piExtChart_eq_of_mem_atlas
import Submission.Work.OddBound.chartAlgebra.contDiffAt_gonEnergy_piExtChart_gen
import Submission.Work.OddBound.gonCritical_of_piExtChart_critical
import Submission.Work.OddBound.polygon.isCritical_gonEnergy_geodesic
import Submission.Work.OddBound.polygonValueBound
import Submission.Work.OddBound.exists_gonEnergy_le_of_balanced_nullhomotopy
import Submission.Work.OddBound.exists_balanced_based_nullhomotopy
import Submission.Work.OddBound.exists_global_geodesic_extension
import Submission.Work.OddBound.indexTransfer.hasNegDefPlane_of_negativeDirichletIndex
import Submission.Work.OddBound.mountainPass3.exists_critical_index_le_one_local
import Submission.Work.OddBound.Minimax
import Submission.Work.OddBound.assembly.Defs
import Submission.Work.OddBound.polygonValue.balancing.continuousRiemannianDist
import Submission.Work.PeriodicLength.curveLength_eq_mul_of_periodic_of_affine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Re-export kit for the `MinimaxExtraction` assembly

Everything the assembly of `Work.OddBound.MinimaxExtraction` needs, in one module, so that a
`depends_on` list can name it (`Submission/Work/` paths only; the main-tree modules imported here
cannot be named directly).
-/
