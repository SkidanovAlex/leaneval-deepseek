import Submission.Rad.Cube
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RadType
open RademacherEnfloType

set_option synthInstance.maxHeartbeats 0 in
instance : IsProbabilityMeasure rademacherDistribution := by
  unfold rademacherDistribution
  infer_instance

set_option synthInstance.maxHeartbeats 0 in
instance (ι : Type*) : IsProbabilityMeasure (rademacherProductDistribution ι) := by
  unfold rademacherProductDistribution
  infer_instance

end RadType
