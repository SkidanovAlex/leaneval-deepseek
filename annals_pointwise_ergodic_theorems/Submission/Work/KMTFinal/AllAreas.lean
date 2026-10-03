import Submission.Work.KMTContract.Composition
import Submission.Work.Peluse.RouteClosed
import Submission.Work.KMTAreas.area_A5
import Submission.Work.KMTAreas.area_A6
import Submission.Work.KMTAreas.area_A7
import Submission.Work.KMTAreas.area_A8

/-! LEAD (curric-46, 2026-10-03): all eight KMT areas, assembled. -/

namespace Work.KMTFinal

theorem allAreas : Work.KMTContract.AllAreas :=
  ⟨Work.KMTAreas.area_A1, Work.Peluse.kMTContract_AreaA2, Work.KMTAreas.area_A3,
    Work.KMTAreas.area_A4, Work.KMTAreas.area_A5, Work.KMTAreas.area_A6, Work.KMTAreas.area_A7,
    Work.KMTAreas.area_A8⟩

end Work.KMTFinal
