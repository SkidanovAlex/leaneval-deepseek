import Mathlib
import Submission.Work.ORVonNeumann.Rep.CosetData
import Submission.Work.ORVonNeumann.Rep.exists_leftCosetTransversal
import Submission.Work.ORVonNeumann.Rep.exists_cosetLiftIso

namespace Work.ORVonNeumann.Rep

theorem exists_cosetData {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (H : Subgroup G) : Nonempty (Work.ORVonNeumann.Rep.CosetData G H) := by
  classical
  obtain ⟨Q, hQ⟩ := Work.ORVonNeumann.Rep.exists_leftCosetTransversal H
  choose e he using fun q : Q => Work.ORVonNeumann.Rep.exists_cosetLiftIso H (q : G)
  exact ⟨{ Q := Q, exists_unique := hQ, e := e, e_delta := he }⟩

end Work.ORVonNeumann.Rep
