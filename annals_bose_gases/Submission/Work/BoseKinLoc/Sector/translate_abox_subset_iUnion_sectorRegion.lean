import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseKinLoc.Defs
import Submission.Work.PerSector.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

theorem translate_abox_subset_iUnion_sectorRegion {N : ℕ} {ℓ L : ℝ} {c : EuclideanSpace ℝ (Fin 3)}
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : ∀ z ∈ Submission.BoseGases.acube L, c + z ∈ A) :
    (fun x : Submission.BoseGases.X N => fun i : Fin N => c + x i) '' Submission.BoseGases.abox N L
      ⊆ ⋃ S : Finset (Fin N),
          (Work.PerSector.slotSet (Submission.BoseGases.acube ℓ) S
            ∩ {x : Submission.BoseGases.X N | ∀ j : Work.PerSector.SlotOut N S,
                x j.1 ∈ A}) := by
  rintro y ⟨x, hx, rfl⟩
  classical
  have hxL : ∀ i : Fin N, x i ∈ Submission.BoseGases.acube L :=
    (Submission.BoseGases.mem_abox_iff N L x).mp hx
  refine Set.mem_iUnion.mpr
    ⟨Finset.univ.filter (fun i : Fin N => c + x i ∈ Submission.BoseGases.acube ℓ), ?_, ?_⟩
  · intro i
    simp [Finset.mem_filter]
  · intro j
    exact hA (x j.1) (hxL j.1)

end Work.BoseKinLoc.Sector
