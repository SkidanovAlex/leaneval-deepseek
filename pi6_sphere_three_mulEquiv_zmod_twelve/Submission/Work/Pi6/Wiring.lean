import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Serre.serrePostnikovTower
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option synthInstance.maxHeartbeats 400000

/-!
# pi6_sphere_three_mulEquiv_zmod_twelve from the areas (lead's glue; no sorry)

`Work.Pi6.pi6_of_areas` is the challenge statement from `BasepointMulEquiv`, `TowerPi`, `EFacts`,
`SqCyclic`, `HomologyAlg` (the other areas feed these through their hypotheses).
-/

set_option autoImplicit false

namespace Work.Pi6

theorem pi6_core_of_areas (hT : TowerPi) (hE : EFacts) (hS : SqCyclic) (hH : HomologyAlg) :
    Pi6Core := by
  obtain ⟨P3, _, g3, h3a, h3b, -⟩ :=
    Work.Serre.serrePostnikovTower_strong (12 - 3) 3 12 S3 rfl (by norm_num)
  have h3 : PostnikovData 3 12 g3 s3 := ⟨fun i hi y => h3a i hi y, h3b⟩
  obtain ⟨P4, _, g4, h4a, h4b, -⟩ :=
    Work.Serre.serrePostnikovTower_strong (12 - 4) 4 12 (Ecov g3) rfl (by norm_num)
  have h4 : PostnikovData 4 12 g4 (e0 g3) := ⟨fun i hi y => h4a i hi y, h4b⟩
  obtain ⟨P5, _, g5, h5a, h5b, -⟩ :=
    Work.Serre.serrePostnikovTower_strong (12 - 5) 5 12 (Ycov g3 g4) rfl (by norm_num)
  have h5 : PostnikovData 5 12 g5 (y0 g3 g4) := ⟨fun i hi y => h5a i hi y, h5b⟩
  obtain ⟨hpi, -, -, -, hP4, hP5⟩ := hT P3 g3 h3 P4 g4 h4 P5 g5 h5
  obtain ⟨hE4, -, -, -, -⟩ := hE P3 g3 h3
  have hK4 := hP4 hE4
  obtain ⟨hY5, hC⟩ := hH P3 g3 h3 P4 g4 h4 hK4
  have hK5 := hP5 hY5
  have hf := hS P3 g3 h3 P4 g4 h4 P5 g5 h5 hK4 hK5
  obtain ⟨hcyc, hcard⟩ := hC P5 g5 h5 hK5 hf
  obtain ⟨φ⟩ := hpi
  have hc : Nat.card (HR ℤ (Zcov g3 g4 g5) 6) = Nat.card (ZMod 12) := by
    rw [hcard, Nat.card_zmod]
  exact ⟨φ.trans (AddEquiv.toMultiplicative (addEquivOfAddCyclicCardEq hc))⟩

theorem pi6_of_areas (hB : BasepointMulEquiv) (hT : TowerPi) (hE : EFacts) (hS : SqCyclic)
    (hH : HomologyAlg) (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    Nonempty (HomotopyGroup.Pi 6 (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) x ≃*
      Multiplicative (ZMod 12)) := by
  obtain ⟨e1⟩ := hB x
  obtain ⟨e2⟩ := pi6_core_of_areas hT hE hS hH
  exact ⟨e1.trans e2⟩

end Work.Pi6
