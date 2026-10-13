/-
  WilE9 / Sharp — the stratum coordinates of a point of the extended set.

  `exStrat z` reads a point of the extended ambient `ℝ^{Next n m}` in the stratum's own
  coordinates `(y, τ, aux)` (`ExtSystem.lean`).  The three facts here are the ones the
  component-restricted construction needs:

  * `exStrat_mem_of_mem_exSemiPf`: the equations of the extended system contain the stratum's
    basics raised (`exRaise`), so the stratum coordinates of an extended point lie in `E.X.set`;
  * `continuous_exStrat`: `exStrat` is a coordinate projection;
  * `exStrat_image_componentIn`: hence the stratum coordinates of a whole component of the
    extended set lie in the component of the stratum point they came from.  This is what makes
    `exComp` (the component-restricted extended set) sound: every point of it has stratum
    coordinates in the prescribed component, where the per-stratum hypothesis
    "the component projects into `Z`" is available.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Sharp.eaEval_exRaise
import Submission.Work.WilE9.Sharp.ExDefs
import Submission.Work.WilE9.Sharp.ExSndAux

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open WilkiesDesign WilkiesDesign.E Filter
namespace Work.WilE9.Sharp

/-- The stratum coordinates of a point of the extended set lie in the stratum's set. -/
theorem exStrat_mem_of_mem_exSemiPf {n m : ℕ} (E : EffStratum n m) (L : List (Fin n))
    {z : Fin (Next n m) → ℝ} (hz : z ∈ (exSemiPf n m E L).set) : exStrat z ∈ E.X.set := by
  obtain ⟨hzcube, B, hBmem, hB⟩ := hz
  obtain ⟨B0, hB0mem, hB0eq⟩ := List.mem_map.mp hBmem
  rw [← hB0eq] at hB
  obtain ⟨hBeqs, hBpos⟩ := hB
  refine ⟨fun i => hzcube (sIdxE n m i), B0, hB0mem, ?_⟩
  refine ⟨?_, ?_⟩
  · intro g hg
    have h1 : eaEval (exChain E.X.c) (exRaise g) z = 0 :=
      hBeqs _ (show exRaise g ∈ (exBasic E.X.c E.h L B0).eqs from
        List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨g, hg, rfl⟩)))
    rwa [eaEval_exRaise] at h1
  · intro g hg
    have h1 : 0 < eaEval (exChain E.X.c) (exRaise g) z :=
      hBpos _ (mem_exPosList_pos B0 hg)
    rwa [eaEval_exRaise] at h1

/-- `exStrat` is a coordinate projection, hence continuous. -/
theorem continuous_exStrat {n m : ℕ} :
    Continuous (fun z : Fin (Next n m) → ℝ => exStrat z) :=
  continuous_pi fun i => continuous_apply (sIdxE n m i)

/-- The stratum coordinates of the points of a component of the extended set stay in the component
of the stratum coordinates of any of its points. -/
theorem exStrat_image_componentIn {n m : ℕ} (E : EffStratum n m) (L : List (Fin n))
    {z : Fin (Next n m) → ℝ} (hz : z ∈ (exSemiPf n m E L).set) :
    exStrat '' connectedComponentIn (exSemiPf n m E L).set z ⊆
      connectedComponentIn E.X.set (exStrat z) := by
  have hpc : IsPreconnected (exStrat '' connectedComponentIn (exSemiPf n m E L).set z) :=
    (isPreconnected_connectedComponentIn (x := z) (F := (exSemiPf n m E L).set)).image
      exStrat continuous_exStrat.continuousOn
  refine hpc.subset_connectedComponentIn ⟨z, mem_connectedComponentIn hz, rfl⟩ ?_
  rintro w ⟨u, hu, rfl⟩
  exact exStrat_mem_of_mem_exSemiPf E L (connectedComponentIn_subset _ _ hu)

end Work.WilE9.Sharp
