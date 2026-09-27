import Mathlib
import Submission.Work.Whitney.PathTools.isPathConnected_compl_finite
import Submission.Work.Whitney.PathTools.LocalRoomAux
import Submission.Work.Whitney.PathTools.arc_nonseparates_surface_clean

/-!
# An arc does not separate an open set of a surface

Main target: `Work.Whitney.PathTools.arc_nonseparates_open_surface`: for an open preconnected `C`
in a topological 2-manifold and a continuous `γ` injective on `[0,1]` whose image lies in `C`,
the complement `C \ γ '' [0,1]` is path connected.

## Route

1. (`arc_nonseparates_open_surface_of_room`, proved below)  If there is a **room**, i.e. an open
   `V` with `γ '' [0,1] ⊆ V ⊆ C` and `IsPreconnected (V \ γ '' [0,1])`, and `C \ γ '' [0,1]` is
   nonempty, then `C \ γ '' [0,1]` is preconnected by
   `Work.Whitney.PathTools.isPreconnected_sdiff_of_isClosed_of_room`; it is then path connected
   because it is open and a charted space over `ℝ²` is locally path connected.
2. The room is `Work.Whitney.PathTools.room_of_arc_surface_pt`.
3. Nonemptiness of the complement is `Work.Whitney.PathTools.nonempty_sdiff_arc_surface`.

## Warning

The naive input "for small `ε`, `γ ⁻¹' (ball (γ s) ε) ∩ [0,1]` is preconnected" is **false**: a
continuous injection may spiral into `γ s` with oscillating radius, so a small ball can meet the
arc in infinitely many chords (a "wild" arc).  Any construction of the room must avoid
decomposing the arc into pieces of a chart ball; the proof of `room_of_arc_surface_pt` handles the
arc by removing only *forward* pieces `γ '' Icc τ b`, where `b` is the exit parameter of a ball
around `γ τ`, which are "pacmen" (an arc from an interior point to a boundary point).
-/

namespace Work.Whitney.PathTools

open Set Metric Topology

/-- **Assembly.**  A room for the arc, together with nonemptiness of the complement, implies the
target theorem. -/
theorem arc_nonseparates_open_surface_of_room
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {C : Set M} (hC : IsOpen C) (hCc : IsPreconnected C)
    {γ : ℝ → M} (hγ : Continuous γ) (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    (hA : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ C)
    (hRoom : ∃ V : Set M, IsOpen V ∧ γ '' Set.Icc (0:ℝ) 1 ⊆ V ∧ V ⊆ C ∧
      IsPreconnected (V \ γ '' Set.Icc (0:ℝ) 1))
    (hNe : (C \ γ '' Set.Icc (0:ℝ) 1).Nonempty) :
    IsPathConnected (C \ γ '' Set.Icc (0:ℝ) 1) := by
  haveI : LocallyPathConnectedSpace M := locallyPathConnectedSpace_chartedSpace (n := 2)
  obtain ⟨V, hVo, hAV, hVC, hVp⟩ := hRoom
  have hAclosed : IsClosed (γ '' Set.Icc (0:ℝ) 1) := (isCompact_Icc.image hγ).isClosed
  have hpc : IsPreconnected (C \ γ '' Set.Icc (0:ℝ) 1) :=
    isPreconnected_sdiff_of_isClosed_of_room hCc hC hAclosed hVo hAV hVC hVp
  exact (hC.sdiff hAclosed).isConnected_iff_isPathConnected.mp ⟨hNe, hpc⟩

/-- **An arc does not separate an open preconnected set of a surface.** -/
theorem arc_nonseparates_open_surface {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {C : Set M} (hC : IsOpen C) (hCc : IsPreconnected C)
    {γ : ℝ → M} (hγ : Continuous γ) (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    (hA : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ C) :
    IsPathConnected (C \ γ '' Set.Icc (0:ℝ) 1) := by
  haveI : LocallyPathConnectedSpace M := locallyPathConnectedSpace_chartedSpace (n := 2)
  have hCne : C.Nonempty := ⟨γ 0, hA 0 ⟨le_rfl, zero_le_one⟩⟩
  have hCpc : IsPathConnected C := hC.isConnected_iff_isPathConnected.mp ⟨hCne, hCc⟩
  exact isPathConnected_sdiff_arc_surface_clean hC hCpc hγ hinj hA

end Work.Whitney.PathTools
