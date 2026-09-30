import Mathlib
import Submission.Work.Serre.SkelPi.Basic
import Submission.Work.Serre.E3aSkDefs
import Submission.Work.Serre.E3aSkDefs

/-!
# The cell classes of the `1`-skeleton, in the homotopy-group formulation

`Work.Serre.SkelPi.cellClassHom` is the class in `π₁` of the loop carried by a `1`-cell of the
skeleton, expressed through the cube model `C(Fin 1 → I, X)` of the homotopy group, and
`cellClassHom_pi1MulEquivFundamentalGroup` identifies it with the interval version
`Work.Serre.SkelPi.cellLoopClass`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre.SkelPi

noncomputable section

/-- The boundary condition of the cube cell loop: it is constant at the base point on the boundary
of the cube. -/
theorem cellCube_boundary (X : Type) [TopologicalSpace X] (pt : X) (w : Idx X pt)
    (u : Fin 1 → unitInterval) (hu : u ∈ Cube.boundary (Fin 1)) :
    ((cellMap X pt w).comp Work.Serre.E3aSk.SkelMap.cubeToD1) u = base X pt := by
  rw [ContinuousMap.comp_apply]
  obtain ⟨i, hi⟩ := hu
  have h0 : u i = 0 ∨ u i = 1 := hi
  have hi0 : i = 0 := Subsingleton.elim i 0
  subst hi0
  rcases h0 with h0 | h0
  · have hpt : Work.Serre.E3aSk.SkelMap.cubeToD1 u = endL := by
      refine Subtype.ext ?_
      rw [endL_coe]
      show 2 * ((u 0 : unitInterval) : ℝ) - 1 = -1
      rw [h0]
      norm_num
    rw [hpt]
    exact cellMap_endL X pt w
  · have hpt : Work.Serre.E3aSk.SkelMap.cubeToD1 u = endR := by
      refine Subtype.ext ?_
      rw [endR_coe]
      show 2 * ((u 0 : unitInterval) : ℝ) - 1 = 1
      rw [h0]
      norm_num
    rw [hpt]
    exact cellMap_endR X pt w

/-- **The class of the loop carried by the `w`-th cell**, in the `HomotopyGroup` formulation. -/
def cellClassHom (X : Type) [TopologicalSpace X] (pt : X) (w : Idx X pt) :
    HomotopyGroup (Fin 1) (Skel X pt) (base X pt) :=
  Quotient.mk _ ⟨(cellMap X pt w).comp Work.Serre.E3aSk.SkelMap.cubeToD1,
    cellCube_boundary X pt w⟩

/-- **The two descriptions of the cell class agree**: the homotopy-group version maps to the
fundamental-group version under the standard identification. -/
theorem cellClassHom_pi1MulEquivFundamentalGroup (X : Type) [TopologicalSpace X] (pt : X)
    (w : Idx X pt) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (cellClassHom X pt w) = cellLoopClass X pt w := by
  rw [cellClassHom, cellLoopClass]
  show Path.Homotopic.Quotient.mk
      (genLoopEquivOfUnique (Fin 1)
        (⟨(cellMap X pt w).comp Work.Serre.E3aSk.SkelMap.cubeToD1,
          cellCube_boundary X pt w⟩ :
          Ω^ (Fin 1) (Skel X pt) (base X pt)))
    = Path.Homotopic.Quotient.mk (cellLoopPath X pt w)
  rw [Path.Homotopic.Quotient.eq]
  have hfun : ((genLoopEquivOfUnique (Fin 1)
        (⟨(cellMap X pt w).comp Work.Serre.E3aSk.SkelMap.cubeToD1,
          cellCube_boundary X pt w⟩ :
          Ω^ (Fin 1) (Skel X pt) (base X pt))) : unitInterval → Skel X pt)
      = (cellLoopPath X pt w : unitInterval → Skel X pt) := by
    funext t
    show (cellMap X pt w) (Work.Serre.E3aSk.SkelMap.cubeToD1 (fun _ => t))
      = ((cellLoopPath X pt w : unitInterval → Skel X pt) t)
    rw [cellLoopPath_apply]
    refine congrArg (cellMap X pt w) ?_
    refine Subtype.ext ?_
    rw [seg_apply_coe, endL_coe, endR_coe]
    show 2 * ((t : unitInterval) : ℝ) - 1 = (1 - (t : ℝ)) * (-1) + (t : ℝ) * 1
    ring
  rw [Path.ext hfun]

end

end Work.Serre.SkelPi
