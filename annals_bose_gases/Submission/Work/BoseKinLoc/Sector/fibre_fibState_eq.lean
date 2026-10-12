import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseKinLoc.Sector.fibre_defs_v3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open Classical

namespace Work.BoseKinLoc.Sector

theorem fibre_fibState_eq {N : ℕ} (S : Finset (Fin N)) (i : Work.PerSector.SlotIn N S)
    (Ψ : Submission.BoseGases.X N → ℝ)
    (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))
    (z : Work.PerSector.SlotIn N S → EuclideanSpace ℝ (Fin 3)) :
    Work.BoseKinLoc.fibre S.card ((Work.BoseKinLoc.Sector.slotIso S) i)
        (Work.BoseKinLoc.Sector.fibState S Ψ y)
        (fun m : Fin S.card => z ((Work.BoseKinLoc.Sector.slotIso S).symm m))
      = Work.BoseKinLoc.fibre N i.1 Ψ (Work.PerSector.slotComb S z y) := by
  funext w
  show Work.BoseKinLoc.Sector.fibState S Ψ y
      (Function.update (fun m : Fin S.card => z ((Work.BoseKinLoc.Sector.slotIso S).symm m))
        ((Work.BoseKinLoc.Sector.slotIso S) i) w)
    = Ψ (Function.update (Work.PerSector.slotComb S z y) i.1 w)
  rw [Work.BoseKinLoc.Sector.fibState_apply]
  congr 1
  have hA : (fun j : Work.PerSector.SlotIn N S =>
      (Function.update (fun m : Fin S.card => z ((Work.BoseKinLoc.Sector.slotIso S).symm m))
        ((Work.BoseKinLoc.Sector.slotIso S) i) w) ((Work.BoseKinLoc.Sector.slotIso S) j))
      = Function.update z i w := by
    funext j
    rw [Function.update_apply, Function.update_apply]
    by_cases hj : (Work.BoseKinLoc.Sector.slotIso S) j = (Work.BoseKinLoc.Sector.slotIso S) i
    · rw [if_pos hj, if_pos ((Work.BoseKinLoc.Sector.slotIso S).injective hj)]
    · rw [if_neg hj, if_neg (fun h => hj (congrArg (Work.BoseKinLoc.Sector.slotIso S) h))]
      rw [Equiv.symm_apply_apply]
  rw [hA]
  funext p
  rw [Work.PerSector.slotComb_apply, Function.update_apply, Work.PerSector.slotComb_apply]
  by_cases hp : p = i.1
  · subst hp
    rw [if_pos rfl, dif_pos i.2]
    have hsub : (⟨i.1, i.2⟩ : Work.PerSector.SlotIn N S) = i := rfl
    rw [hsub, Function.update_apply, if_pos rfl]
  · rw [if_neg hp]
    by_cases hmem : p ∈ S
    · rw [dif_pos hmem, dif_pos hmem, Function.update_apply, if_neg]
      intro hh
      exact hp (congrArg Subtype.val hh)
    · rw [dif_neg hmem, dif_neg hmem]

end Work.BoseKinLoc.Sector
