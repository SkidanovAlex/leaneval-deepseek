import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.twoMapsDefs
import Submission.Work.OROneRel.winFreiheitssatz_easy
import Submission.Work.OROneRel.presentedGroup_map_injective_of_preimage

namespace Work.OROneRel

universe u

theorem winTheta_injective_of_freiheitssatz {α : Type u} (u : FreeGroup α) (l : ℕ)
    {c : α → ℤ} {Wt : ℤ → FreeGroup α} {lo hi : ℤ}
    (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hA : ∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
      Work.OROneRel.winRho Wt c lo hi x ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))) :
    Function.Injective (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin) := by
  -- `winTheta` sends the class of `w` to the class of `winRho w` (`winTheta_mk`), so an element
  -- of the kernel is the class of some `w` with `winRho w ∈ ⟪u ^ l⟫`; the Freiheitssatz `hA`
  -- then places `w` in `⟪winRoot ^ l⟫`, i.e. the class of `w` is trivial.
  intro a b hab
  have h' : a * b⁻¹ = 1 := by
    have h1 : Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    obtain ⟨w, hw⟩ := PresentedGroup.mk_surjective
      ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
        Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) (a * b⁻¹)
    rw [← hw] at h1 ⊢
    rw [Work.OROneRel.winTheta_mk, PresentedGroup.mk_eq_one_iff] at h1
    rw [PresentedGroup.mk_eq_one_iff]
    exact hA w h1
  exact mul_inv_eq_one.mp h'

end Work.OROneRel
