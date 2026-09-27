import Mathlib
import Submission.Work.Mostow.margRegionNrmCSat
import Submission.Work.Mostow.nearId_blk

namespace Work.Mostow

open Submission.Mostow

/-- The `nrmC`-coordinate of a Fermi-chart point `fermiW 1 m v W` is `W`, independently of the
foot `v`. -/
private lemma nrmC_fermiW_eq (m : ℕ) (v : E 1) (W : E m) :
    nrmC 1 m (fermiW 1 m v W) = W :=
  nib_nrmC_fermiW m v W

/-- Membership of `fermiW 1 m · W` in the Margulis region of the pointwise stabiliser is
independent of the first coordinate `v`: the region is a union of level sets of `nrmC 1 m`
(`Work.Mostow.margRegionNrmCSat`), and `nrmC` forgets the foot. -/
theorem fermiW_mem_margRegion (m : ℕ) (hA : Submission.Mostow.POActionProp (1 + m))
    (hI : Submission.Mostow.HypIsometryProp (1 + m)) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) (η₁ : ℝ)
    (v : Submission.Mostow.E 1) (W : Submission.Mostow.E m) :
    Submission.Mostow.fermiW 1 m v W ∈ Work.Mostow.margRegion m Λ η₁ ↔
      Submission.Mostow.fermiW 1 m (0 : Submission.Mostow.E 1) W ∈ Work.Mostow.margRegion m Λ η₁ := by
  have hnm : Submission.Mostow.nrmC 1 m (Submission.Mostow.fermiW 1 m v W)
      = Submission.Mostow.nrmC 1 m (Submission.Mostow.fermiW 1 m (0 : Submission.Mostow.E 1) W) := by
    rw [nrmC_fermiW_eq, nrmC_fermiW_eq]
  exact ⟨fun h => margRegionNrmCSat m hA hI hA1 hI1 Λ η₁ _ _ hnm h,
         fun h => margRegionNrmCSat m hA hI hA1 hI1 Λ η₁ _ _ hnm.symm h⟩

end Work.Mostow
