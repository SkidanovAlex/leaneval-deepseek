import Mathlib
import Submission.Work.Serre.thomCylGluing
import Submission.Work.Serre.bijective_cup_openBall

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cellular step from the shell pieces, with the ball pieces discharged

`Work.Serre.thomCylCellStep_of_shellsBall` is `Work.Serre.thomCylCellStep_of_shells` with its
`hball` family of hypotheses discharged by the proved local statement
`Work.Serre.bijective_cup_openBall` (the cup bijectivity over an open-ball piece of a cell).  The
only remaining hypothesis is the *shell* family `hshell`.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

set_option maxHeartbeats 3200000

/-- **The cellular step, with the ball pieces discharged.** -/
theorem thomCylCellStep_of_shellsBall (r N D : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : ThomCylAt r N (restrictFibre q (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))))
    (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ < R) (hR1 : R ≤ 1)
    (hshell : ∀ i : ι, ∀ m : ℕ, m + (r + 1) ≤ N + 1 → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥((cylRetract q) ⁻¹'
          (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R))) =>
        (Work.Thom.mixedCupC ℚ (glueSub (Set.range (cylIncl q)) ((cylRetract q) ⁻¹'
            (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R)))) m (r + 1)) x
          ((Work.Thom.relCohMap (glueInclT ((cylRetract q) ⁻¹'
              (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R))))
            (glueSub (Set.range (cylIncl q)) ((cylRetract q) ⁻¹'
              (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R))))
            (Set.range (cylIncl q)) (fun _ hy => hy) ℚ (r + 1)).hom
            (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH)))) :
    ThomCylAt r N q :=
  thomCylCellStep_of_shells r N D hr hN hD hΓ ι f q hq hvan hgen hpc IH ρ R hρ hρR hR1
    (fun i m hm => Work.Serre.bijective_cup_openBall r N D hr hN hD hΓ ι f q hq hvan hgen hpc
      IH (lt_trans hρ hρR) hR1 i m hm)
    hshell

end

end Work.Serre
