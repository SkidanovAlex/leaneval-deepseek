import Mathlib
import Submission.Work.Drive.FamBox.Defs
import Submission.Work.Drive.famMeetDefs

/-!
# Smoothness of the two sides of the joint family

`famLoop L p = L (mk2 (p 0) (p 1))` and `famChain N p = N (famPt (p 0) (famT3 (p 2) (p 3) (p 4)))`
are the two sides of the joint family of L6.  Both are compositions of the smooth map `L` resp. `N`
with a *linear* map `ℝ⁵ → ℝ²` resp. `ℝ⁵ → ℝ⁴`, so they are smooth.
-/

namespace Work.Drive.FamBox

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

variable {M : Type*} [TopologicalSpace M]

/-- The index selection `(p 0, p 1)` of the loop side. -/
def lIdx : Fin 2 → Fin 5 := ![0, 1]

/-- The index selection `(p 0, p 2, p 3, p 4)` of the chain side. -/
def cIdx : Fin 4 → Fin 5 := ![0, 2, 3, 4]

/-- `p ↦ mk2 (p 0) (p 1)` as a continuous linear map. -/
def loopArgCLM : EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
    (ContinuousLinearMap.pi (fun i : Fin 2 => PiLp.proj 2 (fun _ : Fin 5 => ℝ) (lIdx i)))

/-- `p ↦ famPt (p 0) (famT3 (p 2) (p 3) (p 4))` as a continuous linear map. -/
def chainArgCLM : EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm
    (ContinuousLinearMap.pi (fun k : Fin 4 => PiLp.proj 2 (fun _ : Fin 5 => ℝ) (cIdx k)))

@[simp] lemma loopArgCLM_apply (p : EuclideanSpace ℝ (Fin 5)) :
    loopArgCLM p = Work.Drive.mk2 (p 0) (p 1) := by
  ext i
  fin_cases i <;> simp [loopArgCLM, lIdx, Work.Drive.mk2]

@[simp] lemma chainArgCLM_apply (p : EuclideanSpace ℝ (Fin 5)) :
    chainArgCLM p = Work.Drive.famPt (p 0) (Work.Drive.famT3 (p 2) (p 3) (p 4)) := by
  ext k
  fin_cases k <;> simp [chainArgCLM, cIdx, Work.Drive.famPt, Work.Drive.famT3]

theorem contMDiff_famLoop {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (L : EuclideanSpace ℝ (Fin 2) → M)
    (hL : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) L) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.famLoop L) := by
  have hfun : Work.Drive.famLoop L = L ∘ ⇑loopArgCLM := by
    funext p
    simp [Work.Drive.famLoop]
  rw [hfun]
  exact hL.comp loopArgCLM.contMDiff

theorem contMDiff_famChain {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (N : EuclideanSpace ℝ (Fin 4) → M)
    (hN : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) N) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.famChain N) := by
  have hfun : Work.Drive.famChain N = N ∘ ⇑chainArgCLM := by
    funext p
    simp [Work.Drive.famChain]
  rw [hfun]
  exact hN.comp chainArgCLM.contMDiff

end

end Work.Drive.FamBox
