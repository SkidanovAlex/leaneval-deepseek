import Mathlib
import Submission.Work.StemsB.FibreTrivial
import Submission.Work.SSSR.StemsB.hasHLP_pullback
import Submission.Work.StemsB.SerreSphereStep
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.uctDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.StemsB
variable {R : Type} [CommRing R] [Nontrivial R]

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval
namespace Work.SSSR.StemsB

noncomputable section

/-! ## The two contractions of the unit interval -/

/-- The straight-line contraction `(t,s) ↦ t * (1-s)` of the interval to `0`. -/
def unitContrZeroFun : ↑unitInterval × ↑unitInterval → ↑unitInterval :=
  fun q => ⟨(q.1 : ℝ) * (1 - (q.2 : ℝ)), by
    have h1 : (0 : ℝ) ≤ (q.1 : ℝ) := q.1.2.1
    have h2 : (q.1 : ℝ) ≤ 1 := q.1.2.2
    have h3 : (0 : ℝ) ≤ (q.2 : ℝ) := q.2.2.1
    have h4 : (q.2 : ℝ) ≤ 1 := q.2.2.2
    exact ⟨by nlinarith, by nlinarith⟩⟩

/-- The contraction `(t,s) ↦ t*(1-s)` as a continuous map. -/
def unitContrZero : C(↑unitInterval × ↑unitInterval, ↑unitInterval) where
  toFun := unitContrZeroFun
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

theorem unitContrZero_zero (t : ↑unitInterval) : unitContrZero (t, 0) = t := by
  refine Subtype.ext ?_
  show (t : ℝ) * (1 - ((0 : ↑unitInterval) : ℝ)) = (t : ℝ)
  simp

theorem unitContrZero_one (t : ↑unitInterval) : unitContrZero (t, 1) = 0 := by
  refine Subtype.ext ?_
  show (t : ℝ) * (1 - ((1 : ↑unitInterval) : ℝ)) = ((0 : ↑unitInterval) : ℝ)
  simp

theorem unitContrZero_fixes (s : ↑unitInterval) : unitContrZero (0, s) = 0 := by
  refine Subtype.ext ?_
  show ((0 : ↑unitInterval) : ℝ) * (1 - (s : ℝ)) = ((0 : ↑unitInterval) : ℝ)
  simp

/-- The straight-line contraction `(t,s) ↦ 1 - (1-t)*(1-s)` of the interval to `1`. -/
def unitContrOneFun : ↑unitInterval × ↑unitInterval → ↑unitInterval :=
  fun q => ⟨1 - (1 - (q.1 : ℝ)) * (1 - (q.2 : ℝ)), by
    have h1 : (0 : ℝ) ≤ (q.1 : ℝ) := q.1.2.1
    have h2 : (q.1 : ℝ) ≤ 1 := q.1.2.2
    have h3 : (0 : ℝ) ≤ (q.2 : ℝ) := q.2.2.1
    have h4 : (q.2 : ℝ) ≤ 1 := q.2.2.2
    exact ⟨by nlinarith, by nlinarith⟩⟩

/-- The contraction `(t,s) ↦ 1 - (1-t)*(1-s)` as a continuous map. -/
def unitContrOne : C(↑unitInterval × ↑unitInterval, ↑unitInterval) where
  toFun := unitContrOneFun
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

theorem unitContrOne_zero (t : ↑unitInterval) : unitContrOne (t, 0) = t := by
  refine Subtype.ext ?_
  show 1 - (1 - (t : ℝ)) * (1 - ((0 : ↑unitInterval) : ℝ)) = (t : ℝ)
  simp

theorem unitContrOne_one (t : ↑unitInterval) : unitContrOne (t, 1) = 1 := by
  refine Subtype.ext ?_
  show 1 - (1 - (t : ℝ)) * (1 - ((1 : ↑unitInterval) : ℝ)) = ((1 : ↑unitInterval) : ℝ)
  simp

theorem unitContrOne_fixes (s : ↑unitInterval) : unitContrOne (1, s) = 1 := by
  refine Subtype.ext ?_
  show 1 - (1 - ((1 : ↑unitInterval) : ℝ)) * (1 - (s : ℝ)) = ((1 : ↑unitInterval) : ℝ)
  simp

section Triv

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

end Triv

section Hom

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

end Hom

section Homology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

end Homology

end

end Work.SSSR.StemsB
