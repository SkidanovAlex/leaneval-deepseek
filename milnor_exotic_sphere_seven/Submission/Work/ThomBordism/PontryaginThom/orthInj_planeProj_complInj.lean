import Mathlib
import Submission.Work.ThomBordism.PontryaginThom.Orthogonal

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# `Pi_agree` for the orthogonal complement insertion

For a chart index `S` and an independent frame `A` (on whose plane `S` projects invertibly), the
complement projection `planeProj A S hS` of `Complement.lean` is the projection onto the coordinate
complement `range (complInj S)`, while `orthInj A = 1 - orthProj A` is the insertion of the
*orthogonal* complement of the plane of `A`.

The two complements differ as subspaces, but `orthInj A` kills every vector in the plane — i.e. the
whole range of `coeffMap A` — and `planeProj A S hS` kills exactly that range.  Consequently
`u - complInj S (planeProj A S hS u)` lies in the plane, so the two insertions agree on it:

`orthInj A (complInj S (planeProj A S hS u)) = orthInj A u`.

This is the identity `Pi_agree` of `Splitting.lean` for the data of the assembly, i.e. the statement
that the complement insertion `I_S = orthInj A ∘ complInj S` is chart-independent on the plane.
-/

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann

noncomputable section

/-- **The orthogonal insertion agrees with the coordinate insertion composed with the complement
projection**: `u - complInj S (planeProj A S hS u)` is the component of `u` in the plane of `A`, on
which `orthInj A` vanishes. -/
theorem orthInj_planeProj_complInj {k : ℕ} (A : Fin 8 → Work.ThomBordism.PontryaginThom.Euc (8 + k))
    (hA : LinearIndependent ℝ A) (S : Work.ThomBordism.Grassmann.ChartIdx 8 k)
    (hS : (Work.ThomBordism.Grassmann.frameMatrix S A).det ≠ 0) (u : Fin (8 + k) → ℝ) :
    Work.ThomBordism.PontryaginThom.orthInj A
        (Work.ThomBordism.PontryaginThom.complInj S
          (Work.ThomBordism.PontryaginThom.planeProj A S hS u))
      = Work.ThomBordism.PontryaginThom.orthInj A u := by
  -- the difference `u - complInj S (planeProj A S hS u)` lies in the range of `coeffMap A`
  have hmem : u - complInj S (planeProj A S hS u) ∈ LinearMap.range (coeffMap A) := by
    rw [← ker_planeProj A S hS]
    rw [LinearMap.mem_ker, map_sub]
    have h1 : planeProj A S hS (complInj S (planeProj A S hS u)) = planeProj A S hS u :=
      congrArg (fun g => g (planeProj A S hS u)) (planeProj_planeInj A S hS)
    rw [h1, sub_self]
  -- and `orthInj A` kills the range of `coeffMap A`
  have hker : orthInj A (u - complInj S (planeProj A S hS u)) = 0 := by
    obtain ⟨v, hv⟩ := hmem
    rw [← hv]
    exact orthInj_coeffMap A hA v
  rw [map_sub, sub_eq_zero] at hker
  exact hker.symm

end

end Work.ThomBordism.PontryaginThom
