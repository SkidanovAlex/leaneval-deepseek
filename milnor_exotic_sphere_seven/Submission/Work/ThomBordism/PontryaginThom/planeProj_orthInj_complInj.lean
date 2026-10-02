import Submission.Work.ThomBordism.PontryaginThom.Complement
import Submission.Work.ThomBordism.PontryaginThom.Orthogonal

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The complement projection inverts the orthogonal insertion

The complement projection `planeProj A S hS` of `Complement.lean` projects `ℝ^{8+k}` onto the
coordinate complement `im (complInj S)` along the plane `im (coeffMap A)` of the frame `A`, and
`planeInj A S hS = complInj S` inserts that complement.

The orthogonal insertion `orthInj A = 1 - orthProj A` of `Orthogonal.lean` inserts the *orthogonal*
complement of the plane.  Its image is still contained in the complement `im (complInj S)` only in
general after applying `planeProj`; the point is that `orthInj A` differs from the identity by an
element of the plane (the orthogonal projection `orthProj A x`), and the plane is exactly the kernel
of `planeProj A S hS`.  Hence `planeProj A S hS ∘ orthInj A` still inverts `complInj S`:

`planeProj A S hS (orthInj A (complInj S w)) = w`.

This is the second of the two round-trip identities making `planeProj A S hS` a left inverse of the
orthogonal insertion `orthInj A ∘ complInj S`; the first is the chart-independence statement
`orthInj_planeProj_complInj`.
-/

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann

noncomputable section

/-- The orthogonal projection of any vector lies in the plane, hence is killed by the complement
projection. -/
theorem planeProj_orthProj {k : ℕ} (A : Fin 8 → Euc (8 + k)) (S : ChartIdx 8 k)
    (hS : (frameMatrix S A).det ≠ 0) (x : Fin (8 + k) → ℝ) :
    planeProj A S hS (orthProj A x) = 0 := by
  obtain ⟨v, hv⟩ := range_orthProj_le A ⟨x, rfl⟩
  rw [← hv]
  have h0 := congrArg (fun g => g v) (planeProj_coeffMap A S hS)
  simpa [LinearMap.comp_apply] using h0

/-- **The complement projection inverts the orthogonal insertion**: `planeProj A S hS` is a left
inverse of the chart-independent insertion `orthInj A ∘ complInj S`. -/
theorem planeProj_orthInj_complInj {k : ℕ} (A : Fin 8 → Work.ThomBordism.PontryaginThom.Euc (8 + k))
    (hA : LinearIndependent ℝ A) (S : Work.ThomBordism.Grassmann.ChartIdx 8 k)
    (hS : (Work.ThomBordism.Grassmann.frameMatrix S A).det ≠ 0) (w : Fin k → ℝ) :
    Work.ThomBordism.PontryaginThom.planeProj A S hS
        (Work.ThomBordism.PontryaginThom.orthInj A (Work.ThomBordism.PontryaginThom.complInj S w))
      = w := by
  have hproj : planeProj A S hS (complInj S w) = w := by
    have h1 := congrArg (fun g => g w) (planeProj_planeInj A S hS)
    simpa [planeInj] using h1
  rw [orthInj, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hproj,
    planeProj_orthProj A S hS (complInj S w), sub_zero]

end

end Work.ThomBordism.PontryaginThom
