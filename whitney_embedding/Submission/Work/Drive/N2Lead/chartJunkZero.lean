import Mathlib
import Submission.Work.Drive.N2.modelBall

namespace Work.Drive.N2Lead

/-- **A chart with its junk values wiped to zero.**

The inverse of an `OpenPartialHomeomorph` is a *total* function: its values outside the target are
arbitrary junk carried by the structure's `invFun` field, and the only laws the structure imposes on
them are the partial-inverse laws on `source` and `target`.  Consequently, given a chart `φ`, one
may replace the *forward* map by "`φ` on `φ.source`, `0` off it" while keeping the source, the
target and the *inverse* untouched: the inverse laws only constrain the forward map on the source,
so the modified map is again a partial homeomorphism with the same inverse function (hence the same
`symm`), and the model balls `Work.Drive.N2.modelBall φ r` are unchanged because `modelBall` tests
source membership first.

This is the "junk-zero" normalisation of a chart: it turns a partially defined chart into a
globally defined map without altering any of the chart data that a consumer of
`Work.Drive.N2.modelBall` (or of the chart's inverse) can see. -/
theorem chartJunkZero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) :
    ∃ ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)),
      ψ.source = φ.source ∧ ψ.target = φ.target ∧
      (∀ y : M, y ∈ φ.source → ψ y = φ y) ∧
      (∀ y : M, y ∉ φ.source → ψ y = 0) ∧
      (∀ z : EuclideanSpace ℝ (Fin 2), ψ.symm z = φ.symm z) ∧
      (∀ r : ℝ, Work.Drive.N2.modelBall ψ r = Work.Drive.N2.modelBall φ r) := by
  classical
  -- The forward map is `φ` on its source and `0` everywhere else; the inverse is *copied* from
  -- `φ`, which is what makes the `symm` clause hold by `rfl`.
  refine ⟨{ toFun := fun y => if y ∈ φ.source then φ y else 0
            invFun := φ.invFun
            source := φ.source
            target := φ.target
            map_source' := fun x hx => by rw [if_pos hx]; exact φ.map_source hx
            map_target' := fun x hx => φ.map_target hx
            left_inv' := fun x hx => by rw [if_pos hx]; exact φ.left_inv hx
            right_inv' := fun x hx => by
              have h : φ.invFun x ∈ φ.source := φ.map_target hx
              rw [if_pos h]
              exact φ.right_inv hx
            continuousOn_toFun := φ.continuousOn_toFun.congr (fun y hy => by simp [hy])
            continuousOn_invFun := φ.continuousOn_invFun
            open_source := φ.open_source
            open_target := φ.open_target }, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- agreement on the source
    intro y hy; simp [hy]
  · -- vanishing off the source
    intro y hy; simp [hy]
  · -- the inverse is untouched (definitionally)
    intro z; rfl
  · -- the model balls only see the source and the forward values on it
    intro r
    ext y
    by_cases hy : y ∈ φ.source <;> simp [Work.Drive.N2.modelBall, hy]

end Work.Drive.N2Lead
