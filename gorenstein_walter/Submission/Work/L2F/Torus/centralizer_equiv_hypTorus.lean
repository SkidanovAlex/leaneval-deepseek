import Mathlib
import Submission.Work.L2F.Torus.Defs
import Submission.Work.L2F.Mat2.nonempty_hypTorus_mulEquiv_centralizer

namespace Work.L2F.Torus

/-- The centralizer of `x` in `SL(2,F)` (`disc F x ≠ 0`) is isomorphic to the "torus"
`hypTorus F (disc F x)`: the map `a • 1 + b • conjMat F x ↦ !![a, disc·b; b, a]` is a group
isomorphism. -/
theorem centralizer_equiv_hypTorus (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F) (hD : disc F x ≠ 0) : Nonempty (cent F x ≃* Work.L2F.hypTorus F (disc F x)) := by
  have hx : ((x : Matrix (Fin 2) (Fin 2) F)).trace ^ 2 ≠ 4 := by
    rw [disc_apply] at hD
    exact sub_ne_zero.mp hD
  obtain ⟨e⟩ :=
    Work.L2F.Mat2.nonempty_hypTorus_mulEquiv_centralizer F h2 x hx
  exact ⟨e.symm⟩

end Work.L2F.Torus
