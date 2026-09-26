import Mathlib
import Submission.Work.Asymptotics.Compact.tailDefs

namespace Work.Asymptotics.Compact

/-- Auxiliary: `𝒢_+ + 𝒢_- = 2 𝒢` for the two allowed dimensions `d = 8` and `d = 24`.
This is a purely algebraic identity between the explicit formulas defining
`Gplus`, `Gminus` and `Gcoef`/`Gfun`; the hypothesis `d = 8 ∨ d = 24` selects the
two branches of the `if d = 8 then … else …` definitions. -/
theorem gfun_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : UpperHalfPlane) : Work.Asymptotics.Compact.Gplus d τ z + Work.Asymptotics.Compact.Gminus d ℓ τ z = 2 * Work.Asymptotics.Compact.Gfun d ℓ τ z := by
  rcases hd with rfl | rfl
  · -- d = 8
    simp only [Work.Asymptotics.Compact.Gplus, Work.Asymptotics.Compact.Gminus,
      Work.Asymptotics.Compact.Gfun, Work.Asymptotics.Compact.Gcoef]
    simp only [if_true, if_false, Fin.reduceEq]
    simp only [Work.Asymptotics.Compact.Gplus8, Work.Asymptotics.Compact.Gminus8]
    field_simp
    simp only [Complex.I_sq]
    ring
  · -- d = 24
    simp only [Work.Asymptotics.Compact.Gplus, Work.Asymptotics.Compact.Gminus,
      Work.Asymptotics.Compact.Gfun, Work.Asymptotics.Compact.Gcoef]
    simp only [if_neg (show ¬ (24 = 8) by decide), if_true, if_false, Fin.reduceEq,
      and_true, and_false]
    simp only [Work.Asymptotics.Compact.Gplus24, Work.Asymptotics.Compact.Gminus24]
    have hD : Work.Kernels.DeltaFun τ ≠ 0 := by
      simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero τ
    field_simp [hD]
    simp only [Complex.I_sq]
    ring

end Work.Asymptotics.Compact
