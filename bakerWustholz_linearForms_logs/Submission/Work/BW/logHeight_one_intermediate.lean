import Mathlib
import Submission.Work.BW.logHeight_intermediate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The affine logarithmic height of an element of an intermediate field, measured in the
ambient number field, scales by the relative degree: `h_K(x) = [K : F] · h_F(x)`. -/
theorem logHeight_one_intermediate {K : Type*} [Field K] [NumberField K]
    (F : IntermediateField ℚ K) (x : F) :
    Height.logHeight₁ (x : K) = (Module.finrank F K : ℝ) * Height.logHeight₁ x := by
  rw [Height.logHeight₁_eq_logHeight (K := K) (x := (x : K)),
      Height.logHeight₁_eq_logHeight (K := F) (x := x)]
  have h := logHeight_intermediate (K := K) F (x := (![x, 1] : Fin 2 → F))
  have hfun : (fun i => (((![x, 1] : Fin 2 → F) i : F) : K)) = ![((x : F) : K), 1] := by
    funext i
    fin_cases i <;> simp
  rw [hfun] at h
  rw [h]

end Work.BW
