import Mathlib
import Submission.Work.WilG4c.Defs

namespace Work.WilG4c

/-- At `r = 0` the predicates `PYLip` and `PYLipDef` coincide: `NormLeOneDef F 0` only asks,
at every point of the open cube, that `‖iteratedFDeriv ℝ 0 (F i l) z‖ ≤ 1`, and
`‖iteratedFDeriv ℝ 0 g z‖ = ‖g z‖` (`norm_iteratedFDeriv_zero`), which is exactly the `m = 0`
instance of `YBound F 0` at the point `z = pt (z 0) (Fin.tail z)`. -/
theorem pylipDef_zero_of_pylip {p n k : ℕ} {F : Work.WilkG4c.Family k p (n + 1)}
    (h : Work.WilkG4c.PYLip p n 0 k F) : Work.WilkG4c.PYLipDef p n 0 k F := by
  obtain ⟨hY, hLip⟩ := h
  refine ⟨hY, hLip, ?_⟩
  intro i l z hz _ m hm
  obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hm
  rw [norm_iteratedFDeriv_zero]
  have hb : ‖F i l z‖ ≤ 1 := by
    have h1 := hY i l (z 0) (hz 0) 0 le_rfl (Fin.tail z) (fun j => hz j.succ)
    rw [norm_iteratedFDeriv_zero] at h1
    rw [Work.WilkG4c.slice_apply, Work.WilkG4c.pt_eta] at h1
    exact h1
  exact hb

end Work.WilG4c
