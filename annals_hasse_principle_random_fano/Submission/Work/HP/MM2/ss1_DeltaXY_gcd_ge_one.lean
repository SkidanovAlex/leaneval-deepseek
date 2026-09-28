import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.DeltaXY_gcd_detL
import Submission.Work.HP.EE_lower2
import Submission.Work.HP.MDEstimates.detL_one_le

namespace Work.HP.MM2

open Work.HP

/-! ## Independence helpers

`LinearIndependent ℤ ![x, y]` forces `x ≠ y` and `x ≠ -y` (the two obvious non-trivial
relations with coefficients `(1,-1)` and `(1,1)`).  These are the private helpers of
`Work.HP.DeltaXY_gcd_detL`, replicated here since `private` declarations are not visible. -/

private lemma ne_of_linInd {ι : Type*} [Fintype ι] (x y : ι → ℤ)
    (h : LinearIndependent ℤ ![x, y]) : x ≠ y := by
  intro hxy
  have h2 := (Fintype.linearIndependent_iff.mp h) ![1, -1]
  have hsum : (∑ i, (![1, -1] : Fin 2 → ℤ) i • (![x, y] i)) = 0 := by
    simp [Fin.sum_univ_two, hxy]
  have := h2 hsum 0
  simp at this

private lemma ne_neg_of_linInd {ι : Type*} [Fintype ι] (x y : ι → ℤ)
    (h : LinearIndependent ℤ ![x, y]) : x ≠ -y := by
  intro hxy
  have h2 := (Fintype.linearIndependent_iff.mp h) ![1, 1]
  have hsum : (∑ i, (![1, 1] : Fin 2 → ℤ) i • (![x, y] i)) = 0 := by
    simp [Fin.sum_univ_two, hxy]
  have := h2 hsum 0
  simp at this

/-- `1 ≤ Δ(x,y)·𝓖(x,y)`.

By `DeltaXY_gcd_detL`, `Δ(x,y)·𝓖(x,y) = ‖ν(x)‖‖ν(y)‖ / det Γ_{x,y}`, and Lemma E's
lower bound `detL_Gam_le_norm` gives `det Γ_{x,y} ≤ ‖ν(x)‖‖ν(y)‖`.  Since `det Γ_{x,y} > 0`
(indeed `≥ 1`, `MDEstimates.detL_one_le`), the quotient is at least one. -/
theorem ss1_DeltaXY_gcd_ge_one (d n : ℕ) [DecidableEq (Work.HP.Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℤ) (hx : Work.HP.IsPrim x) (hy : Work.HP.IsPrim y)
    (hLI : LinearIndependent ℤ ![x, y]) :
    1 ≤ Work.HP.DeltaXY d n x y * (Work.HP.gcdMinors2 x y : ℝ) := by
  have h1 : x ≠ y := ne_of_linInd x y hLI
  have h2 : x ≠ -y := ne_neg_of_linInd x y hLI
  have hkey := Work.HP.DeltaXY_gcd_detL d n hd hn x y hx hy hLI
  have hle : Work.HP.detL (Work.HP.Gam d n x y) ≤
      Work.HP.eNorm (Work.HP.veronese d n x) * Work.HP.eNorm (Work.HP.veronese d n y) :=
    Work.HP.detL_Gam_le_norm d n hd x y hx hy h1 h2
  have hpos : 0 < Work.HP.detL (Work.HP.Gam d n x y) :=
    lt_of_lt_of_le zero_lt_one (Work.HP.MDEstimates.detL_one_le _)
  rw [hkey]
  exact (one_le_div hpos).mpr hle

end Work.HP.MM2
