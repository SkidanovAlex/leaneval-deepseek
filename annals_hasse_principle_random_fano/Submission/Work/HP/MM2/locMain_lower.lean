import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.DeltaXY_gcd_detL
import Submission.Work.HP.EE_lower2
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.MDBasic.nonneg_basic
import Submission.Work.HP.Sig2.lam_Gam_le_muXY
import Submission.Work.HP.bigW_le_pow

namespace Work.HP.MM2

open Work.HP

/-- **Lower bound for the local main term.**  For `0 < A`, `1 < B` and independent primitive
`x, y`, the main term `locMain d n A B (x,y) = 8ι A^{N-2}‖ν(x)‖‖ν(y)‖/((αW)² det Γ_{x,y})`
dominates `8ι A^{N-2}/(αW)²`.  The common positive factor `8ι A^{N-2}` cancels, and the claim is
`1 ≤ ‖ν(x)‖‖ν(y)‖/detL (Gam d n x y)`, which follows from
`detL_Gam_le_norm` (`detL (Gam d n x y) ≤ ‖ν(x)‖‖ν(y)‖`, needing `IsPrim x`, `IsPrim y`,
`x ≠ y`, `x ≠ -y` -- the last two from `ne_of_linInd`/`ne_neg_of_linInd`, module
`Submission.Work.HP.Sig2.lam_Gam_le_muXY`) and `Lat.detL_ge_one` (`1 ≤ detL`), together with
`0 ≤ iotaDN d n` (`MDBasic.nonneg_basic.iotaDN_nonneg`), `0 < Real.log B` (`1 < B`) and
`1 ≤ bigW (wOf B)` (`bigW_le_pow.one_le_bigW`).  Conclude with `le_div_iff₀` and
`div_le_div_of_nonneg_right`/`mul_le_mul_of_nonneg_left`. -/
theorem locMain_lower (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∀ (A B : ℝ) (x y : Fin (n + 1) → ℤ), 0 < A → 1 < B → IsPrim x → IsPrim y →
      LinearIndependent ℤ ![x, y] →
      8 * iotaDN d n * A ^ (NN d n - 2) / ((Real.log B * ((bigW (wOf B) : ℕ) : ℝ)) ^ 2)
        ≤ locMain d n A B (x, y) := by
  intro A B x y hA hB hx hy hlin
  -- `x ≠ ±y` are the non-degeneracy conditions of the key lemma.
  have hxy : x ≠ y := Sig2.ne_of_linInd x y hlin
  have hxny : x ≠ -y := Sig2.ne_neg_of_linInd x y hlin
  -- the covolume of `Γ_{x,y}` is at most `‖ν(x)‖‖ν(y)‖`
  have hE : detL (Gam d n x y) ≤ eNorm (veronese d n x) * eNorm (veronese d n y) :=
    detL_Gam_le_norm d n hd x y hx hy hxy hxny
  -- ... and at least `1`, hence positive
  have hD1 : (1 : ℝ) ≤ detL (Gam d n x y) := Lat.detL_ge_one (Gam d n x y)
  have hDpos : 0 < detL (Gam d n x y) := lt_of_lt_of_le zero_lt_one hD1
  -- the positivity of `α²` and of the common factor
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hW1 : (1 : ℝ) ≤ ((bigW (wOf B) : ℕ) : ℝ) := by
    exact_mod_cast one_le_bigW (wOf B)
  have hWpos : 0 < ((bigW (wOf B) : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hW1
  have ht : 0 < (Real.log B * ((bigW (wOf B) : ℕ) : ℝ)) ^ 2 := by positivity
  have hC : 0 ≤ 8 * iotaDN d n * A ^ (NN d n - 2) := by
    have hι := MDBasic.iotaDN_nonneg d n
    positivity
  -- the whole claim is `det Γ_{x,y} ≤ ‖ν(x)‖‖ν(y)‖` with the common factor cancelled
  unfold locMain
  rw [le_div_iff₀ (by positivity : 0 < ((Real.log B * ((bigW (wOf B) : ℕ) : ℝ)) ^ 2
    * detL (Gam d n x y)))]
  rw [← mul_assoc, div_mul_cancel₀ _ ht.ne']
  exact mul_le_mul_of_nonneg_left hE hC

end Work.HP.MM2
