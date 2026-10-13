import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted bound for the `D_θ`-iterates of `sin²`

`D_θ φ = sin (2θ) · φ'` (`Work.Spaces.dthU`).  The claim is that

`|D_θ^j (sin²) θ| · sin(2θ)^{-α/5} / (α + sin 2θ) ≤ C`,  `j = 1,…,6`, `0 < α ≤ 1`, `θ ∈ Iθ`,

for a universal constant `C` — i.e. the `α`-dependent singular factor `sin(2θ)^{-α/5}` is
absorbed by the *second order* vanishing of the iterates at the endpoints of `Iθ = [0,π/2]`.

The vanishing is the content of `dthUiter_sin_sq_iter`
(`Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired`): for `j = i+1 ≥ 1`

`D_θ^j (sin²) θ = cos²θ · sin²θ · R_i(cos²θ)`,  `R_i = Σ_k c_k X^k`,  `Σ_k |c_k| ≤ 1095801216`

(`dthUiterPRcoef_sum_le`).  Since `cos²θ · sin²θ = sin²(2θ)/4` this gives
`|D_θ^j (sin²) θ| ≤ 1095801216 · sin²(2θ)`, and then for `s = sin 2θ ∈ [0,1]`

`sin²(2θ) · s^{-α/5}/(α+s) ≤ s^{2-α/5}/(α+s) ≤ s^{1-α/5} ≤ 1`

because `α + s ≥ s` and `1 - α/5 ≥ 4/5 ≥ 0`.  Hence `C = 1095801216` works.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ = [0, π/2]`. -/
private lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  obtain ⟨h0, h1⟩ := hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩

/-- **The endpoint vanishing of the `D_θ`-iterates of `sin²`.**  For every `j ≥ 1` and
every real `θ`, `|D_θ^j (sin²) θ| ≤ 1095801216 · sin²(2θ)`; the factor `sin²(2θ)` is what
absorbs the singular weight `sin(2θ)^{-α/5}` near the two endpoints of `Iθ`. -/
private lemma dthU_sinSq_le (j : ℕ) (hj : 1 ≤ j) (hj6 : j ≤ 6) (θ : ℝ) :
    |Work.Spaces.dthU^[j] (fun θ : ℝ => Real.sin θ ^ 2) θ|
      ≤ 1095801216 * Real.sin (2 * θ) ^ 2 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i ≤ 6 := by omega
  rw [Work.FTS.PhiStar.Psi0Aux.dthUiter_sin_sq_iter i hi θ]
  have hb : |(Work.FTS.PhiStar.Psi0Aux.dthUiterPR i).eval (Real.cos θ ^ 2)| ≤ 1095801216 := by
    rw [Work.FTS.PhiStar.Psi0Aux.dthUiterPR_eval]
    exact le_trans
      (Work.FTS.PhiStar.Psi0Aux.dthUiter_abs_sum_pow_le _ _ _
        (sq_nonneg (Real.cos θ)) (Real.cos_sq_le_one θ))
      (Work.FTS.PhiStar.Psi0Aux.dthUiterPRcoef_sum_le i hi)
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ)),
    abs_of_nonneg (sq_nonneg (Real.sin θ))]
  have hcs : Real.cos θ ^ 2 * Real.sin θ ^ 2 = Real.sin (2 * θ) ^ 2 / 4 := by
    rw [Real.sin_two_mul]; ring
  calc Real.cos θ ^ 2 * Real.sin θ ^ 2
        * |(Work.FTS.PhiStar.Psi0Aux.dthUiterPR i).eval (Real.cos θ ^ 2)|
      = Real.sin (2 * θ) ^ 2 / 4
        * |(Work.FTS.PhiStar.Psi0Aux.dthUiterPR i).eval (Real.cos θ ^ 2)| := by rw [hcs]
    _ ≤ Real.sin (2 * θ) ^ 2 * 1095801216 :=
        mul_le_mul (by nlinarith [sq_nonneg (Real.sin (2 * θ))]) hb (abs_nonneg _)
          (sq_nonneg _)
    _ = 1095801216 * Real.sin (2 * θ) ^ 2 := by ring

/-- **The elementary supremum.**  For `0 < α ≤ 1` and `0 ≤ s ≤ 1`,
`s² · s^{-α/5} / (α + s) ≤ 1`:  the singular factor `s^{-α/5}` is defeated by the second
order zero of `s²` at `s = 0` (`s^{2-α/5} = s · s^{1-α/5}` with `1 - α/5 ≥ 4/5 ≥ 0`), and
the denominator `α + s ≥ s` removes the remaining power. -/
private lemma sinSq_mul_rpow_div_le (α s : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : s ^ 2 * s ^ (-(α / 5)) / (α + s) ≤ 1 := by
  rcases eq_or_lt_of_le hs0 with hs | hs
  · rw [← hs]; simp
  · have hs2 : s ^ 2 * s ^ (-(α / 5)) = s ^ (2 - α / 5) := by
      rw [show s ^ 2 = s ^ (2 : ℝ) from (Real.rpow_two s).symm, ← Real.rpow_add hs]
      congr 1
    have hsplit : s ^ (2 - α / 5) = s ^ (1 - α / 5) * s := by
      have h := Real.rpow_add hs (1 - α / 5) 1
      rw [Real.rpow_one] at h
      rw [← h]
      congr 1
      ring
    have h1 : s ^ (1 - α / 5) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hs) hs1 (by linarith)
    have h2 : s / (α + s) ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < α + s)]
      linarith
    calc s ^ 2 * s ^ (-(α / 5)) / (α + s)
        = s ^ (1 - α / 5) * s / (α + s) := by rw [hs2, hsplit]
      _ = s ^ (1 - α / 5) * (s / (α + s)) := by rw [mul_div_assoc]
      _ ≤ 1 * 1 := mul_le_mul h1 h2 (div_nonneg (le_of_lt hs) (by linarith)) (by norm_num)
      _ = 1 := by norm_num

theorem dthU_sinSq_weight : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∀ (j : ℕ), 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] (fun θ => Real.sin θ ^ 2) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) ≤ C := by
  refine ⟨1095801216, by norm_num, ?_⟩
  intro α hα hα1 j hj1 hj6 θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one (2 * θ)
  have hr : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) := Real.rpow_nonneg hs0 _
  have hden : 0 ≤ α + Real.sin (2 * θ) := by linarith
  have h1 : |Work.Spaces.dthU^[j] (fun θ : ℝ => Real.sin θ ^ 2) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5))
      ≤ (1095801216 * Real.sin (2 * θ) ^ 2) * (Real.sin (2 * θ)) ^ (-(α / 5)) :=
    mul_le_mul_of_nonneg_right (dthU_sinSq_le j hj1 hj6 θ) hr
  calc |Work.Spaces.dthU^[j] (fun θ : ℝ => Real.sin θ ^ 2) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
      ≤ (1095801216 * Real.sin (2 * θ) ^ 2) * (Real.sin (2 * θ)) ^ (-(α / 5))
          / (α + Real.sin (2 * θ)) := div_le_div_of_nonneg_right h1 hden
    _ = 1095801216 * (Real.sin (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(α / 5))
          / (α + Real.sin (2 * θ))) := by ring
    _ ≤ 1095801216 * 1 :=
        mul_le_mul_of_nonneg_left (sinSq_mul_rpow_div_le α _ hα hα1 hs0 hs1) (by norm_num)
    _ = 1095801216 := by norm_num

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
