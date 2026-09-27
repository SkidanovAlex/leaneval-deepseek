import Mathlib
import Submission.Work.Mostow.LinAlgMatrixIneqAux
import Submission.Work.Mostow.PhiMaxLine
import Submission.Work.Mostow.twoPtLine_mem_Kset
import Submission.Work.Mostow.hasDerivAt_sum_matG_twoPtLine
import Submission.Work.Mostow.matF_eq_exp_sum
import Submission.Work.Mostow.hasDerivAt_matG
import Submission.Work.Mostow.one_sub_pos_of_mem_Kset

/-!
# The Lagrange condition for the maximum of `matF` on the box `Kset n δ`

`matF lam = (∏ √lamᵢ)/(∏ (1 - lamᵢ))` on the box `Kset n δ = {lam | ∀ i, δ ≤ lam i, ∑ lam i = 1}`.
Writing `matG = log ∘ (the summand)`, we have `matF = exp (∑ i, matG (lam i))` on the interior of the
box.  If `x` is a maximiser in the *interior* of the box, then for any two indices `i ≠ j` the
two-point perturbation `t ↦ TwoPtLine x i j t` (move mass `t` from `j` to `i`) stays in the box for
small `t`, so `0` is a local maximum of `t ↦ matF (TwoPtLine x i j t)`; its derivative
`matF x * (matPhi (x i) - matPhi (x j))` must therefore vanish, and `matF x ≠ 0` forces
`matPhi (x i) = matPhi (x j)`.

This is the Lagrange condition `matPhi (x i) = λ` for all `i` that drives the sharp inequality
`LinAlgMatrixIneq`.
-/

namespace Work.Mostow

open scoped BigOperators

/-- `matF` does not vanish on `Kset n δ` when `δ > 0` and `n ≥ 2`. -/
lemma matF_ne_zero {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ) {y : Fin n → ℝ}
    (hy : y ∈ Kset n δ) : matF y ≠ 0 := by
  have h0 : ∀ i, 0 < y i := fun i => lt_of_lt_of_le hδ (hy.1 i)
  have h1 : ∀ i, 0 < 1 - y i := fun i => one_sub_pos_of_mem_Kset hδ hn hy i
  have hnum : 0 < ∏ i, Real.sqrt (y i) :=
    Finset.prod_pos (fun i _ => Real.sqrt_pos_of_pos (h0 i))
  have hden : 0 < ∏ i, (1 - y i) := Finset.prod_pos (fun i _ => h1 i)
  rw [matF]
  exact ne_of_gt (div_pos hnum hden)

theorem phi_eq_of_isMaxOn_Kset {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    {x : Fin n → ℝ} (hx : x ∈ Kset n δ)
    (hmax : IsMaxOn (fun y : Fin n → ℝ => matF y) (Kset n δ) x)
    (hint : ∀ i, δ < x i) : ∀ i j, matPhi (x i) = matPhi (x j) := by
  intro i j
  by_cases hij : i = j
  · rw [hij]
  set ε : ℝ := min (x i - δ) (x j - δ) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min (by linarith [hint i]) (by linarith [hint j])
  have hεi : ε ≤ x i - δ := by rw [hεdef]; exact min_le_left _ _
  have hεj : ε ≤ x j - δ := by rw [hεdef]; exact min_le_right _ _
  have hnbd : Set.Ioo (-ε) ε ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by linarith) hεpos
  have hxpos : ∀ k, 0 < x k := fun k => lt_of_lt_of_le hδ (hx.1 k)
  have hxlt : ∀ k, x k < 1 := fun k => by linarith [one_sub_pos_of_mem_Kset hδ hn hx k]
  -- `0` is a local maximum of the perturbation line
  have hloc : IsLocalMax (fun t : ℝ => matF (TwoPtLine x i j t)) 0 := by
    have hmaxOn : IsMaxOn (fun t : ℝ => matF (TwoPtLine x i j t)) (Set.Ioo (-ε) ε) 0 := by
      intro t ht
      simpa using hmax (twoPtLine_mem_Kset hx hij hεi hεj (abs_lt.mpr ht))
    exact (IsMaxOn.isLocalMaxOn hmaxOn).isLocalMax hnbd
  -- the perturbation line agrees with `exp (∑ matG)` near `0`
  have hExpEq : (fun t : ℝ => matF (TwoPtLine x i j t))
      =ᶠ[nhds 0] (fun t : ℝ => Real.exp (∑ k, matG (TwoPtLine x i j t k))) := by
    show ∀ᶠ t in nhds (0 : ℝ), matF (TwoPtLine x i j t)
      = Real.exp (∑ k, matG (TwoPtLine x i j t k))
    filter_upwards [hnbd] with t ht
    have hline : TwoPtLine x i j t ∈ Kset n δ :=
      twoPtLine_mem_Kset hx hij hεi hεj (abs_lt.mpr ht)
    exact matF_eq_exp_sum (fun k => lt_of_lt_of_le hδ (hline.1 k))
      (fun k => by linarith [one_sub_pos_of_mem_Kset hδ hn hline k])
  have hS : HasDerivAt (fun t : ℝ => ∑ k, matG (TwoPtLine x i j t k))
      (matPhi (x i) - matPhi (x j)) 0 := hasDerivAt_sum_matG_twoPtLine hn hδ hx hij
  have hval : Real.exp (∑ k, matG (TwoPtLine x i j 0 k)) = matF x := by
    simp only [TwoPtLine_zero]
    exact (matF_eq_exp_sum hxpos hxlt).symm
  have hderiv : HasDerivAt (fun t : ℝ => matF (TwoPtLine x i j t))
      (matF x * (matPhi (x i) - matPhi (x j))) 0 := by
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (∑ k, matG (TwoPtLine x i j t k)))
        (Real.exp (∑ k, matG (TwoPtLine x i j 0 k)) * (matPhi (x i) - matPhi (x j))) 0 :=
      hS.exp
    rw [hval] at hexp
    exact hexp.congr_of_eventuallyEq hExpEq
  -- the derivative of a local maximum vanishes
  have h0 : deriv (fun t : ℝ => matF (TwoPtLine x i j t)) 0 = 0 := hloc.deriv_eq_zero
  rw [hderiv.deriv] at h0
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left (matF_ne_zero hn hδ hx))

end Work.Mostow
