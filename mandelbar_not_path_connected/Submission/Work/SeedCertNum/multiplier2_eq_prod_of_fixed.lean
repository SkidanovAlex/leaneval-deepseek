import Mathlib
import Submission.Work.Landing.Core
import Submission.Work.Landing.Family.deriv_tsq
import Submission.Work.ELRig.deriv_iterate_ne_zero_of_notMem_orbit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The period-5 multiplier as a product of squared orbit norms

For a point `z` with `(T_c)^[5] z = z` (i.e. `z` lies on a period-`5` cycle of the
antiholomorphic quadratic `T_c`), the multiplier of the holomorphic second return map
`(Tsq c)^[5] = (T_c)^[10]` is the **non-negative real number**

  `multiplier2 c 5 z = ∏_{k<5} (2 ‖(T_c)^[k] z‖)²`,

where the product on the right is a product of squares of real numbers (so it is `≥ 0`)
coerced into `ℂ`.

The mechanism is the chain rule for the holomorphic polynomial `Tsq c`,

  `deriv ((Tsq c)^[5]) z = ∏_{i<5} deriv (Tsq c) ((Tsq c)^[i] z)`,

together with `deriv (Tsq c) w = 4 w (w² + c̄) = 4 w · conj(T_c w)` and the periodicity of
the orbit `w k = (T_c)^[k] z`, `w (k+5) = w k`.  Writing `W = ∏_{k<5} w k`, the product
collapses to `4^5 · W · conj W = 4^5 · normSq W = 2^10 ‖W‖²`, and
`‖W‖² = ∏_{k<5} ‖w k‖²`, which is exactly the stated real product.
-/

namespace Work.SeedCertNum

open Function
open LeanEval.ComplexAnalysis (Tantibar)

theorem multiplier2_eq_prod_of_fixed {c z : ℂ} (h : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z = z) :
    Work.Landing.multiplier2 c 5 z =
      ((∏ k ∈ Finset.range 5, (2 * ‖(LeanEval.ComplexAnalysis.Tantibar c)^[k] z‖) ^ 2 : ℝ) : ℂ) := by
  let w : ℕ → ℂ := fun k => (Tantibar c)^[k] z
  have hper : ∀ n, w (n + 5) = w n := by
    intro n
    show (Tantibar c)^[n + 5] z = (Tantibar c)^[n] z
    rw [Function.iterate_add_apply, h]
  have hsucc : ∀ k, w (k + 1) = Tantibar c (w k) := by
    intro k
    show (Tantibar c)^[k + 1] z = Tantibar c ((Tantibar c)^[k] z)
    rw [Function.iterate_succ_apply']
  have hfun : ∀ i, (Work.Landing.Tsq c)^[i] z = w (2 * i) := by
    intro i
    rw [Work.ELRig.Tsq_eq_Tantibar_iterate_two, ← Function.iterate_mul]
  have hstep : ∀ i, deriv (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[i] z)
      = 4 * w (2 * i) * star (w (2 * i + 1)) := by
    intro i
    rw [hfun i, Work.ELRig.deriv_Tsq, ← Work.ELRig.star_Tantibar, ← hsucc (2 * i)]
  have hdiff : Differentiable ℂ (Work.Landing.Tsq c) := by
    show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
    fun_prop
  have hE : (∏ i ∈ Finset.range 5, w (2 * i)) = ∏ k ∈ Finset.range 5, w k := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    norm_num
    rw [show w 6 = w 1 from hper 1, show w 8 = w 3 from hper 3]
    ring
  have hH : (∏ i ∈ Finset.range 5, star (w (2 * i + 1)))
      = star (∏ k ∈ Finset.range 5, w k) := by
    rw [star_prod]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    norm_num
    rw [show w 5 = w 0 from hper 0, show w 7 = w 2 from hper 2, show w 9 = w 4 from hper 4]
    ring
  have hderiv : deriv ((Work.Landing.Tsq c)^[5]) z
      = (4 : ℂ) ^ 5 * ((∏ k ∈ Finset.range 5, w k) * star (∏ k ∈ Finset.range 5, w k)) := by
    rw [Work.ELRig.deriv_iterate_eq_prod hdiff]
    rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.range 5) => hstep i)]
    rw [show (∏ i ∈ Finset.range 5, (4 : ℂ) * w (2 * i) * star (w (2 * i + 1)))
          = ∏ i ∈ Finset.range 5, (4 : ℂ) * (w (2 * i) * star (w (2 * i + 1))) from
        Finset.prod_congr rfl (fun i _ => by ring)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Finset.prod_mul_distrib,
      hE, hH]
  have hmul : (∏ k ∈ Finset.range 5, w k) * star (∏ k ∈ Finset.range 5, w k)
      = ↑(Complex.normSq (∏ k ∈ Finset.range 5, w k)) := by
    rw [← starRingEnd_apply]
    exact Complex.mul_conj _
  have hns : Complex.normSq (∏ k ∈ Finset.range 5, w k)
      = (∏ k ∈ Finset.range 5, ‖w k‖) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, norm_prod]
  have hreal : (∏ k ∈ Finset.range 5, (2 * ‖w k‖) ^ 2 : ℝ)
      = (4 : ℝ) ^ 5 * (∏ k ∈ Finset.range 5, ‖w k‖) ^ 2 := by
    calc (∏ k ∈ Finset.range 5, (2 * ‖w k‖) ^ 2 : ℝ)
        = ∏ k ∈ Finset.range 5, (4 * ‖w k‖ ^ 2) := Finset.prod_congr rfl (fun k _ => by ring)
      _ = (∏ k ∈ Finset.range 5, (4 : ℝ)) * ∏ k ∈ Finset.range 5, ‖w k‖ ^ 2 :=
            Finset.prod_mul_distrib
      _ = (4 : ℝ) ^ 5 * ∏ k ∈ Finset.range 5, ‖w k‖ ^ 2 := by
            rw [Finset.prod_const, Finset.card_range]
      _ = (4 : ℝ) ^ 5 * (∏ k ∈ Finset.range 5, ‖w k‖) ^ 2 := by rw [Finset.prod_pow]
  have hfinal : (4 : ℂ) ^ 5 * ↑(Complex.normSq (∏ k ∈ Finset.range 5, w k))
      = (((∏ k ∈ Finset.range 5, (2 * ‖w k‖) ^ 2 : ℝ)) : ℂ) := by
    rw [hns, hreal]
    push_cast
    ring
  change deriv ((Work.Landing.Tsq c)^[5]) z
      = (((∏ k ∈ Finset.range 5, (2 * ‖w k‖) ^ 2 : ℝ)) : ℂ)
  rw [hderiv, hmul]
  exact hfinal

end Work.SeedCertNum
