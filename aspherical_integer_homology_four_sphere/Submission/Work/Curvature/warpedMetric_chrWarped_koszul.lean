import Mathlib
import Submission.Work.Curvature.Basic
import Submission.Work.Curvature.Deriv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Curvature

/-- `F² · (D / F) = F · D` when `F ≠ 0`.  This is the elementary cancellation
behind the diagonal entries `Γ¹_{·}` and `Γ²_{·}`, `Γ³_{·}` of the warped
Christoffel symbol, which involve `deriv f / f` while the metric carries a factor
`f²`. -/
private lemma sq_mul_div_of_ne {F D : ℝ} (hF : F ≠ 0) : F ^ 2 * (D / F) = F * D := by
  rw [sq, mul_assoc, mul_comm F (D / F), div_mul_cancel₀ D hF]

/-- The reverse orientation of `sq_mul_div_of_ne`, used to convert the products
`deriv f · f` appearing on the right of the Koszul formula into the shape
`f² · (deriv f / f)` in which they occur on the left. -/
private lemma mul_eq_sq_mul_div {F D : ℝ} (hF : F ≠ 0) : D * F = F ^ 2 * (D / F) := by
  rw [eq_comm, sq_mul_div_of_ne hF, mul_comm]

/-- **The Christoffel symbol of the warped metric satisfies the Koszul formula.**

This is the defining property of `chrWarped`: it is the (unique, by
`koszulChr_eq_of_forall`) vector `z` with `warpedMetric f h q z c =
koszulRHS (warpedMetric f h) q a b c` for all `c`; consequently the abstract
`koszulChr (warpedMetric f h) q a b` equals the explicit `chrWarped f h q a b`.

The proof expands both sides: the right hand side is evaluated with
`dG_warpedMetric`, the left hand side with the components of `chrWarped`, the
products `deriv f · f`, `deriv h · h` on the right are rewritten into the
divided shape `f² · (deriv f / f)`, `h² · (deriv h / h)` (using the nonvanishing
hypotheses), and the two polynomial expressions are compared. -/
theorem warpedMetric_chrWarped_koszul (f h : ℝ → ℝ) (q : E4) (a b c : E4)
    (hfd : DifferentiableAt ℝ f (q 0)) (hhd : DifferentiableAt ℝ h (q 0))
    (hf0 : f (q 0) ≠ 0) (hh0 : h (q 0) ≠ 0) :
    warpedMetric f h q (chrWarped f h q a b) c
      = koszulRHS (warpedMetric f h) q a b c := by
  rw [koszulRHS, dG_warpedMetric f h a c b q hfd hhd,
    dG_warpedMetric f h b c a q hfd hhd, dG_warpedMetric f h a b c q hfd hhd]
  simp [warpedMetric_apply, chrWarped]
  rw [mul_eq_sq_mul_div hf0, mul_eq_sq_mul_div hh0]
  field_simp
  ring

end Work.Curvature
