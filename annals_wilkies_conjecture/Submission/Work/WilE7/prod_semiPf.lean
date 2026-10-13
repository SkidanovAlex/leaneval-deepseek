/-
  Area E7: `Work.WilE7.prod_semiPf`.

  The product `{z : ℝ^{k+k'} | projFirst z ∈ X.set ∧ projSnd z ∈ X'.set}` of two restricted
  semi-Pfaffian sets is again restricted semi-Pfaffian, with format bounded by `2 * F` and
  degree bounded by `2 * (1 + (X.deg + X'.deg))^2`, where `F` bounds both formats.

  The construction `SemiPf.prod` (with its defining lemmas, the evaluation rules
  `EAPoly.eaEval_prodL/prodR`, the basic-set semantics `Basic.holds_prod` and the degree
  bounds `Basic.prod_deg_le`, `redBasics_length_le`, `redBasics_deg_le`, `deg_bound_arith`)
  lives in `Submission.Work.WilE7.ProdDefs`.  This file records the two end results
  (`prodSet`: the point set; `prodDeg`: the degree bound) and assembles the statement.

  The format bound is immediate: `SemiPf.prod X X'` has format `(k + k') + (X.r + X'.r)`,
  which is `X.fmt + X'.fmt ≤ 2 * F`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.ProdDefs
import Submission.Work.WilE7.sumProduct
import Submission.Work.WilE7.cubeC_add
import Submission.Work.WilE7.prodSet
import Submission.Work.WilE7.prodDeg

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

theorem prod_semiPf (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (k k' : ℕ) (X : WilkiesDesign.E.SemiPf k)
      (X' : WilkiesDesign.E.SemiPf k'), X.fmt ≤ F → X'.fmt ≤ F →
      ∃ Z : WilkiesDesign.E.SemiPf (k + k'), Z.fmt ≤ a ∧ Z.deg ≤ b.eval (X.deg + X'.deg) ∧
        Z.set = {z : Fin (k + k') → ℝ | WilkiesDesign.E.projFirst k k' z ∈ X.set ∧
          WilkiesDesign.E.projSnd k k' z ∈ X'.set} := by
  refine ⟨2 * F, 2 * (1 + Polynomial.X) ^ 2, ?_⟩
  intro k k' X X' hX hX'
  refine ⟨SemiPf.prod X X', ?_, ?_, prodSet X X'⟩
  · have hf : (SemiPf.prod X X').fmt = X.fmt + X'.fmt := by
      simp only [SemiPf.fmt, SemiPf.prod_r]
      omega
    rw [hf]
    omega
  · have h := prodDeg X X'
    have hev : Polynomial.eval (X.deg + X'.deg) (2 * (1 + Polynomial.X) ^ 2 : Polynomial ℕ)
        = 2 * (1 + (X.deg + X'.deg)) ^ 2 := by simp
    rw [hev]
    exact h

end Work.WilE7
