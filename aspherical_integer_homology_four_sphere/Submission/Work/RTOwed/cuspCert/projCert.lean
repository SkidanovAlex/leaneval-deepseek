/-
# The projection certificate `projCert` of the truncation set `Tset`

This file proves `Work.RTOwed.cuspCert.projCert` (the first of the two certificates of the cover
data, see `Submission/Work/RTOwed/cuspCert/tsetCoverData.lean`):

  `π_a y := kleinPt a (kleinToX a y) = y + truncSlack (cubeVert a) y • projV a`.

## Method

`kleinPt a` is the affine map `x ↦ A_a x + b_a` of the cube `a` and `kleinToX a` its inverse
`y ↦ C_a y + d_a`; the rescaled *integral* tables

  `A10 a i j = 10 * (A_a)_{ij}`,  `b10 a i = 10 * (b_a)_i`   (`cube_quad.lean`),
  `C16 a k l = 16 * (C_a)_{kl}`,  `c16 a k = 16 * (d_a)_k`   (`CuspTabs.lean`),

together with the bridges `kleinPt_apply` / `kleinToX_apply` (`CuspSupport.lean`), turn the
composition `π_a` into the affine map whose coefficient matrix is
`PiZ a i l = ∑_j A10 a i j * C16 a j l` (over `160`) and whose constant part is
`OffZ a i = ∑_j A10 a i j * c16 a j + 16 * b10 a i` (over `160`).  The right hand side is affine in
`y` as well, with coefficient `160 * δ_{il} - 10 * projVZ a i * truncNormal2 (cubeVert a) l` and
constant `16 * projVZ a i` (all over `160`).  The two remaining certificates `projV_coef` and
`projV_const` are therefore *integral* identities, checked for the 48 × 4 × 4 (resp. 48 × 4)
instances by `decide`; the analytic assembly is done once, in coordinates.
-/
import Mathlib
import Submission.Work.RTOwed.cuspCert.tsetCoverData
import Submission.Work.RTOwed.cuspCert.CuspSupport

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped BigOperators

namespace Work.RTOwed.cuspCert

open Work.RTOwed

/-! ## Sum manipulations -/

/-- Swap the order of a double sum: for `Fin 3` and `Fin 4` indices. -/
theorem sum_swap_mul34 (F : Fin 3 → ℝ) (G : Fin 3 → Fin 4 → ℝ) (u : Fin 4 → ℝ) :
    (∑ j : Fin 3, F j * (∑ l : Fin 4, G j l * u l))
      = ∑ l : Fin 4, (∑ j : Fin 3, F j * G j l) * u l := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _
  ring

/-- The expansion of `∑_j F_j * ((∑_l G_{jl} u_l)/16 + c_j/16)` over the product index: this is the
composition of the affine maps `A10` and `C16/16`. -/
theorem sum_swap_div16 (F : Fin 3 → ℝ) (G : Fin 3 → Fin 4 → ℝ) (u : Fin 4 → ℝ) (c : Fin 3 → ℝ) :
    (∑ j : Fin 3, F j * ((∑ l : Fin 4, G j l * u l) / 16 + c j / 16))
      = (∑ l : Fin 4, (∑ j : Fin 3, F j * G j l) * u l) / 16
        + (∑ j : Fin 3, F j * c j) / 16 := by
  have h1 : ∀ j : Fin 3, F j * ((∑ l : Fin 4, G j l * u l) / 16 + c j / 16)
      = (F j * (∑ l : Fin 4, G j l * u l)) / 16 + F j * c j / 16 := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_add_distrib, ← Finset.sum_div,
    ← Finset.sum_div, sum_swap_mul34 F G u]

/-! ## The two coordinates of the identity -/

/-- The coefficient expansion of `π_a y = kleinPt a (kleinToX a y)` in the integral tables. -/
theorem lhs_coord (a : Fin 48) (y : CuspE4) (i : Fin 4) :
    (kleinPt a (kleinToX a y)) i
      = (∑ l : Fin 4, (∑ j : Fin 3, ((A10 a i j : ℤ) : ℝ) * ((C16 a j l : ℤ) : ℝ)) * y l) / 160
        + (∑ j : Fin 3, ((A10 a i j : ℤ) : ℝ) * ((c16 a j : ℤ) : ℝ)) / 160
        + ((b10 a i : ℤ) : ℝ) / 10 := by
  rw [kleinPt_apply]
  simp only [kleinToX_apply]
  rw [sum_swap_div16]
  ring

/-- The coordinate of the right hand side `y + truncSlack (cubeVert a) y • projV a`. -/
theorem rhs_coord (a : Fin 48) (y : CuspE4) (i : Fin 4) :
    (y + Work.FoldInst.truncSlack (Work.RTOwed.cubeVert a) y • projV a) i
      = y i
        + (8 - 5 * ∑ l : Fin 4,
              ((Work.FoldInst.truncNormal2 (Work.RTOwed.cubeVert a) l : ℤ) : ℝ) * y l) / 10
          * (((projVZ a i : ℤ) : ℝ) / 8) := by
  simp only [projV, Work.FoldInst.truncSlack, WithLp.ofLp_add, WithLp.ofLp_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-! ## The integral certificates -/

/-- The coefficient identity: `π_a` differs from the identity by the rank-one term
`-(10/160) * projVZ a i * truncNormal2 (cubeVert a) l`; i.e. the fibre direction of `π_a` is
`projV a` and its fibre coordinate is measured by the truncation slack. -/
theorem projV_coef : ∀ (a : Fin 48) (i l : Fin 4),
    (∑ j : Fin 3, A10 a i j * C16 a j l)
      + 10 * projVZ a i * Work.FoldInst.truncNormal2 (Work.RTOwed.cubeVert a) l
      = 160 * (if i = l then 1 else 0) := by
  decide

/-- The constant identity: `π_a 0 = (4/5) • projV a`, i.e. `OffZ a i = 16 * projVZ a i`. -/
theorem projV_const : ∀ (a : Fin 48) (i : Fin 4),
    (∑ j : Fin 3, A10 a i j * c16 a j) + 16 * b10 a i = 16 * projVZ a i := by
  decide

/-! ## The certificate -/

theorem projCert (a : Fin 48) (y : Work.RTOwed.cuspCert.CuspE4) :
    Work.RTOwed.kleinPt a (Work.RTOwed.kleinToX a y) =
      y + (Work.FoldInst.truncSlack (Work.RTOwed.cubeVert a) y) • Work.RTOwed.cuspCert.projV a := by
  apply WithLp.ofLp_injective 2
  funext i
  rw [lhs_coord a y i, rhs_coord a y i]
  have hP : ∀ l : Fin 4, (∑ j : Fin 3, ((A10 a i j : ℤ) : ℝ) * ((C16 a j l : ℤ) : ℝ))
      = 160 * (if i = l then (1 : ℝ) else 0)
        - 10 * ((projVZ a i : ℤ) : ℝ)
            * ((Work.FoldInst.truncNormal2 (Work.RTOwed.cubeVert a) l : ℤ) : ℝ) := by
    intro l
    have h := projV_coef a i l
    have h2 : (∑ j : Fin 3, ((A10 a i j : ℤ) : ℝ) * ((C16 a j l : ℤ) : ℝ))
        + 10 * ((projVZ a i : ℤ) : ℝ)
            * ((Work.FoldInst.truncNormal2 (Work.RTOwed.cubeVert a) l : ℤ) : ℝ)
        = 160 * (if i = l then (1 : ℝ) else 0) := by
      exact_mod_cast h
    linarith
  have hQ : (∑ j : Fin 3, ((A10 a i j : ℤ) : ℝ) * ((c16 a j : ℤ) : ℝ))
      = 16 * ((projVZ a i : ℤ) : ℝ) - 16 * ((b10 a i : ℤ) : ℝ) := by
    have h := projV_const a i
    have h2 : (∑ j : Fin 3, ((A10 a i j : ℤ) : ℝ) * ((c16 a j : ℤ) : ℝ))
        + 16 * ((b10 a i : ℤ) : ℝ) = 16 * ((projVZ a i : ℤ) : ℝ) := by
      exact_mod_cast h
    linarith
  simp only [hP, hQ]
  fin_cases i <;>
    simp only [Fin.sum_univ_four] <;>
    norm_num <;>
    ring

end Work.RTOwed.cuspCert
