/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the *scaled Rolle determinant* of
  the elimination step of K2 evaluated at a point.

  For `E : ETData N (rt+1) n re` the matrix `E.rolleMatP` (`Elim.lean`) has as its first `rt+1`
  rows the gradients of the arctan equations **scaled by** `1 + t_j²` (which clears the denominators
  `1/(1+t_j²)` in `∇(arctan t_j)`) and as its remaining rows the symbolic derivatives `dPoly` of the
  polynomial equations; its determinant is `E.rolleDetP`.  The Jacobian `E.jac z` has the same rows
  but with the denominators left in place.  Hence

  `E.evalPoly E.rolleDetP z = E.prodEval z * (E.jac z).det`,

  where `E.prodEval z = ∏_j (1 + t_j(z)²)` is the product of the scaling factors.  This is the
  pointwise algebraic input of the Rolle step: the analytic Rolle determinant
  `E.rolleDetFun z = E.evalPoly E.rolleDetP z / E.prodEval z` is turned by this identity into the
  polynomial expression `det (E.jac z)`.

  The proof: `MvPolynomial.eval` is a ring homomorphism, so it commutes with `Matrix.det`
  (`RingHom.map_det`); entrywise, evaluating the scaled `tan` row `dTanPoly j c` gives
  `(1 + t_j²) · dTanFun j z c`; the remaining rows are unaffected.  The evaluated matrix is thus
  `diagonal d * E.jac z` with `d r = if r < rt+1 then 1 + z r² else 1`, and
  `∏_r d r = ∏_j (1 + t_j²)` because `j ↦ tanCoord j` is a bijection onto the coordinates below
  `rt+1`.
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

namespace ETData

variable {N rt n re : ℕ}

/-! ## §1. Evaluating the scaled `tan` rows -/

theorem rolleDetP_evalPoly_zero (E : ETData N rt n re) (z : Fin (N + 1) → ℝ) :
    E.evalPoly (0 : EAPoly (N + 1) re) z = 0 := by
  simp [evalPoly]

theorem rolleDetP_evalPoly_one (E : ETData N rt n re) (z : Fin (N + 1) → ℝ) :
    E.evalPoly (1 : EAPoly (N + 1) re) z = 1 := by
  simp [evalPoly]

/-- The scaled `tan` row at a `tan` column: `1` on the diagonal, `0` off it. -/
theorem rolleDetP_dTanPoly_tan (E : ETData N (rt + 1) n re) (j j' : Fin (rt + 1)) :
    E.dTanPoly j (E.tanCoord j') = if j' = j then (1 : EAPoly (N + 1) re) else 0 := by
  have hlt : ((E.tanCoord j' : Fin (N + 1)) : ℕ) < rt + 1 := by
    simp only [tanCoord]; omega
  unfold dTanPoly
  rw [dif_pos hlt]
  by_cases h : j' = j
  · rw [h]; simp
  · rw [if_neg (fun hc => h (E.tanCoord_injective hc)), if_neg h]

/-- Evaluation of the scaled `tan` row at a `tan` column: the scaling factor `1 + t_j²` turns the
`dTanFun` entry `1/(1 + t_j²)` into `1`. -/
theorem rolleDetP_eval_dTanPoly_tan (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ)
    (j j' : Fin (rt + 1)) :
    E.evalPoly (E.dTanPoly j (E.tanCoord j')) z
      = (1 + z (E.tanCoord j) ^ 2) * E.dTanFun j z (E.tanCoord j') := by
  rw [E.rolleDetP_dTanPoly_tan j j']
  by_cases h : j' = j
  · rw [h]
    rw [if_pos rfl]
    rw [dTanFun_tan, if_pos rfl]
    rw [rolleDetP_evalPoly_one, one_div,
      mul_inv_cancel₀ (ne_of_gt (one_add_sq_pos z (E.tanCoord j)))]
  · rw [if_neg h]
    rw [dTanFun_tan, if_neg h, rolleDetP_evalPoly_zero, mul_zero]

/-- Evaluation of the scaled `tan` row at a free column. -/
theorem rolleDetP_eval_dTanPoly_free (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ)
    (j : Fin (rt + 1)) (i : Fin n) :
    E.evalPoly (E.dTanPoly j (E.freeCoord i)) z
      = (1 + z (E.tanCoord j) ^ 2) * E.dTanFun j z (E.freeCoord i) := by
  have hlt : ¬ (((E.freeCoord i : Fin (N + 1))) : ℕ) < rt + 1 := by
    simp only [freeCoord]; omega
  unfold dTanPoly
  rw [dif_neg hlt]
  rw [E.freeIndex_freeCoord i (not_lt.mp hlt), E.dTanFun_free j z i]
  simp only [evalPoly, Sum.elim_inl, map_neg, map_mul, map_add, map_one, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  ring

/-- **Entrywise evaluation of the scaled `tan` rows**: the row `j` of `E.rolleMatP` evaluated at `z`
is the scaling factor `1 + t_j(z)²` times the corresponding row of `E.jac z`. -/
theorem rolleDetP_eval_dTanPoly (E : ETData N (rt + 1) n re) (z : Fin (N + 1) → ℝ)
    (j : Fin (rt + 1)) (c : Fin (N + 1)) :
    E.evalPoly (E.dTanPoly j c) z = (1 + z (E.tanCoord j) ^ 2) * E.dTanFun j z c := by
  rcases E.eq_tanCoord_or_eq_freeCoord c with ⟨j', rfl⟩ | ⟨i, rfl⟩
  · exact E.rolleDetP_eval_dTanPoly_tan z j j'
  · exact E.rolleDetP_eval_dTanPoly_free z j i

end ETData

/-! ## §2. A product reindexing identity -/

/-- A product over `Fin m` whose `r`-th factor is trivial unless `r < k` is the product over
`Fin k` along the inclusion `Fin.castLE`. -/
theorem rolleDetP_prod_reindex {m k : ℕ} (h : k ≤ m) (g : Fin m → ℝ) :
    (∏ r : Fin m, (if (r : ℕ) < k then g r else 1)) = ∏ j : Fin k, g (Fin.castLE h j) := by
  rw [← Finset.prod_filter (s := Finset.univ) (p := fun r : Fin m => (r : ℕ) < k) (f := g)]
  refine Finset.prod_bij
    (fun (r : Fin m) (hr : r ∈ Finset.univ.filter (fun r : Fin m => (r : ℕ) < k)) =>
      Fin.castLT r (Finset.mem_filter.mp hr).2) ?_ ?_ ?_ ?_
  · intro a ha; exact Finset.mem_univ _
  · intro a1 h1 a2 h2 he
    exact Fin.ext (by simpa using congrArg Fin.val he)
  · intro b hb
    exact ⟨Fin.castLE h b,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using b.isLt⟩,
      Fin.ext rfl⟩
  · intro a ha
    show g a = g (Fin.castLE h (Fin.castLT a (Finset.mem_filter.mp ha).2))
    exact (congrArg g (Fin.ext rfl)).symm

/-! ## §3. The main identity -/

theorem evalPoly_rolleDetP {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re) :
    ∀ z : Fin (N + 1) → ℝ, E.evalPoly E.rolleDetP z = E.prodEval z * (E.jac z).det := by
  intro z
  -- the diagonal scaling factors and the coefficients of `g`
  set g : Fin (N + 1) → ℝ := fun r => 1 + z r ^ 2 with hg
  set dd : Fin (N + 1) → ℝ := fun r => if (r : ℕ) < rt + 1 then g r else 1 with hdd
  -- evaluation of `EAPoly` is a ring homomorphism
  set f : EAPoly (N + 1) re →+* ℝ :=
    MvPolynomial.eval (Sum.elim z fun j => Real.exp (E.ellChain j z)) with hf
  have hfapp : ∀ P : EAPoly (N + 1) re, f P = E.evalPoly P z := by
    intro P; rw [hf]; rfl
  have hA : E.evalPoly E.rolleDetP z = (f.mapMatrix E.rolleMatP).det := by
    rw [← hfapp E.rolleDetP, show E.rolleDetP = E.rolleMatP.det from rfl]
    exact RingHom.map_det f E.rolleMatP
  -- the evaluated Rolle matrix is the row-scaled Jacobian
  have hmap : f.mapMatrix E.rolleMatP = Matrix.diagonal dd * E.jac z := by
    ext r c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_mul, hfapp]
    by_cases hr : (r : ℕ) < rt + 1
    · have h1 : E.rolleMatP r c = E.dTanPoly (E.tanIndex r hr) c := by
        simp only [ETData.rolleMatP, Matrix.of_apply, dif_pos hr]
      have h2 : E.jac z r c = E.dTanFun (E.tanIndex r hr) z c := by
        simp only [ETData.jac, Matrix.of_apply, dif_pos hr]
      have h3 : dd r = 1 + z r ^ 2 := by
        rw [hdd]; simp only [hg]; exact if_pos hr
      rw [h1, h2, h3, ETData.rolleDetP_eval_dTanPoly]
      rw [show E.tanCoord (E.tanIndex r hr) = r from E.tanCoord_tanIndex r hr]
    · have h1 : E.rolleMatP r c = E.dPoly c (E.G (E.freeIndex r (not_lt.mp hr))) := by
        simp only [ETData.rolleMatP, Matrix.of_apply, dif_neg hr]
      have h2 : E.jac z r c
          = E.evalPoly (E.dPoly c (E.G (E.freeIndex r (not_lt.mp hr)))) z := by
        simp only [ETData.jac, Matrix.of_apply, dif_neg hr]
      have h3 : dd r = 1 := by
        rw [hdd]; simp only [hg]; exact if_neg hr
      rw [h1, h2, h3, one_mul]
  -- the product of the scaling factors is `E.prodEval z`
  have hh : rt + 1 ≤ N + 1 := by have h := E.h; omega
  have hprod : (∏ r : Fin (N + 1), dd r) = E.prodEval z := by
    rw [show E.prodEval z = ∏ j : Fin (rt + 1), (1 + z (E.tanCoord j) ^ 2) from rfl]
    have hL : (∏ r : Fin (N + 1), dd r)
        = ∏ r : Fin (N + 1), (if (r : ℕ) < rt + 1 then g r else 1) := by
      refine Finset.prod_congr rfl (fun r _ => ?_)
      simp only [hdd]
    rw [hL, rolleDetP_prod_reindex hh g]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [show Fin.castLE hh j = E.tanCoord j from Fin.ext rfl]
  rw [hA, hmap, Matrix.det_mul, Matrix.det_diagonal, hprod]

end Work.WilE3K
