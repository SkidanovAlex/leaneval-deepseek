import Mathlib
import Submission.Work.WilC4.badScale_aux

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC4.BSpieces

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)

/-- `BSRatWBody Y` is `univ`-definable: it is the conjunction of the two reindexings of `Y`
(the value at `x`, and the value at the auxiliary slot `z`), the equation `z = 2x`, the
disequality `y ≠ 0` and the product equation `w * y = y'`. -/
theorem ratWBody_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (Set.univ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.BSAux.BSRatWBody Y) := by
  have h1 : (Set.univ : Set ℝ).Definable LRc
      (Work.WilC4.GrSub Y (Work.WilC4.BSAux.yEmb k)
        (Sum.inl (Work.WilC4.BSAux.sx : Work.WilC4.BSAux.BSI k))
        (Sum.inr (0 : Fin 3))) :=
    Work.WilC4.BSAux.univ_of_empty
      (Work.WilC4.GrSub_definable hY (Work.WilC4.BSAux.yEmb k)
        (Sum.inl (Work.WilC4.BSAux.sx : Work.WilC4.BSAux.BSI k))
        (Sum.inr (0 : Fin 3)))
  have h2 : (Set.univ : Set ℝ).Definable LRc
      (Work.WilC4.GrSub Y (Work.WilC4.BSAux.yEmb k)
        (Sum.inr (2 : Fin 3)) (Sum.inr (1 : Fin 3))) :=
    Work.WilC4.BSAux.univ_of_empty
      (Work.WilC4.GrSub_definable hY (Work.WilC4.BSAux.yEmb k)
        (Sum.inr (2 : Fin 3)) (Sum.inr (1 : Fin 3)))
  have h3 : (Set.univ : Set ℝ).Definable LRc
      {g : Work.WilC4.BSAux.BSR k → ℝ |
        g (Sum.inr (2 : Fin 3)) =
          2 * g (Sum.inl (Work.WilC4.BSAux.sx : Work.WilC4.BSAux.BSI k))} := by
    have h := Work.WilC4.definable_eval_eq_LRc (σ := Work.WilC4.BSAux.BSR k)
      (MvPolynomial.X (Sum.inr (2 : Fin 3)) -
        MvPolynomial.C 2 *
          MvPolynomial.X (Sum.inl (Work.WilC4.BSAux.sx : Work.WilC4.BSAux.BSI k))) 0
    convert h using 1
    ext g
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_sub,
      MvPolynomial.eval_C, MvPolynomial.eval_mul, sub_eq_zero]
  have h4 : (Set.univ : Set ℝ).Definable LRc
      {g : Work.WilC4.BSAux.BSR k → ℝ | g (Sum.inr (0 : Fin 3)) ≠ 0} := by
    have h := Work.WilC4.definable_ne_LRc (σ := Work.WilC4.BSAux.BSR k)
      (MvPolynomial.X (Sum.inr (0 : Fin 3))) 0
    convert h using 1
    ext g
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X, map_zero]
  have h5 : (Set.univ : Set ℝ).Definable LRc
      {g : Work.WilC4.BSAux.BSR k → ℝ |
        g (Sum.inl (Work.WilC4.BSAux.sw : Work.WilC4.BSAux.BSI k)) *
          g (Sum.inr (0 : Fin 3)) = g (Sum.inr (1 : Fin 3))} := by
    have h := Work.WilC4.definable_eval_eq_LRc (σ := Work.WilC4.BSAux.BSR k)
      (MvPolynomial.X (Sum.inl (Work.WilC4.BSAux.sw : Work.WilC4.BSAux.BSI k)) *
          MvPolynomial.X (Sum.inr (0 : Fin 3)) - MvPolynomial.X (Sum.inr (1 : Fin 3))) 0
    convert h using 1
    ext g
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_sub,
      MvPolynomial.eval_mul, sub_eq_zero]
  have hEq : Work.WilC4.BSAux.BSRatWBody Y =
      Work.WilC4.GrSub Y (Work.WilC4.BSAux.yEmb k)
          (Sum.inl (Work.WilC4.BSAux.sx : Work.WilC4.BSAux.BSI k))
          (Sum.inr (0 : Fin 3)) ∩
        Work.WilC4.GrSub Y (Work.WilC4.BSAux.yEmb k)
          (Sum.inr (2 : Fin 3)) (Sum.inr (1 : Fin 3)) ∩
        {g : Work.WilC4.BSAux.BSR k → ℝ |
          g (Sum.inr (2 : Fin 3)) =
            2 * g (Sum.inl (Work.WilC4.BSAux.sx : Work.WilC4.BSAux.BSI k))} ∩
        {g : Work.WilC4.BSAux.BSR k → ℝ | g (Sum.inr (0 : Fin 3)) ≠ 0} ∩
        {g : Work.WilC4.BSAux.BSR k → ℝ |
          g (Sum.inl (Work.WilC4.BSAux.sw : Work.WilC4.BSAux.BSI k)) *
            g (Sum.inr (0 : Fin 3)) = g (Sum.inr (1 : Fin 3))} := by
    ext g
    simp only [Work.WilC4.BSAux.BSRatWBody, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [hEq]
  exact (((h1.inter h2).inter h3).inter h4).inter h5

end Work.WilC4.BSpieces
