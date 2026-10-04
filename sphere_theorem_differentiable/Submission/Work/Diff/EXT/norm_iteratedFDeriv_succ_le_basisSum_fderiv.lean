import Mathlib
import Submission.Work.Diff.EXT.clmApplyConstAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `(k+1)`-st jet is bounded by the `k`-th jets of the directional derivatives

For a smooth `φ : E → ℝ` on a finite-dimensional real normed space `E` and every `k`, the operator
norm of the `(k+1)`-st iterated Fréchet derivative of `φ` at `y` is bounded by a constant (depending
only on `E`) times the sum, over a basis `e_1, …, e_N` of `E`, of the norms of the `k`-th iterated
Fréchet derivatives of the directional derivatives `y' ↦ (fderiv ℝ φ y') e_a`:

`‖D^{k+1} φ y‖ ≤ C * ∑_a ‖D^k (∂_a φ) y‖`.

The constant is `C = ∑_a ‖coord_a‖` where `coord_a` is the `a`-th coordinate functional of
`Module.finBasis ℝ E`; in particular it is *independent of `k`*.

The proof peels the last argument of the `(k+1)`-st jet
(`iteratedFDeriv_succ_apply_right`) and expands that argument in the basis: for a tuple
`v : Fin (k+1) → E`,

`D^{k+1} φ y v = (D^k (fderiv ℝ φ) y) (Fin.init v) (v (Fin.last k))`,

the last argument is `∑_a coord_a (v (fin.last k)) • e_a`, and the continuous linear map
`(D^k (fderiv ℝ φ) y) (Fin.init v)` is linear, so the value is a sum of `N` terms; each of them is
bounded with `ContinuousMultilinearMap.le_opNorm` by the corresponding `D^k (∂_a φ) y`. The
identification `(D^k (fderiv ℝ φ) y) w e_a = D^k (∂_a φ) y w` is `Work.Diff.EXT.clmApplyConstAt`.
-/

open scoped BigOperators
open ContinuousLinearMap

namespace Work.Diff.EXT

/-- The constant `∑_a ‖coord_a‖` attached to `Module.finBasis ℝ E`. -/
private noncomputable def basisSumCoordConst (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : ℝ :=
  ∑ b : Fin (Module.finrank ℝ E),
    ‖LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord b)‖

private lemma basisSumCoordConst_nonneg (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : 0 ≤ basisSumCoordConst E := by
  simp only [basisSumCoordConst]
  exact Finset.sum_nonneg (fun b _ => norm_nonneg _)

/-- Every coordinate functional of `Module.finBasis ℝ E` is bounded by `basisSumCoordConst E`. -/
private lemma basisSum_coord_le (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (a : Fin (Module.finrank ℝ E)) (x : E) :
    ‖(Module.finBasis ℝ E).coord a x‖ ≤ basisSumCoordConst E * ‖x‖ := by
  have h1 := ContinuousLinearMap.le_opNorm
    (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord a)) x
  rw [LinearMap.coe_toContinuousLinearMap'] at h1
  have h2 : ‖LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord a)‖ ≤
      basisSumCoordConst E := by
    simp only [basisSumCoordConst]
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun b : Fin (Module.finrank ℝ E) =>
        ‖LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord b)‖)
      (fun b _ => norm_nonneg _) (Finset.mem_univ a)
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg x))

/-- The main estimate: the `(k+1)`-st jet is bounded by `basisSumCoordConst E` times the sum of
the `k`-th jets of the directional derivatives along the basis vectors. -/
private lemma basisSum_succ_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (k : ℕ) (φ : E → ℝ) (y : E)
    (hφ : ContDiffAt ℝ (⊤ : ℕ∞) φ y) :
    ‖iteratedFDeriv ℝ (k + 1) φ y‖ ≤ basisSumCoordConst E *
      ∑ a : Fin (Module.finrank ℝ E),
        ‖iteratedFDeriv ℝ k
          (fun y' : E => fderiv ℝ φ y' (Module.finBasis ℝ E a)) y‖ := by
  have hfder : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ φ) y := hφ.fderiv_right (by simp)
  have hS0 : 0 ≤ ∑ a : Fin (Module.finrank ℝ E),
        ‖iteratedFDeriv ℝ k
          (fun y' : E => fderiv ℝ φ y' (Module.finBasis ℝ E a)) y‖ :=
    Finset.sum_nonneg (fun a _ => norm_nonneg _)
  refine ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (basisSumCoordConst_nonneg E) hS0) ?_
  intro v
  have hMsum : iteratedFDeriv ℝ (k + 1) φ y v
      = ∑ a : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).coord a) (v (Fin.last k)) •
            (iteratedFDeriv ℝ k
              (fun y' : E => fderiv ℝ φ y' (Module.finBasis ℝ E a)) y) (Fin.init v) := by
    rw [iteratedFDeriv_succ_apply_right]
    conv_lhs => rw [← Module.Basis.sum_repr (Module.finBasis ℝ E) (v (Fin.last k))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, ← clmApplyConstAt (c := fderiv ℝ φ) hfder (i := k)
      (u := Module.finBasis ℝ E a) (m := Fin.init v)]
    rw [Module.Basis.coord_apply]
  have hB : ∀ a : Fin (Module.finrank ℝ E),
      ‖(iteratedFDeriv ℝ k
          (fun y' : E => fderiv ℝ φ y' (Module.finBasis ℝ E a)) y) (Fin.init v)‖ ≤
        ‖iteratedFDeriv ℝ k
          (fun y' : E => fderiv ℝ φ y' (Module.finBasis ℝ E a)) y‖ *
          (∏ i : Fin k, ‖(Fin.init v) i‖) :=
    fun a => ContinuousMultilinearMap.le_opNorm _ _
  have hprod : (∏ i : Fin (k + 1), ‖v i‖) =
      (∏ i : Fin k, ‖(Fin.init v) i‖) * ‖v (Fin.last k)‖ := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.init]
  calc ‖iteratedFDeriv ℝ (k + 1) φ y v‖
      = ‖∑ a : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).coord a) (v (Fin.last k)) •
            (iteratedFDeriv ℝ k
              (fun y' : E => fderiv ℝ φ y' (Module.finBasis ℝ E a)) y) (Fin.init v)‖ := by
        rw [hMsum]
    _ ≤ ∑ a : Fin (Module.finrank ℝ E),
          ‖((Module.finBasis ℝ E).coord a) (v (Fin.last k)) •
            (iteratedFDeriv ℝ k
              (fun y' : E => fderiv ℝ φ y' (Module.finBasis ℝ E a)) y) (Fin.init v)‖ :=
        norm_sum_le _ _
    _ = ∑ a : Fin (Module.finrank ℝ E),
          ‖((Module.finBasis ℝ E).coord a) (v (Fin.last k))‖ *
            ‖(iteratedFDeriv ℝ k
              (fun y' : E => fderiv ℝ φ y' (Module.finBasis ℝ E a)) y) (Fin.init v)‖ := by
        simp
    _ ≤ ∑ a : Fin (Module.finrank ℝ E),
          (basisSumCoordConst E * ‖v (Fin.last k)‖) *
            (‖iteratedFDeriv ℝ k
              (fun y' : E => fderiv ℝ φ y' (Module.finBasis ℝ E a)) y‖ *
              (∏ i : Fin k, ‖(Fin.init v) i‖)) :=
        Finset.sum_le_sum fun a _ => mul_le_mul
          (basisSum_coord_le E a (v (Fin.last k))) (hB a) (norm_nonneg _)
          (mul_nonneg (basisSumCoordConst_nonneg E) (norm_nonneg _))
    _ = (basisSumCoordConst E *
          (∑ a : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ k
              (fun y' : E => fderiv ℝ φ y' (Module.finBasis ℝ E a)) y‖)) *
          (∏ i : Fin (k + 1), ‖v i‖) := by
        rw [hprod]
        have h1 : (∑ a : Fin (Module.finrank ℝ E),
              (basisSumCoordConst E * ‖v (Fin.last k)‖) *
                (‖iteratedFDeriv ℝ k
                  (fun y' : E => fderiv ℝ φ y' (Module.finBasis ℝ E a)) y‖ *
                  (∏ i : Fin k, ‖(Fin.init v) i‖))) =
            ∑ a : Fin (Module.finrank ℝ E),
              (basisSumCoordConst E * (∏ i : Fin k, ‖(Fin.init v) i‖) *
                ‖v (Fin.last k)‖) *
                ‖iteratedFDeriv ℝ k
                  (fun y' : E => fderiv ℝ φ y' (Module.finBasis ℝ E a)) y‖ :=
          Finset.sum_congr rfl fun a _ => by ring
        rw [h1, ← Finset.mul_sum]
        ring

theorem norm_iteratedFDeriv_succ_le_basisSum_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ K, ∀ (φ : E → ℝ) (y : E),
      ContDiffAt ℝ (⊤ : ℕ∞) φ y →
      ‖iteratedFDeriv ℝ (k + 1) φ y‖ ≤ C * ∑ a : Fin (Module.finrank ℝ E),
        ‖iteratedFDeriv ℝ k (fun y' : E => fderiv ℝ φ y' (Module.finBasis ℝ E a)) y‖ :=
  ⟨basisSumCoordConst E, basisSumCoordConst_nonneg E,
    fun k _ φ y hφ => basisSum_succ_le k φ y hφ⟩

end Work.Diff.EXT
