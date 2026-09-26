import Mathlib
import Submission.Work.Drive.qwDefs
import Submission.Work.Drive.fourCombDefs
import Submission.Work.Drive.fourCombPoly
import Submission.Work.Drive.fourCombMain

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

/-! ## From the kernel bound to surjectivity -/

lemma fc_linSum_apply_coeff (D : Fin 9 → ℝ) (dc : Coeff) :
    linSum D dc = ∑ j : Fin 9, D j • dc j := by
  rw [linSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeffProj_apply]
  rfl

/-- The scalar four-jet evaluation map is surjective at separated windows. -/
theorem fcJetMap_surjective {τ : QP}
    (hsep : ∀ i j : Fin 4, i ≠ j → ∀ m : ℤ, qtp τ i - qtp τ j ≠ (m : ℝ) * period) :
    Function.Surjective (fcJetMap (qtp τ)) := by
  have hker := fc_finrank_ker_le_one (t := qtp τ) hsep
  have hle : Module.finrank ℝ (LinearMap.range (fcJetMap (qtp τ))) ≤ 8 := by
    have := Submodule.finrank_mono (le_top : LinearMap.range (fcJetMap (qtp τ)) ≤ ⊤)
    simpa using this
  have hrange : Module.finrank ℝ (LinearMap.range (fcJetMap (qtp τ))) = 8 := by
    have h := LinearMap.finrank_range_add_finrank_ker (fcJetMap (qtp τ))
    have hdom : Module.finrank ℝ (Fin 9 → ℝ) = 9 := by simp
    omega
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [hrange]
  simp [Module.finrank_prod]


open Work.Drive LeanEval.KnotTheory.Quadrisecant in
/-- **Value-preserving coefficient directions realize arbitrary velocity changes at a window.**

If the four parameters of a window are distinct modulo the period (`hsep`), then for every prescribed
four-tuple `w` of velocity changes there is a coefficient direction `dc` whose induced value changes
at the four parameters all vanish and whose induced perturbation-velocity changes are `w`.

Equivalently, the `8 × 9` real matrix with rows `V (t i)` and `D (t i)` (values and derivatives of
the nine trigonometric basis functions at the four parameters) has rank `8`.  A clean proof
(communicated by a reviewer): put `V = span {z ^ (-4), …, z ^ 4}` and `G (z) = z ^ 4 * F (z)` for
`F (z) = f (exp (t * I))`; then `f (t i) = (z i) ^ (-4) * G (z i)` and
`f' (t i) = I * (z i) ^ (-4) * G' (z i) - 4 * I * (z i) ^ (-5) * G (z i)`, an invertible triangular
transform, so independence of the evaluation and derivative-evaluation functionals is equivalent to
the independence of the Hermite functionals `G ↦ (G (z i), G' (z i))` on the polynomials of degree
at most `8`; their kernel is the one-dimensional space spanned by `∏ i, (z - z i) ^ 2`, hence the
rank is `8`.  A numerical rank check over random, structured and near-merged configurations always
returns `8`, with a genuine drop to `7` only when two parameters coincide modulo the period, which
`hsep` forbids. -/
theorem fourComb_surjective {τ : QP}
    (hsep : ∀ i j : Fin 4, i ≠ j → ∀ m : ℤ, qtp τ i - qtp τ j ≠ (m : ℝ) * period) :
    ∀ w : Fin 4 → Space, ∃ dc : Coeff,
      (∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0) ∧
      (∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasisD j (qtp τ i))) dc = w i) := by
  intro w
  have hsurj := fcJetMap_surjective hsep
  choose x hx using fun k : Fin 3 =>
    hsurj ((fun _ => (0 : ℝ)), fun i => spaceCoord k (w i))
  refine ⟨eCoeff.symm (fun j => spaceOfFun (fun k => x k j)), ?_, ?_⟩
  · intro i
    refine WithLp.ofLp_injective 2 (funext fun k => ?_)
    show spaceCoord k (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))
        (eCoeff.symm (fun j => spaceOfFun (fun k => x k j)))) = 0
    have h1 : spaceCoord k (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))
        (eCoeff.symm (fun j => spaceOfFun (fun k => x k j))))
        = ∑ j : Fin 9, trigBasis j (qtp τ i) * x k j := by
      rw [fc_linSum_apply_coeff, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
      congr 1
    rw [h1]
    have := congrFun (congrArg Prod.fst (hx k)) i
    simpa using this
  · intro i
    refine WithLp.ofLp_injective 2 (funext fun k => ?_)
    show spaceCoord k (linSum (fun j : Fin 9 => trigBasisD j (qtp τ i))
        (eCoeff.symm (fun j => spaceOfFun (fun k => x k j)))) = spaceCoord k (w i)
    have h1 : spaceCoord k (linSum (fun j : Fin 9 => trigBasisD j (qtp τ i))
        (eCoeff.symm (fun j => spaceOfFun (fun k => x k j))))
        = ∑ j : Fin 9, trigBasisD j (qtp τ i) * x k j := by
      rw [fc_linSum_apply_coeff, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
      congr 1
    rw [h1]
    have := congrFun (congrArg Prod.snd (hx k)) i
    simpa using this

end

end Work.Drive
