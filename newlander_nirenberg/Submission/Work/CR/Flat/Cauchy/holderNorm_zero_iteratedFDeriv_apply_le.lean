import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open Set

/-- Multilinear bound: evaluating the `m`-th iterated derivative at `v` costs at most
`∏ i, ‖v i‖` times the operator norm of the derivative. -/
lemma norm_iteratedFDerivWithin_apply_le {n m : ℕ} (f : (Fin n → ℂ) → ℂ)
    (s : Set (Fin n → ℂ)) (x : Fin n → ℂ) (v : Fin m → (Fin n → ℂ)) :
    ‖iteratedFDerivWithin ℝ m f s x v‖ ≤ (∏ i, ‖v i‖) * ‖iteratedFDerivWithin ℝ m f s x‖ := by
  rw [mul_comm]
  exact ContinuousMultilinearMap.le_opNorm _ _

/-- The same bound for the *difference* of two iterated derivatives. -/
lemma norm_iteratedFDerivWithin_apply_sub_le {n m : ℕ} (f : (Fin n → ℂ) → ℂ)
    (s : Set (Fin n → ℂ)) (x y : Fin n → ℂ) (v : Fin m → (Fin n → ℂ)) :
    ‖iteratedFDerivWithin ℝ m f s x v - iteratedFDerivWithin ℝ m f s y v‖
      ≤ (∏ i, ‖v i‖) * ‖iteratedFDerivWithin ℝ m f s x - iteratedFDerivWithin ℝ m f s y‖ := by
  rw [show iteratedFDerivWithin ℝ m f s x v - iteratedFDerivWithin ℝ m f s y v
      = ((iteratedFDerivWithin ℝ m f s x) - (iteratedFDerivWithin ℝ m f s y)) v from rfl,
    mul_comm]
  exact ContinuousMultilinearMap.le_opNorm _ _

/-- The norm of the difference of the `0`-th iterated derivatives is the distance of the values:
the `0`-th iterated derivative is just the function itself, read as a `0`-multilinear map. -/
private lemma norm_iteratedFDerivWithin_zero_sub {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (G : X → ℂ) (s : Set X) (x y : X) :
    ‖iteratedFDerivWithin ℝ 0 G s x - iteratedFDerivWithin ℝ 0 G s y‖ = ‖G x - G y‖ := by
  simpa [dist_eq_norm] using
    dist_iteratedFDerivWithin_zero (𝕜 := ℝ) (f := G) (s := s) (x := x) (g := G) (t := s) (y := y)

/-- The `C^{0,α}`-norm of `y ↦ D^m f(y)[v]` is bounded by `∏ i, ‖v i‖` times the `C^{k,α}`-norm
of `f` on all of `ℂⁿ`, whenever `m ≤ k`.  No smoothness of `f` is needed. -/
lemma holderNorm_zero_iteratedFDeriv_apply_le {n : ℕ} {m k : ℕ} (hm : m ≤ k) {α : ℝ}
    {f : (Fin n → ℂ) → ℂ} (v : Fin m → (Fin n → ℂ)) :
    holderNorm 0 α (fun y => iteratedFDeriv ℝ m f y v) Set.univ
      ≤ ENNReal.ofReal (∏ i, ‖v i‖) * holderNorm k α f Set.univ := by
  let g : (Fin n → ℂ) → ℂ := fun y => iteratedFDeriv ℝ m f y v
  have hg : ∀ x : Fin n → ℂ, g x = iteratedFDerivWithin ℝ m f Set.univ x v := by
    intro x
    show iteratedFDeriv ℝ m f x v = iteratedFDerivWithin ℝ m f Set.univ x v
    rw [← iteratedFDerivWithin_univ (𝕜 := ℝ) (f := f) (n := m)]
  show holderNorm 0 α g Set.univ ≤ ENNReal.ofReal (∏ i, ‖v i‖) * holderNorm k α f Set.univ
  have h1 : iterDerivNorm 0 g Set.univ
      ≤ ENNReal.ofReal (∏ i, ‖v i‖) * iterDerivNorm m f Set.univ := by
    rw [iterDerivNorm_zero]
    refine iSup₂_le fun x _ => ?_
    calc ENNReal.ofReal ‖g x‖
        = ENNReal.ofReal ‖iteratedFDerivWithin ℝ m f Set.univ x v‖ := by rw [hg x]
      _ ≤ ENNReal.ofReal ((∏ i, ‖v i‖) * ‖iteratedFDerivWithin ℝ m f Set.univ x‖) :=
          ENNReal.ofReal_le_ofReal (norm_iteratedFDerivWithin_apply_le f Set.univ x v)
      _ = ENNReal.ofReal (∏ i, ‖v i‖)
            * ENNReal.ofReal ‖iteratedFDerivWithin ℝ m f Set.univ x‖ :=
          ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => norm_nonneg _)
      _ ≤ ENNReal.ofReal (∏ i, ‖v i‖) * iterDerivNorm m f Set.univ :=
          mul_le_mul_right (le_iterDerivNorm m f Set.univ (Set.mem_univ x)) _
  have h2 : holderSeminorm 0 α g Set.univ
      ≤ ENNReal.ofReal (∏ i, ‖v i‖) * holderSeminorm m α f Set.univ := by
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
    have hpos : (0 : ℝ) < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    have hdiff : ‖g x - g y‖
        ≤ (∏ i, ‖v i‖) * ‖iteratedFDerivWithin ℝ m f Set.univ x
            - iteratedFDerivWithin ℝ m f Set.univ y‖ := by
      rw [hg x, hg y]
      exact norm_iteratedFDerivWithin_apply_sub_le f Set.univ x y v
    calc ENNReal.ofReal (‖iteratedFDerivWithin ℝ 0 g Set.univ x
            - iteratedFDerivWithin ℝ 0 g Set.univ y‖ / ‖x - y‖ ^ α)
        = ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α) := by
          rw [norm_iteratedFDerivWithin_zero_sub]
      _ ≤ ENNReal.ofReal (((∏ i, ‖v i‖) * ‖iteratedFDerivWithin ℝ m f Set.univ x
            - iteratedFDerivWithin ℝ m f Set.univ y‖) / ‖x - y‖ ^ α) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hdiff hpos.le)
      _ = ENNReal.ofReal (∏ i, ‖v i‖) * ENNReal.ofReal
            (‖iteratedFDerivWithin ℝ m f Set.univ x
              - iteratedFDerivWithin ℝ m f Set.univ y‖ / ‖x - y‖ ^ α) := by
          rw [mul_div_assoc, ENNReal.ofReal_mul
            (Finset.prod_nonneg fun i _ => norm_nonneg _)]
      _ ≤ ENNReal.ofReal (∏ i, ‖v i‖) * holderSeminorm m α f Set.univ :=
          mul_le_mul_right
            (le_holderSeminorm m α f Set.univ (Set.mem_univ x) (Set.mem_univ y) hxy) _
  have h3 : iterDerivNorm m f Set.univ + holderSeminorm m α f Set.univ
      ≤ holderNorm k α f Set.univ :=
    Finset.single_le_sum (f := fun i => iterDerivNorm i f Set.univ + holderSeminorm i α f Set.univ)
      (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  calc holderNorm 0 α g Set.univ
      = iterDerivNorm 0 g Set.univ + holderSeminorm 0 α g Set.univ := by simp [holderNorm]
    _ ≤ ENNReal.ofReal (∏ i, ‖v i‖) * iterDerivNorm m f Set.univ
          + ENNReal.ofReal (∏ i, ‖v i‖) * holderSeminorm m α f Set.univ := add_le_add h1 h2
    _ = ENNReal.ofReal (∏ i, ‖v i‖)
          * (iterDerivNorm m f Set.univ + holderSeminorm m α f Set.univ) := by rw [mul_add]
    _ ≤ ENNReal.ofReal (∏ i, ‖v i‖) * holderNorm k α f Set.univ := mul_le_mul_right h3 _

end Work.CR.Flat.Cauchy
