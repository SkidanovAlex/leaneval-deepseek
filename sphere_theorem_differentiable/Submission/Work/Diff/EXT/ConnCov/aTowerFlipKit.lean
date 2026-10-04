import Mathlib
import Submission.Work.Diff.EXT.ConnCov.aTowerMovingDefs
import Submission.Work.Diff.EXT.ConnCov.Kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary kit for the moving-tower conversion (`aTower_moving_bound`)

This module collects the *elementary* lemmas that the proof of
`Work.Diff.EXT.ConnCov.aTower_moving_bound` needs and that are independent of the analytic core:

* monotonicity of the bound shape `AMB.Bnd1` in the constant (`Bnd1_mono_const`);
* product bookkeeping for the insertion (`prod_update_succ_le`);
* **closure of `Bnd1` under the insertion** `AMB.Ins` (`Bnd1_ins`), given the pointwise bound of the
  inserted `(1,2)`-tensor `δ` — the elementary half of the "insertion Leibniz": the extra factor
  `(1 + ‖δ(X,Z)‖)` produced by the substitution is *the* `(1 + ‖direction‖)` factor of the new slot,
  so no factor of the product is ever double-counted.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov

namespace AMB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

section Mono

variable {G : ℝ → Submission.Diff.SMet I M} {t : ℝ}

/-- Monotonicity of `Bnd1` in the constant. -/
theorem Bnd1_mono_const {N : ℕ} {τ : Fam (I := I) (M := M) N} {C C' : ℝ} (hC : 0 ≤ C)
    (h : Bnd1 G t τ C) (hCC : C ≤ C') : Bnd1 G t τ C' := by
  intro F x hF
  refine le_trans (h F x hF) ?_
  have hnn : 0 ≤ ∏ j : Fin N, (1 + Real.sqrt ((G t).inner x (F j x) (F j x))) :=
    Finset.prod_nonneg (fun j _ => by positivity)
  calc C * ∏ j : Fin N, (1 + Real.sqrt ((G t).inner x (F j x) (F j x)))
      ≤ C' * ∏ j : Fin N, (1 + Real.sqrt ((G t).inner x (F j x) (F j x))) :=
        mul_le_mul_of_nonneg_right hCC hnn

end Mono

section Ins

variable {G : ℝ → Submission.Diff.SMet I M} {t : ℝ}

/-- **Product bookkeeping for `Bnd1_ins`.**  Replacing the `j`-th factor of a product of numbers
`≥ 1` by a value bounded by `(1+c) · u (j+1) · u 0` costs only the factor `(1+c)`. -/
lemma prod_update_succ_le {N : ℕ} (u : Fin (N + 1) → ℝ) (j : Fin N) {w c : ℝ}
    (hu : ∀ s, 1 ≤ u s) (hc : 0 ≤ c)
    (hw : w ≤ (1 + c) * u (Fin.succ j) * u 0) :
    w * ∏ i ∈ Finset.univ \ {j}, u (Fin.succ i) ≤ (1 + c) * ∏ s : Fin (N + 1), u s := by
  have hsplit : ∏ s : Fin (N + 1), u s
      = u (Fin.succ j) * (u 0 * ∏ i ∈ Finset.univ \ {j}, u (Fin.succ i)) := by
    rw [Fin.prod_univ_succ]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton j (fun i : Fin N => u (Fin.succ i))
      (fun h => (h (Finset.mem_univ j)).elim)]
    ring
  rw [hsplit]
  have h1 : 0 ≤ ∏ i ∈ Finset.univ \ {j}, u (Fin.succ i) :=
    Finset.prod_nonneg (fun i _ => le_trans zero_le_one (hu _))
  have h2 : 0 ≤ u 0 := le_trans zero_le_one (hu 0)
  have h3 : 0 ≤ u (Fin.succ j) := le_trans zero_le_one (hu _)
  calc w * ∏ i ∈ Finset.univ \ {j}, u (Fin.succ i)
      ≤ ((1 + c) * u (Fin.succ j) * u 0) * ∏ i ∈ Finset.univ \ {j}, u (Fin.succ i) :=
        mul_le_mul_of_nonneg_right hw h1
    _ = (1 + c) * (u (Fin.succ j) * (u 0 * ∏ i ∈ Finset.univ \ {j}, u (Fin.succ i))) := by
        ring

/-- **Closure of `Bnd1` under the insertion** `Ins δ`.  If `δ` is pointwise bounded by
`c (1+‖X‖)(1+‖Z‖)` in the `G t`-metric and is smooth on smooth fields, then the insertion `Ins δ τ`
satisfies `Bnd1` with constant `C (N+1) (1+c)`. -/
theorem Bnd1_ins {N : ℕ} {τ : Fam (I := I) (M := M) N} {C : ℝ} (hC : 0 ≤ C)
    (h : Bnd1 G t τ C) {δ : Tens12 (I := I) (M := M)} {c : ℝ} (hc : 0 ≤ c)
    (hδ : ∀ (X Z : TF (I := I) (M := M)), Work.Diff.EXT.ATower.SmE I M X →
      Work.Diff.EXT.ATower.SmE I M Z → ∀ x : M,
      Real.sqrt ((G t).inner x (δ X Z x) (δ X Z x))
        ≤ c * (1 + Real.sqrt ((G t).inner x (X x) (X x)))
            * (1 + Real.sqrt ((G t).inner x (Z x) (Z x))))
    (hδsm : ∀ (X Z : TF (I := I) (M := M)), Work.Diff.EXT.ATower.SmE I M X →
      Work.Diff.EXT.ATower.SmE I M Z → Work.Diff.EXT.ATower.SmE I M (δ X Z)) :
    Bnd1 G t (Ins δ τ) (C * ((N : ℝ) + 1) * (1 + c)) := by
  intro F x hF
  -- pointwise bound of the inserted field in "1+‖·‖" form
  have hins : ∀ j : Fin N,
      1 + Real.sqrt ((G t).inner x (δ (F (Fin.succ j)) (F 0) x)
        (δ (F (Fin.succ j)) (F 0) x))
      ≤ (1 + c) * (1 + Real.sqrt ((G t).inner x (F (Fin.succ j) x) (F (Fin.succ j) x)))
          * (1 + Real.sqrt ((G t).inner x (F 0 x) (F 0 x))) := by
    intro j
    have h1 := hδ (F (Fin.succ j)) (F 0) (hF _) (hF 0) x
    rw [mul_assoc] at h1
    have ha := Real.sqrt_nonneg ((G t).inner x (F (Fin.succ j) x) (F (Fin.succ j) x))
    have hb := Real.sqrt_nonneg ((G t).inner x (F 0 x) (F 0 x))
    have h2 : 1 ≤ (1 + Real.sqrt ((G t).inner x (F (Fin.succ j) x) (F (Fin.succ j) x)))
        * (1 + Real.sqrt ((G t).inner x (F 0 x) (F 0 x))) := by nlinarith
    calc 1 + Real.sqrt ((G t).inner x (δ (F (Fin.succ j)) (F 0) x)
            (δ (F (Fin.succ j)) (F 0) x))
        ≤ 1 + c * ((1 + Real.sqrt ((G t).inner x (F (Fin.succ j) x) (F (Fin.succ j) x)))
            * (1 + Real.sqrt ((G t).inner x (F 0 x) (F 0 x)))) := by linarith
      _ ≤ (1 + Real.sqrt ((G t).inner x (F (Fin.succ j) x) (F (Fin.succ j) x)))
            * (1 + Real.sqrt ((G t).inner x (F 0 x) (F 0 x)))
          + c * ((1 + Real.sqrt ((G t).inner x (F (Fin.succ j) x) (F (Fin.succ j) x)))
            * (1 + Real.sqrt ((G t).inner x (F 0 x) (F 0 x)))) := by linarith
      _ = (1 + c) * (1 + Real.sqrt ((G t).inner x (F (Fin.succ j) x) (F (Fin.succ j) x)))
          * (1 + Real.sqrt ((G t).inner x (F 0 x) (F 0 x))) := by ring
  have hmain : ∀ j : Fin N,
      |τ (Function.update (fun i : Fin N => F (Fin.succ i)) j (δ (F (Fin.succ j)) (F 0))) x|
        ≤ C * (1 + c) * ∏ s : Fin (N + 1),
            (1 + Real.sqrt ((G t).inner x (F s x) (F s x))) := by
    intro j
    have hsm : ∀ i, Work.Diff.EXT.ATower.SmE I M
        ((Function.update (fun i : Fin N => F (Fin.succ i)) j (δ (F (Fin.succ j)) (F 0))) i) := by
      intro i
      rw [Function.update_apply]
      split_ifs with hij
      · exact hδsm (F (Fin.succ j)) (F 0) (hF _) (hF 0)
      · exact hF _
    refine le_trans (h _ x hsm) ?_
    -- the product over `τ`'s slots with the `j`-th factor replaced
    have hprod : ∏ i : Fin N, (1 + Real.sqrt ((G t).inner x
          (Function.update (fun i : Fin N => F (Fin.succ i)) j (δ (F (Fin.succ j)) (F 0)) i x)
          (Function.update (fun i : Fin N => F (Fin.succ i)) j (δ (F (Fin.succ j)) (F 0)) i x)))
        = (1 + Real.sqrt ((G t).inner x (δ (F (Fin.succ j)) (F 0) x)
              (δ (F (Fin.succ j)) (F 0) x)))
          * ∏ i ∈ Finset.univ \ {j},
              (1 + Real.sqrt ((G t).inner x (F (Fin.succ i) x) (F (Fin.succ i) x))) := by
      have hfun : (fun i : Fin N => 1 + Real.sqrt ((G t).inner x
            (Function.update (fun i : Fin N => F (Fin.succ i)) j
              (δ (F (Fin.succ j)) (F 0)) i x)
            (Function.update (fun i : Fin N => F (Fin.succ i)) j
              (δ (F (Fin.succ j)) (F 0)) i x)))
          = Function.update (fun i : Fin N => 1 + Real.sqrt ((G t).inner x
              (F (Fin.succ i) x) (F (Fin.succ i) x))) j
            (1 + Real.sqrt ((G t).inner x (δ (F (Fin.succ j)) (F 0) x)
              (δ (F (Fin.succ j)) (F 0) x))) := by
        funext i
        by_cases hij : i = j
        · subst hij
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hij, Function.update_of_ne hij]
      rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ j)]
    rw [hprod]
    rw [show C * (1 + c) * ∏ s : Fin (N + 1),
          (1 + Real.sqrt ((G t).inner x (F s x) (F s x)))
        = C * ((1 + c) * ∏ s : Fin (N + 1),
          (1 + Real.sqrt ((G t).inner x (F s x) (F s x)))) from by ring]
    refine mul_le_mul_of_nonneg_left ?_ hC
    exact prod_update_succ_le (fun s : Fin (N + 1) =>
        (1 + Real.sqrt ((G t).inner x (F s x) (F s x)))) j
      (fun s => by have := Real.sqrt_nonneg ((G t).inner x (F s x) (F s x)); linarith) hc (hins j)
  calc |Ins δ τ F x|
      = |∑ j : Fin N, τ (Function.update (fun i : Fin N => F (Fin.succ i)) j
          (δ (F (Fin.succ j)) (F 0))) x| := by rw [Ins]
    _ ≤ ∑ j : Fin N, |τ (Function.update (fun i : Fin N => F (Fin.succ i)) j
          (δ (F (Fin.succ j)) (F 0))) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, C * (1 + c) * ∏ s : Fin (N + 1),
          (1 + Real.sqrt ((G t).inner x (F s x) (F s x))) := Finset.sum_le_sum (fun j _ => hmain j)
    _ = (N : ℝ) * (C * (1 + c) * ∏ s : Fin (N + 1),
          (1 + Real.sqrt ((G t).inner x (F s x) (F s x)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ C * ((N : ℝ) + 1) * (1 + c) * ∏ s : Fin (N + 1),
          (1 + Real.sqrt ((G t).inner x (F s x) (F s x))) := by
        have hprodnn : 0 ≤ ∏ s : Fin (N + 1),
            (1 + Real.sqrt ((G t).inner x (F s x) (F s x))) :=
          Finset.prod_nonneg (fun j _ => by positivity)
        have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        have h1 : (N : ℝ) * (C * (1 + c) * ∏ s : Fin (N + 1),
              (1 + Real.sqrt ((G t).inner x (F s x) (F s x))))
            ≤ ((N : ℝ) + 1) * (C * (1 + c) * ∏ s : Fin (N + 1),
              (1 + Real.sqrt ((G t).inner x (F s x) (F s x)))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        calc (N : ℝ) * (C * (1 + c) * ∏ s : Fin (N + 1),
              (1 + Real.sqrt ((G t).inner x (F s x) (F s x))))
            ≤ ((N : ℝ) + 1) * (C * (1 + c) * ∏ s : Fin (N + 1),
              (1 + Real.sqrt ((G t).inner x (F s x) (F s x)))) := h1
          _ = C * ((N : ℝ) + 1) * (1 + c) * ∏ s : Fin (N + 1),
              (1 + Real.sqrt ((G t).inner x (F s x) (F s x))) := by ring

end Ins

end AMB

end Work.Diff.EXT.ConnCov
