import Mathlib
import Submission.Work.Mostow.poAux

/-!
# Continuity of the `O(n,1)` action on the chart and of the time sign

`actO A u = WithLp.toLp 2 (fun i => tsign A * (mat A *ᵥ hlift u) (Sum.inl i))`, so its joint
continuity in `(A, u)` reduces to the continuity of `mat`, of `hlift` and of `tsign`.
The latter is the only non-structural point: `tsign` is the locally constant function
`A ↦ |A₀₀| / A₀₀`, which is continuous because `A₀₀ ≠ 0` on `O(n,1)`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-- The underlying matrix of an element of `O(n,1)` depends continuously on it. -/
lemma cont_mat : Continuous (mat (n := n)) := by
  unfold mat
  fun_prop

/-- The time coordinate `√(1+‖u‖²)` is continuous. -/
lemma cont_tpart : Continuous (tpart (n := n)) := by
  unfold tpart
  fun_prop

/-- The hyperboloid lift `u ↦ (u, √(1+‖u‖²))` is continuous. -/
lemma cont_hlift : Continuous (hlift (n := n)) := by
  rw [continuous_pi_iff]
  intro a
  rcases a with i | j
  · simpa [hlift] using PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simpa [hlift] using cont_tpart

/-- The time-time matrix coefficient is continuous on `O(n,1)`. -/
lemma cont_tt : Continuous (fun A : O1 n => mat A (Sum.inr 0) (Sum.inr 0)) :=
  (continuous_apply (Sum.inr 0)).comp ((continuous_apply (Sum.inr 0)).comp cont_mat)

/-- `tsign` is the sign of the continuous, nowhere vanishing function `A ↦ A₀₀`. -/
lemma tsign_eq_abs_div (A : O1 n) :
    tsign A = |mat A (Sum.inr 0) (Sum.inr 0)| / mat A (Sum.inr 0) (Sum.inr 0) := by
  rcases lt_or_gt_of_ne (O1_tt_ne_zero A) with h | h
  · rw [tsign, if_neg (not_lt.2 h.le), abs_of_neg h, neg_div, div_self (ne_of_lt h)]
  · rw [tsign, if_pos h, abs_of_pos h, div_self (ne_of_gt h)]

/-- The time sign is continuous. -/
lemma cont_tsign : Continuous (tsign (n := n)) := by
  rw [show tsign (n := n) = fun A : O1 n =>
      |mat A (Sum.inr 0) (Sum.inr 0)| / mat A (Sum.inr 0) (Sum.inr 0) from funext tsign_eq_abs_div]
  exact Continuous.div (continuous_abs.comp cont_tt) cont_tt (fun A => O1_tt_ne_zero A)

/-- The action of `O(n,1)` on the chart space is jointly continuous. -/
lemma cont_actO : Continuous (fun p : O1 n × E n => actO p.1 p.2) := by
  change Continuous (fun p : O1 n × E n =>
    WithLp.toLp 2 (fun i => tsign p.1 * ((mat p.1).mulVec (hlift p.2)) (Sum.inl i)))
  refine (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp ?_
  rw [continuous_pi_iff]
  intro i
  refine (cont_tsign.comp continuous_fst).mul ?_
  exact (continuous_apply (Sum.inl i)).comp
    (Continuous.matrix_mulVec (cont_mat.comp continuous_fst) (cont_hlift.comp continuous_snd))

theorem poActCont (n : ℕ) :
    Continuous (fun p : O1 n × E n => actO p.1 p.2) ∧ Continuous (tsign : O1 n → ℝ) :=
  ⟨cont_actO, cont_tsign⟩

end

end Work.Mostow
