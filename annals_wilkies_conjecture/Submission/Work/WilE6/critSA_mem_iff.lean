/-
  WilE6 (area E6): membership in the Taylor-criterion semialgebraic set `critSA`.

  This file: `critSA_mem_iff`, the statement that `pnt` lies in `critSA` exactly when the
  fibre conditions `critFibreCond` hold for one of the `k+1` `DNF` pieces.  This is a purely
  formal unfolding: `critSA` is the disjunction of the `critBasic` pieces (over
  `List.finRange (k+1)`) and `critFibreCond` spells out the fibre coordinates of `critBasic`.

  The auxiliary lemmas below are the vocabulary of that unfolding: evaluation of an
  `saPoly`-lifted polynomial against the empty chain, and a rearrangement of the summands of a
  witness equation (`a - b + c = 0` versus `c + a - b = 0`), which is the only place where
  the order of the summands in `critFibreCond` differs from the order in `critBasic`.
-/
import Mathlib
import Submission.Work.WilE6.CritSA

set_option autoImplicit false
noncomputable section
open Classical Topology

namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- Evaluating an `saPoly`-lifted polynomial against the empty chain (i.e. in the
semialgebraic reading of `critSA`) is ordinary polynomial evaluation. -/
theorem eaEval_nil_saPoly (m : ℕ) (Q : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    eaEval (EAChain.nil m) (saPoly m Q) x = MvPolynomial.eval x Q := by
  rw [eaEval_nil, eval_saPoly]

/-- Commutation of the summands of a witness equation: `a - b + c = 0` is `c + a - b = 0`.
This is the only arithmetic mismatch between the equations of `critBasic` and the
corresponding conjuncts of `critFibreCond`. -/
theorem critSA_shift_iff (c : Prop) [Decidable c] (a b d : ℝ) :
    ((if c then a else -a) - b + d = 0) ↔ ((if c then d + a else d + -a) - b = 0) := by
  by_cases hc : c
  · rw [ite_eq_left hc, ite_eq_left hc]
    constructor <;> intro h <;> linarith
  · rw [ite_eq_right hc, ite_eq_right hc]
    constructor <;> intro h <;> linarith

/-- Membership in the `j`-th basic set of `critSA` is exactly the `j`-th fibre condition. -/
theorem critBasic_holds_iff {k r p : ℕ} (hp : p ≤ k) (κ : ℕ)
    (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) (j : Fin (k + 1))
    (pnt : Fin (BP k r + FQ k p) → ℝ) :
    (critBasic (p := p) hp κ P Gs j).holds (EAChain.nil (BP k r + FQ k p)) pnt ↔
      critFibreCond (k := k) (r := r) (p := p) hp κ P Gs j pnt := by
  by_cases hj : (j : ℕ) < k
  · -- the attained index `j` is a genuine coordinate: the `atomJ` equation
    simp only [critBasic, critFibreCond, Basic.holds, dite_eq_left hj, List.forall_mem_append,
      List.forall_mem_map, List.mem_finRange, List.mem_singleton, and_assoc, true_implies, forall_eq,
      eaEval_nil_saPoly, atomMax, atomJ, atomTz, atomT0, atomWb, atomWe, polU, polT, polWm, polW0,
      polWb, polWe, polThr2, polThr1, atomPos, MvPolynomial.eval_X, MvPolynomial.eval_add,
      MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_rename, MvPolynomial.eval_neg,
      Function.comp_def, apply_ite, sub_pos]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      refine ⟨h1, h2, h3, fun b => ?_, fun e => ?_, h6⟩
      · exact (critSA_shift_iff (((b : ℕ) % 2 == 0) = true) _ _ _).mp (h4 b)
      · exact (critSA_shift_iff (e = 0) _ _ _).mp (h5 e)
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      refine ⟨h1, h2, h3, fun b => ?_, fun e => ?_, h6⟩
      · exact (critSA_shift_iff (((b : ℕ) % 2 == 0) = true) _ _ _).mpr (h4 b)
      · exact (critSA_shift_iff (e = 0) _ _ _).mpr (h5 e)
  · -- the attained index is the degenerate `k = 0` case: the `atomTz` equation
    simp only [critBasic, critFibreCond, Basic.holds, dite_eq_right hj, List.forall_mem_append,
      List.forall_mem_map, List.mem_finRange, List.mem_singleton, and_assoc, true_implies, forall_eq,
      eaEval_nil_saPoly, atomMax, atomJ, atomTz, atomT0, atomWb, atomWe, polU, polT, polWm, polW0,
      polWb, polWe, polThr2, polThr1, atomPos, MvPolynomial.eval_X, MvPolynomial.eval_add,
      MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_rename, MvPolynomial.eval_neg,
      Function.comp_def, apply_ite, sub_pos]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      refine ⟨h1, h2, h3, fun b => ?_, fun e => ?_, h6⟩
      · exact (critSA_shift_iff (((b : ℕ) % 2 == 0) = true) _ _ _).mp (h4 b)
      · exact (critSA_shift_iff (e = 0) _ _ _).mp (h5 e)
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      refine ⟨h1, h2, h3, fun b => ?_, fun e => ?_, h6⟩
      · exact (critSA_shift_iff (((b : ℕ) % 2 == 0) = true) _ _ _).mpr (h4 b)
      · exact (critSA_shift_iff (e = 0) _ _ _).mpr (h5 e)

theorem critSA_mem_iff {k r p : ℕ} (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) (pnt : Fin (Work.WilE6.BP k r + Work.WilE6.FQ k p) → ℝ) : pnt ∈ (Work.WilE6.critSA (p := p) hp κ P Gs).set ↔ ∃ j : Fin (k + 1), Work.WilE6.critFibreCond (k := k) (r := r) (p := p) hp κ P Gs j pnt := by
  simp only [SA.set, Set.mem_ofPred_eq, critSA, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨B, ⟨j, rfl⟩, hB⟩
    exact ⟨j, (critBasic_holds_iff hp κ P Gs j pnt).mp hB⟩
  · rintro ⟨j, hj⟩
    exact ⟨critBasic (p := p) hp κ P Gs j, ⟨j, rfl⟩, (critBasic_holds_iff hp κ P Gs j pnt).mpr hj⟩

end Work.WilE6
