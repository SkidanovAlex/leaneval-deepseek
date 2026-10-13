import Mathlib
import Submission.Work.WilC4aCS.Defs

namespace Work.WilC4aCS

open WilkiesDesign WilkiesDesign.E

/-- Evaluating a `0`-chain atom is the same as `ev0`: the chain is empty, so the two
evaluation maps `Sum.elim v (fun j : Fin 0 => exp …)` and `Sum.elim v (fun _ : Fin 0 => 0)`
agree. -/
lemma eaEval_nil {m : ℕ} (v : Fin m → ℝ) (p : EAPoly m 0) :
    E.eaEval (E.EAChain.nil m) p v = ev0 v p := by
  have h : (Sum.elim v fun j : Fin 0 => Real.exp ((E.EAChain.nil m).ell j v))
      = (Sum.elim v fun _ : Fin 0 => (0 : ℝ)) := by
    funext s
    rcases s with i | j
    · rfl
    · exact j.elim0
  unfold E.eaEval ev0
  rw [h]

/-- The semialgebraic set `SAcoef l d τ` in coefficient space is exactly the set of coefficient
vectors whose Weierstrass polynomials satisfy `Q₀ = 0` and `τⱼ · Q_{j+1} > 0`. -/
theorem SAcoef_set (l : ℕ) (d : Fin (l + 1) → ℕ) (τ : Fin l → ℝ) :
    WilkiesDesign.E.SA.set (Work.WilC4aCS.SAcoef l d τ) =
      {v : Fin (∑ i, d i + 1) → ℝ |
        Work.WilC4aCS.ev0 v (Work.WilC4aCS.Qpoly d 0) = 0 ∧
        ∀ j : Fin l, 0 < τ j * Work.WilC4aCS.ev0 v (Work.WilC4aCS.Qpoly d (Fin.succ j))} := by
  ext v
  simp only [SAcoef, E.SA.set, E.Basic.holds, Set.mem_ofPred_eq, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, exists_eq_left, List.forall_mem_ofFn_iff]
  have hn : ∀ p : EAPoly (∑ i, d i + 1) 0,
      E.eaEval (E.EAChain.nil (∑ i, d i + 1)) p v = ev0 v p := fun p => eaEval_nil v p
  simp only [hn, ev0, MvPolynomial.eval_mul, MvPolynomial.eval_C]

end Work.WilC4aCS
