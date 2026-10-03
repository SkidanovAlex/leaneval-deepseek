/-
# The bridge between `zmodAvg (negReflect P)` and `polyBilinearAverageZMod X P`

The workspace carries two arithmetic bilinear averaging operators on `ℤ/Qℤ`:

* `Work.KMTPlan.A6.zmodAvg P Q u v θ = Q⁻¹ ∑_{y < Q} u (θ + y) · v (θ + P y)` — the
  "plus-sign" convention in which the adelic lift and the frozen-slice assembly
  (`MdlAdelicFormPlusDefs.lean`, `MdlSliceCoreGainMemLp2.lean`) are stated;
* `Work.Analysis.Concentration.polyBilinearAverageZMod P₁ P₂ Q f g x
     = Q⁻¹ ∑_{y : ℤ/Qℤ} f (x - P₁ y) · g (x - P₂ y)` — the paper's arithmetic average
  (Example `avg-mult`), in the "minus-sign" form, i.e. with the substitution `y ↦ -y`,
  which is the convention of (i) the fibre factorisation `Btwist_eq_fiberSum` and (ii) the
  arithmetic bilinear theorem `MdlBileOfR1Improv`.

This file records the elementary identity relating them:

  `zmodAvg (negReflect P) Q u v = polyBilinearAverageZMod X P Q u v`,

i.e. `Q⁻¹ ∑_{y<Q} u(θ + y) v(θ - P(-y)) = Q⁻¹ ∑_{y} u(θ - y) v(θ - P(y))`, the two sides
being related by the reindexation `y ↦ -y` (and the substitution of `P̃(y) = -P(-y)`).
This is what lets the arithmetic bilinear estimate `MdlBileOfR1Improv`, stated for
`polyBilinearAverageZMod X P Q`, be applied to the operator `zmodAvg (negReflect P) Q` that
the adelic lift actually produces.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicFormPlusDefs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

open Polynomial Finset
open Work.Analysis.Concentration

/-- **`polyEvalZMod` at an integer point**: reducing `P` modulo `Q` and evaluating at the
residue of `m : ℤ` is the same as evaluating `P` at `m` and reducing the result. -/
lemma polyEvalZMod_intCast (P : ℤ[X]) (Q : ℕ) (m : ℤ) :
    polyEvalZMod P Q ((m : ℤ) : ZMod Q) = ((P.eval m : ℤ) : ZMod Q) := by
  rw [polyEvalZMod_def, polyMapZMod]
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (p := P) (Int.castRingHom (ZMod Q)) m

/-- **The reflected polynomial evaluated in `ZMod Q`**: with `P̃ = negReflect P = -P(-X)`,
`P̃(y) = - P(-y)` in `ℤ/Qℤ` (for `y : ℕ`, i.e. `y` running over `0, …, Q-1`). -/
lemma negReflect_eval_zmod (P : ℤ[X]) (Q : ℕ) (y : ℕ) :
    (((negReflect P).eval (y : ℤ) : ℤ) : ZMod Q)
      = - polyEvalZMod P Q (-(y : ZMod Q)) := by
  rw [negReflect_eval, Int.cast_neg, ← polyEvalZMod_intCast P Q (-(y : ℤ))]
  congr 1
  push_cast
  ring

/-- **`Finset.range Q` represents `ZMod Q`**: for `Q ≠ 0` the residues of `0, …, Q-1` exhaust
`ℤ/Qℤ`, so summing over `Finset.range Q` and summing over `ZMod Q` agree. -/
lemma sum_range_cast_zmod {M : Type*} [AddCommMonoid M] (Q : ℕ) [NeZero Q]
    (F : ZMod Q → M) : (∑ y ∈ Finset.range Q, F (y : ZMod Q)) = ∑ x : ZMod Q, F x := by
  refine Finset.sum_bij (fun y _ => (y : ZMod Q)) (fun a ha => Finset.mem_univ _) ?_ ?_ ?_
  · intro a ha b hb hab
    have ha' : a < Q := Finset.mem_range.mp ha
    have hb' : b < Q := Finset.mem_range.mp hb
    have h1 := ZMod.val_cast_of_lt ha'
    have h2 := ZMod.val_cast_of_lt hb'
    have h3 : ((a : ZMod Q)).val = ((b : ZMod Q)).val := by rw [hab]
    rw [h1, h2] at h3
    exact h3
  · intro b hb
    exact ⟨b.val, Finset.mem_range.mpr (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩
  · intro a ha; rfl

theorem ZModAvgNegBridge (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] (u v : ZMod Q → ℂ) : Work.KMTPlan.A6.zmodAvg (Work.KMTPlan.A6.negReflect P) Q u v = Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q u v := by
  funext θ
  unfold zmodAvg polyBilinearAverageZMod
  simp only [polyEvalZMod_X]
  congr 1
  -- reindex the right-hand sum by `y ↦ -y`
  have hneg : (∑ y : ZMod Q, u (θ - y) * v (θ - polyEvalZMod P Q y))
      = ∑ z : ZMod Q, u (θ + z) * v (θ - polyEvalZMod P Q (-z)) := by
    refine Finset.sum_bij (fun y _ => -y) (fun a ha => Finset.mem_univ _) ?_ ?_ ?_
    · intro a ha b hb hab; simpa using hab
    · intro b hb; exact ⟨-b, Finset.mem_univ _, by simp⟩
    · intro a ha; simp only [neg_neg, sub_eq_add_neg]
  rw [hneg, ← sum_range_cast_zmod Q
    (fun z : ZMod Q => u (θ + z) * v (θ - polyEvalZMod P Q (-z)))]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  rw [negReflect_eval_zmod, sub_eq_add_neg]

end Work.KMTPlan.A6
