/-
# Non-vanishing of the multiplier of `(Tsq c)^[k]` at a preimage of a point outside the
critical orbit of `Tantibar c`

Area `Submission/Work/ELRig/` of the mandelbar project.  The holomorphic second iterate of the
antiholomorphic quadratic `Tantibar c` is `Tsq c` (`Work.Landing.Tsq`), and `Tsq c = (Tantibar c)^[2]`.

The multiplier of the `k`-th iterate of a polynomial is the product of the derivatives along the
orbit (the chain rule, `deriv_iterate_eq_prod` below):

  `deriv ((Tsq c)^[k]) z = ∏_{i < k} deriv (Tsq c) ((Tsq c)^[i] z)`.

Since `deriv (Tsq c) w = 4·w·(w² + c̄) = 4·w·conj (Tantibar c w)`, this multiplier vanishes exactly
when some `(Tsq c)^[i] z`, `i < k`, is a `0`-preimage of `Tsq c` or of `Tantibar c`.  Both cases
force `b = (Tsq c)^[k] z` to be an iterate `(Tantibar c)^[n] 0` of the critical point: in the first
case `b = (Tantibar c)^[2(k-i)] 0`, in the second `b = (Tantibar c)^[2(k-i)-1] 0`.

Hence if the critical orbit of `Tantibar c` avoids `b`, the multiplier cannot vanish — this is the
statement proved here.  It is the input that guarantees that a landing point of a ray (a preimage
of the `b`-point) is a *repelling* (and not parabolic) periodic point.
-/
import Mathlib
import Submission.Work.ELRig.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.ELRig

open Function
open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Elementary facts about `Tsq c = Tantibar c ∘ Tantibar c` -/

/-- `Tsq c` is the second iterate of the antiholomorphic quadratic `Tantibar c`. -/
lemma Tsq_eq_Tantibar_iterate_two (c : ℂ) : Work.Landing.Tsq c = (Tantibar c)^[2] := by
  funext z
  simp [Work.Landing.Tsq, Tantibar, Function.iterate_succ]

/-- The derivative of `Tsq c`: `deriv (Tsq c) w = 4·w·(w² + c̄)`. -/
lemma deriv_Tsq (c w : ℂ) : deriv (Work.Landing.Tsq c) w = 4 * w * (w^2 + star c) := by
  show deriv (fun z : ℂ => (z^2 + star c)^2 + c) w = 4 * w * (w^2 + star c)
  have h1 : HasDerivAt (fun z : ℂ => z^2 + star c) (2 * w) w := by
    simpa using ((hasDerivAt_id w).pow 2).add_const (star c)
  have h2 : HasDerivAt (fun z : ℂ => (z^2 + star c)^2 + c) (2 * (w^2 + star c) * (2 * w)) w := by
    simpa using ((h1.pow 2).add_const c)
  rw [h2.deriv]
  ring

/-- The conjugate of `Tantibar c w` is `w² + c̄`: the factor occurring in `deriv_Tsq`. -/
lemma star_Tantibar (c w : ℂ) : star (Tantibar c w) = w^2 + star c := by
  simp only [Tantibar, starRingEnd_apply]
  rw [star_add, star_pow, star_star]

/-- The derivative of an iterate is the product of the derivatives along the orbit (chain rule). -/
lemma deriv_iterate_eq_prod {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) (z : ℂ) :
    deriv (f^[n]) z = ∏ i ∈ Finset.range n, deriv f (f^[i] z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', deriv_comp z hf.differentiableAt ((hf.iterate n).differentiableAt), ih,
      Finset.prod_range_succ]
    ring

/-- If `z` is a preimage of `b` under `(Tsq c)^[k]` and the critical orbit of `Tantibar c` avoids
`b`, then the multiplier `deriv ((Tsq c)^[k]) z` of the `k`-th iterate is nonzero. -/
theorem deriv_iterate_ne_zero_of_notMem_orbit {c b z : ℂ} {k : ℕ} (hk : 0 < k)
    (hb : ∀ n : ℕ, ((LeanEval.ComplexAnalysis.Tantibar c)^[n]) 0 ≠ b)
    (hz : ((Work.Landing.Tsq c)^[k]) z = b) :
    deriv (((Work.Landing.Tsq c)^[k])) z ≠ 0 := by
  intro hzero
  have hdiff : Differentiable ℂ (Work.Landing.Tsq c) := by
    show Differentiable ℂ (fun z : ℂ => (z^2 + star c)^2 + c)
    fun_prop
  rw [deriv_iterate_eq_prod hdiff] at hzero
  rw [Finset.prod_eq_zero_iff] at hzero
  obtain ⟨i, hi, hfi⟩ := hzero
  rw [Finset.mem_range] at hi
  set w : ℂ := ((Work.Landing.Tsq c)^[i]) z with hw
  rw [deriv_Tsq] at hfi
  have hi_le : i ≤ k := le_of_lt hi
  have hksub : k - i + i = k := Nat.sub_add_cancel hi_le
  have hpos : 1 ≤ k - i := Nat.sub_pos_of_lt hi
  have hpos2 : 1 ≤ 2 * (k - i) := by omega
  have e2 : ((Work.Landing.Tsq c)^[k-i]) w = ((Work.Landing.Tsq c)^[k]) z := by
    rw [hw, ← Function.iterate_add_apply, hksub]
  rcases mul_eq_zero.mp hfi with h4w | hwc
  · rcases mul_eq_zero.mp h4w with h4 | hw0
    · exact absurd h4 (by norm_num)
    · -- the `i`-th point of the orbit is the critical point `0`
      have hA : ((Work.Landing.Tsq c)^[k-i]) 0 = ((Work.Landing.Tsq c)^[k-i]) w := by rw [hw0]
      have hT : ((Work.Landing.Tsq c)^[k-i]) 0 = ((Tantibar c)^[2*(k-i)]) 0 := by
        rw [Tsq_eq_Tantibar_iterate_two, ← Function.iterate_mul]
      have hmain : ((Tantibar c)^[2*(k-i)]) 0 = b := by
        rw [← hT]
        exact (hA.trans e2).trans hz
      exact hb (2*(k-i)) hmain
  · -- the `i`-th point of the orbit is a `0`-preimage of `Tantibar c`
    have hTw : Tantibar c w = 0 := by
      have : star (Tantibar c w) = 0 := by rw [star_Tantibar, hwc]
      exact star_eq_zero.mp this
    have hsplit : ((Tantibar c)^[2*(k-i)]) w = ((Tantibar c)^[2*(k-i)-1]) (Tantibar c w) := by
      conv_lhs => rw [show 2*(k-i) = (2*(k-i)-1) + 1 from (Nat.sub_add_cancel hpos2).symm]
      exact Function.iterate_add_apply _ _ _ _
    have hT : ((Work.Landing.Tsq c)^[k-i]) w = ((Tantibar c)^[2*(k-i)]) w := by
      rw [Tsq_eq_Tantibar_iterate_two, ← Function.iterate_mul]
    have hA : ((Tantibar c)^[2*(k-i)-1]) 0 = ((Tantibar c)^[2*(k-i)-1]) (Tantibar c w) := by rw [hTw]
    have hmain : ((Tantibar c)^[2*(k-i)-1]) 0 = b :=
      (hA.trans hsplit.symm).trans ((hT.symm.trans e2).trans hz)
    exact hb (2*(k-i)-1) hmain

end Work.ELRig
