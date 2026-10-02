/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# The multiplier at a period-5 point of the antiholomorphic square root is a non-negative real

Let `T_c(z) = z̄² + c` (the antiholomorphic mandelbar iterator), let `g c = (T_c)^[5]` be the
antiholomorphic square root of the second return map `Work.EL.F c = (T_c)^[10] = (g c) ∘ (g c)`,
and let `z` be a fixed point of `g c`.  This module proves that the multiplier of the *holomorphic*
map `Work.EL.F c` at `z` is a non-negative real:

  `deriv (Work.EL.F c) z = |K'(z)|²`  for an explicit holomorphic `K`.

**Why.**  `T_c = conj ∘ H_c` with `H_c(w) = w² + c̄`; hence the odd iterate is
`(T_c)^5 = conj ∘ K_c` with `K_c = H_c ∘ Q_c ∘ H_c ∘ Q_c ∘ H_c`, `Q_c(w) = w² + c`,
and, `(T_c)^2 = Q_c ∘ H_c` being holomorphic, the even iterate is

  `F := Work.EL.F c = (T_c)^10 = (Q_c ∘ H_c)^5 = A_c ∘ K_c`,
  `A_c = Q_c ∘ H_c ∘ Q_c ∘ H_c ∘ Q_c = conj ∘ K_c ∘ conj`.

So `F` is the composite of a holomorphic map `K_c` with its *conjugate* `A_c`.  The chain rule and
the identity `deriv (conj ∘ f ∘ conj) = conj ∘ deriv f ∘ conj`
(`Mathlib.Analysis.Calculus.Deriv.Star.deriv_conj_conj`) give, for `g c z = z` (i.e.
`conj (K_c z) = z`),

  `deriv F z = deriv A_c (K_c z) · deriv K_c z = conj (deriv K_c z) · deriv K_c z
             = ‖deriv K_c z‖²`,

a non-negative real.  This is the realness/non-negativity of the multipliers used in
`Submission/Work/PARIMPL/ParSplit/NOTES.md`, §1, items (F1)–(F2): at a fixed point of the
antiholomorphic square root the multiplier of the second return map is `|(g)'(z)|²`.

This module is self-contained: it only needs `Work.EL.F`, `Work.Landing.Tsq` and `gtc`.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.Split

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL.ParSplit

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The two holomorphic factors and the two words -/

/-- `H_c z = z² + c̄`, the holomorphic factor of `T_c = conj ∘ H_c`. -/
def fixH (c : ℂ) : ℂ → ℂ := fun z => z ^ 2 + star c

/-- `Q_c z = z² + c = conj ∘ H_c ∘ conj`, the holomorphic factor of `(T_c)² = Q_c ∘ H_c`. -/
def fixQ (c : ℂ) : ℂ → ℂ := fun z => z ^ 2 + c

/-- `K_c = H_c ∘ Q_c ∘ H_c ∘ Q_c ∘ H_c`: the holomorphic map with `(T_c)^5 = conj ∘ K_c`. -/
def fixK (c : ℂ) : ℂ → ℂ := fixH c ∘ fixQ c ∘ fixH c ∘ fixQ c ∘ fixH c

/-- `A_c = Q_c ∘ H_c ∘ Q_c ∘ H_c ∘ Q_c`: the holomorphic map with
`A_c = conj ∘ K_c ∘ conj` and `Work.EL.F c = A_c ∘ K_c`. -/
def fixA (c : ℂ) : ℂ → ℂ := fixQ c ∘ fixH c ∘ fixQ c ∘ fixH c ∘ fixQ c

/-! ## The two words, in terms of `K_c` and `A_c` -/

/-- `(T_c)^5 = conj ∘ K_c`. -/
lemma fix_Tantibar_iterate_five (c : ℂ) : ∀ z, (Tantibar c)^[5] z = star (fixK c z) := by
  intro z
  simp [fixH, fixQ, fixK, LeanEval.ComplexAnalysis.Tantibar, Function.iterate_succ_apply',
    map_add, map_pow]

/-- `(T_c)^2 = Q_c ∘ H_c`. -/
lemma fix_Tsq_eq_comp (c : ℂ) : Work.Landing.Tsq c = fixQ c ∘ fixH c := by
  funext z; simp [Work.Landing.Tsq, fixH, fixQ]

/-- `Work.EL.F c = (T_c)^10 = A_c ∘ K_c`. -/
lemma fix_F_eq_comp (c : ℂ) : Work.EL.F c = fixA c ∘ fixK c := by
  show (Work.Landing.Tsq c)^[5] = fixA c ∘ fixK c
  rw [fix_Tsq_eq_comp c]
  funext z
  simp [fixA, fixK, Function.iterate_succ_apply', Function.comp_apply]

/-- `A_c = conj ∘ K_c ∘ conj`: the two words are conjugate. -/
lemma fix_A_eq_conj_comp (c : ℂ) :
    fixA c = ⇑(starRingEnd ℂ) ∘ fixK c ∘ ⇑(starRingEnd ℂ) := by
  funext z; simp [fixA, fixK, fixH, fixQ, map_add, map_pow]

/-! ## The multiplier of `K_c` at the conjugated point -/

/-- **The conjugate-derivative identity**: `deriv A_c w = conj (deriv K_c (conj w))`.  This is
`deriv_conj_conj` applied to the presentation `A_c = conj ∘ K_c ∘ conj`. -/
lemma fix_deriv_A_apply (c w : ℂ) : deriv (fixA c) w = star (deriv (fixK c) (star w)) := by
  rw [fix_A_eq_conj_comp c, deriv_conj_conj]
  rfl

/-- `K_c` is holomorphic (it is a polynomial). -/
lemma fix_differentiable_K (c : ℂ) : Differentiable ℂ (fixK c) := by
  unfold fixK fixH fixQ; fun_prop

/-- `A_c` is holomorphic (it is a polynomial). -/
lemma fix_differentiable_A (c : ℂ) : Differentiable ℂ (fixA c) := by
  unfold fixA fixH fixQ; fun_prop

/-! ## The main statement -/

/-- **At a fixed point of the antiholomorphic square root `gtc c = (T_c)^5`, the multiplier of the
holomorphic second return map `Work.EL.F c = (T_c)^10` is a non-negative real** (namely
`‖deriv (fixK c) z‖²`). -/
theorem deriv_star_self_of_fix {c z : ℂ} (h : gtc c z = z) :
    ∃ r : ℝ, 0 ≤ r ∧ deriv (Work.EL.F c) z = (r : ℂ) := by
  -- `g c z = z` reads `conj (K_c z) = z` on the holomorphic factor.
  have hK : star (fixK c z) = z := by
    rw [← fix_Tantibar_iterate_five c z]
    exact h
  -- Chain rule on `F = A_c ∘ K_c`, then `A_c' = conj ∘ K_c' ∘ conj`.
  have hderiv : deriv (Work.EL.F c) z = star (deriv (fixK c) z) * deriv (fixK c) z := by
    rw [fix_F_eq_comp c, deriv_comp (h₂ := fixA c) (h := fixK c) (x := z)
        (fix_differentiable_A c).differentiableAt (fix_differentiable_K c).differentiableAt,
      fix_deriv_A_apply c (fixK c z), hK]
  refine ⟨‖deriv (fixK c) z‖ ^ 2, sq_nonneg _, ?_⟩
  rw [hderiv]
  -- `conj w * w = ‖w‖²` as complex numbers.
  simpa [Complex.sq_norm] using
    (Complex.normSq_eq_conj_mul_self (z := deriv (fixK c) z)).symm

end Work.PARIMPL.ParSplit
