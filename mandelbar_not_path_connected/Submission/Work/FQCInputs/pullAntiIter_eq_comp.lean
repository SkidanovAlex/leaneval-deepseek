/-
# `Work.FQCInputs.pullAntiIter_eq_comp`

The `n`-fold antiholomorphic pull-back `Work.FQC.pullAntiIter f n μ z` of a Beltrami coefficient
depends on `μ` only through the *single* value `μ (f^[n] z)`, and that dependence is continuous.

This is the elementary step behind `Work.FQC.continuous_muQC_apply`: it is what allows the whole
`t`-dependence of `Work.FQC.muQC d fl P t z` to be read off from the one number
`Work.MRMT.beltramiOf (ell t) (fl.φa …)`.

The proof is the explicit iteration formula

`pullAntiIter f n μ z = antiIterCoeff f n z * star^[n] (μ (f^[n] z))`

(`pullAntiIter_apply` below), where the multiplier is the recursion

`antiIterCoeff f 0 z = 1`,
`antiIterCoeff f (n+1) z = star (antiIterCoeff f n (f z)) * (∂̄ f z / star (∂̄ f z))`,

and `star^[n]` is the `n`-th iterate of complex conjugation (the identity for even `n`, `star`
for odd `n`).  The multiplier absorbs, at every step, the alternating conjugation of `pullAnti`;
the factor `∂̄ f z / star (∂̄ f z)` is the (unimodular where `∂̄ f ≠ 0`) quotient of `pullAnti`.

Since `f`, `n` and `z` are fixed in the statement,
`Φ w = antiIterCoeff f n z * star^[n] w` is the required continuous map.
-/
import Mathlib
import Submission.Work.FQC.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FQCInputs

open Work.FQC

/-- The multiplier of the `n`-fold antiholomorphic pull-back: the recursive factor by which
`pullAntiIter f n μ z` differs from the single value `μ (f^[n] z)` (up to the conjugation
`star^[n]`).  It solves `A 0 z = 1`, `A (n+1) z = star (A n (f z)) * (∂̄ f z / star (∂̄ f z))`. -/
noncomputable def antiIterCoeff (f : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 1
  | n + 1 => fun z => star (antiIterCoeff f n (f z)) *
      (Work.MRMT.dzbar f z / star (Work.MRMT.dzbar f z))

/-- The explicit iteration formula for the `n`-fold antiholomorphic pull-back
`Work.FQC.pullAntiIter`: the `n`-th pull-back of `μ` at `z` is the multiplier
`antiIterCoeff f n z` times `μ` evaluated at the single point `f^[n] z`, conjugated `n` times. -/
theorem pullAntiIter_apply (f : ℂ → ℂ) (n : ℕ) (μ : ℂ → ℂ) (z : ℂ) :
    pullAntiIter f n μ z = antiIterCoeff f n z * star^[n] (μ (f^[n] z)) := by
  induction n generalizing z with
  | zero => simp [pullAntiIter, antiIterCoeff]
  | succ n ih =>
      rw [pullAntiIter_succ, pullAnti, ih (f z),
        Function.iterate_succ_apply f n z,
        Function.iterate_succ_apply' star n (μ (f^[n] (f z)))]
      simp only [antiIterCoeff, star_mul]
      ring_nf

/-- `fun w => star^[n] w` is continuous (complex conjugation is an isometry). -/
theorem continuous_starIterate (n : ℕ) : Continuous (fun w : ℂ => star^[n] w) := by
  have h : Continuous (fun w : ℂ => star w) := Complex.continuous_conj
  exact h.iterate n

/-- **The `n`-fold pull-back depends on `μ` only through `μ (f^[n] z)`, continuously.** -/
theorem pullAntiIter_eq_comp (f : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    ∃ Φ : ℂ → ℂ, Continuous Φ ∧ ∀ μ : ℂ → ℂ, Work.FQC.pullAntiIter f n μ z = Φ (μ (f^[n] z)) := by
  refine ⟨fun w => antiIterCoeff f n z * star^[n] w, ?_, fun μ => pullAntiIter_apply f n μ z⟩
  exact continuous_starIterate n |>.const_mul (antiIterCoeff f n z)

end Work.FQCInputs
