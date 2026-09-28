import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.density_aux

/-!
# N14 `density`: route (design review hasse2, 2026-09-27)

Statement file for the new sub-lemmas of `DESIGN_REVIEW.md` §2. Every statement elaborates
against the workspace; all proofs are `sorry`. Everything lives in the fresh namespace
`Work.HP.DN`.

The fixed level is NOT `LocSet d n M` (exponents `r_p(M)`): with those exponents the deep-failure
loss is `Σ_{p ≤ M} p^{-r_p(M)/2} ≍ 1/log M`, which needs Chebyshev-type prime counting to go to
`0`. We use the uniform exponent `4M` instead, which makes the loss `≤ M·4^{-M}`.

Only EXISTENCE of the limits is needed: no rates, no explicit density, no boundary counts.
-/

set_option autoImplicit false

noncomputable section

open Filter Finset MeasureTheory Pointwise

namespace Work.HP.DN

open Work.HP

/-! ## Definitions -/

/-- The fixed-level set: real solubility plus a primitive zero modulo `p^{4M}` for all `p ≤ M`. -/
def SM (d n M : ℕ) (a : Mon d n → ℤ) : Prop :=
  RealSol d n a ∧ ∀ p : ℕ, p.Prime → p ≤ M → PrimModZero d n a p (4 * M)

/-- Its period `Q_M = ∏_{p ≤ M} p^{4M}`. -/
def QM (M : ℕ) : ℕ := ∏ p ∈ (Finset.range (M + 1)).filter Nat.Prime, p ^ (4 * M)

/-- The real-soluble cone, in real coefficient space. -/
def realSolCone (d n : ℕ) : Set (Mon d n → ℝ) :=
  {t | ∃ x : Fin (n + 1) → ℝ, x ≠ 0 ∧ formEvalR d n t x = 0}

/-- Euclidean closed unit ball in coefficient space. -/
def unitBallR (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {t | rNorm t ≤ 1}

/-! ## D1–D4: counting in `(cone ∩ ball) × (periodic)` -/

end Work.HP.DN
