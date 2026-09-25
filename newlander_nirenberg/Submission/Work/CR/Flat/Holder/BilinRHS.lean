/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The right-hand side of the Leibniz bound for `hSN`

For a bilinear `B : E →L[ℝ] F →L[ℝ] G` and functions `f : D → E`, `g : D → F` on a set `Ω`,
the `n`-th iterated derivative of `x ↦ B (f x) (g x)` obeys the Leibniz-type bound

`‖D^n (B ∘ (f,g))‖ ≤ ‖B‖ * ∑_{i ≤ n} n.choose i * (‖D^i f‖ * ‖D^{n-i} g‖)`

(`ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear`).  Iterating the argument one
level further (including the Hölder seminorms of the derivatives) gives the bound

`[D^n (B ∘ (f,g))]_α ≤ ‖B‖ * ∑_{i ≤ n} n.choose i * ([D^i f]_α * ‖D^{n-i} g‖_∞ + ‖D^i f‖_∞ * [D^{n-i} g]_α)`

in which the Hölder seminorm of the `i`-th derivative of the product is controlled by the
Hölder seminorm of the `i`-th derivative of one factor and the sup norm of the `(n-i)`-th
derivative of the other.  This file records the sum appearing on the right-hand side as
`bilinRHS`, so that it can be referred to in the statements of the auxiliary lemmas.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder.Bilinear

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.CR.Flat.Holder

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- The right-hand side of the Leibniz-type bound for the Hölder seminorm of
`x ↦ B (f x) (g x)`: the extremal case `B = id` of `bilinRHS` is the sum appearing in the
bound `[B ∘ (f,g)]_{k,α} ≤ ‖B‖ * bilinRHS α k f g Ω`. -/
noncomputable def bilinRHS (α : ℝ) (n : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : D → E) (g : D → F) (Ω : Set D) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ≥0∞) *
    (hSN i α f Ω * iDN (n - i) g Ω + iDN i f Ω * hSN (n - i) α g Ω)

@[simp] lemma bilinRHS_zero (α : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : D → E) (g : D → F) (Ω : Set D) :
    bilinRHS α 0 f g Ω = hSN 0 α f Ω * iDN 0 g Ω + iDN 0 f Ω * hSN 0 α g Ω := by
  simp [bilinRHS]

end Work.CR.Flat.Holder
