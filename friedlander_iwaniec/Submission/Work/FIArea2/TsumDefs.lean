import Mathlib
import Submission.Work.FIArea2.G8Defs
import Submission.Work.FIArea2.ramanujan_setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The reduced arithmetic sum `T(n,a,h₁,h₂)` of *FI* (6.10)/(8.2)

`Work.FIArea2.Gsum` is the paper's (6.10) with the two-congruence system (6.4)/(6.5) written out
through `%` on `ℤ`.  By (6.6) the system collapses to the single rational congruence (8.2)
`γ₂² ≡ a γ₁² (mod |Δ|)` with `a` the residue of `z₂/z₁` modulo `|Δ|` (`Work.FIArea2.Cnt_eq_Nsol`
proves the corresponding equality of *counts*).  This file fixes the resulting sum, which is the
object of the arithmetic estimate Lemma 8.1 (8.5).
-/

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **(6.10) in reduced form.**  For `n ≥ 1` and `a, h₁, h₂ : ℤ`,

  `T(n,a,h₁,h₂) = ∑_{x,y (n), y² ≡ a x² (mod n)} e((xh₁ + yh₂)/n)`,

the sum running over `x, y : ZMod n` and the representatives `x.val, y.val ∈ [0,n)` being the
paper's `γ₁, γ₂`.  This is `Work.FIArea2.Gsum z₁ z₂ h₁ h₂` with the congruence (6.4) reduced to
(8.2) via (6.6). -/
def Tsum (n : ℕ) [NeZero n] (a h1 h2 : ℤ) : ℂ :=
  ∑ x : ZMod n, ∑ y : ZMod n,
    (if y ^ 2 = (a : ZMod n) * x ^ 2 then
      E ((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ) / (n : ℝ))
     else 0)

end

end Work.FIArea2
