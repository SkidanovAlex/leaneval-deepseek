/-
# `|f|²_{ℋ¹} ≤ (f,f)_{ℋ¹}` in the interior class `RegQ α 1`

`Work.Coercivity.H1IP_le_self` proves `HkSq α 1 f ≤ H1IP α f f` from `HkMem α 1 f` and
`Spaces.SmoothNbhd f`, i.e. from **real analyticity** of `f` — a hypothesis that no datum of
the paper satisfies (`SmoothNbhd = ContDiffOn ℝ ⊤`, and `⊤ : WithTop ℕ∞ = ω` in this Mathlib).
The usable class is the interior class `RegQ α 1 f = SmoothQuad f ∧ HkMem α 1 f ∧
BdryTraces α 1 f` (`SmoothQuad` is genuine `C^∞` on the open quadrant); this file proves the
same inequality on it, which is what the `coer1`-assembly consumes.

The paper's `H1IP` has *positive* coefficients `10, 10^10, 10^17, 10^21` on the four weighted
`L²`-terms

  `|D_z f · w/√sin^η|²`, `|f · w/√sin^η|²`, `|f · w|²`, `|D_θ f · w/√sin^γ|²`,

while `HkSq α 1 f` is the sum of the first, second and fourth of these (the paper's
`E_{z,θ}¹ f`) — the identity `Coer1.HkSq_one_eq`, which holds on `SmoothQuad f` (interior
`C^∞`) and `HkMem α 1 f`, exactly the two ingredients of `RegQ α 1 f`.  Both sides are sums
of diagonal `wip`-pairings (`EDz_eq_wip`, `EfEta_eq_wip`, `EDth_eq_wip`), each of which is
nonnegative (`wip_self_nonneg`), and each coefficient of `H1IP` is `≥ 1`; so the norm is
dominated term by term by the inner product.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.H1IP_le_self
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Coer1.HkSqOne

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-- **The `ℋ¹` inner product dominates the `ℋ¹` norm on the interior class `RegQ α 1`.** -/
theorem H1IP_le_self_Q (α : ℝ) {f : ℝ → ℝ → ℝ} (hf : Work.FTS.Nonlin.RegQ α 1 f) :
    Work.Spaces.HkSq α 1 f ≤ Work.Coercivity.H1IP α f f := by
  obtain ⟨hquad, hmem, _⟩ := hf
  -- `sin(2θ) ≥ 0` on the angular interval, so all the angular powers are nonnegative
  have hsin : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    simp only [Work.Spaces.Iθ, mem_Icc] at hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  -- nonnegativity of the three `wip`-terms that make up `HkSq α 1 f`
  have hA : 0 ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.Spaces.Dz f) (Work.Spaces.Dz f) :=
    Work.Coercivity.wip_self_nonneg
      (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hB : 0 ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) f f :=
    Work.Coercivity.wip_self_nonneg
      (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hC : 0 ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) f f :=
    Work.Coercivity.wip_self_nonneg (fun z _ _ => sq_nonneg _)
  have hD : 0 ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Work.Spaces.Dth f) (Work.Spaces.Dth f) :=
    Work.Coercivity.wip_self_nonneg
      (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  -- the `ℋ¹` norm is the sum of three of the four inner-product terms
  have hshape : Work.Spaces.HkSq α 1 f
      = Work.Coercivity.EDz f + Work.Coercivity.EDth α f + Work.Coercivity.EfEta f := by
    rw [Work.FTS.CoercivityFix.Coer1.HkSq_one_eq α hquad hmem]
    ring
  rw [hshape, Work.Coercivity.EDz_eq_wip f, Work.Coercivity.EDth_eq_wip α f,
    Work.Coercivity.EfEta_eq_wip f]
  unfold Work.Coercivity.H1IP
  linarith [hA, hB, hC, hD]

end Work.FTS.CoercivityFix.Assembly
