/-
# `FTS/PhiStar/Honesty/ellEstUnif_diff` — the elliptic estimate for a *difference* datum

`EllipticEst.TT.EllEstUnif` (the paper's `prop:Hk`, proved for every `k ≥ 2` as
`EllSol.ellEstUnifAll`, re-homed as `Honesty.ellEstUnifAll_clean`
(note: the original module also imports `EllExist.LevelK`, which would create an import cycle here)) is an estimate for one pair `(F, Ψ)` of the weak class.  The limit passage
of the compact-source route (`NOTES_cptQ_route.md` §3) needs it for the *difference* of two such
pairs, because that is what turns a Cauchy sequence of sources `G n → F` into a Cauchy sequence of
solutions `Ψ n`.  The class is closed under differences (`Honesty.ellWeakPos_sub`), so this is a
one-line corollary; it is recorded here because it is the shape the limit argument consumes and
because the naive route (triangle inequality through the estimates for `(G,Ψ)` and `(H,Φ)` taken
separately) does *not* give it.

The constant is inherited verbatim from `ellEstUnifAll` (hence absolute, uniform on `α ≤ 1/4`).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.PhiStar.Honesty.ellWeakPos_sub
import Submission.Work.FTS.PhiStar.Honesty.EllEstUnifAllClean

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **The `ℋ^k` elliptic estimate for the difference of two weak-class data.** -/
theorem ellEstUnif_diff (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (G H Ψ Φ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k G Ψ →
      Work.FTS.EllipticEst.TT.EllWeakPos α k H Φ →
      α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (fun z' θ' => Ψ z' θ' - Φ z' θ') z θ)
        + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (fun z' θ' => Ψ z' θ' - Φ z' θ'))
        ≤ C * Work.Spaces.HkNorm α k (fun z θ => G z θ - H z θ) := by
  obtain ⟨C, hCpos, hEst⟩ := ellEstUnifAll_clean k hk
  exact ⟨C, hCpos, fun α G H Ψ Φ hα hα4 hG hH =>
    hEst α (fun z θ => G z θ - H z θ) (fun z θ => Ψ z θ - Φ z θ) hα hα4
      (ellWeakPos_sub k hG hH)⟩

end Work.FTS.PhiStar.Honesty
