import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PhiStar.ThetaTraces` — the θ-part of the boundary traces (lead install R6, 2026-10-11)

`cbc/fts_ellnode_ruling.md` §4.2(1), §4.4.  The CptApp chain (`exists_cptQ_approx`) destructures
`BdryTraces α k F` in exactly one place (`Est/hardyShrink_slice`: `(hB 0 s _).2 z hz`): the
θ-limits of `sin(2θ)^{1-γ}·(D_z^s F)²` for `s + 1 ≤ k`, at every `z > 0`.  `ThetaTraces α k F`
is exactly that.  It cannot be derived from `HkMem` (ruling Q1), so it is carried as the last field
`thTr` of `ClassC.ClassC` and of `StrongEps.SoftClass`.

Standalone low-level file (imports only `Spaces.Defs`) so that `ClassC/Defs` can import it without
an import cycle.  `thetaTraces_of_bdryTraces` lives in `PhiStar/ThetaTracesBdry.lean`.
-/

noncomputable section
open scoped Real Topology
open Filter

namespace Work.FTS.PhiStar

/-- θ-traces of the radial iterates of order `s < k` — exactly the part of `BdryTraces α k F`
that the CptApp chain uses (`Est/hardyShrink_slice`: `(hB 0 s _).2 z hz`). -/
def ThetaTraces (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ s : ℕ, s + 1 ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ),
    Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed s 0 F z θ) ^ 2) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed s 0 F z θ) ^ 2) (𝓝[<] (π / 2)) (𝓝 0)

/-- `ThetaTraces` is monotone in the level. -/
theorem thetaTraces_mono {α : ℝ} {k l : ℕ} {F : ℝ → ℝ → ℝ} (hkl : k ≤ l)
    (h : ThetaTraces α l F) : ThetaTraces α k F :=
  fun s hs z hz => h s (le_trans hs hkl) z hz

end Work.FTS.PhiStar
