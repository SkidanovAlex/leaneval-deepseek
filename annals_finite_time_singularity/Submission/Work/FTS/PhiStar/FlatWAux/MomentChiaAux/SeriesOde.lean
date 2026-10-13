/-
# `Work.FTS.PhiStar.FlatWAux.MomentChiaAux.SeriesOde`

The `Lzero`-eigen-series identity: a coefficient family `c` whose `λ`-weighted version
`d m = c m · lam m` is summable produces a `C²` function `∑_m c_m e_m` on `(0, π/2)` with
`Lzero (∑_m c_m e_m) = ∑_m d_m e_m`.  All the analytic work (the growth bounds of the modes,
the termwise differentiation and the termwise `Lzero` computation) is in the companion module
`SeriesOdeAux`, which this file only assembles.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Series.Deleg.psiAngBounds
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.SeriesOdeAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open Filter Set

namespace Work.FTS.PhiStar.FlatWAux.MomentChiaAux

/-! ## 7. The target -/

theorem SeriesOde (c d : ℕ → ℝ)
    (hcd : ∀ m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.lam m = d m)
    (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2))
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1))) :
    ContDiffOn ℝ 2 (fun θ : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        (Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        Work.Elliptic.Lzero (fun _ θ' => ∑' m : ℕ, c m
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ') 0 θ
          = ∑' m : ℕ, d m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  refine ⟨contDiffOn_series hc hd hcd, fun θ hθ => ?_⟩
  obtain ⟨h0, h1⟩ := hθ
  set ε : ℝ := min θ (Real.pi / 2 - θ) / 2 with hεdef
  have hpi : 0 < Real.pi / 2 - θ := by linarith [Real.pi_pos, h1]
  have hε : 0 < ε := by
    rw [hεdef]
    have h2 : (0 : ℝ) < min θ (Real.pi / 2 - θ) := lt_min h0 hpi
    linarith
  have hmem : θ ∈ Set.Ioo ε (Real.pi / 2 - ε) := by
    rw [hεdef]
    constructor
    · have h := min_le_left θ (Real.pi / 2 - θ); linarith
    · have h := min_le_right θ (Real.pi / 2 - θ); linarith
  exact lzero_series hcd hc hd hε hmem

end Work.FTS.PhiStar.FlatWAux.MomentChiaAux
