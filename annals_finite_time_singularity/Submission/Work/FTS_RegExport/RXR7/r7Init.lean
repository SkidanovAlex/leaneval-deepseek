import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXR7.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR7

open scoped Real Topology NNReal
open Set Filter

set_option autoImplicit false

/-- **RX-R7, the `hInit` field.** The full profile of the R7 block at the sanitised
right-Taylor family (`Prof α g = profFull α (extG (gS α (tauExt g)))`) vanishes at `τ = 0`
beyond some radius `Lz7 > 0`, namely (via `hdat`) beyond the `z`-support of the localised datum
`locG6 (pExp α) L β`.

Route: `hdat` at `τ = 0`; `gS` and `tauExt` are inert at `z > 0`, `0 ≤ θ ≤ π/2`, `τ = 0`
(`gS`, `tauExt_of_nonneg`, `extG_of_pos`); `locG6 (pExp α) L β = locData - F_*` with
`locData = F_* · chi(z/L) + β · hLoc` and `hLoc α = bumpZ · Γ`, and `profFull = F_* + extG(·)`
reduces the profile at `τ = 0` to `F_* · chi(z/L) + β · bumpZ(z) · Γ(θ)` which vanishes for
`z > max (2L) (7/4)` (`Stability.chi_eq_zero` with `|z/L| ≥ 2`, `LocData.bumpZ_eq_zero_of_ge`).
`Lz7 := max (2L) (7/4)` works since `1 ≤ L` gives `Lz7 > 0`. -/
theorem r7Init {α : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ,
      g z θ 0 = Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ) :
    ∃ Lz7 : ℝ, 0 < Lz7 ∧ ∀ z θ, Lz7 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS_RegExport.RXR7.Prof α g z θ 0 = 0 := by
  obtain ⟨L, β, hL1, hdat⟩ := hdat
  refine ⟨max (2 * L) (7 / 4), lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro z θ hz hθ0 hθ1
  have hLpos : 0 < L := by linarith
  have hz2L : 2 * L < z := lt_of_le_of_lt (le_max_left _ _) hz
  have hz74 : 7 / 4 < z := lt_of_le_of_lt (le_max_right _ _) hz
  have hz0 : 0 < z := by linarith
  -- the sanitiser and the right-Taylor extension are inert at `τ = 0`
  have hgr : GR α g z θ 0 = g z θ 0 := by
    have h1 : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ 0
        = Work.FTS.FinalV2.tauExt g z θ 0 := by
      simp only [Work.FTS.FinalV2.gS, hz0, hθ0.le, hθ1.le, and_self, ↓reduceIte]
    rw [GR, h1, Work.FTS.FinalV2.tauExt_of_nonneg g (le_refl (0 : ℝ))]
  have hextG : Work.FTS.RegPkgGal.extG (GR α g) z θ 0 = g z θ 0 := by
    rw [Work.FTS.RegPkgGal.extG_of_pos hz0 (le_refl (0 : ℝ)), hgr]
  -- the profile at `τ = 0` is `F_* + g(0)`
  have hprof : Prof α g z θ 0 = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
      + g z θ 0 := by
    simp only [Prof, Work.FTS.Regularity.profFull_apply, hextG]
  -- the two cut-offs vanish beyond `z > max (2L) (7/4)`
  have hchi : Work.Stability.chi (z / L) = 0 := by
    refine Work.Stability.chi_eq_zero ?_
    rw [abs_of_nonneg (div_nonneg hz0.le hLpos.le)]
    rw [le_div_iff₀ hLpos]
    linarith
  have hbump : Work.FTS.LocData.bumpZ z = 0 :=
    Work.FTS.LocDataExt.bumpZ_eq_zero_of_ge hz74.le
  rw [hprof, hdat z θ, Work.FTS.LocData6.locG6_eq, Work.FTS.LocData.locG_apply,
    Work.FTS.LocData.locData_apply, Work.FTS.LocData.hLoc_apply, hchi, hbump]
  ring

end Work.FTS_RegExport.RXR7
