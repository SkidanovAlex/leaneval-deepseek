import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.FarLatDefs
import Submission.Work.BoseFixR.LatGreen.integrableOn_period
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FarLat.tileLatticeLintegral` — the lattice tiling identity for `∫⁻`

The space `ℝ³` is the disjoint union, over the lattice `ℓℤ³`, of the translates `x ↦ x - lat ℓ n`
of the half-open box `cellI ℓ = [-ℓ/2, ℓ/2)³` (which is a fundamental domain, `cellI_ae_eq_cell`
shows that the closed box `cell ℓ` is a.e. the same set).  Consequently, for **any** function
`g : ℝ³ → ℝ≥0∞` (no measurability needed: `lintegral` and `setLIntegral_comp_emb` /
`lintegral_iUnion` are all stated for arbitrary integrands),

    ∫⁻ u, g u = ∑' n : ℤ³, ∫⁻ x in cell ℓ, g (x - lat ℓ n).

The proof is the fundamental-domain identity
`MeasureTheory.IsAddFundamentalDomain.lintegral_eq_tsum''` for `Work.BoseFixR.isAddFundamentalDomain_cellI`
(which packages exactly the disjointness of the translates and their a.e. cover), reindexed along
`latEquiv` (the additive isomorphism `ℤ³ ≃ ℓℤ³`), then along the sign reversal `n ↦ -n`
(`LatGreen.negLab` + `LatGreen.lat_neg`), and finally transferred from `cellI ℓ` to `cell ℓ`
via `setLIntegral_congr` and the a.e. equality `cellI_ae_eq_cell` (the boundary of the box is
a null set, `volume_cell_sdiff_cellI`).
-/

noncomputable section

open scoped Real Topology BigOperators Pointwise
open MeasureTheory Set

namespace Work.BoseFixR.FarLat

/-- **The tiling identity on the half-open cell.**  Integrating over `ℝ³` is the same as summing
the integrals over the translates `cellI ℓ - lat ℓ n` of the fundamental domain. -/
theorem lintegral_tile_cellI {ℓ : ℝ} (hℓ : 0 < ℓ)
    (g : EuclideanSpace ℝ (Fin 3) → ENNReal) :
    ∫⁻ u, g u
      = ∑' n : Fin 3 → ℤ,
          ∫⁻ x in Work.BoseFixR.cellI ℓ, g (x - Work.BoseFixR.lat ℓ n) := by
  haveI : Countable (Work.BoseFixR.latHom ℓ).range :=
    Work.BoseFixR.countable_range_latHom (ne_of_gt hℓ)
  have hplus : ∫⁻ u, g u
      = ∑' n : Fin 3 → ℤ,
          ∫⁻ x in Work.BoseFixR.cellI ℓ, g (x + Work.BoseFixR.lat ℓ n) := by
    rw [(Work.BoseFixR.isAddFundamentalDomain_cellI hℓ).lintegral_eq_tsum'' g,
      ← (Work.BoseFixR.latEquiv (ne_of_gt hℓ)).tsum_eq
        (fun v : (Work.BoseFixR.latHom ℓ).range =>
          ∫⁻ x in Work.BoseFixR.cellI ℓ, g (v +ᵥ x))]
    refine tsum_congr fun n => ?_
    congr 1 with x
    simp [Work.BoseFixR.latEquiv, add_comm]
  rw [hplus, ← Work.BoseFixR.LatGreen.negLab.tsum_eq
    (fun n : Fin 3 → ℤ =>
      ∫⁻ x in Work.BoseFixR.cellI ℓ, g (x + Work.BoseFixR.lat ℓ n))]
  refine tsum_congr fun n => ?_
  rw [show (fun x : EuclideanSpace ℝ (Fin 3) =>
        g (x + Work.BoseFixR.lat ℓ (Work.BoseFixR.LatGreen.negLab n)))
      = (fun x : EuclideanSpace ℝ (Fin 3) => g (x - Work.BoseFixR.lat ℓ n)) from by
    funext x
    simp only [Work.BoseFixR.LatGreen.negLab_apply n,
      Work.BoseFixR.LatGreen.lat_neg ℓ n, sub_eq_add_neg]]

/-- **The lattice tiling identity.**  Integrating a `ℝ≥0∞`-valued function over `ℝ³` is the same as
summing, over the lattice `ℓℤ³`, the integrals of its translates against one period cell. -/
theorem tileLatticeLintegral {ℓ : ℝ} (hℓ : 0 < ℓ)
    (g : EuclideanSpace ℝ (Fin 3) → ENNReal) :
    ∫⁻ u, g u
      = ∑' n : Fin 3 → ℤ,
          ∫⁻ x in Work.BoseFixR.cell ℓ, g (x - Work.BoseFixR.lat ℓ n) := by
  rw [lintegral_tile_cellI hℓ g]
  refine tsum_congr fun n => ?_
  exact MeasureTheory.setLIntegral_congr (Work.BoseFixR.cellI_ae_eq_cell ℓ)

end Work.BoseFixR.FarLat
