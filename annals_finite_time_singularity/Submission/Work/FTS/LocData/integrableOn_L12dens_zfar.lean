/-
# `L₁₂`-density of the far part `zfar L F_*` is integrable on `(0,∞)`

The localisation node of the route replaces the self-similar profile `F_*` by its cut-off far
part `zfar L F_* = (1 - χ(z/L))·F_*` (`Work.Stability.zfar`).  Whereas `F_*` decays only like
`z^{-1}` — so its `L₁₂`-density decays like `z^{-2}`, which is still integrable but with a
`z^{-1}` tail — the far part lives at the *outer* scale `L`, and the factor `1 - χ(z/L)` is
bounded by `1` and vanishes off that scale.

Explicitly, for `0 < α ≤ 1`, `1 ≤ L` and `s > 0`,

  `L₁₂dens (zfar L F_*)(s) = (1 - χ(s/L)) · α · 2/(1+s)²`,

because the radial cut-off factor comes out of the angular integral
(`L12dens_zfar_Fstar`, `Work.FTS.LocData.L12_zfar_Fstar_abs_le`) and the angular integral of
`F_*` collapses to `α·F_*(s)/s = α·2/(1+s)²` (`Work.Construction.L12dens_Fstar`).  The prefactor
`1 - χ(s/L)` is bounded between `0` and `1` (`Work.Stability.chi_nonneg`, `chi_le_one`), and
`s ↦ 2/(1+s)²` is integrable on `(0,∞)` (`integrableOn_add_rpow_Ioi_of_lt`), so the density is
dominated by an integrable function and is integrable on `(0,∞)`.

This is the integrability hypothesis that the linearity lemmas on the localised data
(`L12_add_mul`, `L12_locG`) need when the localised datum
`locG α L β hLoc = -zfar L F_* + β·hLoc` is fed to the existence theorem of the route.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.L12_zfar_Fstar_abs_le
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-- **The `L₁₂`-density of the far part is integrable on `(0,∞)`.**  On `(0,∞)` it is the
explicit elementary function `s ↦ (1 - χ(s/L))·α·2/(1+s)²`, the product of the bounded factor
`1 - χ(s/L) ∈ [0,1]` with the integrable function `α·2/(1+s)²`; domination by an integrable
function gives the result. -/
theorem integrableOn_L12dens_zfar (α L : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.Stability.zfar L (Work.Construction.Fstar α)))
      (Set.Ioi (0 : ℝ)) := by
  have hLpos : (0 : ℝ) < L := by linarith
  -- On `(0,∞)` the density is the elementary function `(1 - χ(s/L))·α·2/(1+s)²`.
  have hpt : ∀ s ∈ Set.Ioi (0 : ℝ),
      Work.FM.L12dens Work.Spaces.K (Work.Stability.zfar L (Work.Construction.Fstar α)) s
        = (1 - Work.Stability.chi (s / L)) * (α * (2 * (s + 1) ^ (-2 : ℝ))) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hs1 : (0 : ℝ) < s + 1 := by linarith
    have hFdiv : Work.FM.Fstar s / s = 2 * (s + 1) ^ (-2 : ℝ) := by
      have h2 : (s + 1) ^ (-2 : ℝ) = 1 / (s + 1) ^ 2 := by
        simp only [Real.rpow_neg (le_of_lt hs1), Real.rpow_ofNat, one_div]
      rw [h2]
      unfold Work.FM.Fstar
      field_simp
      ring
    rw [L12dens_zfar_Fstar, Work.Construction.L12dens_Fstar hα hα1 s, hFdiv]
  -- The dominating function `s ↦ α·2/(1+s)²` is integrable on `(0,∞)`.
  have hbase : MeasureTheory.IntegrableOn (fun s : ℝ => α * (2 * (s + 1) ^ (-2 : ℝ)))
      (Set.Ioi (0 : ℝ)) := by
    have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => (s + 1) ^ (-2 : ℝ))
        (Set.Ioi (0 : ℝ)) :=
      integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
    have h2 : MeasureTheory.IntegrableOn (fun s : ℝ => (2 * α) * (s + 1) ^ (-2 : ℝ))
        (Set.Ioi (0 : ℝ)) := h1.const_mul (2 * α)
    refine MeasureTheory.IntegrableOn.congr_fun h2 (fun s _ => by ring) measurableSet_Ioi
  -- Bounded measurable factor times integrable function.
  have hexp : MeasureTheory.IntegrableOn
      (fun s : ℝ => (1 - Work.Stability.chi (s / L)) * (α * (2 * (s + 1) ^ (-2 : ℝ))))
      (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Integrable.bdd_mul (c := 1) hbase ?_ ?_
    · exact (continuous_const.sub
        (Work.Stability.chi_continuous.comp (continuous_id.div_const L))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun s => ?_)
      rw [Real.norm_eq_abs]
      have h1 : Work.Stability.chi (s / L) ≤ 1 := Work.Stability.chi_le_one _
      have h2 : 0 ≤ Work.Stability.chi (s / L) := Work.Stability.chi_nonneg _
      rw [abs_of_nonneg (by linarith)]
      linarith
  exact MeasureTheory.IntegrableOn.congr_fun hexp (fun s hs => (hpt s hs).symm) measurableSet_Ioi

end Work.FTS.LocData
