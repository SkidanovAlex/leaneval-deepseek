import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.AeCrux.AeVLib.Main
import Submission.Work.FTS.EllSol.HeavyFlat.Defs
import Submission.Work.FTS.EllSol.HeavyFlat.flatHeavy
import Submission.Work.FTS.EllSol.HeavyFlat.omOfFlat

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.EllipticEst.AeCrux

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

set_option linter.unusedSimpArgs false

/-
The *outer* `z`-integrability of the weighted slice functional of the mixed slot
`V = z ∂_z∂_θu`: the second hypothesis of `remov/AeI1PaperOfHonest` (through
`remov/AeI1PaperHolds`), and — up to the harmless factor `w z ^ 2 ≥ 1` — the second conjunct of
`Cores/AeStep2Aux/aeMixedAe_mem`.  With `1 ≤ w z` for `z > 0` the weighted statement implies the
unweighted one used there, so this is the form the `remov` route consumes.

## The route

`aeVGlobalFin2_of_mixIntS` (below) shows that the target is *exactly*
`IntegrableOn (Work.EllipticEst.Core.mixIntS u) Work.Spaces.Iz`, i.e. the outer `z`-integrability
of the mixed slot `D_z∂_θu = z∂_z∂_θu` of the datum.  That is reduced here to the paper's
two-dimensional Agmon interpolation in the flat, shifted, heavy-weight form
`Work.FTS.EllSol.HeavyFlat.FlatHeavy` (a *proved* node, see `Submission/Work/FTS/EllSol/Shift2Flat/`
and `.../HeavyFlat/`):

* `Work.FTS.EllSol.HeavyFlat.flatHeavy : FlatHeavy` — the flat, `b`-shifted, `σ_η`-weighted
  mixed-slot finiteness (the frequency/Plancherel/Fatou route of
  `Shift2Flat/NOTES_mixedSlot_route.md`);
* `Work.FTS.EllSol.HeavyFlat.omOfFlat : FlatHeavy → OmHeavy` — the decomposition
  `Ω(t) = Σ_{k<5} C(4,k) e^{2 b_k t}`;
* `mixIntS_integrableOn_Ioi` (in `AeVLib.Main`) — the pull-back `g(t,θ) = u(e^t,θ)` of the datum,
  the three diagonal slots coming from `AeData` (`HkMem α 0 G` is not needed: only
  `HkMem α 0 (z∂_zu)`, `HkMem α 0 (z²∂_z²u)`, `HkMem α 0 (∂_θ²u)` enter, and `D_z(D_zu)` is
  dominated by the first and the second), the reverse change of variables `z = e^t`, and
  `∫⁻ ofReal (mixIntS u) < ⊤`.

The module `AeVLib.Meas`/`Slots`/`Pullback`/`Main` contain the whole measure-theoretic and
coordinate layer of that reduction; `AeCoreSlots` supplies the remaining `AeData`-side slots.
-/

/-- The target is exactly `IntegrableOn (mixIntS u) Iz`: the two sets `Iθ = Icc 0 (π/2)` and
`Ioo 0 (π/2)` differ by two points, so the `θ`-integrals agree at every `z` (the Bochner value
is a function of the restricted measure, junk value `0` included), and `Ioi 0` differs from
`Iz = Ici 0` by one point. -/
theorem aeVGlobalFin2_of_mixIntS {u : ℝ → ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn (Work.EllipticEst.Core.mixIntS u) Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioi (0 : ℝ)) := by
  -- `Icc 0 (π/2)` and `Ioo 0 (π/2)` differ by two points
  have hIcc : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[MeasureTheory.volume]
      Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)).symm
  -- the two functions agree at every `z`
  have hpoint : Work.EllipticEst.Core.mixIntS u
      = fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    funext z
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
        (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    congr 1
    exact MeasureTheory.setIntegral_congr_set hIcc
  -- `volume.restrict (Ici 0) = volume.restrict (Ioi 0)`
  have hIci_meas : (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ici (0 : ℝ))
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm
  have h1 : MeasureTheory.Integrable (Work.EllipticEst.Core.mixIntS u)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h2 : MeasureTheory.Integrable (Work.EllipticEst.Core.mixIntS u)
        (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))) := h
    rwa [← hIci_meas]
  rw [hpoint] at h1
  exact h1

/-- **The target.**  The paper's two-dimensional Agmon interpolation is available in flat form as
the *proved* node `HeavyFlat.flatHeavy : FlatHeavy`, and `HeavyFlat.omOfFlat` turns it into the
`Ω`-weighted form `OmHeavy`.  Feeding that into the proved `mixIntS_integrableOn_Ioi` gives
`IntegrableOn (mixIntS u) (Ioi 0)`, and `aeVGlobalFin2_of_mixIntS` rewrites the target as exactly
that statement. -/
theorem AeVGlobalFin2 {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioi (0 : ℝ)) := by
  have hOm : Work.FTS.EllSol.HeavyFlat.OmHeavy :=
    Work.FTS.EllSol.HeavyFlat.omOfFlat Work.FTS.EllSol.HeavyFlat.flatHeavy
  have hIoi := mixIntS_integrableOn_Ioi hOm h hU
  have hIz : MeasureTheory.IntegrableOn (Work.EllipticEst.Core.mixIntS u) Work.Spaces.Iz := by
    have h' : (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi (0 : ℝ))
        = MeasureTheory.volume.restrict Work.Spaces.Iz := by
      rw [Work.Spaces.Iz]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))
    have h2 : MeasureTheory.Integrable (Work.EllipticEst.Core.mixIntS u)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [← h']
      exact hIoi
    exact h2
  exact aeVGlobalFin2_of_mixIntS hIz

end Work.FTS.EllipticEst.AeCrux
