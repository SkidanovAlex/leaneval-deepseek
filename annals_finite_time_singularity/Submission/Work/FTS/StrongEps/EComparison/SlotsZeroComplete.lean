import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- NOTE: `open scoped Real` is what makes the bare `π` in the statement below denote
-- `Real.pi` (the intended semantics; without it the statement does not even elaborate,
-- since the workspace sets `autoImplicit = false`).  It also matches `Work.Spaces.Iθ`,
-- which is defined as `Set.Icc 0 (π/2)` with `π = Real.pi`.
open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

theorem SlotsZeroComplete {Φ : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hInt : ∀ z, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => Φ z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (hmom : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) = 0) :
    ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Φ z θ = 0 := by
  -- `Work.Spaces.Iθ` and `Ioo 0 (π/2)` are the two faces of the angular interval.
  have hIθ : Work.Spaces.Iθ = Set.Icc 0 (π / 2) := by simp only [Work.Spaces.Iθ]
  have hIoo : volume.restrict (Set.Ioo 0 (π / 2)) = volume.restrict Work.Spaces.Iθ := by
    rw [hIθ]
    exact MeasureTheory.restrict_Ioo_eq_restrict_Icc (μ := volume) (a := 0) (b := π / 2)
  -- Every `z`-slice of `Φ` is continuous on the open angular interval.
  have hslice : ∀ z, 0 < z → ContinuousOn (fun θ => Φ z θ) (Set.Ioo 0 (π / 2)) := by
    intro z hz
    exact hcont.comp ((continuous_const.prodMk continuous_id).continuousOn)
      (fun θ hθ => ⟨hz, hθ⟩)
  -- STEP 1.  For a.e. `z > 0` the whole `θ`-slice vanishes: the moment condition against the
  -- complete family `eFam` (completeness = `eFam_complete`) gives vanishing a.e. in `θ`, and the
  -- slice is continuous, so it vanishes everywhere on the open interval.
  have hgoodR : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      ∀ θ ∈ Set.Ioo 0 (π / 2), Φ z θ = 0 := by
    filter_upwards [hmom, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hmom_z hz
    have hcs := hslice z hz
    have hgm : AEStronglyMeasurable (fun θ => Φ z θ) (volume.restrict Work.Spaces.Iθ) := by
      rw [← hIoo]
      exact hcs.aestronglyMeasurable measurableSet_Ioo
    have hae : (fun θ => Φ z θ) =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))] (fun _ => 0) := by
      rw [hIoo]
      exact Work.FTS.PhiStar.Gegenbauer.eFam_complete (fun θ => Φ z θ) hgm (hInt z hz) hmom_z
    intro θ hθ
    exact MeasureTheory.Measure.eqOn_Ioo_of_ae_eq volume hae hcs continuousOn_const hθ
  -- the same statement read on `volume` (with the `0 < z` hypothesis stated explicitly)
  have hgood : ∀ᵐ z ∂volume, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Φ z θ = 0 :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp hgoodR
  -- STEP 2.  Upgrade a.e. `z` to every `z > 0` by joint continuity in `(z,θ)`.
  intro z hz θ hθ
  have hzcont : ContinuousOn (fun z' => Φ z' θ) (Set.Ioi 0) :=
    hcont.comp ((continuous_id.prodMk continuous_const).continuousOn)
      (fun z' hz' => ⟨hz', hθ⟩)
  have hgoodθ : ∀ᵐ z' ∂volume, z' ∈ Set.Ioi 0 → Φ z' θ = 0 := by
    filter_upwards [hgood] with z' hz' hzmem
    exact hz' hzmem θ hθ
  have hae : (fun z' => Φ z' θ) =ᵐ[volume.restrict (Set.Ioi 0)] (fun _ => 0) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr hgoodθ
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hzcont continuousOn_const hz

end Work.FTS.StrongEps.EComparison
