import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/leaf_pairIntegral_le_HkSq`

The single-leaf pairing `∫_z ∫_θ ρ z θ · (D_z^b D_θ^a u z θ)²` of a leaf weight `ρ`
(`IsLeafW α a ρ`) at a slot of order `a + b ≤ 1` is dominated by the squared `ℋ¹`-norm
of `u` — with constant `1`.

The content is entirely pointwise.  On the *open* quadrant every leaf weight `ρ` of the
slot `a` is dominated by the slot weight `slotW α a` (`IsLeafW_le`), which in turn prices
the square of the slot derivative by the `ℋ¹`-integrand of `u`
(`H6Pair6Aux.slotW_dom`): together these give

  `ρ z θ · (D_z^bD_θ^a u z θ)² ≤ HkIntegrand α 1 u z θ`    (`θ ∈ (0, π/2)`),

which is `H6Pair6Aux.domLeaf_all`.  The two angular endpoints `θ = 0`, `θ = π/2` carry no
mass for `volume.restrict Iθ` (they form the null set on which the comparison can fail,
because there `sin(2θ) = 0` and the weights `w²σ^{-η}`, `w²σ^{-γ}` degenerate), so the
integral estimate follows by `integral_mono_of_nonneg`.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

open scoped Real Topology
open MeasureTheory

/-- For `volume.restrict Iθ` the two endpoints `0`, `π/2` are null, so `θ` lies in the open
interval almost everywhere.  (`Icc 0 (π/2)` and `Ioo 0 (π/2)` agree a.e.) -/
private theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- **The single-leaf pairing against the squared `ℋ^m`-norm.**  For a leaf weight `ρ` of
the slot `a`, a slot `(a,b)` of order at most `m` and an honest `ℋ^m`-datum `f`, the
leaf-weighted slot energy is dominated by `HkSq α m f` (with constant `1`). -/
private theorem leafSlot_le_HkSq {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {m a b : ℕ}
    (hmem : Work.Spaces.HkMem α m f) (hab : a + b ≤ m)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkSq α m f := by
  have hIoo := ae_mem_Ioo_Iθ
  -- the angular slice estimate, for every `z ∈ Iz`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f z θ := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z hz) ?_
    · filter_upwards [hIoo] with θ hθ
      exact mul_nonneg
        (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _)
    · filter_upwards [hIoo] with θ hθ
      exact Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα hρ hθ hab
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hmem.2 ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    exact MeasureTheory.integral_nonneg_of_ae (hIoo.mono fun θ hθ =>
      mul_nonneg
        (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _))
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    exact hslice z hz

theorem leaf_pairIntegral_le_HkSq {α : ℝ} (hα : 0 < α) {u : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 1 u) {a b : ℕ} (hab : a + b ≤ 1)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (Work.Spaces.mixed b a u z θ) ^ 2) ≤ Work.Spaces.HkSq α 1 u :=
  leafSlot_le_HkSq hα hmem hab hρ

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
