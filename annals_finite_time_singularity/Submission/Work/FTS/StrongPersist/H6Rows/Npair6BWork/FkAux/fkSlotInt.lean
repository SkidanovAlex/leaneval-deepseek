/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FkAux/fkSlotInt` — the leaf-weighted slot integral of a datum in `DatData`

The requested lemma `Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt`: for a datum
`f` satisfying `T6Coef.DatData α f M` (in particular honest `ℋ⁶`-membership and `C^∞` on the
open quadrant) and a slot `(a,b)` of order `≤ 6` paired against a *leaf weight* `ρ` of
`IsLeafW α a ρ`, the leaf-weighted slot energy

  `∫_z ∫_θ ρ z θ · (D_z^b D_θ^a f z θ)²`

is an honest iterated integral (both integrals exist) and is bounded by `C · HkSq α 6 f` with a
universal constant.

The content is the pointwise domination on the open quadrant,

  `ρ z θ · (mixed b a f z θ)² ≤ HkIntegrand α 6 f z θ`   (`θ ∈ (0,π/2)`, `a + b ≤ 6`),

supplied by `H6Pair6Aux.domLeaf_all` (for `a = 0` this is the `D_z^b`-slot with `w²σ^{-η}`,
for `a ≥ 1` the mixed slot `(mixed b a f · Wt)²` with `Wt² = w²σ^{-γ}`), together with

* the a.e. strong measurability of the angular slices, from `SmoothOpen f` (the uncurried
  integrand is continuous on the open quadrant, and `θ ∈ (0,π/2)` is conull in `Iθ`);
* the a.e. strong measurability of the `z`-marginal, from `aesm_of_continuousOn_Qd` and
  `AEStronglyMeasurable.integral_prod_right'`;
* the triviality of the slice at `z = 0`, where every leaf weight vanishes (`w 0 = 0`).

The *value* of the integral is then the single-slot energy estimate `slotEnergyLeHkSq` (constant
`1`), which is the `ℋ⁶`-slot energy of a leaf weight.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.slotEnergyLeHkSq
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbAux.SlotPriceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The two endpoints are null for the angular measure -/

/-- For `volume.restrict Iθ` the two endpoints `0`, `π/2` are null, so `θ` lies in the open
interval almost everywhere. -/
private theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## The leaf weights: vanishing at `z = 0`, and continuity on the open quadrant -/

/-- Every leaf weight vanishes at `z = 0` (the radial factor `w 0` is `0`). -/
private theorem leafW_zero {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (θ : ℝ) : ρ 0 θ = 0 := by
  rcases hρ with h | h | h
  · rw [h, Work.FTS.TransportS.leafEta, Work.Spaces.w]; norm_num
  · rw [h, Work.FTS.TransportS.leafOne, Work.Spaces.w]; norm_num
  · rw [h.2, Work.FTS.TransportS.leafGam, Work.Spaces.w]; norm_num

/-- Every leaf weight is continuous on the open quadrant (each is a `canonW q`). -/
private theorem leafW_continuousOn {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rcases hρ with h | h | h
  · rw [h]
    exact Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbAux.continuousOn_canonW Work.Spaces.eta
  · rw [h]
    refine (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbAux.continuousOn_canonW 0).congr ?_
    intro p _
    simp only [Work.FTS.TransportS.SlotT2.canonW, Work.FTS.TransportS.leafOne,
      neg_zero, Real.rpow_zero, mul_one]
  · rw [h.2]
    exact Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbAux.continuousOn_canonW
      (Work.Spaces.gam α)

/-- The uncurried leaf-weighted slot integrand is continuous on the open quadrant. -/
private theorem leafSlot_continuousOn {α : ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (leafW_continuousOn hρ).mul ((hsm.mixed b a).continuousOn.pow 2)

/-! ## Integrability of the angular slice, and of the `z`-marginal -/

/-- **The angular slice of the leaf-weighted slot is integrable on `Iθ`**, for every `z ∈ Iz`:
at `z = 0` the integrand is identically zero, and for `z > 0` it is dominated a.e. by the
integrable slice `HkIntegrand α 6 f z ·` of the `ℋ⁶`-datum. -/
private theorem sliceIntegrable_leafSlot :
    ∀ α ∈ Set.Ioc 0 1, ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ := by
  intro α hα f a b ρ hsm hm hab hleaf z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hzero : (fun θ : ℝ => ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [← hz0, leafW_zero hleaf θ, zero_mul]
    rw [hzero]
    exact integrableOn_zero
  · refine MeasureTheory.Integrable.mono' (hm.1 z hz)
      (Work.Spaces.aesm_slice_of_continuousOn_Qd _ (leafSlot_continuousOn hsm hleaf) hzpos) ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg
      (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      (sq_nonneg _))]
    exact Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα.1 hleaf hθ hab

/-- **The `z`-marginal of the leaf-weighted slot is integrable on `Iz`.**  a.e. in `z` it is
dominated by the integrable marginal `z ↦ ∫_θ HkIntegrand α 6 f z θ` of the datum (which is the
second conjunct of `HkMem α 6 f`); the a.e. strong measurability comes from the joint
continuity on the open quadrant via `AEStronglyMeasurable.integral_prod_right'`. -/
private theorem zIntegrable_leafSlot :
    ∀ α ∈ Set.Ioc 0 1, ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        Work.Spaces.Iz := by
  intro α hα f a b ρ hsm hm hab hleaf _
  have hX : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (leafSlot_continuousOn hsm hleaf)
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hX.integral_prod_right' (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa using h
  refine MeasureTheory.Integrable.mono' hm.2 haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  have h1 : ‖∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2‖
      ≤ ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    exact Real.norm_of_nonneg (mul_nonneg
      (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      (sq_nonneg _))
  have h2 : (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hm.1 z hz) ?_
    · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      exact mul_nonneg
        (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
        (sq_nonneg _)
    · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      exact Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα.1 hleaf hθ hab
  linarith

/-! ## The requested lemma -/

theorem fkSlotInt : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      MeasureTheory.IntegrableOn
          (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
          Work.Spaces.Iz ∧
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
          (fun θ => ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ) ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        ≤ C * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.slotEnergyLeHkSq
  refine ⟨C, hCpos, fun α hα f M a b ρ hdat hab hleaf => ?_⟩
  have hslice := sliceIntegrable_leafSlot α hα f a b ρ hdat.sm hdat.h6 hab hleaf
  exact ⟨zIntegrable_leafSlot α hα f a b ρ hdat.sm hdat.h6 hab hleaf hslice, hslice,
    hC (α := α) (f := f) 6 hα.1 hdat.h6 a b ρ hab hleaf⟩

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
