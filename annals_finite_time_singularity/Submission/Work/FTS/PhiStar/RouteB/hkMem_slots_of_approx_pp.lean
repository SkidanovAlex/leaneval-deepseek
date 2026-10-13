import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.hkMem_slots_joint_of_approx
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.HkMem_of_outer

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `hkMem_slots_of_approx_pp` — the level-`k` honesty of the three elliptic slots from data at
level `k+2`

`Work.FTS.PhiStar.Honesty.hkMem_slots_of_approx` produces the level-`k` `HkMem` of the slots
`z²∂_z²Φ`, `∂_θ²Φ`, `z∂_z∂_θ²Φ` from data at level `k+1`, but only under an *all-`z`* slice
hypothesis `hup` that the a.e./`L²` limit passage cannot supply.  This file proves the `_pp`
("one extra order") variant: with the *same* hypotheses one level higher — `hF`, `hGn`, `hEll`,
`hconv` at `k+2` — the conclusion at level `k` holds unconditionally.

The route is a two-step transfer:

* `SlotsLimit.hkMem_slots_joint_of_approx` instantiated at parameter `k+1` (its hypotheses are
  exactly this statement's, shifted) yields the joint `IntegrableOn` over `Q0` of
  `HkIntegrand α (k+1) (slot r Φ)` for each of the three slots `r : Fin 3`; by Tonelli (the
  helper `lintegral_Ioi_Iθ_lt_top_of_integrableOn_Q0` below) this is the outer `∫⁻`-bound at
  level `k+1`;
* `ClassCHon.SliceMassUpgrade.HkMem_of_outer` upgrades *any* level-`(k+1)` outer bound of a
  slot to `HkMem α k` of that slot — its slice clause comes from the slice-mass upgrade, its
  outer clause from the (weaker, pointwise-dominated) level-`k` bound, which
  `Work.Spaces.HkIntegrand_mono` supplies for free.

The only bookkeeping is the measurability of the two `∫⁻`-integrals (unconditional for a
`SmoothOpen` slot, `CapstoneMeasurability`) and the `Ioo 0 (π/2) ↔ Iθ` conversion.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.PhiStar.RouteB

local notation "Q0" => Work.FTS.EllipticEst.Q0
local notation "Iθ" => Work.Spaces.Iθ
local notation "slot" => Work.FTS.PhiStar.Honesty.SlotsLimit.slot

/-- **Finiteness of the iterated `∫⁻` of a nonnegative function jointly integrable on `Q0`.**

For `0 ≤ g` with `IntegrableOn (uncurry g) Q0`, the iterated lower integral
`∫⁻_z ∫⁻_θ ofReal (g z θ)` over `(0,∞) × Iθ` is finite.  This is Tonelli applied to the
identity `Q0 = (0,∞) ×ˢ (0,π/2)` of `Measures`, modulo the null endpoints of `Iθ`. -/
theorem lintegral_Ioi_Iθ_lt_top_of_integrableOn_Q0 {g : ℝ → ℝ → ℝ}
    (hnn : ∀ z θ, 0 ≤ g z θ)
    (hg : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => g p.1 p.2) Q0) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (g z θ)) < ⊤ := by
  -- the joint integral, as a `∫⁻` over the product measure, is finite
  have hfin : (∫⁻ p in Q0, ENNReal.ofReal (g p.1 p.2)) < ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg
      (Filter.Eventually.of_forall fun p => hnn p.1 p.2)]
    exact ENNReal.ofReal_lt_top
  -- measurability of the integrand for the product of the two restricted measures
  have hae0 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (g p.1 p.2))
      (MeasureTheory.volume.restrict Q0) :=
    hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hae : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (g p.1 p.2))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))) := by
    rw [MeasureTheory.Measure.prod_restrict (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume)]
    exact hae0
  -- Tonelli: the iterated integral over the open quadrant equals the joint one
  have hswap : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal (g z θ))
      = ∫⁻ p in Q0, ENNReal.ofReal (g p.1 p.2) := by
    have h1 := MeasureTheory.lintegral_prod
      (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
      (ν := MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
      (fun p : ℝ × ℝ => ENNReal.ofReal (g p.1 p.2)) hae
    rw [MeasureTheory.Measure.prod_restrict (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume)] at h1
    exact h1.symm
  -- `Iθ` and `(0,π/2)` differ by two null points
  have hI : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (g z θ))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal (g z θ) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact Work.FTS.ClassCHon.SliceMassUpgrade.slm_lintegral_Iθ_eq_Ioo _
  rw [hI, hswap]
  exact hfin

theorem hkMem_slots_of_approx_pp (k : ℕ) (hk : 2 ≤ k) {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {F : ℝ → ℝ → ℝ} (hsmF : Work.FTS.EllipticEst.SmoothOpen F)
    (hF : Work.Spaces.HkMem α (k + 2) F)
    (G : ℕ → ℝ → ℝ → ℝ) (hsmG : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hGn : ∀ n : ℕ, Work.Spaces.HkMem α (k + 2) (G n))
    (hEll : ∀ n : ℕ, Work.FTS.EllipticEst.TT.EllWeakPos α (k + 2) (G n)
      (Work.FTS.PhiStar.Series.psiSeries α (G n)))
    (hconv : Filter.Tendsto (fun n : ℕ => Work.Spaces.HkSq α (k + 2)
      (fun z θ => G n z θ - F z θ)) Filter.atTop (nhds 0))
    {Φ : ℝ → ℝ → ℝ} (hsmΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hEqΦ : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Φ z θ = F z θ)
    (hL2 : ∀ n : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.FTS.PhiStar.Series.psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0)
    (hL2t : Filter.Tendsto (fun n : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        (Work.FTS.PhiStar.Series.psiSeries α (G n) p.1 p.2 - Φ p.1 p.2) ^ 2)
      Filter.atTop (nhds 0)) :
    Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Φ z θ) ∧
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Φ) ∧
      Work.Spaces.HkMem α k (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) z θ) := by
  classical
  -- ### Step 1: the joint integrability of the level-`(k+1)` integrand of each slot
  obtain ⟨hjoint, -, -⟩ :=
    Work.FTS.PhiStar.Honesty.SlotsLimit.hkMem_slots_joint_of_approx (k + 1) (by omega)
      hα hα4 hsmF hF G hsmG hGn hEll hconv hsmΦ hEqΦ hL2 hL2t
  -- ### Step 2: the level-`k` honesty of each slot, from the outer bound two orders down
  have key : ∀ r : Fin 3, Work.Spaces.HkMem α k (slot r.1 Φ) := by
    intro r
    have hsm : Work.FTS.EllipticEst.SmoothOpen (slot r.1 Φ) :=
      Work.FTS.PhiStar.Honesty.SlotsLimit.smoothOpen_slot hsmΦ r.1
    -- the level-`(k+1)` outer bound, from the joint integral over `Q0` (Tonelli)
    have hlt : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) (slot r.1 Φ) z θ)) < ⊤ :=
      lintegral_Ioi_Iθ_lt_top_of_integrableOn_Q0
        (g := fun z θ => Work.Spaces.HkIntegrand α (k + 1) (slot r.1 Φ) z θ)
        (fun z θ => Work.Spaces.HkIntegrand_nonneg α (k + 1) (slot r.1 Φ) z θ) (hjoint r)
    -- name the bound `C` (a real number, so `0 ≤ C` for free)
    set C : ℝ := (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) (slot r.1 Φ) z θ)).toReal with hC
    have hCn : 0 ≤ C := by rw [hC]; exact ENNReal.toReal_nonneg
    have hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) (slot r.1 Φ) z θ))
        ≤ ENNReal.ofReal C := by
      rw [hC]
      exact le_of_eq (ENNReal.ofReal_toReal hlt.ne).symm
    -- the level-`k` bound is free: the integrand only gains summands
    have hfin0 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (slot r.1 Φ) z θ))
        ≤ ENNReal.ofReal C := by
      refine le_trans ?_ hfin1
      refine lintegral_mono_ae (Filter.Eventually.of_forall fun z => ?_)
      refine lintegral_mono fun θ => ?_
      exact ENNReal.ofReal_le_ofReal (Work.Spaces.HkIntegrand_mono α k (slot r.1 Φ) z θ)
    exact Work.FTS.ClassCHon.SliceMassUpgrade.HkMem_of_outer (α := α) (k := k)
      (F := slot r.1 Φ) (C₀ := C) (C₁ := C) hCn hCn hsm
      (Work.FTS.PhiStar.Honesty.aemeasurable_slice_ofReal_HkIntegrand α k hsm)
      (Work.FTS.PhiStar.Honesty.aemeasurable_lintegral_HkIntegrand α k hsm)
      hfin0
      (Work.FTS.PhiStar.Honesty.aemeasurable_slice_ofReal_HkIntegrand α (k + 1) hsm)
      (Work.FTS.PhiStar.Honesty.aemeasurable_lintegral_HkIntegrand α (k + 1) hsm)
      hfin1
  -- ### Step 3: read off the three slots in the shape of the statement
  exact ⟨key (0 : Fin 3), key (1 : Fin 3), key (2 : Fin 3)⟩

end Work.FTS.PhiStar.RouteB

end
