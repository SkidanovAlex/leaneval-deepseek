import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FockBridge.Defs
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.FockBridge.Count` — the counting layer at work

The API of the Fock/particle-number layer of `Submission.Work.FockBridge.Defs`:

* **the update lemmas** — replacing slot `i` by a point on the same side of `B` does not change the
  occupancy (`boxCount_update`, `boxOccupancy_update`, `mem_sectorSet_update_iff`); these are what
  make the box projections `P_{B,i}, Q_{B,i}` *local on the sectors*;
* **the sector masses** — `Σ_k (sector mass) = ∫_{abox} Φ²` (`sum_sectorMass_eq_sqNorm`), each mass
  finite whenever the total is;
* **the count identity** — `localisedNumber = Σ_k k·(sector mass)`;
* **the multiplication-form additivity** — the corpus potential word `qLHSword` is a
  multiplication form (`qLHSword_eq_mul_integral`), hence *sector-additive*
  (`qLHSword_eq_sum_sectorPiece`).  This is the potential half of the Fock decomposition of the
  residual `Residual.fockSectorBridge`; the kinetic half is the locality of the `Q_{B,i}`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.FockBridge

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false

variable {N : ℕ}

/-! ## 1. The update lemmas: the occupancy is local

Replacing slot `i` by a point on the same side of `B` (both in `B`, or both outside) leaves the
occupancy — and hence the counting function and the sectors — unchanged.  This is the combinatorial
content of "`n_B` commutes with `H_B`" (FS `final_v2.tex` l. 3662). -/

theorem boxCount_update (B : Set ℝ³) (x : X N) (i : Fin N) (z : ℝ³)
    (hz : z ∈ B ↔ x i ∈ B) :
    boxCount B (Function.update x i z) = boxCount B x := by
  classical
  rw [boxCount_eq_sum_indicator B (Function.update x i z), boxCount_eq_sum_indicator B x]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self]
    by_cases h : z ∈ B
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hz.mp h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hx => h (hz.mpr hx))]
  · rw [Function.update_of_ne hj]

theorem boxOccupancy_update (B : Set ℝ³) (x : X N) (i : Fin N) (z : ℝ³)
    (hz : z ∈ B ↔ x i ∈ B) :
    boxOccupancy B (Function.update x i z) = boxOccupancy B x := by
  have h := boxCount_update B x i z hz
  simp only [boxCount, Nat.cast_inj] at h
  exact h

theorem mem_sectorSet_update_iff (B : Set ℝ³) (k : ℕ) (x : X N) (i : Fin N) (z : ℝ³)
    (hz : z ∈ B ↔ x i ∈ B) :
    Function.update x i z ∈ sectorSet B k ↔ x ∈ sectorSet B k := by
  rw [mem_sectorSet_iff, mem_sectorSet_iff, boxOccupancy_update B x i z hz]

/-- For `z ∈ B` and `x i ∈ B` the points `x` and `x[i↦z]` lie in the same `B`-sector — the
combinatorial content of the locality of the fibre integral defining `P_{B,i}`. -/
theorem mem_sectorSet_update_of_mem (B : Set ℝ³) {k : ℕ} {x : X N} {i : Fin N} {z : ℝ³}
    (hz : z ∈ B) (hxi : x i ∈ B) :
    (Function.update x i z ∈ sectorSet B k ↔ x ∈ sectorSet B k) :=
  mem_sectorSet_update_iff B k x i z ⟨fun _ => hxi, fun _ => hz⟩

/-! ## 2. The sector masses -/

theorem sectorMassENN_nonneg (L : ℝ) (B : Set ℝ³) (Φ : X N → ℝ) (k : ℕ) :
    0 ≤ sectorMassENN L B Φ k := by simp

theorem sectorMass_nonneg (L : ℝ) (B : Set ℝ³) (Φ : X N → ℝ) (k : ℕ) :
    0 ≤ sectorMass L B Φ k := ENNReal.toReal_nonneg

/-- Each sector mass is bounded by the total `abox`-`L²`-mass. -/
theorem sectorMassENN_le_total (L : ℝ) (B : Set ℝ³) (Φ : X N → ℝ) (k : ℕ) :
    sectorMassENN L B Φ k ≤ ∫⁻ x in abox N L, ENNReal.ofReal ((Φ x) ^ 2) := by
  refine lintegral_mono (fun x => ?_)
  by_cases hx : x ∈ sectorSet B k
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]; exact bot_le

/-- So the sector masses are finite whenever the total is. -/
theorem sectorMassENN_ne_top_of_ne_top (L : ℝ) (B : Set ℝ³) (Φ : X N → ℝ) (k : ℕ)
    (hfin : (∫⁻ x in abox N L, ENNReal.ofReal ((Φ x) ^ 2)) ≠ ⊤) :
    sectorMassENN L B Φ k ≠ ⊤ :=
  ne_top_of_le_ne_top hfin (sectorMassENN_le_total L B Φ k)

/-- **The sector masses are the pieces of the `abox`-`L²`-mass** (the partition of the levels of
the counting function). -/
theorem sum_sectorMassENN_eq (L : ℝ) {B : Set ℝ³} (hB : MeasurableSet B) {Φ : X N → ℝ}
    (hΦ : Measurable Φ) :
    ∑ k ∈ Finset.range (N + 1), sectorMassENN L B Φ k
      = ∫⁻ x in abox N L, ENNReal.ofReal ((Φ x) ^ 2) := by
  classical
  have hmeas : ∀ k ∈ Finset.range (N + 1),
      Measurable ((sectorSet B k).indicator (fun y : X N => ENNReal.ofReal ((Φ y) ^ 2))) := by
    intro k _
    exact ((hΦ.pow_const 2).ennreal_ofReal).indicator (sectorSet_measurable B hB k)
  have key : (∫⁻ x in abox N L, ∑ k ∈ Finset.range (N + 1),
      (sectorSet B k).indicator (fun y : X N => ENNReal.ofReal ((Φ y) ^ 2)) x)
      = ∑ k ∈ Finset.range (N + 1), sectorMassENN L B Φ k :=
    lintegral_finsetSum (Finset.range (N + 1)) hmeas
  rw [← key]
  refine lintegral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only
  exact sum_indicator_sectorSet B (fun y => ENNReal.ofReal ((Φ y) ^ 2)) x

/-- The real-valued form: the sector masses sum to the `abox`-`L²`-mass. -/
theorem sum_sectorMass_eq_sqNorm (L : ℝ) {B : Set ℝ³} (hB : MeasurableSet B) {Φ : X N → ℝ}
    (hΦ : Measurable Φ)
    (hfin : (∫⁻ x in abox N L, ENNReal.ofReal ((Φ x) ^ 2)) ≠ ⊤) :
    ∑ k ∈ Finset.range (N + 1), sectorMass L B Φ k = ∫ x in abox N L, (Φ x) ^ 2 := by
  have hsum := sum_sectorMassENN_eq (N := N) L hB hΦ
  have hto : (∑ k ∈ Finset.range (N + 1), sectorMass L B Φ k)
      = (∑ k ∈ Finset.range (N + 1), sectorMassENN L B Φ k).toReal :=
    (ENNReal.toReal_sum (fun k _ => sectorMassENN_ne_top_of_ne_top L B Φ k hfin)).symm
  rw [hto, hsum]
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x : X N => sq_nonneg (Φ x)))
    ((hΦ.pow_const 2).aestronglyMeasurable)).symm

/-- The `sectorPiece` is a square-root of the sector indicator: `(1_k Φ)² = 1_k Φ²`. -/
theorem sectorPiece_sq (B : Set ℝ³) (k : ℕ) (Φ : X N → ℝ) (x : X N) :
    (sectorPiece B k Φ x) ^ 2 = (sectorSet B k).indicator (fun y => (Φ y) ^ 2) x := by
  by_cases hx : x ∈ sectorSet B k
  · rw [sectorPiece, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [sectorPiece, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- The sector pieces reproduce the density (the pointwise Fock decomposition of `Φ²`). -/
theorem sum_sectorPiece_sq (B : Set ℝ³) (Φ : X N → ℝ) (x : X N) :
    ∑ k ∈ Finset.range (N + 1), (sectorPiece B k Φ x) ^ 2 = (Φ x) ^ 2 := by
  rw [Finset.sum_congr rfl (fun k _ => sectorPiece_sq B k Φ x)]
  exact sum_indicator_sectorSet B (fun y => (Φ y) ^ 2) x

/-- The mass of the sector piece is the sector mass (Bochner form). -/
theorem sectorMass_eq_integral_sectorPiece (L : ℝ) {B : Set ℝ³} (hB : MeasurableSet B)
    {Φ : X N → ℝ} (hΦ : Measurable Φ) (k : ℕ) (hfin : sectorMassENN L B Φ k ≠ ⊤) :
    sectorMass L B Φ k = ∫ x in abox N L, (sectorPiece B k Φ x) ^ 2 := by
  have hrew : sectorMassENN L B Φ k
      = ∫⁻ x in abox N L, ENNReal.ofReal
          (((sectorSet B k).indicator (fun y => (Φ y) ^ 2)) x) := by
    rw [sectorMassENN]
    refine lintegral_congr (fun x => ?_)
    by_cases hx : x ∈ sectorSet B k
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  have hrew2 : (∫⁻ x in abox N L, ENNReal.ofReal
        (((sectorSet B k).indicator (fun y => (Φ y) ^ 2)) x))
      = ∫⁻ x in abox N L, ENNReal.ofReal ((sectorPiece B k Φ x) ^ 2) := by
    refine lintegral_congr (fun x => ?_)
    rw [sectorPiece_sq]
  rw [sectorMass, hrew, hrew2]
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x : X N => sq_nonneg (sectorPiece B k Φ x)))
    (((hΦ.indicator (sectorSet_measurable B hB k)).pow_const 2).aestronglyMeasurable)).symm

/-! ## 3. The count identity -/

/-- **`n_B = Σ_k k·1_{sector k}`** pointwise: the counting function is the sector index. -/
theorem boxCount_mul_sq_eq_sum (B : Set ℝ³) (Φ : X N → ℝ) (x : X N) :
    boxCount B x * (Φ x) ^ 2
      = ∑ k ∈ Finset.range (N + 1), (k : ℝ) * (sectorPiece B k Φ x) ^ 2 := by
  classical
  rw [← sum_sectorPiece_sq B Φ x, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hx : x ∈ sectorSet B k
  · rw [boxCount_eq_of_mem_sectorSet B hx]
  · rw [sectorPiece, Set.indicator_of_notMem hx]
    simp

/-- **The count identity**: the localised particle number is the sector-count-weighted mixture of
the sector masses. -/
theorem localisedNumber_eq_sum_sectorMass (L : ℝ) {B : Set ℝ³} (hB : MeasurableSet B)
    {Φ : X N → ℝ} (hΦ : Measurable Φ) (hfin : (∫⁻ x in abox N L, ENNReal.ofReal ((Φ x) ^ 2)) ≠ ⊤)
    (hint : ∀ k ∈ Finset.range (N + 1),
      IntegrableOn (fun x => (sectorPiece B k Φ x) ^ 2) (abox N L)) :
    localisedNumber L B Φ
      = ∑ k ∈ Finset.range (N + 1), (k : ℝ) * sectorMass L B Φ k := by
  rw [localisedNumber]
  have h1 : (∫ x in abox N L, boxCount B x * (Φ x) ^ 2)
      = ∫ x in abox N L, ∑ k ∈ Finset.range (N + 1),
          (k : ℝ) * (sectorPiece B k Φ x) ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => boxCount_mul_sq_eq_sum B Φ x))
  rw [h1, integral_finsetSum _ (fun k hk => (hint k hk).const_mul _)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [integral_const_mul,
    sectorMass_eq_integral_sectorPiece L hB hΦ k (sectorMassENN_ne_top_of_ne_top L B Φ k hfin)]

/-- The localised number is nonnegative. -/
theorem localisedNumber_nonneg (L : ℝ) (B : Set ℝ³) (Φ : X N → ℝ) :
    0 ≤ localisedNumber L B Φ := by
  rw [localisedNumber]
  refine integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact mul_nonneg (boxCount_nonneg B x) (sq_nonneg _)

/-! ## 4. The multiplication-form additivity (the potential half of the Fock decomposition) -/

/-- `qLHSword` is a multiplication form: it only sees the state through its density `Φ²`. -/
theorem qLHSword_eq_mul_integral {ℓ μ : ℝ} (w w1 : ℝ³ → ℝ³ → ℝ) (Φ : X N → ℝ) :
    qLHSword (N := N) ℓ μ w w1 Φ
      = ∫ x in abox N ℓ, qLHSden N ℓ μ w w1 x * (Φ x) ^ 2 := by
  rw [qLHSword]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only
  rw [show qLHSden N ℓ μ w w1 x
      = - μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))
        + (1 / 2 : ℝ) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)) from rfl]
  ring

/-- **The potential word is sector-additive.**  A multiplication form integrates over a partition
by disjointly supported pieces by the additivity of the integral over the pieces. -/
theorem qLHSword_eq_sum_sectorPiece {ℓ μ : ℝ} {B : Set ℝ³} (w w1 : ℝ³ → ℝ³ → ℝ)
    {Φ : X N → ℝ}
    (hint : ∀ k ∈ Finset.range (N + 1),
      IntegrableOn (fun x => qLHSden N ℓ μ w w1 x * (sectorPiece B k Φ x) ^ 2) (abox N ℓ)) :
    qLHSword (N := N) ℓ μ w w1 Φ
      = ∑ k ∈ Finset.range (N + 1), qLHSword (N := N) ℓ μ w w1 (sectorPiece B k Φ) := by
  rw [qLHSword_eq_mul_integral (μ := μ) (ℓ := ℓ) w w1 Φ]
  have h1 : (∫ x in abox N ℓ, qLHSden N ℓ μ w w1 x * (Φ x) ^ 2)
      = ∫ x in abox N ℓ, ∑ k ∈ Finset.range (N + 1),
          qLHSden N ℓ μ w w1 x * (sectorPiece B k Φ x) ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    dsimp only
    rw [← sum_sectorPiece_sq B Φ x, Finset.mul_sum]
  rw [h1, integral_finsetSum _ (fun k hk => hint k hk)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [qLHSword_eq_mul_integral (μ := μ) (ℓ := ℓ) w w1 (sectorPiece B k Φ)]

end Work.FockBridge
