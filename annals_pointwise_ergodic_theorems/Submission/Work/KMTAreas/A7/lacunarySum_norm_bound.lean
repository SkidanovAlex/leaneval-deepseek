import Mathlib
import Submission.Work.Analysis.CzShift.lacunary_sums

/-!
# The lacunary sum norm bound (Area A7)

For a `lam`-lacunary family of positive scales `σ : ι → ℝ` on a finite set `D`, a non-zero
frequency `ξ`, and a family `f : ι → ℂ` which is

* bounded by `C · (σ i · |ξ|)` on the scales with `σ i · |ξ| ≤ 1`, and
* *supported* on those scales (i.e. vanished once `1 < σ i · |ξ|`),

one has `∑_{i ∈ D} ‖f i‖ ≤ 2 C / (1 - lam⁻¹)`.

The proof splits `D` at the cutoff `σ i · |ξ| = 1` (outside which `f` vanishes), applies the
pointwise bound, and then bounds the resulting lacunary weight sum
`∑_{σ i |ξ| ≤ 1} σ i |ξ|` using the head-sum estimate of
`Work.Analysis.CzShift.lacunary_sums` at threshold `2` (for the rescaled family
`i ↦ σ i · |ξ|`, which is lacunary with the same parameter `lam`).
-/

namespace Work.KMTAreas.A7

open Finset

variable {ι : Type*}

/-- Rescaling a lacunary family on the right by a positive constant preserves lacunarity. -/
private lemma LacunaryFam.mul_right {D : Finset ι} {σ : ι → ℝ} {lam c : ℝ} (hc : 0 < c)
    (hlac : Work.Analysis.CzShift.LacunaryFam lam D σ) :
    Work.Analysis.CzShift.LacunaryFam lam D (fun i => σ i * c) := by
  refine ⟨fun i hi => mul_pos (hlac.1 i hi) hc, ?_⟩
  intro i hi j hj hij
  have h := hlac.2 i hi j hj hij
  have hmin : min (σ i * c) (σ j * c) = min (σ i) (σ j) * c := by
    rcases le_total (σ i) (σ j) with hle | hle
    · rw [min_eq_left hle, min_eq_left (mul_le_mul_of_nonneg_right hle hc.le)]
    · rw [min_eq_right hle, min_eq_right (mul_le_mul_of_nonneg_right hle hc.le)]
  have hmax : max (σ i * c) (σ j * c) = max (σ i) (σ j) * c := by
    rcases le_total (σ i) (σ j) with hle | hle
    · rw [max_eq_right hle, max_eq_right (mul_le_mul_of_nonneg_right hle hc.le)]
    · rw [max_eq_left hle, max_eq_left (mul_le_mul_of_nonneg_right hle hc.le)]
  rw [hmin, hmax, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h hc.le

/-- The lacunary weight sum at the unit cutoff: for a `lam`-lacunary family of positive scales
`σ`, the sum of the (rescaled) scales not exceeding `1` is bounded by `2 / (1 - lam⁻¹)`. -/
private lemma sum_scale_le_one {D : Finset ι} {σ : ι → ℝ} {lam c : ℝ} (hlam : 1 < lam) (hc : 0 < c)
    (hlac : Work.Analysis.CzShift.LacunaryFam lam D σ) :
    ∑ i ∈ D.filter (fun i => σ i * c ≤ 1), σ i * c ≤ 2 / (1 - lam⁻¹) := by
  have hlac' := LacunaryFam.mul_right hc hlac
  have hhead :=
    (Work.Analysis.CzShift.lacunary_sums D (fun i => σ i * c) hlam hlac').2.2 2 (by norm_num)
  -- `hhead : ∑ i ∈ D.filter (fun i => σ i * c < 2), σ i * c / 2 ≤ 1 / (1 - lam⁻¹)`
  have hmul := mul_le_mul_of_nonneg_right hhead (show (0 : ℝ) ≤ 2 by norm_num)
  rw [Finset.sum_mul] at hmul
  have h2 : ∑ i ∈ D.filter (fun i => σ i * c < 2), σ i * c ≤ 2 / (1 - lam⁻¹) := by
    have hcongr : ∑ i ∈ D.filter (fun i => σ i * c < 2), (σ i * c / 2) * 2
        = ∑ i ∈ D.filter (fun i => σ i * c < 2), σ i * c :=
      Finset.sum_congr rfl (fun i _ => by ring)
    have hh : (1 / (1 - lam⁻¹)) * 2 = 2 / (1 - lam⁻¹) := by ring
    rw [hcongr, hh] at hmul
    exact hmul
  have hsub : D.filter (fun i => σ i * c ≤ 1) ⊆ D.filter (fun i => σ i * c < 2) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, lt_of_le_of_lt hi.2 (by norm_num)⟩
  have hss : ∑ i ∈ D.filter (fun i => σ i * c ≤ 1), σ i * c
      ≤ ∑ i ∈ D.filter (fun i => σ i * c < 2), σ i * c :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ =>
      (mul_pos (hlac.1 i (Finset.mem_of_mem_filter i hi)) hc).le)
  linarith

theorem lacunarySum_norm_bound {ι : Type*} {D : Finset ι} {σ : ι → ℝ} {lam : ℝ} (hlam : 1 < lam)
    (hlac : Work.Analysis.CzShift.LacunaryFam lam D σ) {ξ : ℝ} (hξ : ξ ≠ 0) {f : ι → ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hf : ∀ i ∈ D, σ i * |ξ| ≤ 1 → ‖f i‖ ≤ C * (σ i * |ξ|))
    (hzero : ∀ i ∈ D, 1 < σ i * |ξ| → f i = 0) :
    ∑ i ∈ D, ‖f i‖ ≤ 2 * C / (1 - lam⁻¹) := by
  classical
  have hξpos : 0 < |ξ| := abs_pos.mpr hξ
  set E : Finset ι := D.filter (fun i => σ i * |ξ| ≤ 1) with hE
  -- outside `E` the family `f` vanishes
  have hsumE : ∑ i ∈ D, ‖f i‖ = ∑ i ∈ E, ‖f i‖ := by
    refine (Finset.sum_subset (s₁ := E) (s₂ := D) ?_ ?_).symm
    · intro i hi
      rw [hE] at hi
      exact Finset.mem_of_mem_filter i hi
    · intro i hiD hiE
      have hnot : ¬ (σ i * |ξ| ≤ 1) := by
        intro hle
        exact hiE (by rw [hE]; exact Finset.mem_filter.mpr ⟨hiD, hle⟩)
      have hgt : 1 < σ i * |ξ| := lt_of_not_ge hnot
      rw [hzero i hiD hgt, norm_zero]
  rw [hsumE]
  -- pointwise bound on `E`, then factor out `C`
  have hstep2 : ∑ i ∈ E, ‖f i‖ ≤ C * ∑ i ∈ E, σ i * |ξ| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hiD : i ∈ D := by rw [hE] at hi; exact Finset.mem_of_mem_filter i hi
    have hle : σ i * |ξ| ≤ 1 := by rw [hE] at hi; exact (Finset.mem_filter.mp hi).2
    exact hf i hiD hle
  have hstep3 : ∑ i ∈ E, σ i * |ξ| ≤ 2 / (1 - lam⁻¹) := by
    rw [hE]
    exact sum_scale_le_one hlam hξpos hlac
  calc ∑ i ∈ E, ‖f i‖ ≤ C * ∑ i ∈ E, σ i * |ξ| := hstep2
    _ ≤ C * (2 / (1 - lam⁻¹)) := mul_le_mul_of_nonneg_left hstep3 hC
    _ = 2 * C / (1 - lam⁻¹) := by ring

end Work.KMTAreas.A7
