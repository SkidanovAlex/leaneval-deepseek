import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The loss weight is at least `1` (both factors are `≥ 1`).  This is the ingredient that lets an
absolute constant (the constant of the fibre/cut bound) be absorbed by
`lossWeight A ρ l₁ l₂ k₁ k₂` in the target: `A := 4` and `C := fun _ => ⌈D⌉₊` work. -/
theorem one_le_lossWeight_of_nonneg (c ρ : ℝ) (hc : 0 ≤ c) (hρ : 0 ≤ ρ)
    (l₁ l₂ k₁ k₂ : ℕ) : 1 ≤ Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂ := by
  have hnn0 : (0:ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁:ℤ) (k₂:ℤ) := by
    unfold Work.Analysis.EndVar.lmax; positivity
  have hnn : (0:ℝ) ≤ ((Work.Analysis.EndVar.lmax l₁ l₂ (k₁:ℤ) (k₂:ℤ) : ℤ) : ℝ) := by
    exact_mod_cast hnn0
  simp only [Work.KMTAreas.A7.lossWeight, Work.KMTAreas.A7.lmaxR]
  have h1 : (1:ℝ) ≤ (1 + ((Work.Analysis.EndVar.lmax l₁ l₂ (k₁:ℤ) (k₂:ℤ) : ℤ) : ℝ)) ^ c :=
    Real.one_le_rpow (by linarith) hc
  have h2 : (1:ℝ) ≤ (2:ℝ) ^ (c * ρ * ((Work.Analysis.EndVar.lmax l₁ l₂ (k₁:ℤ) (k₂:ℤ) : ℤ) : ℝ)) := by
    apply Real.one_le_rpow (by norm_num)
    exact mul_nonneg (mul_nonneg hc hρ) hnn
  exact le_trans (by norm_num : (1:ℝ) ≤ 1 * 1) (mul_le_mul h1 h2 (by norm_num) (by linarith))

/-- **The `g`-side bump `mStargF d u` is `1` on the disc of radius `2^{-2du}/2`** (the plateau).
This is the `hplateau`/`hm` ingredient of every cut/range statement (`FiberOpCutTex`,
`fiberOpCutBoundUniform`, `fiberOpRephasingUniformBound`). -/
theorem mStargF_eq_one (d u : ℕ) {θ : ℝ}
    (h : |θ| ≤ (1/2) * (2:ℝ)^(-((d:ℤ)*2*(u:ℤ)))) :
    Work.KMTAreas.A7.mStargF d u θ = 1 := by
  unfold Work.KMTAreas.A7.mStargF Work.Analysis.IonescuWainger.etaCut
  rw [div_eq_mul_inv, ← zpow_neg, neg_neg]
  refine Work.KMTContract.kmtEta_one ?_
  rw [abs_mul, abs_of_nonneg (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)]
  calc |θ| * (2:ℝ)^((d:ℤ)*2*(u:ℤ))
      ≤ ((1/2) * (2:ℝ)^(-((d:ℤ)*2*(u:ℤ)))) * (2:ℝ)^((d:ℤ)*2*(u:ℤ)) :=
        mul_le_mul_of_nonneg_right h (zpow_nonneg (by norm_num) _)
    _ = 1/2 := by
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
          show -((d:ℤ)*2*(u:ℤ)) + (d:ℤ)*2*(u:ℤ) = 0 from by ring, zpow_zero, mul_one]

/-- **The `g`-side bump `mStargF d u` vanishes outside the disc of radius `2^{-2du}`** (the support).
This is the `hsupp` ingredient of every cut/range statement. -/
theorem mStargF_eq_zero (d u : ℕ) {θ : ℝ}
    (h : (2:ℝ)^(-((d:ℤ)*2*(u:ℤ))) < |θ|) :
    Work.KMTAreas.A7.mStargF d u θ = 0 := by
  unfold Work.KMTAreas.A7.mStargF Work.Analysis.IonescuWainger.etaCut
  rw [div_eq_mul_inv, ← zpow_neg, neg_neg]
  refine Work.KMTContract.kmtEta_zero ?_
  rw [abs_mul, abs_of_nonneg (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)]
  have hbal : (2:ℝ)^(-((d:ℤ)*2*(u:ℤ))) * (2:ℝ)^((d:ℤ)*2*(u:ℤ)) = 1 := by
    rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
      show -((d:ℤ)*2*(u:ℤ)) + (d:ℤ)*2*(u:ℤ) = 0 from by ring, zpow_zero]
  nlinarith [h, abs_nonneg θ, zpow_pos (by norm_num : (0:ℝ) < 2) ((d:ℤ)*2*(u:ℤ)), hbal]

/-- **The loss weight is monotone in its exponent** (`c ↦ (1+L)^c·2^{cρL}` is increasing for
`c ≥ 0`, `ρ ≥ 0`, `L ≥ 0`).  This is what lets the two cases of the assembly (`L ≤ B` and `L > B`)
be compared at the larger of the two exponents `A₁`, `A₂`. -/
theorem lossWeight_mono {c c' ρ : ℝ} (hcc : c ≤ c') (hc : 0 ≤ c) (hρ : 0 ≤ ρ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂
      ≤ Work.KMTAreas.A7.lossWeight c' ρ l₁ l₂ k₁ k₂ := by
  have hL : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR]
    have h : (0 : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      rw [Work.Analysis.EndVar.lmax]; omega
    exact_mod_cast h
  have h1 : (1 : ℝ) ≤ 1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by linarith
  have hA : (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ c
      ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ c' :=
    Real.rpow_le_rpow_of_exponent_le h1 hcc
  have hB : (2 : ℝ) ^ (c * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)
      ≤ (2 : ℝ) ^ (c' * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
    have hsub : (0 : ℝ) ≤ (c' - c) * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hcc) hρ) hL
    nlinarith [hsub]
  unfold Work.KMTAreas.A7.lossWeight
  exact mul_le_mul hA hB (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (by linarith) _)

end

end Work.KMTAreas.A7Hi
