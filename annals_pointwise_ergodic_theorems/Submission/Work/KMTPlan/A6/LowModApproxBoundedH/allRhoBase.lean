import Mathlib
import Submission.Work.KMTPlan.A6.LowModApproxBoundedH.lvl0Transfer
import Submission.Work.KMTAreas.A7.LoModelLargeScaleHolds

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.LowModApproxBoundedH

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7

/-!
# The level-`0` clipped estimate at *every* `ρ > 0`

The goal of this file is the unconditional statement

  `∀ ρ : ℝ, 0 < ρ → Lvl0 P r C₀ B ρ`

for every polynomial `P` of degree `≥ 2` (and also for `P.natDegree ≤ 1`, but that case is not
needed here).  The paper's linear estimate `(lin-2)` at arithmetic height `0`
(`Work.KMTAreas.A7.LoGLinVarClipped`, used through `lvl0DegTwo`) is available only for
`ρ ≤ 1/(2C₀)`; the `ρ`-transfer `Work.KMTPlan.A6.LowModApproxBoundedH.lvl0Transfer` removes the
smallness restriction (the two clips differ only on finitely many scales).  This file records the
combination, *without* importing `lvl0DegTwo` (which imports the target file
`LowModApproxBoundedH.mainPartTupleVar` and would create an import cycle): the small-`ρ` case is
reproved here as `lvl0DegTwoBase`.

The exports are

* `lmaxR_eq_lcL_base`, `lmaxR_nonneg_base` — local copies of the two elementary facts about
  `lmaxR` (their originals live in `mainPartTupleVar.lean`);
* `lvl0DegTwoBase` — `Lvl0 P r C₀ B ρ` for `2 ≤ P.natDegree` and `ρ ≤ 1/(2C₀)`;
* `Lvl0_all` — `Lvl0 P r C₀ B ρ` for **every** `ρ > 0`.
-/

/-- `lmaxR` is the real cast of `lcL`. -/
lemma lmaxR_eq_lcL_base (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ = (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℝ) := by
  rw [Work.KMTAreas.A7.lmaxR, ← Work.KMTPlan.A6.lcL_eq]
  push_cast
  ring

lemma lmaxR_nonneg_base (l₁ l₂ k₁ k₂ : ℕ) : 0 ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR_eq_lcL_base]
  positivity

/-- **The level-`0` clipped estimate for `2 ≤ P.natDegree` and `ρ ≤ 1/(2C₀)`.**

Directly from the proved `Work.KMTAreas.A7.LoGLinVarClipped` (the paper's (lin-2) at arithmetic
height `0`, exponents `(p,p)`, `1 < p < ∞`): at `p = 2` its conclusion is the level-`0` family
`lvl0Fam` with the clip `core ρ C₀ l₁ l₂ k₁ k₂`; the loss `lossWeight 4 ρ l₁ l₂ k₁ k₂` is absorbed
into a constant using `lmaxR ≤ B`. -/
theorem lvl0DegTwoBase (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (B : ℕ) :
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / (2 * (C₀ : ℝ)) → Lvl0 P r C₀ B ρ := by
  intro ρ hρ hρC
  classical
  have hρ1 : ρ ≤ 1 := by
    have h2 : (1 : ℝ) ≤ 2 * (C₀ : ℝ) := by
      have h1 : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
      linarith
    have hpos : (0 : ℝ) < 2 * (C₀ : ℝ) := by linarith
    calc ρ ≤ 1 / (2 * (C₀ : ℝ)) := hρC
      _ ≤ 1 := by rw [div_le_one hpos]; linarith
  have hloss : ∀ (l₁ l₂ k₁ k₂ : ℕ), lcL l₁ l₂ k₁ k₂ ≤ B →
      Work.KMTAreas.A7.lossWeight 4 ρ l₁ l₂ k₁ k₂
        ≤ (1 + (B : ℝ)) ^ (4 : ℝ) * (2 : ℝ) ^ (4 * ρ * (B : ℝ)) := by
    intro l₁ l₂ k₁ k₂ hlcL
    have hL0 : 0 ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
      rw [lmaxR_eq_lcL_base]; positivity
    have hLB : Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ ≤ (B : ℝ) := by
      rw [lmaxR_eq_lcL_base]; exact_mod_cast hlcL
    rw [Work.KMTAreas.A7.lossWeight_eq]
    refine mul_le_mul (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
      (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by nlinarith [mul_le_mul_of_nonneg_left hLB (le_of_lt hρ)]))
      (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by positivity) _)
  have hbase : ∀ Λ : NNReal, 1 < Λ → ∃ D : NNReal,
      ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (l₁ l₂ k₁ k₂ : ℕ), lcL l₁ l₂ k₁ k₂ ≤ B → ∀ (t : ℝ),
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ F : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => lvl0Fam ρ P C₀ a l₁ l₂ k₁ k₂ t F n x)) 2 MeasureTheory.Measure.count
          ≤ (D : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
    intro Λ hΛ
    obtain ⟨C, hCpos, hC⟩ :=
      LoGLinVarClipped P hdeg C₀ hC₀ ρ hρ hρ1 hρC 2 (by norm_num) (by norm_num) r hr Λ hΛ
    set T : ℝ := (1 + (B : ℝ)) ^ (4 : ℝ) * (2 : ℝ) ^ (4 * ρ * (B : ℝ)) with hT
    refine ⟨(((⌈max 1 (C * T)⌉₊ : ℕ)) : NNReal), ?_⟩
    intro a ha ha1 l₁ l₂ k₁ k₂ hlcL t ht F
    have hbound := hC a ha ha1 l₁ l₂ k₁ k₂ t ht F
    have hloss' : Work.KMTAreas.A7.lossWeight 4 ρ l₁ l₂ k₁ k₂ ≤ T := by
      rw [hT]; exact hloss l₁ l₂ k₁ k₂ hlcL
    have hconst : ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight 4 ρ l₁ l₂ k₁ k₂)
        ≤ (((⌈max 1 (C * T)⌉₊ : ℕ) : NNReal) : ENNReal) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal ?_
      refine le_trans (le_trans (mul_le_mul_of_nonneg_left hloss' hCpos.le)
        (le_max_right (1 : ℝ) (C * T))) ?_
      exact_mod_cast (Nat.le_ceil (max 1 (C * T)))
    simp only [lvl0Fam]
    exact hbound.trans (mul_le_mul_left hconst _)
  refine ⟨fun Λ => if h : 1 < Λ then Classical.choose (hbase Λ h) else 1, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t F hΛ ha ha1 hlcL ht
  simpa only [dif_pos hΛ] using
    (Classical.choose_spec (hbase Λ hΛ)) a ha ha1 l₁ l₂ k₁ k₂ hlcL t ht F

/-- **The level-`0` clipped estimate at every `ρ > 0`** (for `2 ≤ P.natDegree`): the small-`ρ`
estimate `lvl0DegTwoBase` transported along `lvl0Transfer`. -/
theorem Lvl0_all (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (B : ℕ) :
    ∀ ρ : ℝ, 0 < ρ → Lvl0 P r C₀ B ρ :=
  lvl0Transfer P r hr C₀ hC₀ B (lvl0DegTwoBase P hdeg r hr C₀ hC₀ B)

end

end Work.KMTPlan.A6.LowModApproxBoundedH
