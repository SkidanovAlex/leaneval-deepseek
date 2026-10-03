/-
# The low case (`CaseRest`) of area A6: **assembly of the scale split**

`Work.KMTPlan.A6.lowCase` is the low case `CaseRest` (`k₁ = 0 ∨ k₂ = 0`) of Krause--Mirek--Tao's
Theorem `varp` at `(p₁,p₂,p) = (2,2,1)` with the exponential gain `2^{-c·L}`,
`L = max(max l₁ l₂)(max k₁ k₂)`.

Following the paper's §6, the scale set `I^{l,k₁,k₂}` is split at `2^{2^u}`,
`u = ⌊C₂2^{2ρL}⌋`, into the *small* scales (`colSmall`) and the *large* scales (`colLarge`),
whose estimates are the two halves of the analysis:

* `LowDefs.colSmall` / `LcSmall` — §7: the Rademacher--Menshov inequality `rm-bil` plus the
  single-scale estimate `ssu` (`mod-approx` run backwards at `N = 2^u`, plus `improv`);
  proved by `Work.KMTPlan.A6.lowSmallScaled`;
* `LowDefs.colLarge` / `LcLarge` — §8: the quantitative Shannon sampling theorem, the arithmetic
  bilinear estimate `bile`, the vector-valued Lépingle inequality;
  proved by `Work.KMTPlan.A6.lowLargeScaled`.

This module proves the **assembly** of the two halves: the columns are the pointwise sum of the
two clamped families (`LowDefs.colSmall_add_colLarge`), the variational norm is subadditive, so the
two estimates add; the weights `2^{-c₁L}` and `2^{-c₂L}` are both dominated by
`2^{-(min c₁ c₂)L}`, and the constants are absorbed by `2 · max (C₁ Λ) (C₂ Λ)`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.lowSmallScaled
import Submission.Work.KMTPlan.A6.lowLargeScaled
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract

/-- The two clamped families sum to the full column family, so the variational norm of the full
column family is at most the sum of the two variational norms. -/
theorem variationalNorm_varpCol_le_small_add_large (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) {r : ℝ≥0} (hr : 1 ≤ r) (l₁ l₂ k₁ k₂ : ℕ) (x : ℤ) :
    variationalNorm r (fun n : ℕ =>
        varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)
      ≤ variationalNorm r (fun n : ℕ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        + variationalNorm r (fun n : ℕ => colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
  have heq : (fun n : ℕ => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)
      = (fun n : ℕ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          + colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
    funext n
    exact (congrFun (congrFun (colSmall_add_colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂) n) x).symm
  rw [heq]
  exact variationalNorm_add_le hr _ _

theorem lowCase (P : ℤ[X]) (hd : 2 ≤ P.natDegree) (r : ℝ≥0) (hr : 2 < r)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      Work.KMTPlan.PieceBoundOn ρ P C₀ 2 2 1 r
        (fun l₁ l₂ k₁ k₂ => (2 : ℝ) ^ (-(c * (Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ))))
        Work.KMTPlan.CaseRest := by
  have hS₀ : LcSmall P r C₀ := lowSmallScaled P hd r hr hA1 hI C₀ hC₀
  have hL₀ : LcLarge P r C₀ := lowLargeScaled P hd r hr hA1 hI C₀ hC₀
  obtain ⟨c₁, hc₁, ρ₁, hρ₁, hS⟩ := hS₀ hC₀
  obtain ⟨c₂, hc₂, ρ₂, hρ₂, hL⟩ := hL₀ hC₀
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
  intro ρ hρ hρle
  obtain ⟨C₁, hC₁⟩ := hS ρ hρ (le_trans hρle (min_le_left _ _))
  obtain ⟨C₂, hC₂⟩ := hL ρ hρ (le_trans hρle (min_le_right _ _))
  refine ⟨fun Λ => 2 * max (C₁ Λ) (C₂ Λ), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ
  have h1 := hC₁ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ
  have h2 := hC₂ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ
  -- the split of the variational norm and the triangle inequality in `ℓ¹`
  have hmain :
      eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
          varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
        ≤ eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
          + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count := by
    refine (eLpNorm_mono_enorm (hf := by pw_aesm)
      (f := fun x : ℤ => variationalNorm r (fun n : ℕ =>
          varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x))
      (g := fun x : ℤ => variationalNorm r (fun n : ℕ =>
            colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + variationalNorm r (fun n : ℕ =>
            colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      (fun x => ?_)).trans ?_
    · simp only [enorm_eq_self]
      exact variationalNorm_varpCol_le_small_add_large ρ P C₀ a f g
        (le_trans (by norm_num : (1 : ℝ≥0) ≤ 2) hr.le) l₁ l₂ k₁ k₂ x
    exact eLpNorm_add_le le_rfl
  -- the arithmetic of the two weights
  set M : ℝ≥0 := max (C₁ Λ) (C₂ Λ) with hM
  have hC1 : (C₁ Λ : ℝ≥0∞) ≤ (M : ℝ≥0∞) := by
    rw [hM]; exact_mod_cast le_max_left (C₁ Λ) (C₂ Λ)
  have hC2 : (C₂ Λ : ℝ≥0∞) ≤ (M : ℝ≥0∞) := by
    rw [hM]; exact_mod_cast le_max_right (C₁ Λ) (C₂ Λ)
  have hw1 : ENNReal.ofReal (lcWeight c₁ l₁ l₂ k₁ k₂)
      ≤ ENNReal.ofReal (lcWeight (min c₁ c₂) l₁ l₂ k₁ k₂) :=
    ENNReal.ofReal_le_ofReal (lcWeight_le_of_le (min_le_left c₁ c₂) l₁ l₂ k₁ k₂)
  have hw2 : ENNReal.ofReal (lcWeight c₂ l₁ l₂ k₁ k₂)
      ≤ ENNReal.ofReal (lcWeight (min c₁ c₂) l₁ l₂ k₁ k₂) :=
    ENNReal.ofReal_le_ofReal (lcWeight_le_of_le (min_le_right c₁ c₂) l₁ l₂ k₁ k₂)
  set A : ℝ≥0∞ := eLpNorm f 2 Measure.count with hA
  set B : ℝ≥0∞ := eLpNorm g 2 Measure.count with hB
  have harith :
      (C₁ Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight c₁ l₁ l₂ k₁ k₂) * A * B
        + (C₂ Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight c₂ l₁ l₂ k₁ k₂) * A * B
      ≤ ((2 * M : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (lcWeight (min c₁ c₂) l₁ l₂ k₁ k₂) * A * B := by
    have hstep :
        (C₁ Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight c₁ l₁ l₂ k₁ k₂) * A * B
          + (C₂ Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight c₂ l₁ l₂ k₁ k₂) * A * B
        ≤ (M : ℝ≥0∞) * ENNReal.ofReal (lcWeight (min c₁ c₂) l₁ l₂ k₁ k₂) * A * B
          + (M : ℝ≥0∞) * ENNReal.ofReal (lcWeight (min c₁ c₂) l₁ l₂ k₁ k₂) * A * B := by
      refine add_le_add ?_ ?_
      · exact mul_le_mul' (mul_le_mul' (mul_le_mul' hC1 hw1) le_rfl) le_rfl
      · exact mul_le_mul' (mul_le_mul' (mul_le_mul' hC2 hw2) le_rfl) le_rfl
    refine hstep.trans (le_of_eq ?_)
    rw [ENNReal.coe_mul]
    ring_nf
    norm_num
  exact hmain.trans (add_le_add h1 h2 |>.trans harith)

end Work.KMTPlan.A6
