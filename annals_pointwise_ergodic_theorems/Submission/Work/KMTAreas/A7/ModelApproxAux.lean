/-
# Auxiliary definitions for the model approximation (`mod-approx`) of Area A7

This module fixes the weight in which the *single-scale* model approximation of §6 of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022

is stated, and the bookkeeping that turns it into the loss weight `lossWeight c ρ l₁ l₂ k₁ k₂` of
the target `Work.KMTAreas.A7.ModelApprox`.

The paper's Proposition `mod-approx` bounds the difference between the concrete halved average
`Ã_N(F_N,G_N)` and the model operator `B^{l₁,l₂,m_Ẑ}_{(η⊗η)m̃_{N,ℝ}}(F,G)` by

  `2^{O(max(2^{ρl}, s))} N^{-1} ‖F‖_{ℓ^{p₁}} ‖G‖_{ℓ^{p₂}}`,   `l = max (l₁,l₂)`, `s = max (s₁,s₂)`,

and the point of the estimate is the gain `N^{-1`}: summed over the admissible lacunary scales
(which are `≥ 2^{2^{L/C₀}}`, `L = max (max l₁ l₂) (max k₁ k₂)`, because of the index set
`I^{l,k₁,k₂}`), it beats the exponential factor `2^{O(2^{ρL})}` provided `ρ` is small compared with
`1/C₀`.  This module records

* `modelWeight A ρ l₁ l₂ k₁ k₂ = ⟨L⟩^A · 2^{A·2^{ρL}}`, the weight of the single-scale estimate;
* the elementary facts that make the passage to `lossWeight` possible.

We keep the objects of `Work.KMTAreas.A7.Large.Defs` (the model tuple of §6/§8) unchanged.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.EndVar
open PointwiseErgodicTheorems

/-- **The weight of the single-scale model approximation.**  The paper's Proposition
`mod-approx` gives an error `2^{O(max(2^{ρl},s))} N^{-1}`; since `s ≤ L` and `l ≤ L`, the factor
`2^{O(max(2^{ρl},s))}` is dominated by `⟨L⟩^A 2^{A 2^{ρL}}` for a suitable `A`. -/
noncomputable def modelWeight (A ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) : ℝ :=
  (1 + lmaxR l₁ l₂ k₁ k₂) ^ A * (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂))

theorem lmaxR_nonneg (l₁ l₂ k₁ k₂ : ℕ) : 0 ≤ lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR]
  have h : (0 : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
    rw [Work.Analysis.EndVar.lmax]
    exact le_trans (Int.natCast_nonneg l₁)
      (le_trans (le_max_left _ _) (le_max_left _ _))
  exact_mod_cast h

theorem one_add_lmaxR_pos (l₁ l₂ k₁ k₂ : ℕ) : 0 < 1 + lmaxR l₁ l₂ k₁ k₂ := by
  have := lmaxR_nonneg l₁ l₂ k₁ k₂
  linarith

theorem one_add_lmaxR_ge_one (l₁ l₂ k₁ k₂ : ℕ) : 1 ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by
  have := lmaxR_nonneg l₁ l₂ k₁ k₂
  linarith

theorem modelWeight_nonneg (A ρ : ℝ) (hA : 0 ≤ A) (l₁ l₂ k₁ k₂ : ℕ) :
    0 ≤ modelWeight A ρ l₁ l₂ k₁ k₂ := by
  rw [modelWeight]
  have h1 : 0 ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ A :=
    Real.rpow_nonneg (le_of_lt (one_add_lmaxR_pos l₁ l₂ k₁ k₂)) A
  have h2 : 0 ≤ (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)) :=
    Real.rpow_nonneg (by norm_num) _
  exact mul_nonneg h1 h2

theorem lossWeight_nonneg (c ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    0 ≤ lossWeight c ρ l₁ l₂ k₁ k₂ := by
  rw [lossWeight]
  have h1 : 0 ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ c :=
    Real.rpow_nonneg (le_of_lt (one_add_lmaxR_pos l₁ l₂ k₁ k₂)) c
  have h2 : 0 ≤ (2 : ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂) := Real.rpow_nonneg (by norm_num) _
  exact mul_nonneg h1 h2

/-- **The single-scale model approximation of §6** (Proposition `mod-approx`), as a `Prop`:
for every `n`, the `ℓ^p` distance between the concrete column `varpPiece` and the model operator
of §6 is at most `C(Λ) · ⟨L⟩^A · 2^{A·2^{ρL}} · ⌊a n⌋^{-1} · ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`, with
`L = max (max l₁ l₂) (max k₁ k₂)` and `p = (p₁⁻¹+p₂⁻¹)⁻¹`.

This is the paper's §6 `mod-approx` together with the (trivial) observation that the difference
vanishes off the index set `I^{l,k₁,k₂}`, off the large scales and off the main regime. -/
def ModelApproxCoreStatement (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : ℝ≥0 → ℝ≥0,
      ∀ (C₀ : ℕ) (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 ≤ C₀ → 1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        ∀ n : ℕ,
          MeasureTheory.eLpNorm (fun x : ℤ =>
              (mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) * ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂)
              * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)
              * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

end

end Work.KMTAreas.A7
