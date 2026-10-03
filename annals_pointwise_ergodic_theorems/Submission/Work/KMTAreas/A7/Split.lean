/-
# The scale split of Theorem `varp` (paper §6--§8) and its assembly

The proof of Theorem `varp` for the exponents `(p₁,p₂) ≠ (2,2)` (area `A7` of the KMT contract)
follows the paper's §6--§8: after the approximation of the halved averages by the *model
operators* (§6, Proposition `mod-approx` and the functional-calculus identity `bn-ident`), the
scale set `I = {N ∈ D : l,s₁,s₂ ≤ l_(N)}` is split into the *small scales*
`I_sml = {N ≤ 2^{2^u}}` and the *large scales* `I_lrg = {N > 2^{2^u}}`, where
`u = ⌊C₂ 2^{2ρl}⌋` (`l = max(l₁,l₂)`, `C₂` a constant of the proof), and the two regimes are
estimated separately:

* **small scales** (§7): the two-parameter Rademacher--Menshov inequality `rm-bil` applied to the
  model tuple (which is independent of `N` after `bn-ident`), reducing to a single-scale estimate
  `SSU`, itself obtained from `mod-approx` at `N = 2^u` and the single-scale Hölder bound `anf`;
  the Rademacher--Menshov loss is `u^{O(1)} ≲_{C₂} 2^{O(ρl)}`, and the sums `∑_{N∈I} N^{-1}` of the
  `mod-approx` errors are dominated by the (doubly exponentially small) value of the smallest
  admissible scale;
* **large scales** (§8): the quantitative Shannon sampling theorem (replacing `ℤ` by the adelic
  integers / `ℝ × ℤ/Q`), the `form-1` factorisation of the twisted bilinear multiplier through the
  arithmetic averaging operator, Hölder's inequality and the *linear* variational estimates
  `LIN-VAR` for the lacunary families `T_{φ_{N,t}}` — which require no gain in the exponents
  `(p₁,p₂) ≠ (2,2)`.

This module fixes the two families (`VarpLossSmall`, `VarpLossLarge`) at the paper's threshold
`splitCut ρ lmax = 2^{2^{⌊2^{2ρ·lmax}⌋}}` (the constant `C₂ = 1` is immaterial: the loss `u^{O(1)}`
of the Rademacher--Menshov step, and the `2^{O(max(2^{ρl},s))}` factor of `mod-approx`, are both
absorbed into the constant `C_ρ` and into the weight `2^{Aρ·lmax}`), and proves the assembly

  `VarpLossKMT P p₁ p₂`  from  `VarpLossSmall P p₁ p₂`  and  `VarpLossLarge P p₁ p₂`,

i.e. Theorem `varp` (without gain) for the exponents `(p₁,p₂) ≠ (2,2)` from the two regimes of the
paper's §7 and §8.
-/
import Mathlib
import Submission.Work.KMTContract.Areas
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract

/-- The threshold `2^{2^u}` of the paper's scale split, with `u = ⌊C₂ 2^{2ρ lmax}⌋` and the
constant `C₂ = 1`.  (Any fixed `C₂ ≥ 1` gives an equivalent statement: the constants of the two
regimes absorb a fixed factor.) -/
noncomputable def splitCut (ρ : ℝ) (L : ℕ) : ℕ :=
  2 ^ (2 ^ (scaleCount 1 ρ L))

/-- **The small-scale part of Theorem `varp`** (paper §7), at the exponents `(p₁,p₂)`, without
gain: the columns `varpCol` restricted to the scales `N ≤ splitCut ρ lmax` obey the estimate with
the loss `2^{Aρ·lmax}`. -/
def VarpLossSmall (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞) : Prop :=
  ∀ (C₀ : ℕ) (r : ℝ≥0), 1 ≤ C₀ → (2 : ℝ≥0) < r → ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : ℝ≥0 → ℝ≥0,
      ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
        eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
            if Nat.floor (a n) ≤ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) then
              varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x else 0))
          (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
        ≤ (C Λ : ℝ≥0∞) *
            ENNReal.ofReal ((2 : ℝ) ^ (A * ρ * (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ))) *
          eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count

/-- **The large-scale part of Theorem `varp`** (paper §8), at the exponents `(p₁,p₂)`, without
gain: the columns `varpCol` restricted to the scales `N > splitCut ρ lmax` obey the estimate with
the loss `2^{Aρ·lmax}`. -/
def VarpLossLarge (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞) : Prop :=
  ∀ (C₀ : ℕ) (r : ℝ≥0), 1 ≤ C₀ → (2 : ℝ≥0) < r → ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : ℝ≥0 → ℝ≥0,
      ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
        eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
            if splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) then
              varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x else 0))
          (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
        ≤ (C Λ : ℝ≥0∞) *
            ENNReal.ofReal ((2 : ℝ) ^ (A * ρ * (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ))) *
          eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count

/-- **The assembly of the two regimes**: the small-scale and large-scale parts of Theorem `varp`
(at the same threshold) give `VarpLossKMT`, i.e. the loss form of Theorem `varp` at the exponents
`(p₁,p₂)`. -/
theorem varpLossKMT_of_small_large {P : ℤ[X]} {p₁ p₂ : ℝ≥0∞}
    (hp1 : 1 ≤ (p₁⁻¹ + p₂⁻¹)⁻¹) (hS : VarpLossSmall P p₁ p₂)
    (hL : VarpLossLarge P p₁ p₂) : Work.KMTContract.VarpLossKMT P p₁ p₂ := by
  intro C₀ r hC₀ hr
  obtain ⟨A₁, hA₁, ρ₁, hρ₁, hS'⟩ := hS C₀ r hC₀ hr
  obtain ⟨A₂, hA₂, ρ₂, hρ₂, hL'⟩ := hL C₀ r hC₀ hr
  refine ⟨max A₁ A₂, le_max_of_le_left hA₁, min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
  intro ρ hρ hρle
  obtain ⟨C₁, hC₁⟩ := hS' ρ hρ (le_trans hρle (min_le_left _ _))
  obtain ⟨C₂, hC₂⟩ := hL' ρ hρ (le_trans hρle (min_le_right _ _))
  rw [PieceBound, VarpStatementΛWith]
  refine ⟨fun Λ => C₁ Λ + C₂ Λ, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
  -- the two families of the scale split
  set b₁ : ℕ → ℤ → ℂ := fun n x =>
    if Nat.floor (a n) ≤ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) then
      varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x else 0 with hb₁
  set b₂ : ℕ → ℤ → ℂ := fun n x =>
    if splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) then
      varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x else 0 with hb₂
  set L : ℝ := ((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℤ) : ℝ) with hLdef
  -- the two estimates
  have hsmall : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => b₁ n x))
        (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
      ≤ (C₁ Λ : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (A₁ * ρ * L)) *
          eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
    rw [hb₁, hLdef]
    exact hC₁ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
  have hlarge : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => b₂ n x))
        (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
      ≤ (C₂ Λ : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (A₂ * ρ * L)) *
          eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
    rw [hb₂, hLdef]
    exact hC₂ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
  -- the pointwise split of the columns
  have hpoint : ∀ x : ℤ,
      (fun n : ℕ => (b₁ n x + b₂ n x))
        = fun n : ℕ => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x := by
    intro x
    funext n
    simp only [hb₁, hb₂]
    by_cases h : Nat.floor (a n) ≤ splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
    · have h2 : ¬ (splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)) := not_lt.mpr h
      rw [if_pos h, if_neg h2, add_zero]
    · have h2 : splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) := not_le.mp h
      rw [if_neg h, if_pos h2, zero_add]
  -- the weights
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    have : (0 : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      rw [Work.Analysis.EndVar.lmax]
      exact le_trans (Int.natCast_nonneg l₁)
        (le_trans (le_max_left _ _) (le_max_left _ _))
    exact_mod_cast this
  have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt hρ
  have hw₁ : ENNReal.ofReal ((2 : ℝ) ^ (A₁ * ρ * L))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (max A₁ A₂ * ρ * L)) := by
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have h1 : A₁ * ρ ≤ max A₁ A₂ * ρ := mul_le_mul_of_nonneg_right (le_max_left _ _) hρ0
    exact mul_le_mul_of_nonneg_right h1 hL0
  have hw₂ : ENNReal.ofReal ((2 : ℝ) ^ (A₂ * ρ * L))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (max A₁ A₂ * ρ * L)) := by
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have h1 : A₂ * ρ ≤ max A₁ A₂ * ρ := mul_le_mul_of_nonneg_right (le_max_right _ _) hρ0
    exact mul_le_mul_of_nonneg_right h1 hL0
  -- the estimate for the weight-normalised form of each family
  have h₁ : (C₁ Λ : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (A₁ * ρ * L))
        * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count
      ≤ (C₁ Λ : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (max A₁ A₂ * ρ * L))
        * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count :=
    mul_le_mul_left (mul_le_mul_left (mul_le_mul_right hw₁ (C₁ Λ))
      (eLpNorm f p₁ Measure.count)) (eLpNorm g p₂ Measure.count)
  have h₂ : (C₂ Λ : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (A₂ * ρ * L))
        * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count
      ≤ (C₂ Λ : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (max A₁ A₂ * ρ * L))
        * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count :=
    mul_le_mul_left (mul_le_mul_left (mul_le_mul_right hw₂ (C₂ Λ))
      (eLpNorm f p₁ Measure.count)) (eLpNorm g p₂ Measure.count)
  -- the chain
  refine (le_trans (le_of_eq ?_) (le_trans (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
    (f := fun x : ℤ => variationalNorm r (fun n : ℕ => b₁ n x + b₂ n x))
    (g := fun x : ℤ => variationalNorm r (fun n : ℕ => b₁ n x)
      + variationalNorm r (fun n : ℕ => b₂ n x))
    (fun x => by
      simp only [enorm_eq_self]
      exact variationalNorm_add_le (le_trans (by norm_num : (1 : ℝ≥0) ≤ 2) hr.le)
        (fun n : ℕ => b₁ n x) (fun n : ℕ => b₂ n x)))
    (le_trans (MeasureTheory.eLpNorm_add_le hp1)
      (le_trans (add_le_add (hsmall.trans h₁) (hlarge.trans h₂)) (le_of_eq ?_)))))
  · congr 1
    funext x
    exact congrArg (fun u => variationalNorm r u) (hpoint x).symm
  · rw [ENNReal.coe_add, add_mul, add_mul, add_mul]

/-- **Area `A7` from the two scale regimes.**  Packaged form of the assembly: the two halves of
the paper's §7/§8 analysis (with the hypotheses of the frozen area `A7`) give `AreaA7`. -/
theorem areaA7_of_halves
    (hS : ∀ (P : Polynomial ℤ) (p₁ p₂ : ENNReal), 2 ≤ P.natDegree →
      1 < p₁ → p₁ < ⊤ → 1 < p₂ → p₂ < ⊤ → p₁⁻¹ + p₂⁻¹ ≤ 1 → (p₁ ≠ 2 ∨ p₂ ≠ 2) →
      Work.KMTContract.AreaA1 → VarpLossSmall P p₁ p₂)
    (hL : ∀ (P : Polynomial ℤ) (p₁ p₂ : ENNReal), 2 ≤ P.natDegree →
      1 < p₁ → p₁ < ⊤ → 1 < p₂ → p₂ < ⊤ → p₁⁻¹ + p₂⁻¹ ≤ 1 → (p₁ ≠ 2 ∨ p₂ ≠ 2) →
      Work.KMTContract.AreaA1 → VarpLossLarge P p₁ p₂) :
    Work.KMTContract.AreaA7 := by
  intro P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum hneq hA1
  exact varpLossKMT_of_small_large (ENNReal.one_le_inv.mpr hsum)
    (hS P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum hneq hA1)
    (hL P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum hneq hA1)

end

end Work.KMTAreas.A7
