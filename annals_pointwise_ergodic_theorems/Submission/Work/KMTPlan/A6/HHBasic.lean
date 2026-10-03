/-
# Elementary vocabulary for the high–high case of area A6 (`Work.KMTPlan.A6.highHighCase`)

This module fixes the notation of the high–high case (`CaseHH`, i.e. `k₁,k₂ ≥ 1`) of
Krause--Mirek--Tao's Theorem `varp` at `(p₁,p₂,p) = (2,2,1)`, in the form used by
`Work.KMTPlan.A6.highHighCase`:

* `kmtM l₁ l₂ k₁ k₂ = max (max l₁ l₂) (max k₁ k₂)` — the natural-number form of the exponent
  `EndVar.lmax l₁ l₂ k₁ k₂` of the exponential gain;
* `hhWeight c l₁ l₂ k₁ k₂ = 2^{-c·kmtM}` — the gain weight;
* `hhGood R ρ M N` — the *good-scale condition* at height `M`: `M + R·2^{ρM} + 2 ≤ Log N`;

together with the elementary identities used everywhere below
(`kmtM_cast_lmax`, `hhWeight_eq`, `inIndexSet ⟹ kmtM ≤ heightScale`,
`AhalfR` depends on its scale only through `Nat.floor`).

Nothing is postulated here.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract

/-! ## The exponent and the weight -/

/-- **The exponent `M = max(max l₁ l₂)(max k₁ k₂)`** of the high–high gain. -/
def kmtM (l₁ l₂ k₁ k₂ : ℕ) : ℕ := max (max l₁ l₂) (max k₁ k₂)

/-- `kmtM` is the natural-number form of `EndVar.lmax`. -/
theorem kmtM_cast_lmax (l₁ l₂ k₁ k₂ : ℕ) :
    (kmtM l₁ l₂ k₁ k₂ : ℤ) = lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
  rw [kmtM, Work.Analysis.EndVar.lmax]
  push_cast
  ring

/-- **The gain weight** `2^{-c·M}` of the high–high case, `M = kmtM l₁ l₂ k₁ k₂`. -/
def hhWeight (c : ℝ) (l₁ l₂ k₁ k₂ : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(c * (kmtM l₁ l₂ k₁ k₂ : ℝ)))

/-- `hhWeight` is the weight `2^{-c·lmax}` of the contract. -/
theorem hhWeight_eq (c : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    hhWeight c l₁ l₂ k₁ k₂
      = (2 : ℝ) ^ (-(c * (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ))) := by
  have h : ((kmtM l₁ l₂ k₁ k₂ : ℕ) : ℝ) = (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ) := by
    exact_mod_cast kmtM_cast_lmax l₁ l₂ k₁ k₂
  rw [hhWeight, h]

theorem hhWeight_nonneg (c : ℝ) (l₁ l₂ k₁ k₂ : ℕ) : 0 ≤ hhWeight c l₁ l₂ k₁ k₂ :=
  Real.rpow_nonneg (by norm_num) _

/-- The weight is antitone in the rate. -/
theorem hhWeight_le_of_le {c c' : ℝ} (hc : c ≤ c') (l₁ l₂ k₁ k₂ : ℕ) :
    hhWeight c' l₁ l₂ k₁ k₂ ≤ hhWeight c l₁ l₂ k₁ k₂ := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ (kmtM l₁ l₂ k₁ k₂ : ℝ) := Nat.cast_nonneg _
  nlinarith

/-! ## The good-scale condition -/

/-- **The good-scale condition** at height `M` and scale `N`: `M + R·2^{ρM} + 2 ≤ Log N`. -/
def hhGood (R ρ : ℝ) (M N : ℕ) : Prop :=
  (M : ℝ) + R * (2 : ℝ) ^ (ρ * (M : ℝ)) + 2 ≤ ((logN N : ℤ) : ℝ)

/-- The good-scale condition is monotone in the height. -/
theorem hhGood_mono_height {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 ≤ ρ) {M M' N : ℕ}
    (h : M ≤ M') (hg : hhGood R ρ M' N) : hhGood R ρ M N := by
  have h1 : (M : ℝ) ≤ (M' : ℝ) := by exact_mod_cast h
  have h2 : (2 : ℝ) ^ (ρ * (M : ℝ)) ≤ (2 : ℝ) ^ (ρ * (M' : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left h1 hρ)
  have h3 : R * (2 : ℝ) ^ (ρ * (M : ℝ)) ≤ R * (2 : ℝ) ^ (ρ * (M' : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 hR
  simp only [hhGood] at hg ⊢
  linarith

/-! ## The index set -/

/-- On the index set `I^{max(l₁,l₂),k₁,k₂}` the exponent `kmtM` is at most the height scale. -/
theorem kmtM_le_heightScale {C₀ N l₁ l₂ k₁ k₂ : ℕ}
    (h : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N) :
    kmtM l₁ l₂ k₁ k₂ ≤ heightScale C₀ N := by
  rw [inIndexSet_iff_le] at h
  exact max_le (max_le h.1 h.2.1) (max_le h.2.2.1 h.2.2.2)

/-! ## The scale of `AhalfR` -/

/-- `AhalfR` depends on its scale only through `Nat.floor`, so it is unchanged when a
nonnegative real scale is replaced by its floor. -/
theorem AhalfR_floor (a : ℕ → ℝ≥0) (n : ℕ) (P₁ P₂ : ℤ[X]) (f g : ℤ → ℂ) :
    AhalfR TZ (a n) P₁ P₂ f g
      = AhalfR TZ ((Nat.floor (a n) : ℕ) : ℝ≥0) P₁ P₂ f g := by
  unfold AhalfR
  rw [Nat.floor_natCast]

/-- The clamped column at an index of the index set is the halved average of the two pieces. -/
theorem varpCol_eq_AhalfR {ρ : ℝ} {P : ℤ[X]} {C₀ : ℕ} {a : ℕ → ℝ≥0} {f g : ℤ → ℂ}
    {l₁ l₂ k₁ k₂ n : ℕ}
    (h : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))) :
    varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n
      = AhalfR TZ (a n) X P
          (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f)
          (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) := by
  rw [varpCol_eq_piece_of_indexSet (P := P) h]
  rfl

end

end Work.KMTPlan.A6
