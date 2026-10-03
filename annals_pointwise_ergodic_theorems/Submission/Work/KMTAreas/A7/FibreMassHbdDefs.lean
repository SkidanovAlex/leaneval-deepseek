/-
# The constants and frequency radii of the fibre mass bound

The derivative `∫`-bound of §6 for the symbol `σ = φ_N ⊗ φ̃_N · weylAvg` needs the two
frequency radii

* `fibLam₁ N k₁ = 2^{k₁}/2^{Log N}` — the *inverse* scale of the first bump (the bump lives at
  scale `1/λ₁`), and
* `fibLam₂ P N k₂ = 2^{d k₂}/2^{d Log N}` — the inverse scale of the second bump,

together with the *reduced* second radius `fibR₂ = min (N^{-d}) λ₂`.  The reduction is what makes
the statement true at `N = 1`: there `N^{-d} = 1 > λ₂` is possible (`λ₂ = 2^{-d}`), and the sharp
`L¹`-computation of the `φ̃`-derivatives produces the factor `(1 + λ₂N^d)^j`, which is only
comparable with `(λ₂N^d)^j` when `λ₂N^d ≥ 1`.

The constant `fibHbdC` is `64 · M₀ · Cφ · Cψ · q²(1+S²/N) · λ₁ · max (λ₂N^d) 1`: the factor
`max (λ₂N^d) 1` is exactly the two-regime bookkeeping (`λ₂N^d ≥ 1` = the physical regime, and
`λ₂N^d < 1`, which can only happen at `N = 1`, where the `(1+B)^j` factor is bounded by `4`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FibreMassAux

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-- The first frequency scale `λ₁ = 2^{k₁}/2^{Log N}` (the inverse scale of the bump `φ_N`). -/
noncomputable def fibLam₁ (N k₁ : ℕ) : ℝ := (2 : ℝ) ^ k₁ / Work.KMTPlan.A6.lothN N

/-- The second frequency scale `λ₂ = 2^{d k₂}/2^{d Log N}` (the inverse scale of `φ̃_N`). -/
noncomputable def fibLam₂ (P : Polynomial ℤ) (N k₂ : ℕ) : ℝ :=
  (2 : ℝ) ^ (P.natDegree * k₂) / (Work.KMTPlan.A6.lothN N) ^ P.natDegree

/-- The reduced second frequency radius `min (N^{-d}) λ₂`. -/
noncomputable def fibR₂ (P : Polynomial ℤ) (N k₂ : ℕ) : ℝ :=
  min (((N : ℝ) ^ P.natDegree)⁻¹) (fibLam₂ P N k₂)

/-- The constant of the derivative `∫`-bound. -/
noncomputable def fibHbdC (P : Polynomial ℤ) (N q k₁ k₂ : ℕ) : ℝ :=
  64 * fibM0C P * fibBumpCφ P * fibBumpCψ P * (q : ℝ) ^ 2
    * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ)) * fibLam₁ N k₁
    * max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1

/-! ## Elementary properties -/

theorem fibLam₁_pos (N k₁ : ℕ) : 0 < fibLam₁ N k₁ :=
  div_pos (pow_pos (by norm_num) _) (Work.KMTPlan.A6.lothN_pos N)

theorem fibLam₂_pos (P : Polynomial ℤ) (N k₂ : ℕ) : 0 < fibLam₂ P N k₂ :=
  div_pos (pow_pos (by norm_num) _) (pow_pos (Work.KMTPlan.A6.lothN_pos N) _)

theorem fibR₂_pos (P : Polynomial ℤ) {N k₂ : ℕ} (hN : 1 ≤ N) : 0 < fibR₂ P N k₂ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  exact lt_min (inv_pos.mpr (pow_pos hNpos _)) (fibLam₂_pos P N k₂)

theorem fibR₂_le_one (P : Polynomial ℤ) {N k₂ : ℕ} (hN : 1 ≤ N) : fibR₂ P N k₂ ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine (min_le_left _ _).trans ?_
  rw [inv_le_one₀ (pow_pos hNpos _)]
  exact one_le_pow₀ hN1

/-- `λ₁` is the inverse of the elementary scale `2^{Log N}/2^{k₁}`. -/
theorem fibLam₁_eq_inv (N k₁ : ℕ) :
    fibLam₁ N k₁ = (Work.KMTPlan.A6.lothN N / (2 : ℝ) ^ k₁)⁻¹ := by
  rw [fibLam₁, inv_div]

/-- `λ₂` is the inverse of `lopsN`. -/
theorem fibLam₂_eq_inv (P : Polynomial ℤ) (N k₂ : ℕ) :
    fibLam₂ P N k₂ = (Work.KMTPlan.A6.lopsN P.natDegree N k₂)⁻¹ := by
  rw [fibLam₂, Work.KMTPlan.A6.lopsN_eq, div_pow, inv_div, ← pow_mul, Nat.mul_comm k₂ P.natDegree]

/-- The elementary scale `2^{Log N}` is at most `2N` (for `N ≥ 1`). -/
theorem lothN_le_two_mul_N {N : ℕ} (hN : 1 ≤ N) : Work.KMTPlan.A6.lothN N ≤ 2 * (N : ℝ) := by
  have h := Nat.pow_log_le_self 2 (x := max N 2) (by positivity)
  have hcast : (((2 : ℕ) ^ Nat.log 2 (max N 2) : ℕ) : ℝ) ≤ ((max N 2 : ℕ) : ℝ) := by
    exact_mod_cast h
  have hmax : ((max N 2 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    have : max N 2 ≤ 2 * N := by omega
    exact_mod_cast this
  have heq : Work.KMTPlan.A6.lothN N = (((2 : ℕ) ^ Nat.log 2 (max N 2) : ℕ) : ℝ) := by
    rw [Work.KMTPlan.A6.lothN, Work.Analysis.EndVar.logN]
    push_cast
    rw [Real.rpow_natCast]
  rw [heq]
  linarith

/-- `1/2 ≤ λ₁ N`: the elementary scale `2^{Log N}` is at most `2N`. -/
theorem fibLam₁_mul_N_ge_half (N k₁ : ℕ) (hN : 1 ≤ N) :
    1 / 2 ≤ fibLam₁ N k₁ * (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hth : Work.KMTPlan.A6.lothN N ≤ 2 * (N : ℝ) := lothN_le_two_mul_N hN
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k₁ := one_le_pow₀ (by norm_num)
  have hpos : 0 < Work.KMTPlan.A6.lothN N := Work.KMTPlan.A6.lothN_pos N
  rw [fibLam₁, div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith [hth, h2, hNpos, hpos]

theorem fibHbdC_pos (P : Polynomial ℤ) (N q k₁ k₂ : ℕ) (hq : 0 < q) (hN : 1 ≤ N) :
    0 < fibHbdC P N q k₁ k₂ := by
  have h1 : 0 < fibM0C P := fibM0C_pos P
  have h2 : 0 < fibBumpCφ P := fibBumpCφ_pos P
  have h3 : 0 < fibBumpCψ P := fibBumpCψ_pos P
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h4 : 0 < fibLam₁ N k₁ := fibLam₁_pos N k₁
  have h5 : 1 ≤ max (fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) 1 := le_max_right _ _
  have h6 : 0 < 1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ) := by
    have : (0 : ℝ) ≤ (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ) := by positivity
    linarith
  rw [fibHbdC]
  positivity

end

end Work.KMTAreas.A7
