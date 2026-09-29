import Mathlib
import Submission.Work.Resample.auDefs

/-!
# Definitions for the tail estimate `Work.Resample.auTail`

The lemma `Work.Resample.auTail` compares the finite windowed sum of the fixed-point
resampling weights `auWi` with the exact matrix entry `(resA s t α).mulVec u k`, whose
definition is an infinite (`tsum`) sum over the cosets of `s`.  To state that
comparison cleanly we fix here:

* `finMod s n` — the Euclidean representative of `n : ℤ` in `Fin s`;
* `auZeta s t k` — the real centre `ζ = s·k/t`;
* `auGauss α ζ n` — the Gaussian weight `exp (−π (n−ζ)²/α²)`;
* `auHf s α ζ u n` — the transferred summand `exp (−π (n−ζ)²/α²) · u (n mod s)`;
* `auW0 p α s t k` — the start `K − m` of the retained window.

With these, both the finite window sum and the exact `resA`-row are `1/(2α)` times a
sum of `auHf` over the window resp. over all of `ℤ`, so their difference is a
Gaussian tail in `ℤ`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- Euclidean representative of `n : ℤ` in `Fin s`. -/
def finMod (s : ℕ) (hs : 0 < s) (n : ℤ) : Fin s :=
  ⟨(n % (s : ℤ)).toNat, by
    have h1 : 0 ≤ n % (s : ℤ) := Int.emod_nonneg n (by omega)
    have h2 : n % (s : ℤ) < (s : ℤ) := Int.emod_lt_of_pos n (by omega)
    omega⟩

@[simp] theorem finMod_val (s : ℕ) (hs : 0 < s) (n : ℤ) :
    ((finMod s hs n : ℕ)) = (n % (s : ℤ)).toNat := rfl

theorem finMod_val_cast (s : ℕ) (hs : 0 < s) (n : ℤ) :
    ((finMod s hs n : ℕ) : ℤ) = n % (s : ℤ) := by
  rw [finMod_val]
  exact Int.toNat_of_nonneg (Int.emod_nonneg n (by omega))

/-- `finMod` depends only on the residue class `n mod s`. -/
theorem finMod_eq_of (s : ℕ) (hs : 0 < s) (j : Fin s) (q : ℤ) :
    finMod s hs ((j : ℤ) + (s : ℤ) * q) = j := by
  apply Fin.ext
  rw [finMod_val]
  have hj0 : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le (j : ℕ)
  have h : ((j : ℤ) + (s : ℤ) * q) % (s : ℤ) = (j : ℤ) := by
    rw [show (j : ℤ) + (s : ℤ) * q = (s : ℤ) * q + (j : ℤ) by ring,
      Int.mul_add_emod_self_left, Int.emod_eq_of_lt hj0 (by exact_mod_cast j.isLt)]
  rw [h]
  apply Nat.cast_injective (R := ℤ)
  exact Int.toNat_of_nonneg hj0

/-- The index `auJ` of the lemma is `finMod` of the unwrapped window index. -/
theorem auJ_eq_finMod (p α s t k i : ℕ) (hs : 2 ≤ s) :
    (⟨auJ p α s t k i, auJ_lt p α s t k i hs⟩ : Fin s)
      = finMod s (by omega) ((auK s t k : ℤ) + (i : ℤ) - (auM p α : ℤ)) := by
  apply Fin.ext
  simp only [auJ, finMod, Fin.val_mk]

/-- The real centre `ζ = s·k/t`. -/
noncomputable def auZeta (s t k : ℕ) : ℝ := (s : ℝ) * (k : ℝ) / (t : ℝ)

/-- The Gaussian weight `exp (−π (n−ζ)²/α²)`. -/
noncomputable def auGauss (α ζ : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-(Real.pi * ((n : ℝ) - ζ) ^ 2 / α ^ 2))

/-- The transferred summand `exp (−π (n−ζ)²/α²) · u (n mod s)`. -/
noncomputable def auHf (s : ℕ) (hs : 0 < s) (α ζ : ℝ) (u : Fin s → ℂ) (n : ℤ) : ℂ :=
  ((auGauss α ζ n : ℝ) : ℂ) * u (finMod s hs n)

/-- Start `K − m` of the retained window. -/
def auW0 (p α s t : ℕ) (k : ℕ) : ℤ := (auK s t k : ℤ) - (auM p α : ℤ)

@[simp] theorem auGauss_zero (α : ℝ) (ζ : ℝ) (n : ℤ) :
    auGauss α ζ n = Real.exp (-(Real.pi * ((n : ℝ) - ζ) ^ 2 / α ^ 2)) := rfl

/-- The summand of the `resSmat` theta series: `exp(−(π s²/α²)(k/t − j/s − q)²)`. -/
noncomputable def auTailE (s t α k : ℕ) (j : ℕ) (q : ℤ) : ℝ :=
  Real.exp (-Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2 *
    ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2)

theorem auW0_add (p α s t k i : ℕ) :
    auW0 p α s t k + (i : ℤ) = (auK s t k : ℤ) + (i : ℤ) - (auM p α : ℤ) := by
  simp only [auW0]; ring

theorem auGauss_nonneg (α ζ : ℝ) (n : ℤ) : 0 ≤ auGauss α ζ n := Real.exp_nonneg _

theorem auHf_norm_le (s : ℕ) (hs : 0 < s) (α ζ : ℝ) (u : Fin s → ℂ) (hu : ‖u‖ ≤ 1) (n : ℤ) :
    ‖auHf s hs α ζ u n‖ ≤ auGauss α ζ n := by
  rw [auHf, norm_mul]
  have h1 : ‖((auGauss α ζ n : ℝ) : ℂ)‖ = auGauss α ζ n := by
    exact (RCLike.norm_ofReal (auGauss α ζ n)).trans (abs_of_nonneg (Real.exp_nonneg _))
  rw [h1]
  exact mul_le_of_le_one_right (Real.exp_nonneg _) (le_trans (norm_le_pi_norm u _) hu)

theorem auHf_eq (s : ℕ) (hs : 0 < s) (α ζ : ℝ) (u : Fin s → ℂ) (n : ℤ) :
    auHf s hs α ζ u n = ((auGauss α ζ n : ℝ) : ℂ) * u (finMod s hs n) := rfl

end Work.Resample
