import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces

/-!
# `EKLC6Core.conjBox_nhds` — the conjugated box is a neighbourhood of `1` inside `U`

For a horospherical subgroup `U ≤ SL₃(ℝ)` (i.e. `IsHoro U`: closed, normalised by the diagonal
flow `t ↦ aDiag t`, and contracted by some `aDiag t₀`) and *any* exponent vector `t`, the
conjugated box

`conjBox U t = aDiag t · Box1 U · (aDiag t)⁻¹`

contains `U ∩ V δ` for some `δ > 0` (`V δ` = the matrices of max-entry distance `< δ` from `1`).

The argument is elementary.  `Box1 U ⊇ V (1/2) ∩ U`, so `Box1 U` is a neighbourhood of `1` in
`U`; conjugation by `aDiag t` maps `U` to itself (`IsHoro` provides the normalisation) and scales
the entries by `e^{tᵢ - tⱼ}`:

`(aDiag (-t) · g · aDiag t)ᵢⱼ = e^{tⱼ - tᵢ} gᵢⱼ`   (`aDiag_conj_entry` below).

Hence, for `δ = min 1 (e^{-S})` with `S = ∑_{i,j} |tᵢ - tⱼ|`, every `g ∈ U ∩ V δ` has
`|(aDiag (-t) g aDiag t)ᵢⱼ - δᵢⱼ| ≤ 1`, i.e. `aDiag (-t) g aDiag t ∈ Box1 U`; conjugating back
by `aDiag t` puts `g` in `conjBox U t`.

This is the ingredient that makes `conjBox U t` a genuine neighbourhood of the identity in `U`
for *both* orientations of the exponent vector `t` (contracting as well as expanding), and hence
that the "information" `growthFun U ν t = -log (ν x (conjBox U t))` is finite near the identity.
-/

namespace Work.EKLC6Core

open Work.EKLContract

noncomputable section

/-! ## Conjugation by the diagonal flow, entrywise -/

/-- `(aDiag t)⁻¹ = aDiag (-t)`. -/
private theorem aDiag_inv_neg_aux (t : Fin 3 → ℝ) : (aDiag t)⁻¹ = aDiag (-t) :=
  inv_eq_of_mul_eq_one_left (aDiag_neg_mul t)

/-- `(aDiag (-t))⁻¹ = aDiag t`. -/
private theorem aDiag_neg_inv_aux (t : Fin 3 → ℝ) : (aDiag (-t))⁻¹ = aDiag t :=
  inv_eq_of_mul_eq_one_left (aDiag_mul_neg t)

/-- The underlying matrix of `aDiag t`, stated for the coercion `SL₃(ℝ) → Matrix`. -/
private theorem coe_aDiag_aux (t : Fin 3 → ℝ) :
    ((aDiag t : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = Matrix.diagonal (fun i => Real.exp (t i - (∑ j, t j) / 3)) := rfl

/-- The underlying matrix of a product, stated for the coercion `SL₃(ℝ) → Matrix`. -/
private theorem coe_mul_aux (A B : SL3) :
    ((A * B : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = (A : Matrix (Fin 3) (Fin 3) ℝ) * (B : Matrix (Fin 3) (Fin 3) ℝ) := rfl

/-- **The diagonal flow scales the entries of a matrix**: conjugating `g` by the diagonal
`aDiag t` multiplies the entry `(i,j)` by `e^{tᵢ - tⱼ}`, i.e.
`(aDiag (-t) · g · aDiag t)ᵢⱼ = e^{tⱼ - tᵢ} gᵢⱼ`. -/
theorem aDiag_conj_entry (t : Fin 3 → ℝ) (g : SL3) (i j : Fin 3) :
    (aDiag (-t) * g * aDiag t) i j = Real.exp (t j - t i) * g i j := by
  have hsum : ((-t) i - (∑ j, (-t) j) / 3) + (t j - (∑ k, t k) / 3) = t j - t i := by
    simp only [Pi.neg_apply]
    rw [Finset.sum_neg_distrib]
    ring
  have hexp : Real.exp ((-t) i - (∑ j, (-t) j) / 3) * Real.exp (t j - (∑ k, t k) / 3)
      = Real.exp (t j - t i) := by
    rw [← Real.exp_add, hsum]
  rw [coe_mul_aux, coe_mul_aux, coe_aDiag_aux, coe_aDiag_aux]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  calc Real.exp ((-t) i - (∑ j, (-t) j) / 3)
        * ((g : Matrix (Fin 3) (Fin 3) ℝ) i j * Real.exp (t j - (∑ k, t k) / 3))
      = Real.exp ((-t) i - (∑ j, (-t) j) / 3) * Real.exp (t j - (∑ k, t k) / 3)
          * (g : Matrix (Fin 3) (Fin 3) ℝ) i j := by ring
    _ = Real.exp (t j - t i) * (g : Matrix (Fin 3) (Fin 3) ℝ) i j := by rw [hexp]
    _ = Real.exp (t j - t i) * g i j := rfl

/-! ## The main statement -/

/-- **The conjugated box is a neighbourhood of `1` in `U`.**  For a horospherical subgroup `U`
and any `t : Fin 3 → ℝ` there is `δ > 0` with `U ∩ V δ ⊆ conjBox U t`. -/
theorem conjBox_nhds {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    (t : Fin 3 → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : Work.EKLContract.SL3,
      g ∈ Work.EKLContract.V δ → g ∈ U → g ∈ Work.EKLC6Core.conjBox U t := by
  set S : ℝ := ∑ p : Fin 3 × Fin 3, |t p.1 - t p.2| with hS
  refine ⟨min 1 (Real.exp (-S)), lt_min zero_lt_one (Real.exp_pos _), ?_⟩
  intro g hg hgU
  rw [conjBox, conjBy, Set.mem_image]
  refine ⟨aDiag (-t) * g * aDiag t, ⟨?_, ?_⟩, ?_⟩
  · -- the conjugate lies in the subgroup
    have h := hU.2.1 (-t) g hgU
    rwa [aDiag_neg_inv_aux] at h
  · -- and in the box `Box1 U`
    intro i j
    rw [aDiag_conj_entry]
    by_cases hij : i = j
    · rw [hij, sub_self, Real.exp_zero, one_mul, Matrix.one_apply_eq]
      have h := hg j j
      rw [Matrix.one_apply_eq] at h
      exact le_trans (le_of_lt h) (min_le_left 1 (Real.exp (-S)))
    · rw [Matrix.one_apply_ne hij, sub_zero]
      have hgij : |g i j| < Real.exp (-S) := by
        have h := hg i j
        rw [Matrix.one_apply_ne hij, sub_zero] at h
        exact lt_of_lt_of_le h (min_le_right 1 (Real.exp (-S)))
      have hSij : |t i - t j| ≤ S := by
        rw [hS]
        exact Finset.single_le_sum (f := fun p : Fin 3 × Fin 3 => |t p.1 - t p.2|)
          (fun p _ => abs_nonneg _) (Finset.mem_univ (i, j))
      have hexp_le : Real.exp (t j - t i) ≤ Real.exp S := by
        apply Real.exp_le_exp_of_le
        calc t j - t i ≤ |t j - t i| := le_abs_self _
          _ = |t i - t j| := abs_sub_comm _ _
          _ ≤ S := hSij
      calc |Real.exp (t j - t i) * g i j|
          = Real.exp (t j - t i) * |g i j| := by
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp S * Real.exp (-S) :=
            mul_le_mul hexp_le (le_of_lt hgij) (abs_nonneg _) (le_of_lt (Real.exp_pos _))
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  · -- conjugating back recovers `g`
    rw [aDiag_inv_neg_aux]
    calc aDiag t * (aDiag (-t) * g * aDiag t) * aDiag (-t)
        = (aDiag t * aDiag (-t)) * g * (aDiag t * aDiag (-t)) := by group
      _ = g := by rw [aDiag_mul_neg, one_mul, mul_one]

end

end Work.EKLC6Core
