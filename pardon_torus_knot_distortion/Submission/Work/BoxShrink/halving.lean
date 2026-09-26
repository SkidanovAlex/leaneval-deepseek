import Mathlib
import Submission.Work.Box.Shrink

/-!
# The halving geometry of Pardon's box, for an arbitrary coordinate permutation

`Submission.halfBox_upper_subset` and `Submission.halfBox_lower_subset` describe the two halves of
`PBox r c 1` cut by the plane `{y 2 = c 2 + s}`.  Pardon's shrinking step needs the same statement
for a *general* permutation `σ`, i.e. for the box `PBox r c σ` cut by the plane
`{y (σ 2) = c (σ 2) + s}`: the two halves then fit in boxes whose coordinate permutation is
`cycPerm.trans σ` (the cyclic permutation of the three coordinate *directions of the box*), with
size `b * r + |s| / 2`.

Everything here is a direct transcription of the proofs in `Submission/Box.lean`, with the
coordinate `i` replaced by `σ i`.
-/

namespace Work.BoxShrink

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-- The shift in the direction `σ 2`: the vector with `d` at the coordinate `σ 2` and `0`
elsewhere.  For `σ = 1` it is `Submission.shiftV d`. -/
def shiftVσ (σ : Equiv.Perm (Fin 3)) (d : ℝ) : R3 :=
  WithLp.toLp 2 (fun m : Fin 3 => if m = σ 2 then d else 0)

@[simp] theorem shiftVσ_apply (σ : Equiv.Perm (Fin 3)) (d : ℝ) (m : Fin 3) :
    (shiftVσ σ d) m = if m = σ 2 then d else 0 := rfl

theorem add_shiftVσ_σ_zero (σ : Equiv.Perm (Fin 3)) (d : ℝ) (c : R3) :
    (c + shiftVσ σ d) (σ 0) = c (σ 0) := by
  have h : σ 0 ≠ σ 2 := by
    intro h
    have : (0 : Fin 3) = 2 := σ.injective h
    exact absurd this (by decide)
  simp [shiftVσ, h]

theorem add_shiftVσ_σ_one (σ : Equiv.Perm (Fin 3)) (d : ℝ) (c : R3) :
    (c + shiftVσ σ d) (σ 1) = c (σ 1) := by
  have h : σ 1 ≠ σ 2 := by
    intro h
    have : (1 : Fin 3) = 2 := σ.injective h
    exact absurd this (by decide)
  simp [shiftVσ, h]

theorem add_shiftVσ_σ_two (σ : Equiv.Perm (Fin 3)) (d : ℝ) (c : R3) :
    (c + shiftVσ σ d) (σ 2) = c (σ 2) + d := by simp [shiftVσ]

@[simp] theorem cycPerm_trans_zero (σ : Equiv.Perm (Fin 3)) :
    (Submission.cycPerm.trans σ) 0 = σ 2 := rfl
@[simp] theorem cycPerm_trans_one (σ : Equiv.Perm (Fin 3)) :
    (Submission.cycPerm.trans σ) 1 = σ 0 := rfl
@[simp] theorem cycPerm_trans_two (σ : Equiv.Perm (Fin 3)) :
    (Submission.cycPerm.trans σ) 2 = σ 1 := rfl

/-- **The upper half of Pardon's box (general coordinate permutation) fits in a permuted box.**

Cutting `PBox r c σ` by the plane `{y (σ 2) = c (σ 2) + u}`, the upper half
`{y (σ 2) < c (σ 2) + u}` is contained in the box
`PBox (b * r + |u|/2) (c + shiftVσ σ ((u - boxSide 2 * r)/2)) (cycPerm.trans σ)`. -/
theorem halfBox_upper_subset_perm (r u : ℝ) (hr : 0 < r) (_hu : |u| < Submission.boxSide 2 * r)
    (c : R3) (σ : Equiv.Perm (Fin 3)) :
    {y : R3 | y ∈ Submission.PBox r c σ ∧ y (σ 2) < c (σ 2) + u} ⊆
      Submission.PBox (Submission.b * r + |u| / 2)
        (c + shiftVσ σ ((u - Submission.boxSide 2 * r) / 2)) (Submission.cycPerm.trans σ) := by
  intro y hy
  obtain ⟨hybox, hy2⟩ := hy
  have h0 : |y (σ 0) - c (σ 0)| < r := by simpa using hybox 0
  have h1 : |y (σ 1) - c (σ 1)| < Submission.boxSide 1 * r := by simpa using hybox 1
  have h2 : |y (σ 2) - c (σ 2)| < Submission.boxSide 2 * r := by simpa using hybox 2
  have hb2 : Submission.boxSide 2 = 2 * Submission.b := Submission.two_mul_b.symm
  set d : ℝ := (u - Submission.boxSide 2 * r) / 2 with hd
  have key0 : |y (σ 2) - (c + shiftVσ σ d) (σ 2)| < Submission.b * r + |u| / 2 := by
    rw [add_shiftVσ_σ_two, hd]
    rw [abs_lt]
    have hle : (Submission.boxSide 2 * r + u) / 2 ≤ Submission.b * r + |u| / 2 := by
      rw [hb2]; have := le_abs_self u; linarith
    have hle' : -(Submission.b * r + |u| / 2) ≤ -(Submission.boxSide 2 * r + u) / 2 := by
      have := neg_le_abs u; linarith
    constructor
    · have := (abs_lt.mp h2).1; linarith
    · have := (abs_lt.mp h2).2; linarith
  have key1 : |y (σ 0) - (c + shiftVσ σ d) (σ 0)|
      < Submission.boxSide 1 * (Submission.b * r + |u| / 2) := by
    rw [add_shiftVσ_σ_zero]
    have hb1 : Submission.boxSide 1 * Submission.b = 1 := by
      rw [mul_comm, Submission.b_mul_boxSide_one]
    have hle : r ≤ Submission.boxSide 1 * (Submission.b * r + |u| / 2) := by
      nlinarith [hb1, Submission.boxSide_pos 1, hr, abs_nonneg u]
    linarith [abs_lt.mp h0]
  have key2 : |y (σ 1) - (c + shiftVσ σ d) (σ 1)|
      < Submission.boxSide 2 * (Submission.b * r + |u| / 2) := by
    rw [add_shiftVσ_σ_one]
    have hb : Submission.boxSide 2 * Submission.b = Submission.boxSide 1 := by
      rw [mul_comm, Submission.b_mul_boxSide_two]
    have hle : Submission.boxSide 1 * r ≤ Submission.boxSide 2 * (Submission.b * r + |u| / 2) := by
      have h : Submission.boxSide 2 * (Submission.b * r) = Submission.boxSide 1 * r := by
        rw [← mul_assoc, hb]
      nlinarith [h, Submission.boxSide_pos 2, hr, abs_nonneg u]
    linarith [abs_lt.mp h1]
  intro i
  fin_cases i
  · simpa [Equiv.trans_apply, Submission.boxSide_zero] using key0
  · simpa [Equiv.trans_apply, Submission.boxSide_one] using key1
  · simpa [Equiv.trans_apply, Submission.boxSide_two] using key2

/-- **The lower half of Pardon's box (general coordinate permutation) fits in a permuted box.**

Cutting `PBox r c σ` by the plane `{y (σ 2) = c (σ 2) + u}`, the lower half
`{c (σ 2) + u < y (σ 2)}` is contained in the box
`PBox (b * r + |u|/2) (c + shiftVσ σ ((u + boxSide 2 * r)/2)) (cycPerm.trans σ)`. -/
theorem halfBox_lower_subset_perm (r u : ℝ) (hr : 0 < r) (_hu : |u| < Submission.boxSide 2 * r)
    (c : R3) (σ : Equiv.Perm (Fin 3)) :
    {y : R3 | y ∈ Submission.PBox r c σ ∧ c (σ 2) + u < y (σ 2)} ⊆
      Submission.PBox (Submission.b * r + |u| / 2)
        (c + shiftVσ σ ((u + Submission.boxSide 2 * r) / 2)) (Submission.cycPerm.trans σ) := by
  intro y hy
  obtain ⟨hybox, hy2⟩ := hy
  have h0 : |y (σ 0) - c (σ 0)| < r := by simpa using hybox 0
  have h1 : |y (σ 1) - c (σ 1)| < Submission.boxSide 1 * r := by simpa using hybox 1
  have h2 : |y (σ 2) - c (σ 2)| < Submission.boxSide 2 * r := by simpa using hybox 2
  have hb2 : Submission.boxSide 2 = 2 * Submission.b := Submission.two_mul_b.symm
  set d : ℝ := (u + Submission.boxSide 2 * r) / 2 with hd
  have key0 : |y (σ 2) - (c + shiftVσ σ d) (σ 2)| < Submission.b * r + |u| / 2 := by
    rw [add_shiftVσ_σ_two, hd]
    rw [abs_lt]
    have hle : (Submission.boxSide 2 * r - u) / 2 ≤ Submission.b * r + |u| / 2 := by
      rw [hb2]; have := neg_le_abs u; linarith
    have hle' : -(Submission.b * r + |u| / 2) ≤ -(Submission.boxSide 2 * r - u) / 2 := by
      have := le_abs_self u; linarith
    constructor
    · have := (abs_lt.mp h2).1; linarith
    · have := (abs_lt.mp h2).2; linarith
  have key1 : |y (σ 0) - (c + shiftVσ σ d) (σ 0)|
      < Submission.boxSide 1 * (Submission.b * r + |u| / 2) := by
    rw [add_shiftVσ_σ_zero]
    have hb1 : Submission.boxSide 1 * Submission.b = 1 := by
      rw [mul_comm, Submission.b_mul_boxSide_one]
    have hle : r ≤ Submission.boxSide 1 * (Submission.b * r + |u| / 2) := by
      nlinarith [hb1, Submission.boxSide_pos 1, hr, abs_nonneg u]
    linarith [abs_lt.mp h0]
  have key2 : |y (σ 1) - (c + shiftVσ σ d) (σ 1)|
      < Submission.boxSide 2 * (Submission.b * r + |u| / 2) := by
    rw [add_shiftVσ_σ_one]
    have hb : Submission.boxSide 2 * Submission.b = Submission.boxSide 1 := by
      rw [mul_comm, Submission.b_mul_boxSide_two]
    have hle : Submission.boxSide 1 * r ≤ Submission.boxSide 2 * (Submission.b * r + |u| / 2) := by
      have h : Submission.boxSide 2 * (Submission.b * r) = Submission.boxSide 1 * r := by
        rw [← mul_assoc, hb]
      nlinarith [h, Submission.boxSide_pos 2, hr, abs_nonneg u]
    linarith [abs_lt.mp h1]
  intro i
  fin_cases i
  · simpa [Equiv.trans_apply, Submission.boxSide_zero] using key0
  · simpa [Equiv.trans_apply, Submission.boxSide_one] using key1
  · simpa [Equiv.trans_apply, Submission.boxSide_two] using key2

/-- The size of a half-box is at most `shrinkFactor * r` once `|u| ≤ eps * r`. -/
theorem b_add_half_le (r u : ℝ) (hr : 0 ≤ r) (hu : |u| ≤ Submission.eps * r) :
    Submission.b * r + |u| / 2 ≤ Submission.shrinkFactor * r := by
  have h1 : Submission.b + Submission.eps / 2 ≤ Submission.shrinkFactor := by
    rw [Submission.shrinkFactor, Submission.eps]
    nlinarith [Submission.b_pos]
  have h2 : |u| / 2 ≤ Submission.eps * r / 2 := by linarith
  nlinarith [h1, h2, hr]

end

end Work.BoxShrink
