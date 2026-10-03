/-
# `Submission.Work.FIArea3.JointCount.jointPieceBoxLat_basis`

A two-element ℤ-basis of the *box* lattice

  `L = (yLat (star z₁ * w).re (star z₁ * w).im e).map (AddMonoidHom.mulRight w)`

with the paper's size bound (the index being that of `jointPieceLat z₁ w e`).

The box lattice differs from `jointPieceLat z₁ w e` only by the transposition of the two
coefficients of `yLat`: here they are `(s.re, s.im)` with `s = star z₁ * w`, whereas
`jointPieceLat` uses `(s.im, s.re)`.  Since `Nat.gcd` is commutative the two lattices have the
same index, which is what the statement records (the index appearing in the conclusion is
`(jointPieceLat z₁ w e).index`).

The basis itself is produced by `jpl_yLat_basis` (`jointPieceLat_basis.lean`) applied to the
congruence lattice `yLat s.re s.im e`, multiplied by `w`; the transfer step is the same one
used for `jointPieceLat`, with the two `gcd`s identified through `Nat.gcd_comm`.
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.pieces
import Submission.Work.FIArea3.JointCount.jointPieceLat_basis
import Submission.Work.FIArea3.JointCount.index_jointPieceLat

namespace Work.FIArea3.JointCount

open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The additive endomorphism `y ↦ y * w` is injective for `w ≠ 0`. -/
lemma jpl_mulRight_injective {w : GaussianInt} (hw : w ≠ 0) :
    Function.Injective (AddMonoidHom.mulRight w) := by
  intro a b hab
  simp only [AddMonoidHom.mulRight_apply] at hab
  exact mul_right_cancel₀ hw hab

/-- The index of the box lattice `(yLat (star z₁ * w).re (star z₁ * w).im e).map (mulRight w)`
equals the index of the joint piece lattice `jointPieceLat z₁ w e`. -/
lemma jpl_boxMap_index (z₁ w : GaussianInt) (e : ℕ) (he : 1 ≤ e) (hw : w ≠ 0) :
    ((yLat (star z₁ * w).re (star z₁ * w).im e).map (AddMonoidHom.mulRight w)).index
      = (jointPieceLat z₁ w e).index := by
  have hinj := jpl_mulRight_injective hw
  rw [AddSubgroup.index_map_of_injective _ hinj, mulRight_range_index w hw,
    yLat_index_formula (star z₁ * w).re (star z₁ * w).im e he,
    index_jointPieceLat z₁ w e he hw,
    Nat.gcd_comm (star z₁ * w).re.natAbs (star z₁ * w).im.natAbs]
  exact mul_comm _ _

/-- **Transfer step for the box lattice.**  A two-element ℤ-basis `m₁, m₂` of
`yLat (star z₁ * w).re (star z₁ * w).im e` whose determinant is
`q = e / gcd e (gcd (star z₁ * w).re.natAbs (star z₁ * w).im.natAbs)` and whose lengths sum to at
most `5 q`, when multiplied by `w`, gives the requested determinant, carrier and length bound. -/
lemma jpl_box_transfer (z₁ w : GaussianInt) (e : ℕ) (hw : w ≠ 0) (he : 1 ≤ e)
    {m₁ m₂ : GaussianInt}
    (hmem : ∀ z : GaussianInt, z ∈ yLat (star z₁ * w).re (star z₁ * w).im e ↔
      ∃ a b : ℤ, z = (a : GaussianInt) * m₁ + (b : GaussianInt) * m₂)
    (hdet : (m₁.re * m₂.im - m₁.im * m₂.re).natAbs
      = e / Nat.gcd e (Nat.gcd (star z₁ * w).re.natAbs (star z₁ * w).im.natAbs))
    (hbound : Real.sqrt ((gnorm m₁ : ℕ) : ℝ) + Real.sqrt ((gnorm m₂ : ℕ) : ℝ)
      ≤ 5 * ((e / Nat.gcd e (Nat.gcd (star z₁ * w).re.natAbs (star z₁ * w).im.natAbs) : ℕ) : ℝ)) :
    ((m₁ * w).re * (m₂ * w).im - (m₁ * w).im * (m₂ * w).re).natAbs
        = (jointPieceLat z₁ w e).index
      ∧ ((yLat (star z₁ * w).re (star z₁ * w).im e).map (AddMonoidHom.mulRight w)).carrier
          = {z : GaussianInt | ∃ a b : ℤ,
              z = (a : GaussianInt) * (m₁ * w) + (b : GaussianInt) * (m₂ * w)}
      ∧ Real.sqrt ((gnorm (m₁ * w) : ℕ) : ℝ) + Real.sqrt ((gnorm (m₂ * w) : ℕ) : ℝ)
          ≤ ((jointPieceLat z₁ w e).index : ℝ) * (5 / Real.sqrt ((gnorm w : ℕ) : ℝ)) := by
  have hinj := jpl_mulRight_injective hw
  refine ⟨?_, ?_, ?_⟩
  · rw [jpl_det_mul, hdet, ← jpl_boxMap_index z₁ w e he hw,
      AddSubgroup.index_map_of_injective _ hinj, mulRight_range_index w hw,
      yLat_index_formula (star z₁ * w).re (star z₁ * w).im e he]
  · ext z
    simp only [Set.mem_ofPred_eq]
    change z ∈ (yLat (star z₁ * w).re (star z₁ * w).im e).map (AddMonoidHom.mulRight w)
      ↔ ∃ a b : ℤ, z = (a : GaussianInt) * (m₁ * w) + (b : GaussianInt) * (m₂ * w)
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, b, rfl⟩ := (hmem y).mp hy
      exact ⟨a, b, by rw [AddMonoidHom.mulRight_apply]; ring⟩
    · rintro ⟨a, b, rfl⟩
      refine ⟨(a : GaussianInt) * m₁ + (b : GaussianInt) * m₂, (hmem _).mpr ⟨a, b, rfl⟩, ?_⟩
      rw [AddMonoidHom.mulRight_apply]
      ring
  · have hindex : (jointPieceLat z₁ w e).index
        = gnorm w * (e / Nat.gcd e
            (Nat.gcd (star z₁ * w).re.natAbs (star z₁ * w).im.natAbs)) := by
      rw [← jpl_boxMap_index z₁ w e he hw, AddSubgroup.index_map_of_injective _ hinj,
        mulRight_range_index w hw, yLat_index_formula (star z₁ * w).re (star z₁ * w).im e he]
      exact mul_comm _ _
    have e1 : Real.sqrt ((gnorm (m₁ * w) : ℕ) : ℝ)
        = Real.sqrt ((gnorm m₁ : ℕ) : ℝ) * Real.sqrt ((gnorm w : ℕ) : ℝ) := by
      rw [jpl_gnorm_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    have e2 : Real.sqrt ((gnorm (m₂ * w) : ℕ) : ℝ)
        = Real.sqrt ((gnorm m₂ : ℕ) : ℝ) * Real.sqrt ((gnorm w : ℕ) : ℝ) := by
      rw [jpl_gnorm_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    rw [e1, e2, hindex]
    have hrhs : ((gnorm w * (e / Nat.gcd e
            (Nat.gcd (star z₁ * w).re.natAbs (star z₁ * w).im.natAbs)) : ℕ) : ℝ)
          * (5 / Real.sqrt ((gnorm w : ℕ) : ℝ))
        = 5 * ((e / Nat.gcd e
            (Nat.gcd (star z₁ * w).re.natAbs (star z₁ * w).im.natAbs) : ℕ) : ℝ)
          * Real.sqrt ((gnorm w : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      have hs2 : Real.sqrt ((gnorm w : ℕ) : ℝ) ^ 2 = ((gnorm w : ℕ) : ℝ) :=
        Real.sq_sqrt (Nat.cast_nonneg _)
      have hpos : (0 : ℝ) < ((gnorm w : ℕ) : ℝ) := by
        exact_mod_cast jpl_gnorm_pos hw
      have hsne : Real.sqrt ((gnorm w : ℕ) : ℝ) ≠ 0 := by
        intro h
        have h0 : ((gnorm w : ℕ) : ℝ) = 0 := by rw [← hs2, h]; ring
        linarith
      rw [← mul_div_assoc, div_eq_iff hsne]
      nlinarith [hs2]
    rw [hrhs]
    nlinarith [hbound, Real.sqrt_nonneg ((gnorm w : ℕ) : ℝ)]

theorem jointPieceBoxLat_basis (z₁ w : GaussianInt) (e : ℕ) (hw : w ≠ 0) (he : 1 ≤ e) :
    ∃ g₁ g₂ : GaussianInt,
      (g₁.re * g₂.im - g₁.im * g₂.re).natAbs
          = (Work.FIArea3.JointCount.jointPieceLat z₁ w e).index
        ∧ ((Work.FIArea3.JointCount.yLat (star z₁ * w).re (star z₁ * w).im e).map
              (AddMonoidHom.mulRight w)).carrier
            = {z : GaussianInt | ∃ a b : ℤ,
                z = (a : GaussianInt) * g₁ + (b : GaussianInt) * g₂}
        ∧ Real.sqrt ((Work.FIPlan.gnorm g₁ : ℝ)) + Real.sqrt ((Work.FIPlan.gnorm g₂ : ℝ))
            ≤ ((Work.FIArea3.JointCount.jointPieceLat z₁ w e).index : ℝ)
                * (5 / Real.sqrt ((Work.FIPlan.gnorm w : ℝ))) := by
  obtain ⟨m₁, m₂, hmem, hdet, hbound⟩ :=
    jpl_yLat_basis (star z₁ * w).re (star z₁ * w).im e he
  exact ⟨m₁ * w, m₂ * w, jpl_box_transfer z₁ w e hw he hmem hdet hbound⟩

end

end Work.FIArea3.JointCount
