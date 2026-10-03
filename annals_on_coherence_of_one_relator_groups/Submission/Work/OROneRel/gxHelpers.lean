/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# Elementary bridge lemmas for the global gauge extension of a window

Small lemmas about `wordOf`, `lsig` and the cohomological weight that the proof of
`Work.OROneRel.exists_globalGauge_of_windowData` uses: the reduced word of a product is a reduction
of the concatenation of the reduced words, the reduced word of an `x`-power is a list of letters, the
weight of the reduced word of an element is its cohomological weight.
-/
import Mathlib
import Submission.Work.OROneRel.gaugeExtWindowDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The weight of the reduced word of an element is its cohomological weight. -/
theorem gx_lsig_wordOf (c : α → ℤ) (u : FreeGroup α) :
    lsig c (wordOf u) = (cohom c u).toAdd := by
  have h := cohom_mk c (wordOf u)
  rw [mk_wordOf] at h
  simpa using (congrArg Multiplicative.toAdd h).symm

/-- The weight of the reduced word of an element of cohomological weight `v` is `v`. -/
theorem gx_lsig_wordOf_of_cohom (c : α → ℤ) {u : FreeGroup α} {v : ℤ}
    (h : cohom c u = Multiplicative.ofAdd v) : lsig c (wordOf u) = v := by
  rw [gx_lsig_wordOf, h]
  rfl

/-- `wordOf` of a product is a reduction of the concatenation of the reduced words. -/
theorem gx_wordOf_mul_red (A B : FreeGroup α) :
    FreeGroup.Red (wordOf A ++ wordOf B) (wordOf (A * B)) := by
  have h : wordOf (A * B) = @FreeGroup.reduce α (Classical.decEq α) (wordOf A ++ wordOf B) := by
    show @FreeGroup.toWord α (Classical.decEq α) (A * B) =
      @FreeGroup.reduce α (Classical.decEq α)
        (@FreeGroup.toWord α (Classical.decEq α) A ++ @FreeGroup.toWord α (Classical.decEq α) B)
    rw [@FreeGroup.toWord_mul α (Classical.decEq α)]
  rw [h]
  exact @FreeGroup.reduce.red α (wordOf A ++ wordOf B) (Classical.decEq α)

/-- Reversing a constant list. -/
theorem gx_invRev_replicate (x : α) (b : Bool) (n : ℕ) :
    FreeGroup.invRev (List.replicate n (x, b)) = List.replicate n (x, !b) := by
  simp [FreeGroup.invRev, List.map_replicate]

/-- The reduced word of a positive power of a generator. -/
theorem gx_wordOf_pow (x : α) (n : ℕ) :
    wordOf ((FreeGroup.of x) ^ n) = List.replicate n (x, true) := by
  show @FreeGroup.toWord α (Classical.decEq α) ((FreeGroup.of x : FreeGroup α) ^ n) = _
  rw [@FreeGroup.toWord_of_pow α (Classical.decEq α) x n]

/-- The reduced word of a negative power of a generator. -/
theorem gx_wordOf_zpow_neg (x : α) (n : ℕ) :
    wordOf ((FreeGroup.of x) ^ (-(n : ℤ))) = List.replicate n (x, false) := by
  have h1 : (FreeGroup.of x : FreeGroup α) ^ (-(n : ℤ)) =
      (((FreeGroup.of x : FreeGroup α)) ^ n)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [h1]
  have h2 : wordOf ((((FreeGroup.of x : FreeGroup α)) ^ n)⁻¹) =
      FreeGroup.invRev (wordOf (((FreeGroup.of x : FreeGroup α)) ^ n)) := by
    show @FreeGroup.toWord α (Classical.decEq α) ((((FreeGroup.of x : FreeGroup α)) ^ n)⁻¹) = _
    rw [@FreeGroup.toWord_inv α (Classical.decEq α)]
    rfl
  rw [h2, gx_wordOf_pow, gx_invRev_replicate]
  simp

/-- The powers of `ofAdd d` in the multiplicative copy of `ℤ`. -/
theorem gx_ofAdd_zpow (d k : ℤ) :
    (Multiplicative.ofAdd d : Multiplicative ℤ) ^ k = Multiplicative.ofAdd (k * d) := by
  rw [← Int.ofAdd_mul, mul_comm]

/-- The cohomological weight of a power of a generator. -/
theorem gx_cohom_of_zpow (c : α → ℤ) (x : α) (k : ℤ) :
    cohom c ((FreeGroup.of x) ^ k) = Multiplicative.ofAdd (k * c x) := by
  rw [map_zpow, cohom_of, gx_ofAdd_zpow]

end Work.OROneRel
