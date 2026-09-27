import Mathlib
import Submission.Work.Drive.WindingNumber

/-!
# Crossing data for the winding-number bound

The proof of `Work.Drive.winding_values` (a smooth Jordan curve winds `0` or `±1` times, i.e. `0` or
`±2` times in the doubled `dirC` convention) runs as follows.

Fix `p` off the curve `γ` and a line `L` through `p` meeting `γ` transversally.  The classical
**signed crossing count formula** expresses the winding number as the sum, over the crossings of `L`
with `γ`, of the sign of the cross product `det(γ t - p, γ' t)` (the derivative of the *angle* of
`γ t - p`).  Along a *ray* of `L` these signs alternate, so each ray contributes `0` or `±1`; the two
rays contribute with opposite overall sign, and the total number of crossings being even forces the
two contributions to vanish together.  Hence the winding number is in `{0, ±2}`.

This file collects the vocabulary: the two-dimensional cross product `cross2`, the crossing sets
`crossings` and `rayCrossings`, and the signed crossing sums.
-/

namespace Work.Drive

/-- The two-dimensional cross product (determinant) of two plane vectors. -/
def cross2 (a b : ℝ × ℝ) : ℝ := a.1 * b.2 - a.2 * b.1

lemma cross2_skew (a b : ℝ × ℝ) : cross2 a b = - cross2 b a := by
  simp only [cross2]; ring

lemma cross2_smul_left (r : ℝ) (a b : ℝ × ℝ) : cross2 (r • a) b = r * cross2 a b := by
  simp only [cross2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma cross2_smul_right (r : ℝ) (a b : ℝ × ℝ) : cross2 a (r • b) = r * cross2 a b := by
  simp only [cross2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

lemma cross2_self (a : ℝ × ℝ) : cross2 a a = 0 := by simp only [cross2]; ring

lemma cross2_neg_left (a b : ℝ × ℝ) : cross2 (-a) b = - cross2 a b := by
  rw [show (-a : ℝ × ℝ) = (-1 : ℝ) • a from by simp, cross2_smul_left]
  ring

/-- If `b` is a multiple of `a` then the cross product vanishes. -/
lemma cross2_eq_zero_of_smul (r : ℝ) (a : ℝ × ℝ) : cross2 a (r • a) = 0 := by
  rw [cross2_smul_right, cross2_self, mul_zero]

/-- Conversely, if `a ≠ 0` and the cross product vanishes then `b` is a multiple of `a`. -/
lemma exists_smul_of_cross2_eq_zero {a b : ℝ × ℝ} (ha : a ≠ 0) (h : cross2 a b = 0) :
    ∃ r : ℝ, b = r • a := by
  have hkey : a.1 * b.2 = a.2 * b.1 := by
    have := h; simp only [cross2] at this; linarith
  rcases eq_or_ne a.1 0 with h1 | h1
  · have h2 : a.2 ≠ 0 := by
      intro h2; exact ha (Prod.ext h1 h2)
    refine ⟨b.2 / a.2, ?_⟩
    have hb1 : b.1 = 0 := by
      rw [h1, zero_mul] at hkey
      exact (mul_eq_zero.mp hkey.symm).resolve_left h2
    have hb2 : b.2 = (b.2 / a.2) * a.2 := (div_mul_cancel₀ b.2 h2).symm
    refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst]; simp [hb1, h1]
    · rw [Prod.smul_snd]; simpa using hb2
  · refine ⟨b.1 / a.1, ?_⟩
    have hb1 : b.1 = (b.1 / a.1) * a.1 := (div_mul_cancel₀ b.1 h1).symm
    have hb2 : b.2 = (b.1 / a.1) * a.2 := by
      rw [div_mul_eq_mul_div, eq_div_iff h1]; linarith
    refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst]; simpa using hb1
    · rw [Prod.smul_snd]; simpa using hb2

lemma cross2_eq_zero_iff_of_ne {a b : ℝ × ℝ} (ha : a ≠ 0) :
    cross2 a b = 0 ↔ ∃ r : ℝ, b = r • a :=
  ⟨exists_smul_of_cross2_eq_zero ha, fun ⟨r, hr⟩ => by rw [hr, cross2_eq_zero_of_smul]⟩

/-- The periodic derivative of the plane curve `γ`. -/
noncomputable def cderiv (γ : UnitAddCircle → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  deriv (fun s : ℝ => γ (s : UnitAddCircle)) t

/-- The crossings of the line through `p` in direction `v` with the curve `γ`, as parameters in one
period `[0,1)`. -/
def crossings (γ : UnitAddCircle → ℝ × ℝ) (p v : ℝ × ℝ) : Set ℝ :=
  {t | t ∈ Set.Ico 0 1 ∧ ∃ s : ℝ, γ (t : UnitAddCircle) - p = s • v}

/-- The crossings lying on the *ray* from `p` in direction `v` (strictly positive parameter). -/
def rayCrossings (γ : UnitAddCircle → ℝ × ℝ) (p v : ℝ × ℝ) : Set ℝ :=
  {t | t ∈ Set.Ico 0 1 ∧ ∃ s : ℝ, 0 < s ∧ γ (t : UnitAddCircle) - p = s • v}

lemma rayCrossings_subset_crossings (γ : UnitAddCircle → ℝ × ℝ) (p v : ℝ × ℝ) :
    rayCrossings γ p v ⊆ crossings γ p v := by
  rintro t ⟨ht, s, _, hs⟩
  exact ⟨ht, s, hs⟩

/-- The signed crossing sum: over a finite set `S` of crossings, `+1` for each crossing at which
`t ↦ cross2 (γ t - p) (γ' t)` is positive and `-1` otherwise. -/
noncomputable def signedCrossingSum (γ : UnitAddCircle → ℝ × ℝ) (p : ℝ × ℝ) (S : Finset ℝ) : ℤ :=
  S.sum (fun t => if 0 < cross2 (γ (t : UnitAddCircle) - p) (cderiv γ t) then (1 : ℤ) else -1)

/-- The signed "up/down" crossing sum over a finite set of crossings, with respect to a fixed
direction `u`: `+1` when `cross2 u (γ' t) > 0`. -/
noncomputable def signedRaySum (γ : UnitAddCircle → ℝ × ℝ) (u : ℝ × ℝ) (S : Finset ℝ) : ℤ :=
  S.sum (fun t => if 0 < cross2 u (cderiv γ t) then (1 : ℤ) else -1)

end Work.Drive
