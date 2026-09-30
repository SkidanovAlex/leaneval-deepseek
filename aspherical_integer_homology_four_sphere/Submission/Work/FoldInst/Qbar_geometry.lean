/-
# The geometry of the truncated 24-cell `Q̄`

`Q̄ ⊂ E4 = ℝ⁴` is the intersection of the 24 *side* constraints `sideSlack S y ≥ 0` — the facets of
the Klein-model hyperbolic 24-cell `Q` — and the 24 *truncation* constraints `truncSlack w y ≥ 0`,
which cut off the ideal vertices `p_w = truncNormal w` of `Q`.

This file proves `Qbar_geometry`: `Q̄` is compact, convex, closed, nonempty, and contained in the
open unit ball `HypModel.ball` (the Klein model of `H⁴`).

The proof rests on three finite lookups in the tables of `Submission.Work.FoldInst.Data`
(`Qbar_side_lookup`, `Qbar_trunc_sign_lookup`, `Qbar_trunc_e_lookup`), from which membership in
`Q̄` gives the three numerical bounds `|y i| ≤ 4/5`, `|y i| + |y j| ≤ 1` and `∑ |y i| ≤ 8/5`
(`Qbar_abs_le`, `Qbar_pair_le`, `Qbar_sum_abs_le`).  These imply `∑ (y i)² ≤ 4/5 < 1`
(`Qbar_sum_sq_lt_one`), hence the ball inclusion `Qbar_subset_ball` and — combined with closedness
and nonemptiness, read off the 48 half-space presentation — compactness, convexity and the final
statement.
-/
import Mathlib
import Submission.Work.FoldInst.Continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000

noncomputable section

open Matrix
open scoped Matrix

namespace Work.FoldInst

/-! ### The three finite lookups in the tables of `Data.lean` -/

/-- The `±1` attached to a bit (`0 ↦ +1`, `1 ↦ −1`). -/
def Qbar_sgnZ (ε : ZMod 2) : ℤ := if ε = 0 then 1 else -1

/-- **Lookup 1 (the sides).**  For every pair of distinct coordinates and every prescribed pair of
signs there is a side normal that takes exactly those values on those two coordinates and vanishes
elsewhere.  (The 24 side normals are the vectors `(±1,±1,0,0)`, `(±1,0,±1,0)`, … for the six
coordinate pairs.) -/
theorem Qbar_side_lookup (g : Fin 4 → ZMod 2) (i j : Fin 4) (hij : i ≠ j) :
    ∃ S : Fin 24, ∀ k : Fin 4,
      sideNormal S k = (if k = i then signVec g i else 0) + (if k = j then signVec g j else 0) := by
  decide +revert

/-- **Lookup 2 (the truncation sign vectors).**  Every sign vector `(±1,±1,±1,±1)` occurs among the
24 truncation normals `truncNormal2 w` (namely for `w < 16`). -/
theorem Qbar_trunc_sign_lookup (g : Fin 4 → ZMod 2) :
    ∃ w : Fin 24, ∀ i : Fin 4, truncNormal2 w i = signVec g i := by
  decide +revert

/-- **Lookup 3 (the coordinate directions).**  For every coordinate `i` both normals `±2 e_i` occur
among the `truncNormal2` (namely for `w = 16, …, 23`). -/
theorem Qbar_trunc_e_lookup (i : Fin 4) (ε : ZMod 2) :
    ∃ w : Fin 24, ∀ k : Fin 4, truncNormal2 w k = (if k = i then 2 * Qbar_sgnZ ε else 0) := by
  decide +revert

/-! ### Reading the constraints as linear inequalities -/

theorem Qbar_side_sum_le (S : Fin 24) (y : E4) (h : 0 ≤ sideSlack S y) :
    (∑ i, (sideNormal S i : ℝ) * y i) ≤ 1 := by
  simp only [sideSlack] at h
  linarith

theorem Qbar_trunc_sum_le (w : Fin 24) (y : E4) (h : 0 ≤ truncSlack w y) :
    (∑ i, (truncNormal2 w i : ℝ) * y i) ≤ 8 / 5 := by
  simp only [truncSlack] at h
  linarith

/-- A two-point functional evaluated against a vector. -/
theorem Qbar_sum_two_point (i j : Fin 4) (h : i ≠ j) (c d : ℝ) (y : E4) :
    (∑ k : Fin 4, (((if k = i then c else 0) + (if k = j then d else 0)) * y k)) =
      c * y i + d * y j := by
  have hpoint : ∀ k : Fin 4, (((if k = i then c else 0) + (if k = j then d else 0)) * y k) =
      (if k = i then c * y k else 0) + (if k = j then d * y k else 0) := by
    intro k
    by_cases hki : k = i
    · subst hki; simp [h]
    · by_cases hkj : k = j
      · subst hkj; simp [hki]
      · simp [hki, hkj]
  rw [Finset.sum_congr rfl (fun k _ => hpoint k), Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

/-- A one-point functional evaluated against a vector. -/
theorem Qbar_sum_one_point (i : Fin 4) (c : ℝ) (y : E4) :
    (∑ k : Fin 4, ((if k = i then c else 0) * y k)) = c * y i := by
  have hpoint : ∀ k : Fin 4, ((if k = i then c else 0) * y k) =
      (if k = i then c * y k else 0) := by
    intro k
    by_cases hki : k = i <;> simp [hki]
  rw [Finset.sum_congr rfl (fun k _ => hpoint k), Finset.sum_ite_eq']
  simp

/-- The sign pattern of a point of `E4`: the bit is `0` where the coordinate is `≥ 0`. -/
def Qbar_signOfPoint (y : E4) : Fin 4 → ZMod 2 := fun i => if 0 ≤ y i then 0 else 1

/-- The sign vector of `Qbar_signOfPoint y` reproduces the absolute values of `y`. -/
theorem signVec_Qbar_signOfPoint (y : E4) (i : Fin 4) :
    (signVec (Qbar_signOfPoint y) i : ℝ) * y i = |y i| := by
  by_cases h : 0 ≤ y i
  · have hg : Qbar_signOfPoint y i = 0 := by simp [Qbar_signOfPoint, h]
    simp [signVec, hg, abs_of_nonneg h]
  · have hg : Qbar_signOfPoint y i = 1 := by simp [Qbar_signOfPoint, h]
    have hlt : y i < 0 := lt_of_not_ge h
    simp [signVec, hg, abs_of_neg hlt]

/-! ### The three numerical consequences of membership in `Q̄` -/

/-- Membership in `Q̄` bounds every coordinate by `4/5` (the truncation normals `±2e_i`). -/
theorem Qbar_abs_le (y : E4) (hy : y ∈ Qbar) (i : Fin 4) : |y i| ≤ 4 / 5 := by
  obtain ⟨w₁, h₁⟩ := Qbar_trunc_e_lookup i 0
  obtain ⟨w₂, h₂⟩ := Qbar_trunc_e_lookup i 1
  have hR₁ : ∀ k : Fin 4, (truncNormal2 w₁ k : ℝ) = if k = i then (2 : ℝ) else 0 := by
    intro k
    rw [show truncNormal2 w₁ k = (if k = i then (2 : ℤ) else 0) from by rw [h₁ k]; simp [Qbar_sgnZ]]
    push_cast
    ring
  have hR₂ : ∀ k : Fin 4, (truncNormal2 w₂ k : ℝ) = if k = i then (-2 : ℝ) else 0 := by
    intro k
    rw [show truncNormal2 w₂ k = (if k = i then (-2 : ℤ) else 0) from by rw [h₂ k]; simp [Qbar_sgnZ]]
    push_cast
    ring
  have e₁ : (∑ k, (truncNormal2 w₁ k : ℝ) * y k) = 2 * y i := by
    have hsum : (∑ k, (truncNormal2 w₁ k : ℝ) * y k) =
        ∑ k, ((if k = i then (2 : ℝ) else 0) * y k) :=
      Finset.sum_congr rfl fun k _ => by rw [hR₁ k]
    rw [hsum, Qbar_sum_one_point]
  have e₂ : (∑ k, (truncNormal2 w₂ k : ℝ) * y k) = -2 * y i := by
    have hsum : (∑ k, (truncNormal2 w₂ k : ℝ) * y k) =
        ∑ k, ((if k = i then (-2 : ℝ) else 0) * y k) :=
      Finset.sum_congr rfl fun k _ => by rw [hR₂ k]
    rw [hsum, Qbar_sum_one_point]
  have h₁' := Qbar_trunc_sum_le w₁ y (hy.2 w₁)
  have h₂' := Qbar_trunc_sum_le w₂ y (hy.2 w₂)
  rw [e₁] at h₁'
  rw [e₂] at h₂'
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Membership in `Q̄` bounds every sum of two coordinates by `1` (the side normals
`±e_i ± e_j`). -/
theorem Qbar_pair_le (y : E4) (hy : y ∈ Qbar) {i j : Fin 4} (hij : i ≠ j) :
    |y i| + |y j| ≤ 1 := by
  obtain ⟨S, hS⟩ := Qbar_side_lookup (Qbar_signOfPoint y) i j hij
  have hle : (∑ k, (sideNormal S k : ℝ) * y k) ≤ 1 := Qbar_side_sum_le S y (hy.1 S)
  have heq : (∑ k, (sideNormal S k : ℝ) * y k) =
      (signVec (Qbar_signOfPoint y) i : ℝ) * y i + (signVec (Qbar_signOfPoint y) j : ℝ) * y j := by
    have hsum : (∑ k, (sideNormal S k : ℝ) * y k) =
        ∑ k, (((if k = i then (signVec (Qbar_signOfPoint y) i : ℝ) else 0)
          + (if k = j then (signVec (Qbar_signOfPoint y) j : ℝ) else 0)) * y k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hSR : (sideNormal S k : ℝ) =
          (if k = i then (signVec (Qbar_signOfPoint y) i : ℝ) else 0)
            + (if k = j then (signVec (Qbar_signOfPoint y) j : ℝ) else 0) := by
        rw [hS k]
        push_cast
        ring
      rw [hSR]
    rw [hsum, Qbar_sum_two_point i j hij]
  rw [heq, signVec_Qbar_signOfPoint y i, signVec_Qbar_signOfPoint y j] at hle
  exact hle

/-- Membership in `Q̄` bounds the sum of the absolute values by `8/5` (the truncation normal
`(±1,±1,±1,±1)` matching the signs of `y`). -/
theorem Qbar_sum_abs_le (y : E4) (hy : y ∈ Qbar) : ∑ i, |y i| ≤ 8 / 5 := by
  obtain ⟨w, hw⟩ := Qbar_trunc_sign_lookup (Qbar_signOfPoint y)
  have hle : (∑ k, (truncNormal2 w k : ℝ) * y k) ≤ 8 / 5 := Qbar_trunc_sum_le w y (hy.2 w)
  have heq : (∑ k, (truncNormal2 w k : ℝ) * y k) = ∑ k, |y k| := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (truncNormal2 w k : ℝ) = (signVec (Qbar_signOfPoint y) k : ℝ) from by rw [hw k]]
    exact signVec_Qbar_signOfPoint y k
  rwa [heq] at hle

/-! ### The `ℓ²` bound -/

/-- **The numerical core.**  Four nonnegative numbers with pairwise sums `≤ 1`, each `≤ 4/5`, and
total `≤ 8/5` have sum of squares `< 1`.

If the largest entry is `≤ 1/2` then `∑ a_i² ≤ (1/2) ∑ a_i ≤ 4/5`.  Otherwise, for the index `k` of
the maximum `m > 1/2` the other three entries are each `≤ 1 - m`, so
`∑ a_i² ≤ m² + (1-m)(8/5 - m) ≤ 4/5` because `m² + (1-m)(8/5-m) - 4/5 = ((2m-1)(5m-4))/10 ≤ 0`
for `1/2 ≤ m ≤ 4/5`. -/
theorem Qbar_sum_sq_lt_one (a : Fin 4 → ℝ) (h0 : ∀ i, 0 ≤ a i) (h45 : ∀ i, a i ≤ 4 / 5)
    (hpair : ∀ i j, i ≠ j → a i + a j ≤ 1) (hsum : ∑ i, a i ≤ 8 / 5) :
    ∑ i, (a i) ^ 2 < 1 := by
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin 4)) a Finset.univ_nonempty
  have hm : ∀ i, a i ≤ a k := fun i => hk i (Finset.mem_univ i)
  set m := a k with hmk
  have hm45 : m ≤ 4 / 5 := h45 k
  rcases le_or_gt m (1 / 2) with hmle | hmgt
  · have hbound : ∑ i, (a i) ^ 2 ≤ (1 / 2) * ∑ i, a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hai : a i ≤ 1 / 2 := le_trans (hm i) hmle
      calc (a i) ^ 2 = a i * a i := sq (a i)
        _ ≤ (1 / 2) * a i := mul_le_mul_of_nonneg_right hai (h0 i)
    linarith
  · have herase_le : ∑ i ∈ Finset.univ.erase k, a i ≤ 8 / 5 - m := by
      have hsplit : ∑ i : Fin 4, a i = m + ∑ i ∈ Finset.univ.erase k, a i := by
        rw [hmk]
        exact (Finset.add_sum_erase _ a (Finset.mem_univ k)).symm
      linarith
    have hrest : ∀ i ∈ Finset.univ.erase k, a i ≤ 1 - m := by
      intro i hi
      have hik : i ≠ k := (Finset.mem_erase.mp hi).1
      have := hpair i k hik
      linarith
    have herase_sq : ∑ i ∈ Finset.univ.erase k, (a i) ^ 2 ≤
        (1 - m) * ∑ i ∈ Finset.univ.erase k, a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      calc (a i) ^ 2 = a i * a i := sq (a i)
        _ ≤ (1 - m) * a i := mul_le_mul_of_nonneg_right (hrest i hi) (h0 i)
    have hsq_le : ∑ i, (a i) ^ 2 ≤ m ^ 2 + (1 - m) * (8 / 5 - m) := by
      have hsplit : ∑ i : Fin 4, (a i) ^ 2 = m ^ 2 + ∑ i ∈ Finset.univ.erase k, (a i) ^ 2 := by
        rw [hmk]
        exact (Finset.add_sum_erase _ (fun i => (a i) ^ 2) (Finset.mem_univ k)).symm
      have h1m : 0 ≤ 1 - m := by linarith
      calc ∑ i, (a i) ^ 2 = m ^ 2 + ∑ i ∈ Finset.univ.erase k, (a i) ^ 2 := hsplit
        _ ≤ m ^ 2 + (1 - m) * ∑ i ∈ Finset.univ.erase k, a i := by linarith
        _ ≤ m ^ 2 + (1 - m) * (8 / 5 - m) := by
            have := mul_le_mul_of_nonneg_left herase_le h1m
            linarith
    have hfm : m ^ 2 + (1 - m) * (8 / 5 - m) ≤ 4 / 5 := by
      have h₁ : (0 : ℝ) ≤ 2 * m - 1 := by linarith
      have h₂ : 5 * m - 4 ≤ 0 := by linarith
      nlinarith [mul_nonpos_of_nonneg_of_nonpos h₁ h₂]
    linarith

/-- Every point of `Q̄` lies in the open unit ball. -/
theorem Qbar_subset_ball : Qbar ⊆ Work.HypModel.ball := by
  intro y hy
  have hsq : ∑ i : Fin 4, (y i) ^ 2 < 1 := by
    have h := Qbar_sum_sq_lt_one (fun i => |y i|) (fun i => abs_nonneg _)
      (fun i => Qbar_abs_le y hy i) (fun i j hij => Qbar_pair_le y hy hij) (Qbar_sum_abs_le y hy)
    simpa [sq_abs] using h
  have hnorm : ‖y‖ ^ 2 = ∑ i : Fin 4, (y i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  simp only [Work.HypModel.ball]
  have h2 : ‖y‖ ^ 2 < (1 : ℝ) ^ 2 := by rw [one_pow, hnorm]; exact hsq
  have := sq_lt_sq.mp h2
  simpa using this

/-! ### Closedness, convexity, nonemptiness -/

/-- `Q̄` is the intersection of its 48 half-space constraints. -/
theorem Qbar_eq_iInter :
    Qbar = (⋂ S : Fin 24, {y : E4 | 0 ≤ sideSlack S y}) ∩
      (⋂ w : Fin 24, {y : E4 | 0 ≤ truncSlack w y}) := by
  ext y
  simp [Qbar]

theorem isClosed_Qbar : IsClosed Qbar := by
  rw [Qbar_eq_iInter]
  refine IsClosed.inter (isClosed_iInter fun S => ?_) (isClosed_iInter fun w => ?_)
  · exact isClosed_le continuous_const (continuous_sideSlack S)
  · exact isClosed_le continuous_const (continuous_truncSlack w)

/-- The coordinates of a convex combination in `E4`. -/
theorem Qbar_E4_smul_add_apply (a b : ℝ) (y z : E4) (i : Fin 4) :
    (a • y + b • z) i = a * y i + b * z i := by
  simp

/-- `sideSlack S` is affine, hence `{y | 0 ≤ sideSlack S y}` is convex. -/
theorem sideSlack_affine (S : Fin 24) {a b : ℝ} (hab : a + b = 1) (y z : E4) :
    sideSlack S (a • y + b • z) = a * sideSlack S y + b * sideSlack S z := by
  have h : (∑ i, (sideNormal S i : ℝ) * (a • y + b • z) i) =
      a * (∑ i, (sideNormal S i : ℝ) * y i) + b * (∑ i, (sideNormal S i : ℝ) * z i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Qbar_E4_smul_add_apply]
    ring
  simp only [sideSlack, h]
  linarith

/-- `truncSlack w` is affine, hence `{y | 0 ≤ truncSlack w y}` is convex. -/
theorem truncSlack_affine (w : Fin 24) {a b : ℝ} (hab : a + b = 1) (y z : E4) :
    truncSlack w (a • y + b • z) = a * truncSlack w y + b * truncSlack w z := by
  have h : (∑ i, (truncNormal2 w i : ℝ) * (a • y + b • z) i) =
      a * (∑ i, (truncNormal2 w i : ℝ) * y i) + b * (∑ i, (truncNormal2 w i : ℝ) * z i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Qbar_E4_smul_add_apply]
    ring
  simp only [truncSlack, h]
  linarith

theorem convex_Qbar : Convex ℝ Qbar := by
  intro y hy z hz a b ha hb hab
  refine ⟨fun S => ?_, fun w => ?_⟩
  · rw [sideSlack_affine S hab]
    exact add_nonneg (mul_nonneg ha (hy.1 S)) (mul_nonneg hb (hz.1 S))
  · rw [truncSlack_affine w hab]
    exact add_nonneg (mul_nonneg ha (hy.2 w)) (mul_nonneg hb (hz.2 w))

theorem Qbar_nonempty : Qbar.Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨fun S => ?_, fun w => ?_⟩
  · simp [sideSlack]
  · simp only [truncSlack]
    norm_num

/-! ### The main statement -/

theorem Qbar_geometry : IsCompact Qbar ∧ Convex ℝ Qbar ∧ IsClosed Qbar ∧ Qbar.Nonempty ∧ Qbar ⊆ Work.HypModel.ball := by
  refine ⟨?_, convex_Qbar, isClosed_Qbar, Qbar_nonempty, Qbar_subset_ball⟩
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E4) 1) isClosed_Qbar
    fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_lt (Qbar_subset_ball hy)

end Work.FoldInst
