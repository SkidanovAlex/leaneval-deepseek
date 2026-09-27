import Mathlib
import Submission.Mostow.GeodDefs

/-! Guidance from the project lead (the requester): the `k = 1` geodesic stratum design
(L1–L12).  This file proves **L9 `dirichletBox`**, the pure combinatorial Dirichlet
pigeonhole on the torus `(ℝ/2πℤ)^r` used in step G of the design.

**L9 dirichletBox** [certain now, pure combinatorics]

```
∀ (A : AddSubgroup (Fin r → AddCircle (2*π))) [Finite A] ψ (α : Fin r → ℝ) J,
 (∀ i, 0 < α i ∧ α i ≤ 2*π) → (∀ a ∈ A, (∀ i, ‖a i‖ < α i) → a = 0) →
 ∏ i, ⌈2*π / α i⌉₊ < (J+1) * Nat.card A → ∃ j, 1 ≤ j ∧ j ≤ J ∧ ∃ a ∈ A, ∀ i, ‖j • ψ i + a i‖ < α i
```
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- The additive circle of period `2 * π` carries the canonical `Fact` positivity instance
(needed by `AddCircle.equivIco`). -/
instance dirichletBox_twoPiPos : Fact (0 < 2 * Real.pi) := Fact.mk Real.two_pi_pos

/-- The representative in `[0, 2π)` of a point of the additive circle of period `2π`. -/
noncomputable def circleRep (x : AddCircle (2 * Real.pi)) : ℝ :=
  (AddCircle.equivIco (2 * Real.pi) 0 x : ℝ)

lemma circleRep_mem (x : AddCircle (2 * Real.pi)) : circleRep x ∈ Set.Ico 0 (2 * Real.pi) := by
  rw [circleRep]
  simpa using (AddCircle.equivIco (2 * Real.pi) 0 x).2

lemma circleRep_coe (x : AddCircle (2 * Real.pi)) : (circleRep x : AddCircle (2 * Real.pi)) = x := by
  rw [circleRep]
  simp

/-- The index of the `α`-box of the unit (period `2π`) circle that contains `x`: the integers
`k` with `circleRep x ∈ [k α, (k+1) α)`.  There are at most `⌈2π/α⌉₊` of them. -/
noncomputable def boxIdx {r : ℕ} (α : Fin r → ℝ) (hα : ∀ i, 0 < α i)
    (i : Fin r) (x : AddCircle (2 * Real.pi)) : Fin ⌈2 * Real.pi / α i⌉₊ :=
  ⟨⌊circleRep x / α i⌋₊, by
    rw [Nat.floor_lt (div_nonneg (circleRep_mem x).1 (le_of_lt (hα i)))]
    exact lt_of_lt_of_le (div_lt_div_of_pos_right (circleRep_mem x).2 (hα i)) (Nat.le_ceil _)⟩

/-- Two points of the circle lying in the same `α`-box are within `α` of each other. -/
lemma boxIdx_eq_imp {r : ℕ} (α : Fin r → ℝ) (hα : ∀ i, 0 < α i) (i : Fin r)
    {x y : AddCircle (2 * Real.pi)} (h : boxIdx α hα i x = boxIdx α hα i y) :
    ‖x - y‖ < α i := by
  have hval : ⌊circleRep x / α i⌋₊ = ⌊circleRep y / α i⌋₊ := by
    have := congrArg Fin.val h; simpa [boxIdx] using this
  have hx0 : 0 ≤ circleRep x / α i := div_nonneg (circleRep_mem x).1 (le_of_lt (hα i))
  have hy0 : 0 ≤ circleRep y / α i := div_nonneg (circleRep_mem y).1 (le_of_lt (hα i))
  have habs : |circleRep x / α i - circleRep y / α i| < 1 := by
    have h1 : (⌊circleRep y / α i⌋₊ : ℝ) ≤ circleRep x / α i := by
      rw [← hval]; exact Nat.floor_le hx0
    have h2 : circleRep x / α i < (⌊circleRep y / α i⌋₊ : ℝ) + 1 := by
      rw [← hval]; exact Nat.lt_floor_add_one _
    have h3 : (⌊circleRep y / α i⌋₊ : ℝ) ≤ circleRep y / α i := Nat.floor_le hy0
    have h4 : circleRep y / α i < (⌊circleRep y / α i⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [abs_lt]; constructor <;> linarith
  have hdiff : circleRep x - circleRep y = α i * (circleRep x / α i - circleRep y / α i) := by
    rw [div_sub_div_same, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt (hα i))]
  have hxy : ‖x - y‖ ≤ |circleRep x - circleRep y| := by
    have h1 : ((circleRep x - circleRep y : ℝ) : AddCircle (2 * Real.pi)) = x - y := by
      simp [circleRep_coe]
    rw [← h1]; exact QuotientAddGroup.norm_mk_le_norm
  calc ‖x - y‖ ≤ |circleRep x - circleRep y| := hxy
    _ = α i * |circleRep x / α i - circleRep y / α i| := by rw [hdiff, abs_mul, abs_of_pos (hα i)]
    _ < α i := mul_lt_of_lt_one_right (hα i) habs

/-- Elementary algebra of natural-number multiples on the circle. -/
private lemma smul_sub_smul {r : ℕ} (ψ b d : Fin r → AddCircle (2 * Real.pi))
    {j1 j2 : ℕ} (h : j2 ≤ j1) (i : Fin r) :
    (j1 • ψ i + b i) - (j2 • ψ i + d i) = (j1 - j2) • ψ i + (b i - d i) := by
  have hsplit : (j1 - j2) • ψ i + j2 • ψ i = j1 • ψ i := by
    rw [← add_nsmul, Nat.sub_add_cancel h]
  rw [← hsplit]
  abel

/-- **Dirichlet box counting** (L9 of the `k = 1` geodesic stratum design).

Let `A` be a finite additive subgroup of the torus `(ℝ/2πℤ)^r` with no non-zero element all of
whose coordinates are `< α i`, and let `ψ` be a point of the torus.  If the number
`∏ i, ⌈2π / α i⌉₊` of `α`-boxes is strictly smaller than `(J+1) * |A|`, then one of the points
`j • ψ + a`, `1 ≤ j ≤ J`, `a ∈ A`, has all coordinates of norm `< α i`.

This is the pigeonhole used in step G of the design: the `(J+1)·|A|` points
`j • ψ + a` are put in the `∏ ⌈2π/α i⌉₊` boxes; a collision with `j = j'` would produce a
non-zero element of `A` with all coordinates `< α i`, so a collision has `j ≠ j'`, and its
difference is the required point. -/
theorem dirichletBox (r : ℕ) (A : AddSubgroup (Fin r → AddCircle (2 * Real.pi))) [Finite A]
    (ψ : Fin r → AddCircle (2 * Real.pi)) (α : Fin r → ℝ) (J : ℕ)
    (hα : ∀ i, 0 < α i ∧ α i ≤ 2 * Real.pi)
    (hsep : ∀ a ∈ A, (∀ i, ‖a i‖ < α i) → a = 0)
    (hcount : ∏ i, ⌈2 * Real.pi / α i⌉₊ < (J + 1) * Nat.card A) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ J ∧ ∃ a ∈ A, ∀ i, ‖j • ψ i + a i‖ < α i := by
  classical
  have hAfin : Fintype A := Fintype.ofFinite A
  have hα0 : ∀ i, 0 < α i := fun i => (hα i).1
  -- the box map on the `(J+1) * |A|` points `j • ψ + a`
  let f : Fin (J + 1) × A → ((i : Fin r) → Fin ⌈2 * Real.pi / α i⌉₊) :=
    fun p i => boxIdx α hα0 i ((p.1 : ℕ) • ψ i + (p.2 : Fin r → AddCircle (2 * Real.pi)) i)
  have hcard : Fintype.card ((i : Fin r) → Fin ⌈2 * Real.pi / α i⌉₊)
      < Fintype.card (Fin (J + 1) × A) := by
    have h := hcount
    simp only [Fintype.card_pi, Fintype.card_fin, Fintype.card_prod, Nat.card_eq_fintype_card] at h ⊢
    exact h
  obtain ⟨p, q, hpq, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have heqi : ∀ i, boxIdx α hα0 i ((p.1 : ℕ) • ψ i + (p.2 : Fin r → AddCircle (2 * Real.pi)) i)
      = boxIdx α hα0 i ((q.1 : ℕ) • ψ i + (q.2 : Fin r → AddCircle (2 * Real.pi)) i) :=
    fun i => by simpa [f] using congrFun heq i
  by_cases hjj : p.1 = q.1
  · -- same `j`: the two points differ by a non-zero element of `A` of small norm
    exfalso
    have hcoord : ∀ i, ‖(p.2 : Fin r → AddCircle (2 * Real.pi)) i
        - (q.2 : Fin r → AddCircle (2 * Real.pi)) i‖ < α i := by
      intro i
      have hb := boxIdx_eq_imp α hα0 i (heqi i)
      simpa [hjj] using hb
    have hmem : ((p.2 : Fin r → AddCircle (2 * Real.pi))
        - (q.2 : Fin r → AddCircle (2 * Real.pi))) ∈ A := A.sub_mem p.2.2 q.2.2
    have hzero : ((p.2 : Fin r → AddCircle (2 * Real.pi))
        - (q.2 : Fin r → AddCircle (2 * Real.pi))) = 0 :=
      hsep _ hmem (by intro i; simpa using hcoord i)
    exact hpq (Prod.ext hjj (Subtype.ext (sub_eq_zero.mp hzero)))
  · rcases lt_or_gt_of_ne hjj with hlt | hgt
    · -- `p.1 < q.1`: the difference `(q.1 - p.1) • ψ + (q.2 - p.2)` is the required point
      have hval_lt : p.1.val < q.1.val := hlt
      refine ⟨q.1.val - p.1.val, ?_, ?_, (q.2 : Fin r → AddCircle (2 * Real.pi))
        - (p.2 : Fin r → AddCircle (2 * Real.pi)), A.sub_mem q.2.2 p.2.2, ?_⟩
      · have := p.1.isLt; omega
      · have := q.1.isLt; omega
      · intro i
        have hb := boxIdx_eq_imp α hα0 i (heqi i)
        have hX : (q.1.val • ψ i + (q.2 : Fin r → AddCircle (2 * Real.pi)) i)
            - (p.1.val • ψ i + (p.2 : Fin r → AddCircle (2 * Real.pi)) i)
            = (q.1.val - p.1.val) • ψ i
              + ((q.2 : Fin r → AddCircle (2 * Real.pi)) i - (p.2 : Fin r → AddCircle (2 * Real.pi)) i) :=
          smul_sub_smul ψ _ _ (le_of_lt hval_lt) i
        calc ‖(q.1.val - p.1.val) • ψ i
              + ((q.2 : Fin r → AddCircle (2 * Real.pi)) - (p.2 : Fin r → AddCircle (2 * Real.pi))) i‖
            = ‖(q.1.val • ψ i + (q.2 : Fin r → AddCircle (2 * Real.pi)) i)
                - (p.1.val • ψ i + (p.2 : Fin r → AddCircle (2 * Real.pi)) i)‖ := by
              rw [hX, Pi.sub_apply]
          _ = ‖(p.1.val • ψ i + (p.2 : Fin r → AddCircle (2 * Real.pi)) i)
                - (q.1.val • ψ i + (q.2 : Fin r → AddCircle (2 * Real.pi)) i)‖ := norm_sub_rev _ _
          _ < α i := hb
    · -- `q.1 < p.1`: symmetric
      have hval_lt : q.1.val < p.1.val := hgt
      refine ⟨p.1.val - q.1.val, ?_, ?_, (p.2 : Fin r → AddCircle (2 * Real.pi))
        - (q.2 : Fin r → AddCircle (2 * Real.pi)), A.sub_mem p.2.2 q.2.2, ?_⟩
      · have := q.1.isLt; omega
      · have := p.1.isLt; omega
      · intro i
        have hb := boxIdx_eq_imp α hα0 i (heqi i)
        have hX : (p.1.val • ψ i + (p.2 : Fin r → AddCircle (2 * Real.pi)) i)
            - (q.1.val • ψ i + (q.2 : Fin r → AddCircle (2 * Real.pi)) i)
            = (p.1.val - q.1.val) • ψ i
              + ((p.2 : Fin r → AddCircle (2 * Real.pi)) i - (q.2 : Fin r → AddCircle (2 * Real.pi)) i) :=
          smul_sub_smul ψ _ _ (le_of_lt hval_lt) i
        calc ‖(p.1.val - q.1.val) • ψ i
              + ((p.2 : Fin r → AddCircle (2 * Real.pi)) - (q.2 : Fin r → AddCircle (2 * Real.pi))) i‖
            = ‖(p.1.val • ψ i + (p.2 : Fin r → AddCircle (2 * Real.pi)) i)
                - (q.1.val • ψ i + (q.2 : Fin r → AddCircle (2 * Real.pi)) i)‖ := by
              rw [hX, Pi.sub_apply]
          _ < α i := hb

end Work.Mostow
