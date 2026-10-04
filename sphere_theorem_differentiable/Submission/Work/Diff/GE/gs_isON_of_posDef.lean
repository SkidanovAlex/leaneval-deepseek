import Mathlib
import Submission.Work.Diff.GE.frame_family_defs
import Submission.Work.Diff.GE.isONFrame_frameFamily

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Gram–Schmidt of a linearly independent family, for a positive definite form

The Gram–Schmidt recursion `Work.Diff.GE.gs` normalises, at each index `i`, the vector

`U i = gsU b κ (gs b κ) i = κ i - ∑_{j < i} b (κ i) (gs b κ j) • gs b κ j`.

The reduction of orthonormality to the non-vanishing of the `U i` is the abstract Gram–Schmidt
induction `gs_orthonormal` of `Submission/Work/Diff/GE/isONFrame_frameFamily.lean`.  What is added
here is the proof that `U i ≠ 0` as soon as `κ` is linearly independent: if `U i` vanished then
`κ i` would be a `b`-linear combination of the vectors `gs b κ j`, `j < i`, each of which lies in
the span of `κ 0, …, κ j` (this is `gs_mem_gsSpan`, an induction which uses nothing about `b`), so
`κ i` would lie in the span of `κ 0, …, κ i-1`, contradicting linear independence.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Work.Diff.GE

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The span of the vectors `κ j` with `j.val < m`. -/
private noncomputable def gsSpan {n : ℕ} (κ : Fin n → V) (m : ℕ) : Submodule ℝ V :=
  Submodule.span ℝ (κ '' {j : Fin n | j.val < m})

private theorem gsSpan_mono {n : ℕ} (κ : Fin n → V) {m m' : ℕ} (h : m ≤ m') :
    gsSpan κ m ≤ gsSpan κ m' := by
  refine Submodule.span_mono (Set.image_mono fun j hj => ?_)
  exact lt_of_lt_of_le hj h

/-- `κ i` lies in the span of `κ 0, …, κ i`. -/
private theorem mem_gsSpan_succ {n : ℕ} (κ : Fin n → V) (i : Fin n) :
    κ i ∈ gsSpan κ (i.val + 1) :=
  Submodule.subset_span ⟨i, by simp⟩

/-- Each Gram–Schmidt vector `gs b κ j` lies in the span of `κ 0, …, κ j`.  (Nothing about `b` is
used: only the shape of the recursion, since the coefficients in the recursion do not matter for
membership in a span.) -/
private theorem gs_mem_gsSpan {n : ℕ} (b : V → V → ℝ) (κ : Fin n → V) (j : Fin n) :
    gs b κ j ∈ gsSpan κ (j.val + 1) := by
  suffices key : ∀ m : ℕ, ∀ k : Fin n, k.val = m → gs b κ k ∈ gsSpan κ (k.val + 1) from
    key j.val j rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hk
    rw [gs_apply b κ k]
    refine Submodule.smul_mem _ _ ?_
    have hU : gsU b κ (gs b κ) k
        = κ k - ∑ j : Fin n,
            (if j.val < k.val then b (κ k) (gs b κ j) • gs b κ j else 0) := rfl
    rw [hU]
    refine Submodule.sub_mem _ (mem_gsSpan_succ κ k) ?_
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j.val < k.val
    · rw [if_pos hj]
      exact Submodule.smul_mem _ _ (gsSpan_mono κ (by omega) (ih j.val (by omega) j rfl))
    · rw [if_neg hj]
      exact Submodule.zero_mem _

/-- If `κ` is linearly independent, no pre-normalisation vector of the Gram–Schmidt recursion
vanishes. -/
private theorem gsU_ne_zero_of_linearIndependent {n : ℕ} (b : V → V → ℝ) (κ : Fin n → V)
    (hind : LinearIndependent ℝ κ) (i : Fin n) : gsU b κ (gs b κ) i ≠ 0 := by
  intro h0
  have hU : κ i - ∑ j : Fin n,
      (if j.val < i.val then b (κ i) (gs b κ j) • gs b κ j else 0) = 0 := h0
  have hmem : κ i ∈ gsSpan κ i.val := by
    rw [sub_eq_zero.mp hU]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j.val < i.val
    · rw [if_pos hj]
      exact Submodule.smul_mem _ _ (gsSpan_mono κ (by omega) (gs_mem_gsSpan b κ j))
    · rw [if_neg hj]
      exact Submodule.zero_mem _
  exact (hind.notMem_span_image (v := κ) (s := {j : Fin n | j.val < i.val}) (x := i)
    (by simp)) hmem

end Generic

/-- **Gram–Schmidt of a linearly independent family, for a positive definite symmetric bilinear
form, is orthonormal.**  With `b` symmetric and bilinear and positive definite, and `κ` linearly
independent, the Gram–Schmidt recursion `gs b κ` of `Work.Diff.GE` (defined by the explicit
recursion `gs b κ i = (√ (b (U i) (U i)))⁻¹ • U i`, `U i = κ i - ∑_{j<i} b (κ i) (E j) • E j`) is
`b`-orthonormal.  (Standard Gram–Schmidt induction; the point of the hypotheses is that
`b (U i) (U i) > 0`, which needs both positivity and linear independence of `κ`.) -/
theorem gs_isON_of_posDef {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : V → V → ℝ) (κ : Fin n → V)
    (hadd₁ : ∀ (u v w : V), b (u + v) w = b u w + b v w)
    (hsmul₁ : ∀ (c : ℝ) (u v : V), b (c • u) v = c * b u v)
    (hadd₂ : ∀ (u v w : V), b u (v + w) = b u v + b u w)
    (hsmul₂ : ∀ (c : ℝ) (u v : V), b u (c • v) = c * b u v)
    (hsymm : ∀ (u v : V), b u v = b v u)
    (hpos : ∀ (u : V), u ≠ 0 → 0 < b u u)
    (hind : LinearIndependent ℝ κ) :
    ∀ i j : Fin n, b (Work.Diff.GE.gs b κ i) (Work.Diff.GE.gs b κ j) = if i = j then 1 else 0 :=
  gs_orthonormal b κ hadd₁ hsmul₁ hsymm hpos
    fun i => gsU_ne_zero_of_linearIndependent b κ hind i

end Work.Diff.GE
