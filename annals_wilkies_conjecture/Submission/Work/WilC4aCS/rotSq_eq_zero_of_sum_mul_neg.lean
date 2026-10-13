import Mathlib
import Submission.Work.WilC4aCS.Defs

namespace Work.WilC4aCS

/-- The linear functional `v ↦ ∑ i, x i * v i`, i.e. `v ↦ ⟨x, v⟩`.

It is the direction of the constraint whose one-sided negativity is assumed in
`rotSq_eq_zero_of_sum_mul_neg`.  Packing it as a `LinearMap` makes the linear bookkeeping
(`(∑ i, x i * (v i - t * x i)) = (∑ i, x i * v i) - t * (∑ i, x i * x i)`) automatic. -/
def sumMulLM {m : ℕ} (x : Fin m → ℝ) : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, x i * v i
  map_add' u v := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- `sumMulLM x` evaluated at a standard basis vector. -/
lemma sumMulLM_single {m : ℕ} (x : Fin m → ℝ) (b : Fin m) :
    sumMulLM x (Pi.single b 1) = x b := by
  simp [sumMulLM, Pi.single_apply]

/-- If the one-sided derivative `∂_v ψ(x)` is `≤ 0` on the whole open half-space
`{v | ⟨x,v⟩ < 0}`, then `∇ψ(x)` is parallel to `x` (including the case `∇ψ(x) = 0`), hence the
radial-orthogonality defect `rotSq ψ x` vanishes.

The mathematical content is that a linear functional which is `≤ 0` on an open half-space is `≤ 0`
on its closure, hence vanishes on the boundary hyperplane `{⟨x,v⟩ = 0}`; so `ker ⟨x,·⟩ ⊆ ker dψ`,
which says exactly that `rotTerm ψ x a b = 0` for all `a`, `b`. -/
theorem rotSq_eq_zero_of_sum_mul_neg {m : ℕ} (ψ : (Fin m → ℝ) → ℝ) {x : Fin m → ℝ}
    (h : ∀ v : Fin m → ℝ, (∑ i, x i * v i) < 0 → fderiv ℝ ψ x v ≤ 0) :
    Work.WilC4aCS.rotSq ψ x = 0 := by
  by_cases hx : x = 0
  · -- `x = 0`: the hypothesis is vacuous and every term of `rotSq` carries a factor `x _ = 0`.
    subst hx
    simp [rotSq]
  · -- `x ≠ 0`: `⟨x,·⟩` is a nonzero functional with positive value at `x` itself.
    have hSx : 0 < sumMulLM x x := by
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hx (funext fun i => hcon i)
      have hxx : sumMulLM x x = ∑ i, x i * x i := rfl
      rw [hxx]
      refine Finset.sum_pos' (fun i _ => mul_self_nonneg (x i)) ⟨i, Finset.mem_univ i, ?_⟩
      exact mul_self_pos.mpr hi
    -- Step 1: `dψ` is `≤ 0` on the *closed* half-space `{⟨x,·⟩ ≤ 0}`.
    -- Move any such `v` strictly into the open half-space along `v - t·x` and let `t → 0`.
    have key : ∀ v : Fin m → ℝ, sumMulLM x v ≤ 0 → fderiv ℝ ψ x v ≤ 0 := by
      intro v hv
      by_contra hcon
      rw [not_le] at hcon
      set t : ℝ := fderiv ℝ ψ x v / (2 * (|fderiv ℝ ψ x x| + 1)) with ht
      have ht0 : 0 < t := by
        rw [ht]; exact div_pos hcon (by positivity)
      have ht_eq : t * (2 * (|fderiv ℝ ψ x x| + 1)) = fderiv ℝ ψ x v := by
        rw [ht]; field_simp
      have ht_lt : t * |fderiv ℝ ψ x x| < fderiv ℝ ψ x v := by
        nlinarith [abs_nonneg (fderiv ℝ ψ x x)]
      have hvt : sumMulLM x (v - t • x) < 0 := by
        rw [map_sub, map_smul, smul_eq_mul]
        nlinarith
      have hL := h (v - t • x) hvt
      rw [map_sub, map_smul, smul_eq_mul] at hL
      have h2 : t * fderiv ℝ ψ x x ≤ t * |fderiv ℝ ψ x x| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (le_of_lt ht0)
      linarith
    -- Step 2: hence `dψ` vanishes on `ker ⟨x,·⟩`, since `v` and `-v` both lie in the closed
    -- half-space when `⟨x,v⟩ = 0`.
    have key0 : ∀ v : Fin m → ℝ, sumMulLM x v = 0 → fderiv ℝ ψ x v = 0 := by
      intro v hv
      have h1 : fderiv ℝ ψ x v ≤ 0 := key v (le_of_eq hv)
      have h2 : fderiv ℝ ψ x (-v) ≤ 0 := key (-v) (by rw [map_neg]; simp [hv])
      rw [map_neg] at h2
      linarith
    -- Step 3: `x a · e_b - x b · e_a` lies in that kernel, and its derivative is `rotTerm`.
    have hT : ∀ a b : Fin m, rotTerm ψ x a b = 0 := by
      intro a b
      have hv0 : sumMulLM x (x a • Pi.single b 1 - x b • Pi.single a 1) = 0 := by
        rw [map_sub, map_smul, map_smul, sumMulLM_single, sumMulLM_single, smul_eq_mul,
          smul_eq_mul]
        ring
      have hL0 := key0 _ hv0
      have hexp : fderiv ℝ ψ x (x a • Pi.single b 1 - x b • Pi.single a 1)
          = x a * fderiv ℝ ψ x (Pi.single b 1) - x b * fderiv ℝ ψ x (Pi.single a 1) := by
        rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      change x a * fderiv ℝ ψ x (Pi.single b 1) - x b * fderiv ℝ ψ x (Pi.single a 1) = 0
      linarith [hL0, hexp]
    rw [rotSq_eq_sum]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    rw [hT p.1 p.2]
    norm_num

end Work.WilC4aCS
