import Mathlib
import Submission.Work.BourgainPlan.Maximal.minor_arc_lp
import Submission.Work.BourgainPlan.Maximal.ellp_interpolation

/-!
# The `ℓ²`-membership of the `ℤ`-average `discAvgZC`

`discAvgZC P N g m = N⁻¹ ∑_{i<N} g (m + P i)` is a *convex combination of shifts* of `g` with
weights `N⁻¹`.  Hence it is an `ℓ²`-contraction: `‖A_N g‖_{ℓ²(ℤ)} ≤ ‖g‖_{ℓ²(ℤ)}`, so
`Memℓp g 2 ⟹ Memℓp (discAvgZC P N g) 2`.

The `Memℓp` here is Mathlib's ℓᵖ-space predicate of `Mathlib.Analysis.Normed.Lp.lpSpace`
(`Memℓp f 2 ↔ Summable (fun i ↦ ‖f i‖ ^ 2)`), which is the predicate under which the
Ionescu–Wainger modules state their `ℓ²(ℤ)` hypotheses.  The proof below is the elementary
`ℓ²` bound: the weighted Cauchy–Schwarz / `N⁻¹`-mass estimate
`(∑_i N⁻¹ ‖g (m + P i)‖)² ≤ N · ∑_i (N⁻¹ ‖g (m + P i)‖)² ≤ ∑_i N⁻¹ ‖g (m + P i)‖²`
(the last step using `N · N⁻¹ ≤ 1`), summed over `m` with the translation invariance of the
summability of `m ↦ ‖g (m + a)‖²` on `ℤ`.
-/

open Finset MeasureTheory

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

noncomputable section

/-- A finite sum of summable `ℤ`-indexed real sequences is summable. -/
lemma summable_finset_sum_int {ι : Type*} (s : Finset ι) {f : ι → ℤ → ℝ}
    (h : ∀ i ∈ s, Summable (f i)) : Summable (fun m => ∑ i ∈ s, f i m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
      have hi : Summable (f i) := h i (Finset.mem_insert_self i s)
      have hs : Summable (fun m => ∑ j ∈ s, f j m) :=
        ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      simpa [Finset.sum_insert his] using hi.add hs

/-- **The `ℤ`-average `A_N = discAvgZC P N` maps `ℓ²(ℤ)` into itself.**  The average
`N⁻¹ ∑_{i<N} g (m + P i)` is a convex combination of shifts of `g` (the weights `N⁻¹` sum to
`≤ 1`), so it is an `ℓ²`-contraction. -/
theorem memlp_discAvgZC (P : Polynomial ℤ) (N : ℕ) {g : ℤ → ℂ} (hg : Memℓp g 2) :
    Memℓp (Work.BourgainPlan.Maximal.discAvgZC P N g) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)] at hg ⊢
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at hg ⊢
  -- the weight `w = N⁻¹`, with `0 ≤ w` and `w * N ≤ 1`
  set w : ℝ := (N : ℝ)⁻¹ with hw
  have hw0 : 0 ≤ w := by positivity
  have hwN : w * (N : ℝ) ≤ 1 := by
    rcases eq_or_ne N 0 with hN | hN
    · subst hN; simp [hw]
    · simp [hw, inv_mul_cancel₀ (by exact_mod_cast hN : (N : ℝ) ≠ 0)]
  -- the pointwise triangle-inequality bound
  have hsum : ∀ m : ℤ, ‖discAvgZC P N g m‖
      ≤ w * ∑ i ∈ Finset.range N, ‖g (m + P.eval (i : ℤ))‖ := by
    intro m
    unfold discAvgZC
    rw [norm_mul, show ‖((N : ℂ))⁻¹‖ = w from by simp [hw, norm_inv]]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw0
  -- the dominating sequence is summable (a finite sum of shifts of the square-summable `g`)
  have hb : Summable (fun m : ℤ =>
      ∑ i ∈ Finset.range N, w * ‖g (m + P.eval (i : ℤ))‖ ^ 2) := by
    refine summable_finset_sum_int _ fun i _ => ?_
    refine Summable.mul_left w ?_
    simpa only [Function.comp_def] using hg.comp_injective (add_left_injective (P.eval (i : ℤ)))
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hb
  -- Cauchy–Schwarz with the mass bound `∑_{i<N} w = N · w ≤ 1`
  calc ‖discAvgZC P N g m‖ ^ 2
      ≤ (w * ∑ i ∈ Finset.range N, ‖g (m + P.eval (i : ℤ))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hsum m) 2
    _ = w ^ 2 * (∑ i ∈ Finset.range N, ‖g (m + P.eval (i : ℤ))‖) ^ 2 := by ring
    _ ≤ w ^ 2 * ((N : ℝ) * ∑ i ∈ Finset.range N, ‖g (m + P.eval (i : ℤ))‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range N)
          (f := fun i => ‖g (m + P.eval (i : ℤ))‖)
    _ = (w * (N : ℝ)) * (w * ∑ i ∈ Finset.range N, ‖g (m + P.eval (i : ℤ))‖ ^ 2) := by ring
    _ ≤ 1 * (w * ∑ i ∈ Finset.range N, ‖g (m + P.eval (i : ℤ))‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hwN (by positivity)
    _ = ∑ i ∈ Finset.range N, w * ‖g (m + P.eval (i : ℤ))‖ ^ 2 := by
        rw [one_mul, Finset.mul_sum]

end

end Work.BourgainPlan.Maximal
