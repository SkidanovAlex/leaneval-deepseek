import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.tsum_sq_pow_le_sunflower

/-!
# The layer-wise sunflower bound, summed over layers

This file assembles the `k`-layer square-function sunflower bound from the single-layer bound
`Work.BourgainPlan.IonescuWainger.tsum_sq_pow_le_sunflower` by splitting the `k`-layer square
function into its `k'`-layers (`0 ≤ k' ≤ k`) and applying the power-mean inequality across the
`k + 1` layers.

The three elementary ingredients are isolated as standalone lemmas:

* `sum_filter_card_le_eq_sum_layers` — the layer decomposition of a sum over the sets of
  cardinality at most `k` into the sums over cardinality exactly `k'`, `k' ∈ {0, …, k}`;
* `pow_sum_le_card_pow_mul_sum_pow` — the power-mean inequality
  `(Σ_{i ∈ s} u_i)^r ≤ (#s)^{r-1} Σ_{i ∈ s} u_i^r` for `r ≥ 1` and `u_i ≥ 0`;
* `tsum_pow_sum_le_mul_sum_tsum_pow` — the `ℓ²(ℤ)`-summed form of the previous inequality,
  including the interchange of the `ℤ`-sum with the finite layer sum (using summability of the
  layers).
-/

open Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

/-- **Layer decomposition.** A sum over all subsets of a finite type whose cardinality is at most
`k` splits into the sums over the individual layers of cardinality exactly `k'`, for
`k' ∈ {0, 1, …, k}`. -/
lemma sum_filter_card_le_eq_sum_layers {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (g : Finset ι → ℝ) :
    ∑ A ∈ (Finset.univ : Finset (Finset ι)).filter (fun A => A.card ≤ k), g A
      = ∑ k' ∈ Finset.range (k + 1), ∑ A ∈ (Finset.univ : Finset (Finset ι)).filter
          (fun A => A.card = k'), g A := by
  rw [Finset.sum_filter]
  have h2 : (∑ k' ∈ Finset.range (k + 1), ∑ A ∈ (Finset.univ : Finset (Finset ι)).filter
        (fun A => A.card = k'), g A)
      = ∑ k' ∈ Finset.range (k + 1), ∑ A ∈ (Finset.univ : Finset (Finset ι)),
          (if A.card = k' then g A else 0) := by
    refine Finset.sum_congr rfl (fun k' _ => ?_)
    rw [Finset.sum_filter]
  rw [h2, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- **Power mean (a.k.a. the convexity inequality for power functions).** For `r ≥ 1` and
nonnegative `u`, the `r`-th power of the sum is bounded by `(#s)^{r-1}` times the sum of the
`r`-th powers. -/
lemma pow_sum_le_card_pow_mul_sum_pow {α : Type*} (s : Finset α) {r : ℕ} (hr : 1 ≤ r)
    (u : α → ℝ) (hu : ∀ i ∈ s, 0 ≤ u i) :
    (∑ i ∈ s, u i) ^ r ≤ (s.card : ℝ) ^ (r - 1) * ∑ i ∈ s, (u i) ^ r := by
  have hp : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s (f := u) hp hu
  simp_rw [Real.rpow_natCast] at h
  have hcast : ((r : ℝ) - 1) = ((r - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hr]; ring
  rw [hcast, Real.rpow_natCast] at h
  exact h

/-- **The layer-wise power-mean bound after summing over `ℤ`.** For a finite family of summable
nonnegative functions `u i : ℤ → ℝ`, the `ℓ¹(ℤ)`-sum of the `r`-th power of the layer sum is
bounded by `(#s)^{r-1}` times the sum over layers of the `ℓ¹(ℤ)`-sums of the `r`-th powers. -/
lemma tsum_pow_sum_le_mul_sum_tsum_pow {β : Type*} (s : Finset β) {r : ℕ} (hr : 1 ≤ r)
    {u : β → ℤ → ℝ} (hu : ∀ i ∈ s, ∀ x, 0 ≤ u i x)
    (hsum : ∀ i ∈ s, Summable (fun x => u i x)) :
    ∑' x : ℤ, (∑ i ∈ s, u i x) ^ r ≤ (s.card : ℝ) ^ (r - 1) * ∑ i ∈ s, ∑' x : ℤ, (u i x) ^ r := by
  have hpow : ∀ i ∈ s, Summable (fun x => (u i x) ^ r) :=
    fun i hi => summable_pow_of_summable (hsum i hi) (fun x => hu i hi x) hr
  have hL : Summable (fun x => (∑ i ∈ s, u i x) ^ r) :=
    summable_pow_of_summable (summable_finset_sum hsum)
      (fun x => Finset.sum_nonneg (fun i hi => hu i hi x)) hr
  have hR : Summable (fun x => ∑ i ∈ s, (u i x) ^ r) := summable_finset_sum hpow
  calc ∑' x : ℤ, (∑ i ∈ s, u i x) ^ r
      ≤ ∑' x : ℤ, (s.card : ℝ) ^ (r - 1) * (∑ i ∈ s, (u i x) ^ r) := by
        refine Summable.tsum_le_tsum
          (fun x => pow_sum_le_card_pow_mul_sum_pow s hr (fun i => u i x)
            (fun i hi => hu i hi x)) hL (hR.mul_left _)
    _ = (s.card : ℝ) ^ (r - 1) * ∑' x : ℤ, (∑ i ∈ s, (u i x) ^ r) := by rw [tsum_mul_left]
    _ = (s.card : ℝ) ^ (r - 1) * ∑ i ∈ s, ∑' x : ℤ, (u i x) ^ r := by
        rw [Summable.tsum_finsetSum hpow]

/-- **The layer-wise sunflower bound, summed over layers.**  Splitting the `k`-layer square
function into its `k'`-layers (`k' ≤ k`) and applying Tao's sunflower bound
(`tsum_sq_pow_le_sunflower`) to each layer gives

`Σ_x (Σ_{|A| ≤ k} ‖f_A(x)‖²)^r ≤ (k+1)^{r-1} (4M)^r Σ_{k' ≤ k} Σ_{A₀, |A₀| ≤ k'} Σ^{**}_A Σ_x ∏_i ‖f_{A₀∪A_i}(x)‖²`,

where `Σ^{**}` runs over tuples of pairwise disjoint `A_i` with `A_i ⊆ α ∖ A₀`, `|A_i| = k' - |A₀|`
(the sunflower condition), and `M` is the Erdős–Rado sunflower threshold.  The first factor is the
power-mean inequality `(Σ_{i≤k+1} u_i)^r ≤ (k+1)^{r-1} Σ_i u_i^r` applied to the `k+1` layers. -/
theorem layer_sunflower_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {k r M : ℕ} (hr : 2 ≤ r)
    (hM : 2 ≤ M)
    (hsun : ∀ T : Finset (Finset ι), (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
      ∃ A : Fin r → Finset ι, (∀ i, A i ∈ T) ∧ Function.Injective A ∧ IsSunflower A)
    (f : Finset ι → ℤ → ℂ) (hf : ∀ A, Memℓp (f A) 2) :
    ∑' x : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset ι)).filter (fun A => A.card ≤ k), ‖f A x‖ ^ 2) ^ r
      ≤ (k + 1 : ℝ) ^ (r - 1) * ∑ k' ∈ Finset.range (k + 1),
          (4 * M : ℝ) ^ r *
            ∑ A₀ ∈ (Finset.univ : Finset (Finset ι)).filter (fun A => A.card ≤ k'),
              ∑ A : Fin r → Finset ι,
                (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k' - A₀.card) ∧
                    (∀ i j, i ≠ j → Disjoint (A i) (A j))
                 then ∑' x : ℤ, ∏ i, ‖f (A₀ ∪ A i) x‖ ^ 2 else 0) := by
  classical
  have hr1 : 1 ≤ r := by omega
  -- Step 1: layer decomposition + power mean + interchange with the `ℤ`-sum.
  have hkey : (∑' x : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset ι)).filter
        (fun A => A.card ≤ k), ‖f A x‖ ^ 2) ^ r)
      ≤ (k + 1 : ℝ) ^ (r - 1) *
          ∑ k' ∈ Finset.range (k + 1), ∑' x : ℤ,
            (∑ A ∈ (Finset.univ : Finset (Finset ι)).filter (fun A => A.card = k'),
              ‖f A x‖ ^ 2) ^ r := by
    rw [show (∑' x : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset ι)).filter
            (fun A => A.card ≤ k), ‖f A x‖ ^ 2) ^ r)
          = ∑' x : ℤ, (∑ k' ∈ Finset.range (k + 1),
              ∑ A ∈ (Finset.univ : Finset (Finset ι)).filter (fun A => A.card = k'),
                ‖f A x‖ ^ 2) ^ r from
        tsum_congr (fun x => by rw [sum_filter_card_le_eq_sum_layers])]
    have h := tsum_pow_sum_le_mul_sum_tsum_pow (s := (Finset.range (k + 1))) (r := r) hr1
      (u := fun k' x => ∑ A ∈ (Finset.univ : Finset (Finset ι)).filter (fun A => A.card = k'),
        ‖f A x‖ ^ 2)
      (fun k' _ x => Finset.sum_nonneg (fun A _ => sq_nonneg _))
      (fun k' _ => summable_finset_sum (fun A _ => summable_norm_sq_of_memℓp (hf A)))
    simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using h
  -- Step 2: the single-layer sunflower bound.
  have hlayer : ∀ k' ∈ Finset.range (k + 1),
      (∑' x : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset ι)).filter (fun A => A.card = k'),
        ‖f A x‖ ^ 2) ^ r)
      ≤ (4 * M : ℝ) ^ r * ∑ A₀ ∈ (Finset.univ : Finset (Finset ι)).filter
          (fun A => A.card ≤ k'),
          ∑ A : Fin r → Finset ι,
            (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k' - A₀.card) ∧
                (∀ i j, i ≠ j → Disjoint (A i) (A j))
             then ∑' x : ℤ, ∏ i, ‖f (A₀ ∪ A i) x‖ ^ 2 else 0) := by
    intro k' hk'
    have hk'le : k' ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk')
    exact tsum_sq_pow_le_sunflower (α := ι) hr hM
      (fun T hT => hsun T (fun A hA => le_trans (hT A hA) hk'le)) f hf
  calc ∑' x : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset ι)).filter (fun A => A.card ≤ k),
        ‖f A x‖ ^ 2) ^ r
      ≤ (k + 1 : ℝ) ^ (r - 1) * ∑ k' ∈ Finset.range (k + 1), ∑' x : ℤ,
            (∑ A ∈ (Finset.univ : Finset (Finset ι)).filter (fun A => A.card = k'),
              ‖f A x‖ ^ 2) ^ r := hkey
    _ ≤ (k + 1 : ℝ) ^ (r - 1) * ∑ k' ∈ Finset.range (k + 1),
            (4 * M : ℝ) ^ r * ∑ A₀ ∈ (Finset.univ : Finset (Finset ι)).filter
              (fun A => A.card ≤ k'),
              ∑ A : Fin r → Finset ι,
                (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k' - A₀.card) ∧
                    (∀ i j, i ≠ j → Disjoint (A i) (A j))
                 then ∑' x : ℤ, ∏ i, ‖f (A₀ ∪ A i) x‖ ^ 2 else 0) := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlayer) (by positivity)

end Work.BourgainPlan.IonescuWainger
