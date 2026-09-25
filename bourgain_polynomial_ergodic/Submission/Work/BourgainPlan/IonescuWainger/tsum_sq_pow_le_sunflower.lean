import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.sunflower_square_function

/-!
# The time-summed sunflower bound on square functions

This file derives the `ℓ²(ℤ)`-summed form of Tao's sunflower bound
(`Work.BourgainPlan.IonescuWainger.sunflower_square_function`) which is the pointwise
(for fixed frequency `m`) combinatorial input of the Ionescu–Wainger square-function
estimate.

If `f A : ℤ → ℂ` is `ℓ²` for every `k`-element set `A`, then

`∑_m (∑_{|A| = k} ‖f A m‖²)^r ≤ (4M)^r ∑_{A₀, |A₀| ≤ k} ∑_{A}` (sunflower configs)
`      ∑_m ∏_i ‖f (A₀ ∪ A_i) m‖²`,

where the inner sum runs over tuples of pairwise disjoint petals `A_i ⊆ α \ A₀` of size
`k - |A₀|`, i.e. the sets `A₀ ∪ A_i` form a sunflower with core `A₀`.
-/

open Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.BourgainPlan.IonescuWainger

/-- `Memℓp f 2` on `ℤ` (with counting measure) is exactly summability of `‖f ·‖²`. -/
lemma summable_norm_sq_of_memℓp {f : ℤ → ℂ} (hf : Memℓp f 2) :
    Summable (fun m => ‖f m‖ ^ 2) := by
  rw [memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num : 0 < (2 : ENNReal).toReal)] at hf
  simpa using hf

/-- A finite sum of summable functions of `m : ℤ` is summable. -/
lemma summable_finset_sum {ι : Type*} {s : Finset ι} {f : ι → ℤ → ℝ}
    (h : ∀ i ∈ s, Summable (f i)) : Summable (fun m => ∑ i ∈ s, f i m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (summable_zero : Summable (fun _ : ℤ => (0 : ℝ)))
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- A finite product of summable nonnegative functions of `m : ℤ` is summable. -/
lemma summable_fin_prod {r : ℕ} (hr : 1 ≤ r) {g : Fin r → ℤ → ℝ}
    (hg : ∀ i, Summable (g i)) (hgn : ∀ i m, 0 ≤ g i m) :
    Summable (fun m => ∏ i, g i m) := by
  classical
  set i0 : Fin r := ⟨0, hr⟩ with hi0
  set C : ℝ := ∏ i ∈ (Finset.univ : Finset (Fin r)).erase i0, (∑' m, g i m) with hC
  refine Summable.of_nonneg_of_le (fun m => Finset.prod_nonneg (fun i _ => hgn i m)) (fun m => ?_)
    ((hg i0).mul_left C)
  have hsplit : (∏ i, g i m) =
      (∏ i ∈ (Finset.univ : Finset (Fin r)).erase i0, g i m) * g i0 m := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin r)) (fun i => g i m)
      (Finset.mem_univ i0)]
    ring
  rw [hsplit]
  have hrest : (∏ i ∈ (Finset.univ : Finset (Fin r)).erase i0, g i m) ≤ C := by
    rw [hC]
    refine Finset.prod_le_prod₀ (fun i _ => hgn i m) (fun i _ => ?_)
    exact (hg i).le_tsum m (fun j _ => hgn i j)
  exact mul_le_mul_of_nonneg_right hrest (hgn i0 m)

/-- A nonnegative summable function of `m : ℤ` has summable `r`-th powers, `r ≥ 1`. -/
lemma summable_pow_of_summable {g : ℤ → ℝ} (hg : Summable g) (hgn : ∀ m, 0 ≤ g m)
    {r : ℕ} (hr : 1 ≤ r) : Summable (fun m => g m ^ r) := by
  set B : ℝ := ∑' m, g m with hB
  have hle : ∀ m, g m ≤ B := fun m => hg.le_tsum m (fun j _ => hgn j)
  have hCm : ∀ m, g m ^ r ≤ B ^ (r - 1) * g m := by
    intro m
    have h1 : g m ^ r = g m ^ (r - 1) * g m :=
      (pow_sub_one_mul (by omega : r ≠ 0) (g m)).symm
    rw [h1]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hgn m) (hle m) (r - 1)) (hgn m)
  exact Summable.of_nonneg_of_le (fun m => pow_nonneg (hgn m) r) hCm (hg.mul_left (B ^ (r - 1)))

/-- A pointwise `if` (with a Prop not depending on `m`) of a summable function is summable. -/
lemma summable_ite_zero {c : Prop} [Decidable c] {g : ℤ → ℝ} (hg : Summable g) :
    Summable (fun m => if c then g m else 0) := by
  by_cases h : c
  · simpa only [if_pos h] using hg
  · simpa only [if_neg h] using (summable_zero : Summable (fun _ : ℤ => (0 : ℝ)))

/-- The `tsum` of a pointwise `if` with a `m`-independent Prop. -/
lemma tsum_ite_zero {c : Prop} [Decidable c] {g : ℤ → ℝ} :
    (∑' m, if c then g m else 0) = if c then ∑' m, g m else 0 := by
  by_cases h : c
  · rw [tsum_congr (fun m => if_pos h), if_pos h]
  · rw [tsum_congr (fun m => if_neg h), if_neg h, tsum_zero]

/-- The pointwise (fixed frequency `m`) sunflower bound in `ℝ`, obtained from the `ℝ≥0`
version `sunflower_square_function` by coercion. -/
lemma sq_pow_le_sunflower_pointwise {α : Type*} [Fintype α] [DecidableEq α]
    {r k M : ℕ} (hr : 2 ≤ r) (hM : 2 ≤ M)
    (hsun : ∀ T : Finset (Finset α), (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
      ∃ A : Fin r → Finset α, (∀ i, A i ∈ T) ∧ Function.Injective A ∧ IsSunflower A)
    (f : Finset α → ℤ → ℂ) (m : ℤ) :
    (∑ A ∈ (Finset.univ : Finset (Finset α)).filter (fun A => A.card = k), ‖f A m‖ ^ 2) ^ r
      ≤ (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ (Finset.univ : Finset (Finset α)).filter (fun A => A.card ≤ k),
            ∑ A : Fin r → Finset α,
              (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
                  (∀ i j, i ≠ j → Disjoint (A i) (A j))
               then ∏ i, ‖f (A₀ ∪ A i) m‖ ^ 2 else 0) := by
  set w : Finset α → NNReal := fun A => ⟨‖f A m‖ ^ 2, sq_nonneg _⟩ with hw
  have h := sunflower_square_function (α := α) k r M hr hM hsun w
  have hw' : ∀ A, (w A : ℝ) = ‖f A m‖ ^ 2 := fun A => rfl
  have E1 : ((∑ A : Finset α, if A.card = k then w A else 0 : NNReal) : ℝ)
      = ∑ A ∈ (Finset.univ : Finset (Finset α)).filter (fun A => A.card = k), ‖f A m‖ ^ 2 := by
    have h1 : (∑ A : Finset α, if A.card = k then w A else 0 : NNReal)
        = ∑ A ∈ (Finset.univ : Finset (Finset α)).filter (fun A => A.card = k), w A := by
      rw [← Finset.sum_filter]
    rw [h1, NNReal.coe_sum]
    exact Finset.sum_congr rfl (fun A _ => hw' A)
  have E2 : ((∑ A₀ : Finset α, if A₀.card ≤ k then
        (∑ A : Fin r → Finset α,
          (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
              (∀ i j, i ≠ j → Disjoint (A i) (A j))
           then ∏ i, w (A₀ ∪ A i) else 0)) else 0 : NNReal) : ℝ)
      = ∑ A₀ ∈ (Finset.univ : Finset (Finset α)).filter (fun A => A.card ≤ k),
          ∑ A : Fin r → Finset α,
            (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
                (∀ i j, i ≠ j → Disjoint (A i) (A j))
             then ∏ i, ‖f (A₀ ∪ A i) m‖ ^ 2 else 0) := by
    have h1 : (∑ A₀ : Finset α, if A₀.card ≤ k then
          (∑ A : Fin r → Finset α,
            (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
                (∀ i j, i ≠ j → Disjoint (A i) (A j))
             then ∏ i, w (A₀ ∪ A i) else 0)) else 0 : NNReal)
        = ∑ A₀ ∈ (Finset.univ : Finset (Finset α)).filter (fun A => A.card ≤ k),
            ∑ A : Fin r → Finset α,
              (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
                  (∀ i j, i ≠ j → Disjoint (A i) (A j))
               then ∏ i, w (A₀ ∪ A i) else 0) := by
      rw [← Finset.sum_filter]
    rw [h1, NNReal.coe_sum]
    refine Finset.sum_congr rfl (fun A₀ _ => ?_)
    rw [NNReal.coe_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    by_cases hc : (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
        (∀ i j, i ≠ j → Disjoint (A i) (A j))
    · rw [if_pos hc, if_pos hc, NNReal.coe_prod]
      exact Finset.prod_congr rfl (fun i _ => hw' _)
    · rw [if_neg hc, if_neg hc, NNReal.coe_zero]
  calc (∑ A ∈ (Finset.univ : Finset (Finset α)).filter (fun A => A.card = k), ‖f A m‖ ^ 2) ^ r
      = (((∑ A : Finset α, if A.card = k then w A else 0 : NNReal) ^ r : NNReal) : ℝ) := by
        rw [NNReal.coe_pow, E1]
    _ ≤ (((4 * M : NNReal) ^ r * (∑ A₀ : Finset α, if A₀.card ≤ k then
          (∑ A : Fin r → Finset α,
            (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
                (∀ i j, i ≠ j → Disjoint (A i) (A j))
             then ∏ i, w (A₀ ∪ A i) else 0)) else 0) : NNReal) : ℝ) :=
        NNReal.coe_le_coe.mpr h
    _ = (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ (Finset.univ : Finset (Finset α)).filter (fun A => A.card ≤ k),
            ∑ A : Fin r → Finset α,
              (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
                  (∀ i j, i ≠ j → Disjoint (A i) (A j))
               then ∏ i, ‖f (A₀ ∪ A i) m‖ ^ 2 else 0) := by
        rw [NNReal.coe_mul, NNReal.coe_pow, E2]
        congr 1

theorem tsum_sq_pow_le_sunflower {α : Type*} [Fintype α] [DecidableEq α]
    {r k M : ℕ} (hr : 2 ≤ r) (hM : 2 ≤ M)
    (hsun : ∀ T : Finset (Finset α), (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
      ∃ A : Fin r → Finset α, (∀ i, A i ∈ T) ∧ Function.Injective A ∧ IsSunflower A)
    (f : Finset α → ℤ → ℂ) (hf : ∀ A, Memℓp (f A) 2) :
    ∑' m : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset α)).filter (fun A => A.card = k),
        ‖f A m‖ ^ 2) ^ r
      ≤ (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ (Finset.univ : Finset (Finset α)).filter (fun A => A.card ≤ k),
            ∑ A : Fin r → Finset α,
              (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
                  (∀ i j, i ≠ j → Disjoint (A i) (A j))
               then ∑' m : ℤ, ∏ i, ‖f (A₀ ∪ A i) m‖ ^ 2 else 0) := by
  classical
  set Fk : Finset (Finset α) := (Finset.univ : Finset (Finset α)).filter (fun A => A.card = k)
    with hFk
  set Fle : Finset (Finset α) := (Finset.univ : Finset (Finset α)).filter (fun A => A.card ≤ k)
    with hFle
  have hsq : ∀ A : Finset α, Summable (fun m : ℤ => ‖f A m‖ ^ 2) :=
    fun A => summable_norm_sq_of_memℓp (hf A)
  have hprod : ∀ B : Fin r → Finset α, Summable (fun m : ℤ => ∏ i, ‖f (B i) m‖ ^ 2) :=
    fun B => summable_fin_prod (by omega : 1 ≤ r) (fun i => hsq (B i)) (fun i m => sq_nonneg _)
  have hG : Summable (fun m : ℤ => ∑ A ∈ Fk, ‖f A m‖ ^ 2) :=
    summable_finset_sum (fun A _ => hsq A)
  have hGnn : ∀ m : ℤ, 0 ≤ ∑ A ∈ Fk, ‖f A m‖ ^ 2 :=
    fun m => Finset.sum_nonneg (fun A _ => sq_nonneg _)
  have hL : Summable (fun m : ℤ => (∑ A ∈ Fk, ‖f A m‖ ^ 2) ^ r) :=
    summable_pow_of_summable hG hGnn (by omega : 1 ≤ r)
  have hT : ∀ (A₀ : Finset α) (B : Fin r → Finset α),
      Summable (fun m : ℤ => if (∀ i, B i ⊆ Finset.univ \ A₀) ∧ (∀ i, (B i).card = k - A₀.card) ∧
          (∀ i j, i ≠ j → Disjoint (B i) (B j)) then ∏ i, ‖f (A₀ ∪ B i) m‖ ^ 2 else 0) :=
    fun A₀ B => summable_ite_zero (hprod (fun i => A₀ ∪ B i))
  have hRg : Summable (fun m : ℤ => ∑ A₀ ∈ Fle, ∑ B : Fin r → Finset α,
      (if (∀ i, B i ⊆ Finset.univ \ A₀) ∧ (∀ i, (B i).card = k - A₀.card) ∧
          (∀ i j, i ≠ j → Disjoint (B i) (B j)) then ∏ i, ‖f (A₀ ∪ B i) m‖ ^ 2 else 0)) := by
    refine summable_finset_sum (fun A₀ _ => ?_)
    exact summable_finset_sum (fun B _ => hT A₀ B)
  have hpt : ∀ m : ℤ, (∑ A ∈ Fk, ‖f A m‖ ^ 2) ^ r ≤ (4 * M : ℝ) ^ r *
      ∑ A₀ ∈ Fle, ∑ B : Fin r → Finset α,
        (if (∀ i, B i ⊆ Finset.univ \ A₀) ∧ (∀ i, (B i).card = k - A₀.card) ∧
            (∀ i j, i ≠ j → Disjoint (B i) (B j)) then ∏ i, ‖f (A₀ ∪ B i) m‖ ^ 2 else 0) := by
    intro m
    have h := sq_pow_le_sunflower_pointwise (α := α) hr hM hsun f m
    simpa only [hFk, hFle] using h
  have hinterchange : (∑' m : ℤ, (∑ A₀ ∈ Fle, ∑ B : Fin r → Finset α,
        (if (∀ i, B i ⊆ Finset.univ \ A₀) ∧ (∀ i, (B i).card = k - A₀.card) ∧
            (∀ i j, i ≠ j → Disjoint (B i) (B j)) then ∏ i, ‖f (A₀ ∪ B i) m‖ ^ 2 else 0)))
      = ∑ A₀ ∈ Fle, ∑ B : Fin r → Finset α,
        (if (∀ i, B i ⊆ Finset.univ \ A₀) ∧ (∀ i, (B i).card = k - A₀.card) ∧
            (∀ i j, i ≠ j → Disjoint (B i) (B j))
         then ∑' m : ℤ, ∏ i, ‖f (A₀ ∪ B i) m‖ ^ 2 else 0) := by
    rw [Summable.tsum_finsetSum (fun A₀ _ => summable_finset_sum (fun B _ => hT A₀ B))]
    refine Finset.sum_congr rfl (fun A₀ _ => ?_)
    rw [Summable.tsum_finsetSum (fun B _ => hT A₀ B)]
    exact Finset.sum_congr rfl (fun B _ => tsum_ite_zero)
  calc ∑' m : ℤ, (∑ A ∈ Fk, ‖f A m‖ ^ 2) ^ r
      ≤ ∑' m : ℤ, (4 * M : ℝ) ^ r * (∑ A₀ ∈ Fle, ∑ B : Fin r → Finset α,
          (if (∀ i, B i ⊆ Finset.univ \ A₀) ∧ (∀ i, (B i).card = k - A₀.card) ∧
              (∀ i j, i ≠ j → Disjoint (B i) (B j)) then ∏ i, ‖f (A₀ ∪ B i) m‖ ^ 2 else 0)) :=
        Summable.tsum_le_tsum hpt hL (hRg.mul_left _)
    _ = (4 * M : ℝ) ^ r * ∑' m : ℤ, (∑ A₀ ∈ Fle, ∑ B : Fin r → Finset α,
          (if (∀ i, B i ⊆ Finset.univ \ A₀) ∧ (∀ i, (B i).card = k - A₀.card) ∧
              (∀ i j, i ≠ j → Disjoint (B i) (B j)) then ∏ i, ‖f (A₀ ∪ B i) m‖ ^ 2 else 0)) := by
        rw [tsum_mul_left]
    _ = (4 * M : ℝ) ^ r * ∑ A₀ ∈ Fle, ∑ B : Fin r → Finset α,
          (if (∀ i, B i ⊆ Finset.univ \ A₀) ∧ (∀ i, (B i).card = k - A₀.card) ∧
              (∀ i j, i ≠ j → Disjoint (B i) (B j))
           then ∑' m : ℤ, ∏ i, ‖f (A₀ ∪ B i) m‖ ^ 2 else 0) := by
        rw [hinterchange]

end Work.BourgainPlan.IonescuWainger
