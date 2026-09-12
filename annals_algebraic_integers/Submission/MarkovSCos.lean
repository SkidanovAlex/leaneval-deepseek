import Submission.MarkovSHelper

noncomputable section

open scoped Real BigOperators
open Polynomial

namespace Submission.MarkovSCos

open MarkovSHelper

/-!
# cos powers are degree-≤ n trig polynomials

Every real polynomial `P` of natDegree ≤ n, composed with `cos`, is a degree-≤ n
trigonometric polynomial with vanishing sin-coefficients.  The proof:

1. `cos_pow_span k`: `cos^k θ = ∑_{j ≤ k} d j · cos (jθ)` for some coefficients `d`,
   shown by induction using the product-to-sum identity
   `cos(jθ)·cos θ = (cos((j+1)θ) + cos((j-1)θ))/2`.
2. Expand `P.eval (cos θ) = ∑ᵢ P.coeff i · cosⁱ θ` and regroup the double sum.
-/


/-! ## core trig identity and finset reindexing -/

lemma cos_mul_cos_nat (j : ℕ) (θ : ℝ) :
    Real.cos (((j : ℝ) + 1) * θ) + Real.cos (((j : ℝ) - 1) * θ)
      = 2 * Real.cos ((j : ℝ) * θ) * Real.cos θ := by
  rw [Real.cos_add_cos]
  congr 1
  · ring
  · ring

lemma cos_nat_mul_cos (j : ℕ) (θ : ℝ) :
    Real.cos ((j : ℝ) * θ) * Real.cos θ =
      (Real.cos (((j : ℝ) + 1) * θ) + Real.cos (((j : ℝ) - 1) * θ)) / 2 := by
  have h := cos_mul_cos_nat j θ
  linarith

lemma sum_range_shift (k : ℕ) (F : ℕ → ℝ) :
    (∑ j ∈ Finset.range (k + 1), F (j + 1)) =
      ∑ m ∈ (Finset.range (k + 2)).erase 0, F m := by
  classical
  refine Finset.sum_bij' (s := Finset.range (k+1)) (t := (Finset.range (k+2)).erase 0)
    (fun a _ => a + 1) (fun b _ => b - 1) ?hi ?hj ?ln ?rn ?h
  · intro a ha
    simp at ha ⊢
    omega
  · intro b hb
    simp at hb ⊢
    omega
  · intro a ha
    simp
  · intro b hb
    simp at hb ⊢
    omega
  · intro a ha
    rfl

lemma sum_erase_zero (k : ℕ) (F : ℕ → ℝ) :
    (∑ m ∈ (Finset.range (k + 2)).erase 0, F m) =
      ∑ m ∈ Finset.range (k + 2), (if m = 0 then 0 else F m) := by
  classical
  let f : ℕ → ℝ := fun m => if m = 0 then 0 else F m
  calc
    (∑ m ∈ (Finset.range (k + 2)).erase 0, F m)
        = ∑ m ∈ (Finset.range (k + 2)).erase 0, f m := by
            dsimp [f]
            apply Finset.sum_congr rfl
            intro m hm
            have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
            simp [hm0]
    _ = ∑ m ∈ (Finset.range (k + 2)), f m := by
            rw [← Finset.sum_erase_add (s := Finset.range (k+2)) (f := f) (a := 0) (by simp)]
            simp [f]

lemma sum_shift_if (k : ℕ) (F : ℕ → ℝ) :
    (∑ j ∈ Finset.range (k + 1), F (j + 1)) =
      ∑ m ∈ Finset.range (k + 2), (if m = 0 then 0 else F m) := by
  rw [sum_range_shift, sum_erase_zero]

lemma sum_range_pad (k : ℕ) (F : ℕ → ℝ) :
    (∑ m ∈ Finset.range (k + 2), (if m < k then F m else 0)) = ∑ m ∈ Finset.range k, F m := by
  classical
  rw [← Finset.sum_filter (s := Finset.range (k+2)) (p := fun m : ℕ => m < k)]
  · apply Finset.sum_congr
    · ext m
      simp
      omega
    · intro m hm
      by_cases hmk : m < k <;> simp [hmk]

/-! ## trig-specific helpers -/

lemma cos_shift_add (j : ℕ) (θ : ℝ) :
    Real.cos (((j : ℝ) + 1) * θ) = Real.cos (((j + 1 : ℕ) : ℝ) * θ) := by
  congr 1
  norm_num

lemma cos_head_zero (θ : ℝ) : Real.cos (((0 : ℝ) - 1) * θ) = Real.cos θ := by
  rw [show ((0 : ℝ) - 1) * θ = -θ by norm_num]
  exact Real.cos_neg θ

lemma cos_head_zero' (θ : ℝ) : Real.cos ((((0 : ℕ) : ℝ) - 1) * θ) = Real.cos θ := by
  norm_num [Real.cos_neg]

/-- S1 part -/
lemma s1_sum (k : ℕ) (d : ℕ → ℝ) (θ : ℝ) :
    (∑ j ∈ Finset.range (k + 1), (d j / 2) * Real.cos (((j : ℝ) + 1) * θ))
      = ∑ m ∈ Finset.range (k + 2),
          (if m = 0 then 0 else d (m - 1) / 2) * Real.cos ((m : ℝ) * θ) := by
  classical
  calc
    (∑ j ∈ Finset.range (k + 1), (d j / 2) * Real.cos (((j : ℝ) + 1) * θ))
        = ∑ j ∈ Finset.range (k + 1),
            (if j + 1 = 0 then 0 else d ((j + 1) - 1) / 2) * Real.cos (((j + 1 : ℕ) : ℝ) * θ) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj0 : j + 1 ≠ 0 := by omega
            have hsub : (j + 1) - 1 = j := by omega
            rw [if_neg hj0, hsub, cos_shift_add]
    _ = ∑ m ∈ Finset.range (k + 2), (if m = 0 then 0 else
            (if m = 0 then 0 else d (m - 1) / 2) * Real.cos ((m : ℝ) * θ)) := by
            rw [← sum_shift_if k (fun m => (if m = 0 then 0 else d (m - 1) / 2) * Real.cos ((m : ℝ) * θ))]
    _ = ∑ m ∈ Finset.range (k + 2),
          (if m = 0 then 0 else d (m - 1) / 2) * Real.cos ((m : ℝ) * θ) := by
            apply Finset.sum_congr rfl
            intro m hm
            by_cases hm0 : m = 0
            · subst m
              simp
            · simp [hm0]

/-- head of S2 -/
lemma s2_head_sum (k : ℕ) (d : ℕ → ℝ) (θ : ℝ) :
    (d 0 / 2) * Real.cos θ
      = ∑ m ∈ Finset.range (k + 2), (if m = 1 then d 0 / 2 else 0) * Real.cos ((m : ℝ) * θ) := by
  classical
  rw [Finset.sum_eq_single 1]
  · simp
  · intro b _ hb1
    simp [hb1]
  · intro h1
    simp at h1

/-! S2 full: split off j = 0 head via sum_range_succ' -/
lemma s2_full_sum (k : ℕ) (d : ℕ → ℝ) (θ : ℝ) :
    (∑ j ∈ Finset.range (k + 1), (d j / 2) * Real.cos (((j : ℝ) - 1) * θ))
      = (d 0 / 2) * Real.cos θ + ∑ m ∈ Finset.range k, (d (m + 1) / 2) * Real.cos ((m : ℝ) * θ) := by
  calc
    (∑ j ∈ Finset.range (k + 1), (d j / 2) * Real.cos (((j : ℝ) - 1) * θ))
        = (∑ m ∈ Finset.range k, (d (m + 1) / 2) * Real.cos ((((m + 1 : ℕ) : ℝ) - 1) * θ)) + (d 0 / 2) * Real.cos ((((0 : ℕ) : ℝ) - 1) * θ) := by
            rw [Finset.sum_range_succ' (fun j => (d j / 2) * Real.cos (((j : ℝ) - 1) * θ)) k]
    _ = (∑ m ∈ Finset.range k, (d (m + 1) / 2) * Real.cos ((m : ℝ) * θ)) + (d 0 / 2) * Real.cos θ := by
            congr 1
            · apply Finset.sum_congr rfl
              intro m hm
              have harg : (((m + 1 : ℕ) : ℝ) - 1) * θ = (m : ℝ) * θ := by norm_num
              rw [harg]
            · rw [cos_head_zero']
    _ = (d 0 / 2) * Real.cos θ + ∑ m ∈ Finset.range k, (d (m + 1) / 2) * Real.cos ((m : ℝ) * θ) := by
            ring

/-! C-guarded sum -/
lemma s2_guard_sum (k : ℕ) (d : ℕ → ℝ) (θ : ℝ) :
    (∑ m ∈ Finset.range k, (d (m + 1) / 2) * Real.cos ((m : ℝ) * θ))
      = ∑ m ∈ Finset.range (k + 2),
          (if m < k then d (m + 1) / 2 else 0) * Real.cos ((m : ℝ) * θ) := by
  classical
  calc
    (∑ m ∈ Finset.range k, (d (m + 1) / 2) * Real.cos ((m : ℝ) * θ))
        = ∑ m ∈ Finset.range (k + 2),
            (if m < k then (d (m + 1) / 2) * Real.cos ((m : ℝ) * θ) else 0) := by
            rw [← sum_range_pad k (fun m => (d (m + 1) / 2) * Real.cos ((m : ℝ) * θ))]
    _ = ∑ m ∈ Finset.range (k + 2),
          (if m < k then d (m + 1) / 2 else 0) * Real.cos ((m : ℝ) * θ) := by
            apply Finset.sum_congr rfl
            intro m hm
            by_cases hmk : m < k <;> simp [hmk]

/-! combining three guarded sums into one -/
lemma three_sum_combine (k : ℕ) (A B C : ℕ → ℝ) (θ : ℝ) :
    (∑ m ∈ Finset.range (k + 2), A m * Real.cos ((m : ℝ) * θ)) +
      ((∑ m ∈ Finset.range (k + 2), B m * Real.cos ((m : ℝ) * θ)) +
       (∑ m ∈ Finset.range (k + 2), C m * Real.cos ((m : ℝ) * θ)))
      = ∑ m ∈ Finset.range (k + 2), (A m + B m + C m) * Real.cos ((m : ℝ) * θ) := by
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- induction step for cos powers -/
lemma cos_pow_succ_span (k : ℕ) (d : ℕ → ℝ)
    (hd : ∀ θ : ℝ, Real.cos θ ^ k = ∑ j ∈ Finset.range (k + 1), d j * Real.cos ((j : ℝ) * θ)) :
    ∃ e : ℕ → ℝ, ∀ θ : ℝ,
      Real.cos θ ^ (k + 1) = ∑ m ∈ Finset.range (k + 2), e m * Real.cos ((m : ℝ) * θ) := by
  let A : ℕ → ℝ := fun m => if m = 0 then 0 else d (m - 1) / 2
  let B : ℕ → ℝ := fun m => if m = 1 then d 0 / 2 else 0
  let C : ℕ → ℝ := fun m => if m < k then d (m + 1) / 2 else 0
  refine ⟨fun m => A m + B m + C m, ?_⟩
  intro θ
  calc
    Real.cos θ ^ (k + 1) = Real.cos θ ^ k * Real.cos θ := by rw [pow_succ]
    _ = (∑ j ∈ Finset.range (k + 1), d j * Real.cos ((j : ℝ) * θ)) * Real.cos θ := by
          rw [hd θ]
    _ = ∑ j ∈ Finset.range (k + 1), (d j * Real.cos ((j : ℝ) * θ)) * Real.cos θ := by
          rw [Finset.sum_mul]
    _ = ∑ j ∈ Finset.range (k + 1), (d j / 2) * (Real.cos (((j : ℝ) + 1) * θ) + Real.cos (((j : ℝ) - 1) * θ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          calc
            (d j * Real.cos ((j : ℝ) * θ)) * Real.cos θ
                = d j * (Real.cos ((j : ℝ) * θ) * Real.cos θ) := by ring
            _ = d j * ((Real.cos (((j : ℝ) + 1) * θ) + Real.cos (((j : ℝ) - 1) * θ)) / 2) := by
                  rw [cos_nat_mul_cos j θ]
            _ = (d j / 2) * (Real.cos (((j : ℝ) + 1) * θ) + Real.cos (((j : ℝ) - 1) * θ)) := by ring
    _ = ∑ j ∈ Finset.range (k + 1), ((d j / 2) * Real.cos (((j : ℝ) + 1) * θ) + (d j / 2) * Real.cos (((j : ℝ) - 1) * θ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = (∑ j ∈ Finset.range (k + 1), (d j / 2) * Real.cos (((j : ℝ) + 1) * θ)) +
          (∑ j ∈ Finset.range (k + 1), (d j / 2) * Real.cos (((j : ℝ) - 1) * θ)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ m ∈ Finset.range (k + 2), A m * Real.cos ((m : ℝ) * θ)) +
          ((d 0 / 2) * Real.cos θ + ∑ m ∈ Finset.range k, (d (m + 1) / 2) * Real.cos ((m : ℝ) * θ)) := by
          dsimp [A]
          rw [s1_sum, s2_full_sum]
    _ = (∑ m ∈ Finset.range (k + 2), A m * Real.cos ((m : ℝ) * θ)) +
          ((∑ m ∈ Finset.range (k + 2), B m * Real.cos ((m : ℝ) * θ)) +
           (∑ m ∈ Finset.range (k + 2), C m * Real.cos ((m : ℝ) * θ))) := by
          dsimp [B, C]
          rw [← s2_head_sum, ← s2_guard_sum]
    _ = ∑ m ∈ Finset.range (k + 2), (A m + B m + C m) * Real.cos ((m : ℝ) * θ) := by
          exact three_sum_combine k A B C θ
    _ = ∑ m ∈ Finset.range (k + 2), (fun m => A m + B m + C m) m * Real.cos ((m : ℝ) * θ) := by rfl

/-- powers of cos are linear combinations of cos(j·) with j ≤ k -/
lemma cos_pow_span (k : ℕ) : ∃ d : ℕ → ℝ, ∀ θ : ℝ,
    Real.cos θ ^ k = ∑ j ∈ Finset.range (k + 1), d j * Real.cos ((j : ℝ) * θ) := by
  induction k with
  | zero =>
      refine ⟨fun j => if j = 0 then 1 else 0, ?_⟩
      intro θ
      simp
  | succ k ih =>
      rcases ih with ⟨d, hd⟩
      exact cos_pow_succ_span k d hd


lemma eval_eq_sum_range_le {p : Polynomial ℝ} {n : ℕ} (hn : p.natDegree ≤ n) (x : ℝ) :
    p.eval x = ∑ i ∈ Finset.range (n + 1), p.coeff i * x ^ i := by
  rw [Polynomial.eval_eq_sum_range]
  apply Finset.sum_subset
  · intro i hi
    simp at hi ⊢
    omega
  · intro i hi hi'
    have hnd : p.natDegree < i := by
      simp at hi hi'
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hnd]
    ring

lemma sum_swap_le (n : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1), f i j)
      = ∑ j ∈ Finset.range (n + 1), ∑ i ∈ (Finset.range (n + 1)).filter (fun i => j ≤ i), f i j := by
  classical
  let sA : Finset (Σ _ : ℕ, ℕ) := (Finset.range (n+1)).sigma (fun i => Finset.range (i+1))
  let sB : Finset (Σ _ : ℕ, ℕ) := (Finset.range (n+1)).sigma (fun j => (Finset.range (n+1)).filter (fun i => j ≤ i))
  calc
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1), f i j)
        = ∑ x ∈ sA, f x.1 x.2 := by
            dsimp [sA]
            rw [Finset.sum_sigma' (Finset.range (n + 1)) (fun i => Finset.range (i + 1)) f]
    _ = ∑ x ∈ sB, f x.2 x.1 := by
            dsimp [sA, sB]
            refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1⟩) (fun y _ => ⟨y.2, y.1⟩) ?hi ?hj ?ln ?rn ?h
            · intro x hx
              simp [Finset.mem_sigma] at hx ⊢
              omega
            · intro y hy
              simp [Finset.mem_sigma] at hy ⊢
              omega
            · intro x hx
              rcases x with ⟨i, j⟩
              simp
            · intro y hy
              rcases y with ⟨j, i⟩
              simp
            · intro x hx
              rcases x with ⟨i, j⟩
              simp
    _ = ∑ j ∈ Finset.range (n + 1), ∑ i ∈ (Finset.range (n + 1)).filter (fun i => j ≤ i), f i j := by
            dsimp [sB]
            rw [Finset.sum_sigma' (Finset.range (n + 1))
              (fun j => (Finset.range (n + 1)).filter (fun i => j ≤ i)) (fun j i => f i j)]

lemma inner_factor (n : ℕ) (j : ℕ) (c d : ℕ → ℝ) (θ : ℝ) :
    (∑ i ∈ Finset.range (n + 1), (if j ≤ i then (c i * d i) * Real.cos ((j : ℝ) * θ) else 0))
      = (∑ i ∈ Finset.range (n + 1), if j ≤ i then c i * d i else 0) * Real.cos ((j : ℝ) * θ) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hji : j ≤ i
  · simp [hji]
  · simp [hji]

lemma poly_eval_cos_is_TPoly {n : ℕ} (P : Polynomial ℝ) (hdeg : P.natDegree ≤ n) :
    ∃ a : ℕ → ℝ, ∀ θ : ℝ, P.eval (Real.cos θ) = TPoly n a (fun _ => 0) θ := by
  classical
  let d : ℕ → ℕ → ℝ := fun i => Classical.choose (cos_pow_span i)
  have hd (i : ℕ) : ∀ θ : ℝ,
      Real.cos θ ^ i = ∑ j ∈ Finset.range (i + 1), d i j * Real.cos ((j : ℝ) * θ) := by
    intro θ
    have hs := Classical.choose_spec (cos_pow_span i)
    simpa [d] using hs θ
  refine ⟨fun m => ∑ i ∈ Finset.range (n + 1), if m ≤ i then P.coeff i * d i m else 0, ?_⟩
  intro θ
  calc
    P.eval (Real.cos θ) = ∑ i ∈ Finset.range (n + 1), P.coeff i * (Real.cos θ) ^ i := by
          exact eval_eq_sum_range_le hdeg (Real.cos θ)
    _ = ∑ i ∈ Finset.range (n + 1), P.coeff i *
          (∑ j ∈ Finset.range (i + 1), d i j * Real.cos ((j : ℝ) * θ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hd i θ]
    _ = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1),
          P.coeff i * (d i j * Real.cos ((j : ℝ) * θ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1),
          (P.coeff i * d i j) * Real.cos ((j : ℝ) * θ) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ j ∈ Finset.range (n + 1), ∑ i ∈ (Finset.range (n + 1)).filter (fun i => j ≤ i),
          (P.coeff i * d i j) * Real.cos ((j : ℝ) * θ) := by
          exact sum_swap_le n (fun i j => (P.coeff i * d i j) * Real.cos ((j : ℝ) * θ))
    _ = ∑ j ∈ Finset.range (n + 1),
          (∑ i ∈ Finset.range (n + 1), (if j ≤ i then (P.coeff i * d i j) * Real.cos ((j : ℝ) * θ) else 0)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_filter]
    _ = ∑ j ∈ Finset.range (n + 1),
          (∑ i ∈ Finset.range (n + 1), if j ≤ i then P.coeff i * d i j else 0) * Real.cos ((j : ℝ) * θ) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact inner_factor n j (P.coeff) (fun i => d i j) θ
    _ = TPoly n (fun m => ∑ i ∈ Finset.range (n + 1), if m ≤ i then P.coeff i * d i m else 0)
          (fun _ => 0) θ := by
          unfold TPoly
          simp [Finset.sum_filter]

end Submission.MarkovSCos
