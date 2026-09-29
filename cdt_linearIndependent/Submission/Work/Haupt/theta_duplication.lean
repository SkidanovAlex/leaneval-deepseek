import Mathlib
import Submission.Work.Haupt.defs
import Submission.Work.Haupt.theta_aux

/-!
# Theta duplication formulas (`Area M`)

With the nome-variable theta series of `Submission.Work.Haupt.defs`,

* `T3 x = θ₃(x) = ∑' n : ℤ, x ^ (n^2)`,
* `T4 x = θ₄(x) = ∑' n : ℤ, (-1)^n x ^ (n^2)`,
* `T2 x = θ₂(x)/x^{1/4} = ∑' n : ℤ, x ^ (n(n+1))`,

we prove the three *duplication* identities (`x ↦ x^2`):

* `T3 x ^ 2 = T3 (x^2)^2 + x * T2 (x^2)^2`,
* `T4 x ^ 2 = T3 (x^2)^2 - x * T2 (x^2)^2`,
* `T2 x ^ 2 = 2 * T2 (x^2) * T3 (x^2)`.

All three have the same shape: expand the square into a double `tsum` over `ℤ × ℤ`, split
the index set according to the parity of `m + n` (`tsum_int_sq_split`), and evaluate the two
halves (`*_even_sum`, `*_odd_sum`) against products of theta series.  The shared machinery —
absolute convergence of the model series, the parity splitting, and the pointwise exponent
identities — lives in `Submission.Work.Haupt.theta_aux`.

The proofs are split into small top-level lemmas with no nested local abbreviations, both for
modularity and to keep the elaborator's work per declaration modest.
-/

namespace Work.Haupt

open scoped BigOperators

noncomputable section

/-- `‖x‖ < 1 → ‖x^2‖ < 1`. -/
lemma norm_sq_lt_one (x : ℂ) (hx : ‖x‖ < 1) : ‖x ^ 2‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)

/-- Absolute convergence of the `θ₃`-type double series. -/
lemma summable_pow_sq_pair (x : ℂ) (hx : ‖x‖ < 1) :
    Summable (fun p : ℤ × ℤ => x ^ (p.1^2 + p.2^2)) := by
  have h := summable_mul_of_summable_norm (summable_norm_pow_sq x hx) (summable_norm_pow_sq x hx)
  refine Summable.congr h (fun p => ?_)
  exact (zpow_add_nn x (sq_nonneg p.1) (sq_nonneg p.2)).symm

/-- Absolute convergence of the `θ₄`-type double series. -/
lemma summable_neg_pow_sq_pair (x : ℂ) (hx : ‖x‖ < 1) :
    Summable (fun p : ℤ × ℤ => ((-1)^p.1 * x^(p.1^2)) * ((-1)^p.2 * x^(p.2^2))) :=
  summable_mul_of_summable_norm
    (f := fun n : ℤ => (-1 : ℂ)^n * x ^ (n^2)) (g := fun n : ℤ => (-1 : ℂ)^n * x ^ (n^2))
    (summable_norm_pow_sq_mul x hx) (summable_norm_pow_sq_mul x hx)

/-- Absolute convergence of the `θ₂`-type double series. -/
lemma summable_pow_mul_pair (x : ℂ) (hx : ‖x‖ < 1) :
    Summable (fun p : ℤ × ℤ => x ^ (p.1*(p.1+1) + p.2*(p.2+1))) := by
  have h := summable_mul_of_summable_norm (summable_norm_pow_mul_succ x hx)
    (summable_norm_pow_mul_succ x hx)
  refine Summable.congr h (fun p => ?_)
  exact (zpow_add_nn x (mul_self_add_self_nonneg p.1) (mul_self_add_self_nonneg p.2)).symm

/-! ### The two halves of each double sum -/

lemma theta3_even_sum (x : ℂ) (hx2 : ‖x ^ 2‖ < 1) :
    (∑' q : ℤ × ℤ, x^((q.1+q.2)^2 + (q.1-q.2)^2)) = T3 (x^2)^2 := by
  have hc : (fun q : ℤ × ℤ => x^((q.1+q.2)^2 + (q.1-q.2)^2))
      = fun q => (x^2)^(q.1^2) * (x^2)^(q.2^2) := by
    funext q; exact dup_even x q.1 q.2
  rw [hc, sq_sum_eq (x^2) hx2]

lemma theta3_odd_sum (x : ℂ) (hx2 : ‖x ^ 2‖ < 1) :
    (∑' q : ℤ × ℤ, x^((q.1+q.2)^2 + (q.1-q.2-1)^2)) = x * T2 (x^2)^2 := by
  have hc : (fun q : ℤ × ℤ => x^((q.1+q.2)^2 + (q.1-q.2-1)^2))
      = fun q => x * ((x^2)^(q.1*(q.1-1)) * (x^2)^(q.2*(q.2+1))) := by
    funext q; exact dup_odd x q.1 q.2
  rw [hc, tsum_mul_left]
  congr 1
  exact odd_sum_eq (x^2) hx2

lemma theta4_even_sum (x : ℂ) (hx2 : ‖x ^ 2‖ < 1) :
    (∑' q : ℤ × ℤ, ((-1)^(q.1+q.2) * x^((q.1+q.2)^2))
        * ((-1)^(q.1-q.2) * x^((q.1-q.2)^2))) = T3 (x^2)^2 := by
  have hc : (fun q : ℤ × ℤ => ((-1)^(q.1+q.2) * x^((q.1+q.2)^2))
        * ((-1)^(q.1-q.2) * x^((q.1-q.2)^2)))
      = fun q => (x^2)^(q.1^2) * (x^2)^(q.2^2) := by
    funext q; exact dup_even4 x q.1 q.2
  rw [hc, sq_sum_eq (x^2) hx2]

lemma theta4_odd_sum (x : ℂ) (hx2 : ‖x ^ 2‖ < 1) :
    (∑' q : ℤ × ℤ, ((-1)^(q.1+q.2) * x^((q.1+q.2)^2))
        * ((-1)^(q.1-q.2-1) * x^((q.1-q.2-1)^2))) = - (x * T2 (x^2)^2) := by
  have hc : (fun q : ℤ × ℤ => ((-1)^(q.1+q.2) * x^((q.1+q.2)^2))
        * ((-1)^(q.1-q.2-1) * x^((q.1-q.2-1)^2)))
      = fun q => - (x * ((x^2)^(q.1*(q.1-1)) * (x^2)^(q.2*(q.2+1)))) := by
    funext q; exact dup_odd4 x q.1 q.2
  rw [hc, tsum_neg]
  congr 1
  rw [tsum_mul_left]
  congr 1
  exact odd_sum_eq (x^2) hx2

lemma theta2_even_sum (x : ℂ) (hx2 : ‖x ^ 2‖ < 1) :
    (∑' q : ℤ × ℤ, x^((q.1+q.2)*(q.1+q.2+1) + (q.1-q.2)*(q.1-q.2+1)))
      = T2 (x^2) * T3 (x^2) := by
  have hc : (fun q : ℤ × ℤ => x^((q.1+q.2)*(q.1+q.2+1) + (q.1-q.2)*(q.1-q.2+1)))
      = fun q => (x^2)^(q.1*(q.1+1)) * (x^2)^(q.2^2) := by
    funext q; exact dup_even2 x q.1 q.2
  rw [hc, mixed_sum_eq (x^2) hx2]

lemma theta2_odd_sum (x : ℂ) (hx2 : ‖x ^ 2‖ < 1) :
    (∑' q : ℤ × ℤ, x^((q.1+q.2)*((q.1+q.2)+1) + (q.1-q.2-1)*((q.1-q.2-1)+1)))
      = T3 (x^2) * T2 (x^2) := by
  have hc : (fun q : ℤ × ℤ => x^((q.1+q.2)*((q.1+q.2)+1) + (q.1-q.2-1)*((q.1-q.2-1)+1)))
      = fun q => (x^2)^(q.1^2) * (x^2)^(q.2*(q.2+1)) := by
    funext q; exact dup_odd2 x q.1 q.2
  rw [hc, mixed_sum_eq' (x^2) hx2]

/-! ### The three chains -/

lemma theta3_chain (x : ℂ) (hx : ‖x‖ < 1)
    (hF1 : Summable (fun p : ℤ × ℤ => x ^ (p.1^2 + p.2^2)))
    (heven : (∑' q : ℤ × ℤ, x^((q.1+q.2)^2 + (q.1-q.2)^2)) = T3 (x^2)^2)
    (hodd : (∑' q : ℤ × ℤ, x^((q.1+q.2)^2 + (q.1-q.2-1)^2)) = x * T2 (x^2)^2) :
    T3 x ^ 2 = T3 (x ^ 2) ^ 2 + x * T2 (x ^ 2) ^ 2 := by
  rw [show T3 x ^ 2 = T3 x * T3 x from by ring]
  simp only [T3]
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_pow_sq x hx) (summable_norm_pow_sq x hx)]
  rw [show (∑' p : ℤ × ℤ, x^(p.1^2) * x^(p.2^2)) = ∑' p : ℤ × ℤ, x^(p.1^2 + p.2^2) from by
    apply tsum_congr; intro p
    exact (zpow_add_nn x (sq_nonneg p.1) (sq_nonneg p.2)).symm]
  rw [tsum_int_sq_split _ hF1]
  rw [heven, hodd]
  simp only [T3]

lemma theta4_chain (x : ℂ)
    (hfN : Summable (fun n : ℤ => ‖(-1 : ℂ)^n * x ^ (n^2)‖))
    (hF2 : Summable (fun p : ℤ × ℤ => ((-1)^p.1 * x^(p.1^2)) * ((-1)^p.2 * x^(p.2^2))))
    (heven : (∑' q : ℤ × ℤ, ((-1)^(q.1+q.2) * x^((q.1+q.2)^2))
        * ((-1)^(q.1-q.2) * x^((q.1-q.2)^2))) = T3 (x^2)^2)
    (hodd : (∑' q : ℤ × ℤ, ((-1)^(q.1+q.2) * x^((q.1+q.2)^2))
        * ((-1)^(q.1-q.2-1) * x^((q.1-q.2-1)^2))) = - (x * T2 (x^2)^2)) :
    T4 x ^ 2 = T3 (x ^ 2) ^ 2 - x * T2 (x ^ 2) ^ 2 := by
  rw [show T4 x ^ 2 = T4 x * T4 x from by ring]
  simp only [T4]
  rw [tsum_mul_tsum_of_summable_norm hfN hfN]
  rw [tsum_int_sq_split _ hF2]
  rw [heven, hodd]
  ring

lemma theta2_chain (x : ℂ) (hx : ‖x‖ < 1)
    (hF3 : Summable (fun p : ℤ × ℤ => x ^ (p.1*(p.1+1) + p.2*(p.2+1))))
    (heven : (∑' q : ℤ × ℤ, x^((q.1+q.2)*(q.1+q.2+1) + (q.1-q.2)*(q.1-q.2+1)))
        = T2 (x^2) * T3 (x^2))
    (hodd : (∑' q : ℤ × ℤ, x^((q.1+q.2)*((q.1+q.2)+1) + (q.1-q.2-1)*((q.1-q.2-1)+1)))
        = T3 (x^2) * T2 (x^2)) :
    T2 x ^ 2 = 2 * T2 (x ^ 2) * T3 (x ^ 2) := by
  rw [show T2 x ^ 2 = T2 x * T2 x from by ring]
  simp only [T2]
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_pow_mul_succ x hx)
    (summable_norm_pow_mul_succ x hx)]
  rw [show (∑' p : ℤ × ℤ, x^(p.1*(p.1+1)) * x^(p.2*(p.2+1)))
        = ∑' p : ℤ × ℤ, x^(p.1*(p.1+1) + p.2*(p.2+1)) from by
    apply tsum_congr; intro p
    exact (zpow_add_nn x (mul_self_add_self_nonneg p.1) (mul_self_add_self_nonneg p.2)).symm]
  rw [tsum_int_sq_split _ hF3]
  rw [heven, hodd]
  simp only [T2]
  ring

/-! ### The three identities -/

theorem theta_duplication_T3 (x : ℂ) (hx : ‖x‖ < 1) :
    T3 x ^ 2 = T3 (x ^ 2) ^ 2 + x * T2 (x ^ 2) ^ 2 :=
  theta3_chain x hx (summable_pow_sq_pair x hx)
    (theta3_even_sum x (norm_sq_lt_one x hx)) (theta3_odd_sum x (norm_sq_lt_one x hx))

theorem theta_duplication_T4 (x : ℂ) (hx : ‖x‖ < 1) :
    T4 x ^ 2 = T3 (x ^ 2) ^ 2 - x * T2 (x ^ 2) ^ 2 :=
  theta4_chain x (summable_norm_pow_sq_mul x hx) (summable_neg_pow_sq_pair x hx)
    (theta4_even_sum x (norm_sq_lt_one x hx)) (theta4_odd_sum x (norm_sq_lt_one x hx))

theorem theta_duplication_T2 (x : ℂ) (hx : ‖x‖ < 1) :
    T2 x ^ 2 = 2 * T2 (x ^ 2) * T3 (x ^ 2) :=
  theta2_chain x hx (summable_pow_mul_pair x hx)
    (theta2_even_sum x (norm_sq_lt_one x hx)) (theta2_odd_sum x (norm_sq_lt_one x hx))

/-- **Theta duplication formulas.**  Collected statement of the three identities. -/
theorem theta_duplication (x : ℂ) (hx : ‖x‖ < 1) :
    T3 x ^ 2 = T3 (x ^ 2) ^ 2 + x * T2 (x ^ 2) ^ 2 ∧
    T4 x ^ 2 = T3 (x ^ 2) ^ 2 - x * T2 (x ^ 2) ^ 2 ∧
    T2 x ^ 2 = 2 * T2 (x ^ 2) * T3 (x ^ 2) :=
  ⟨theta_duplication_T3 x hx, theta_duplication_T4 x hx, theta_duplication_T2 x hx⟩

end

end Work.Haupt
