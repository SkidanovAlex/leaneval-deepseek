import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The squared Frobenius norm of the Ricci tensor of the Böhm–Wilking transform `ell a 1/2`

`Work.Diff.Alg.Pinch.ric_ell_aux` computes the Ricci tensor of the Böhm–Wilking transform
`ell a b`:

`ric (ell a b R) i j = (1 + (n-2)b) · Ric₀ R i j + (scal R (1 + 2(n-1)a)/n) · δᵢⱼ`.

At `b = 1/2` this is a rank-one (multiple of the identity) perturbation of `(1 + (n-2)/2) · Ric₀ R`.
The traceless Ricci tensor has vanishing trace (`ric0_trace_zero`), so the cross term in the sum of
squares drops out and one obtains the Frobenius norm identity

`|Ric(ell a (1/2) R)|² = (1 + (n-2)/2)² |Ric₀ R|² + (scal R (1 + 2(n-1)a)/n)² · n`,

which is the statement proved below.

The combinatorial content is isolated in `sum_sum_sq_add_diag`: for a matrix `A` with vanishing
trace, `∑ᵢⱼ (k·Aᵢⱼ + c·δᵢⱼ)² = k² ∑ᵢⱼ Aᵢⱼ² + c²·n`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- Contracting one index of a matrix with the identity matrix extracts the diagonal:
`∑ᵢⱼ Aᵢⱼ · δᵢⱼ = ∑ᵢ Aᵢᵢ`. -/
lemma sum_sum_ite_diag_mul (A : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, A i j * (if i = j then (1 : ℝ) else 0)) = ∑ i, A i i := by
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg (fun h : i = j => hj h.symm)]
    ring
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The sum of the squares of the entries of the identity matrix is the dimension:
`∑ᵢⱼ δᵢⱼ² = n`. -/
lemma sum_sum_ite_diag_sq :
    (∑ i : Fin n, ∑ j, ((if i = j then (1 : ℝ) else 0)) ^ 2) = (n : ℝ) := by
  have h : ∀ i : Fin n, (∑ j, ((if i = j then (1 : ℝ) else 0)) ^ 2) = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; rw [if_neg (fun h : i = j => hj h.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Pull a constant out of a double sum: `∑ᵢⱼ k · Aᵢⱼ = k ∑ᵢⱼ Aᵢⱼ`. -/
lemma sum_sum_const_mul (k : ℝ) (A : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, k * A i j) = k * (∑ i, ∑ j, A i j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]

/-- **Sum of squares of a rank-one perturbation of a traceless matrix.**
For `A` with `∑ᵢ Aᵢᵢ = 0`,
`∑ᵢⱼ (k·Aᵢⱼ + c·δᵢⱼ)² = k² ∑ᵢⱼ Aᵢⱼ² + c²·n`. The cross term `2kc ∑ᵢⱼ Aᵢⱼ δᵢⱼ = 2kc ∑ᵢ Aᵢᵢ`
vanishes by the trace hypothesis. -/
lemma sum_sum_sq_add_diag (A : Fin n → Fin n → ℝ) (k c : ℝ) (hA : ∑ i, A i i = 0) :
    (∑ i, ∑ j, (k * A i j + c * (if i = j then (1 : ℝ) else 0))
        * (k * A i j + c * (if i = j then (1 : ℝ) else 0)))
      = k ^ 2 * (∑ i, ∑ j, A i j * A i j) + c ^ 2 * (n : ℝ) := by
  set d : Fin n → Fin n → ℝ := fun i j => (if i = j then (1 : ℝ) else 0) with hd
  have h1 : ∀ i j : Fin n,
      (k * A i j + c * d i j) * (k * A i j + c * d i j)
      = k ^ 2 * (A i j * A i j) + (2 * k * c) * (A i j * d i j) + c ^ 2 * (d i j) ^ 2 := by
    intro i j; ring
  have hdA : (∑ i, ∑ j, A i j * d i j) = ∑ i, A i i := by
    simp only [hd]; exact sum_sum_ite_diag_mul A
  have hdd : (∑ i, ∑ j, (d i j) ^ 2) = (n : ℝ) := by
    simp only [hd]; exact sum_sum_ite_diag_sq (n := n)
  have e1 : (∑ i, ∑ j, k ^ 2 * (A i j * A i j)) = k ^ 2 * (∑ i, ∑ j, A i j * A i j) :=
    sum_sum_const_mul (k ^ 2) (fun i j => A i j * A i j)
  have e2 : (∑ i, ∑ j, (2 * k * c) * (A i j * d i j)) = 0 := by
    rw [sum_sum_const_mul (2 * k * c) (fun i j => A i j * d i j), hdA, hA, mul_zero]
  have e3 : (∑ i, ∑ j, c ^ 2 * (d i j) ^ 2) = c ^ 2 * (n : ℝ) :=
    (sum_sum_const_mul (c ^ 2) (fun i j => (d i j) ^ 2)).trans (by rw [hdd])
  have key : (∑ i, ∑ j,
        (k ^ 2 * (A i j * A i j) + (2 * k * c) * (A i j * d i j) + c ^ 2 * (d i j) ^ 2))
      = k ^ 2 * (∑ i, ∑ j, A i j * A i j) + c ^ 2 * (n : ℝ) := by
    simp only [Finset.sum_add_distrib]
    rw [e1, e2, e3]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h1 i j))]
  exact key

/-- **Frobenius norm of the Ricci tensor of `ell a (1/2)`.** Combining `ric_ell_aux` at `b = 1/2`
with the vanishing trace of the traceless Ricci tensor and `sum_sum_sq_add_diag`. -/
theorem sum_ricE_sq (n : ℕ) {a : ℝ} {S : Submission.Diff.Alg.Curv4 n}
    (hS : Submission.Diff.Alg.IsAlgCurv S) :
    (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric (Work.Diff.Alg.Pinch.ell a (1 / 2) S) i j
        * Work.Diff.Alg.Pinch.ric (Work.Diff.Alg.Pinch.ell a (1 / 2) S) i j)
      = (1 + ((n : ℝ) - 2) * (1 / 2)) ^ 2
          * (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric0 S i j * Work.Diff.Alg.Pinch.ric0 S i j)
        + (Submission.Diff.Alg.scalAlg S * (1 + 2 * ((n : ℝ) - 1) * a) / (n : ℝ)) ^ 2 * (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
    have hric : ∀ i j : Fin n, ric (ell a (1 / 2) S) i j
        = (1 + ((n : ℝ) - 2) * (1 / 2)) * ric0 S i j
          + (scalAlg S * (1 + 2 * ((n : ℝ) - 1) * a) / (n : ℝ))
              * (if i = j then (1 : ℝ) else 0) :=
      fun i j => ric_ell_aux a (1 / 2) hn hS i j
    have htrace : ∑ i, ric0 S i i = 0 := ric0_trace_zero S hS
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hric i j]))]
    exact sum_sum_sq_add_diag (ric0 S) (1 + ((n : ℝ) - 2) * (1 / 2))
      (scalAlg S * (1 + 2 * ((n : ℝ) - 1) * a) / (n : ℝ)) htrace

end Work.Diff.Alg.Pinch
