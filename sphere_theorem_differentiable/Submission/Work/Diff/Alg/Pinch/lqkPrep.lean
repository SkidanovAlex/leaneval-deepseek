import Mathlib
import Submission.Work.Diff.Alg.Pinch.lqkDefs
import Submission.Work.Diff.Alg.Pinch.lqkSums
import Submission.Work.Diff.Alg.Pinch.lqk_Q_knProd
import Submission.Work.Diff.Alg.Pinch.ric_knProd_id2
import Submission.Work.Diff.Alg.Pinch.scalAlg_knProd
import Submission.Work.Diff.Alg.Pinch.scalAlg_Q
import Submission.Work.Diff.Alg.Pinch.ric_Q

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Preparatory algebra for the Böhm–Wilking identity on `A ∧ id`

Helpers for `Work.Diff.Alg.Pinch.linv_Q_ell_knProd`: the affine behaviour of `trT`, `sqT`, `frobT`,
the Ricci/traceless data of `knProd A (id2 n)`, Hamilton's `Q` on `knProd A (id2 n)`, and the
action of the Böhm–Wilking transform `ell a b` on `knProd A (id2 n)`.

Notation (all indexed by `Fin n`, with `R i j k l = ⟪R(eᵢ,eⱼ)eₗ, eₖ⟫`):
`id2` the Kronecker delta, `knProd` the Kulkarni–Nomizu product (no factor `1/2`), `sqT A = A * A`
the matrix square, `trT A` the trace, `frobT A` the squared Frobenius norm, `traceless A = A - (tr A / n) • id2`,
`ric`, `ric0`, `ric0sq`, `ric0Frob2` the Ricci data, and `Submisssion.Diff.Alg.Q` Hamilton's quadratic term.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}



lemma lqk_knProd_I_left (A : Fin n → Fin n → ℝ) :
    knProd (id2 n) A = knProd A (id2 n) := by
  funext i j k l
  simp only [knProd]
  ring

lemma lqk_sum_const (c : ℝ) : (∑ _i : Fin n, c) = (n : ℝ) * c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma lqk_trT_affine {A : Fin n → Fin n → ℝ} (c μ : ℝ) :
    trT (c • A + μ • (id2 n)) = c * trT A + μ * (n : ℝ) := by
  rw [trT_apply, trT_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, lqk_sum_delta_diag]

lemma lqk_sqT_affine {A : Fin n → Fin n → ℝ} (c μ : ℝ) :
    sqT (c • A + μ • (id2 n)) = c ^ 2 • sqT A + (2 * c * μ) • A + μ ^ 2 • (id2 n) := by
  funext i j
  rw [sqT_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [sqT_apply]
  have hsplit : (∑ k, (c * A i k + μ * id2 n i k) * (c * A k j + μ * id2 n k j))
      = (∑ k, c * A i k * (c * A k j)) + (∑ k, c * A i k * (μ * id2 n k j))
        + (∑ k, μ * id2 n i k * (c * A k j)) + (∑ k, μ * id2 n i k * (μ * id2 n k j)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [hsplit]
  have h1 : (∑ k, c * A i k * (c * A k j)) = c ^ 2 * ∑ k, A i k * A k j := by
    rw [show (∑ k, c * A i k * (c * A k j)) = c ^ 2 * ∑ k, A i k * A k j from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring]
  have h2 : (∑ k, c * A i k * (μ * id2 n k j)) = c * μ * A i j := by
    rw [show (∑ k, c * A i k * (μ * id2 n k j)) = c * μ * ∑ k, A i k * id2 n k j from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring]
    rw [lqk_sum_mul_id2']
  have h3 : (∑ k, μ * id2 n i k * (c * A k j)) = μ * c * A i j := by
    rw [show (∑ k, μ * id2 n i k * (c * A k j)) = μ * c * ∑ k, id2 n i k * A k j from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring]
    rw [lqk_sum_id2_mul]
  have h4 : (∑ k, μ * id2 n i k * (μ * id2 n k j)) = μ ^ 2 * id2 n i j := by
    rw [show (∑ k, μ * id2 n i k * (μ * id2 n k j)) = μ ^ 2 * ∑ k, id2 n i k * id2 n k j from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring]
    rw [sum_id2_mul_id2]
  rw [h1, h2, h3, h4]
  ring

lemma lqk_frobT_affine {A : Fin n → Fin n → ℝ} (c μ : ℝ) :
    frobT (c • A + μ • (id2 n)) = c ^ 2 * frobT A + 2 * c * μ * trT A + μ ^ 2 * (n : ℝ) := by
  rw [frobT_apply, frobT_apply, trT_apply]
  have hinner : ∀ i : Fin n,
      (∑ j, (c * A i j + μ * id2 n i j) * (c * A i j + μ * id2 n i j))
        = c ^ 2 * (∑ j, A i j * A i j) + 2 * c * μ * A i i + μ ^ 2 := by
    intro i
    have hsplit : (∑ j, (c * A i j + μ * id2 n i j) * (c * A i j + μ * id2 n i j))
        = (∑ j, c * A i j * (c * A i j)) + (∑ j, c * A i j * (μ * id2 n i j))
          + (∑ j, μ * id2 n i j * (c * A i j)) + (∑ j, μ * id2 n i j * (μ * id2 n i j)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hsplit]
    have h1 : (∑ j, c * A i j * (c * A i j)) = c ^ 2 * ∑ j, A i j * A i j := by
      rw [show (∑ j, c * A i j * (c * A i j)) = c ^ 2 * ∑ j, A i j * A i j from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring]
    have h2 : (∑ j, c * A i j * (μ * id2 n i j)) = c * μ * A i i := by
      rw [show (∑ j, c * A i j * (μ * id2 n i j)) = c * μ * ∑ j, A i j * id2 n i j from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring]
      rw [lqk_sum_diag]
    have h3 : (∑ j, μ * id2 n i j * (c * A i j)) = μ * c * A i i := by
      rw [show (∑ j, μ * id2 n i j * (c * A i j)) = μ * c * ∑ j, id2 n i j * A i j from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring]
      rw [lqk_sum_diag']
    have h4 : (∑ j, μ * id2 n i j * (μ * id2 n i j)) = μ ^ 2 := by
      rw [show (∑ j, μ * id2 n i j * (μ * id2 n i j)) = μ ^ 2 * ∑ j, id2 n i j * id2 n i j from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring]
      rw [sum_id2_row (i := i) (j := i), lqk_id2_eq_one rfl, mul_one]
    rw [h1, h2, h3, h4]
    ring
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ i, ∑ j, (c * A i j + μ * id2 n i j) * (c * A i j + μ * id2 n i j))
      = ∑ i, (c ^ 2 * (∑ j, A i j * A i j) + 2 * c * μ * A i i + μ ^ 2) from
    Finset.sum_congr rfl (fun i _ => hinner i)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [show (∑ i, c ^ 2 * (∑ j, A i j * A i j)) = c ^ 2 * ∑ i, ∑ j, A i j * A i j from by
    rw [Finset.mul_sum]]
  rw [show (∑ i, 2 * c * μ * A i i) = 2 * c * μ * ∑ i, A i i from by
    rw [Finset.mul_sum]]
  rw [lqk_sum_const]
  ring


lemma lqk_knProd_smul_right (c : ℝ) (M N : Fin n → Fin n → ℝ) :
    knProd M (c • N) = c • knProd M N := by
  funext i j k l
  simp only [knProd, Pi.smul_apply, smul_eq_mul]
  ring

lemma lqk_scalAlg_knProd_id2 (A : Fin n → Fin n → ℝ) :
    scalAlg (knProd A (id2 n)) = 2 * (trT A * (n : ℝ) - trT A) := by
  rw [scalAlg_knProd, trT_apply]
  have h1 : (∑ j, id2 n j j) = (n : ℝ) := lqk_sum_delta_diag
  have h2 : (∑ i, ∑ j, A i j * id2 n j i) = ∑ i, A i i := by
    apply Finset.sum_congr rfl; intro i _
    rw [lqk_sum_mul_id2']
  rw [h1, h2]

lemma lqk_traceless_apply (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    traceless A i j = A i j - (trT A / (n : ℝ)) * id2 n i j := rfl

lemma lqk_ric0_knProd (A : Fin n → Fin n → ℝ) :
    ric0 (knProd A (id2 n)) = ((n : ℝ) - 2) • traceless A := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    funext i j; exact i.elim0
  · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    have hn' : (n : ℝ) ≠ 0 := ne_of_gt hn
    funext i j
    rw [ric0, ric_knProd_id2, lqk_scalAlg_knProd_id2]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [lqk_traceless_apply]
    simp only [id2]
    rw [trT_apply]
    field_simp
    ring

lemma lqk_ric0sq_knProd (A : Fin n → Fin n → ℝ) :
    ric0sq (knProd A (id2 n)) = ((n : ℝ) - 2) ^ 2 • sqT (traceless A) := by
  funext i j
  rw [ric0sq, lqk_ric0_knProd]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [sqT_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _
  ring

lemma lqk_ric0Frob2_knProd (A : Fin n → Fin n → ℝ) :
    ric0Frob2 (knProd A (id2 n)) = ((n : ℝ) - 2) ^ 2 * frobT (traceless A) := by
  rw [ric0Frob2, frobT_apply, lqk_ric0_knProd]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

lemma lqk_scalAlg_Q_knProd {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) :
    scalAlg (Q (knProd A (id2 n)))
      = 2 * (((3 : ℝ) * (n : ℝ) - 4) * trT A ^ 2 + ((n : ℝ) - 2) ^ 2 * frobT A) := by
  have hric : ∀ i j, ric (knProd A (id2 n)) i j = ((n : ℝ) - 2) * A i j + trT A * id2 n i j := by
    intro i j
    rw [ric_knProd_id2, trT_apply]
    simp only [id2]
    ring
  rw [scalAlg_Q n (knProd_isAlgCurv hA (fun i j => id2_symm i j))]
  simp only [hric]
  rw [← frobT_apply]
  rw [show frobT (fun x x_1 => ((n : ℝ) - 2) * A x x_1 + trT A * id2 n x x_1)
      = frobT (((n : ℝ) - 2) • A + trT A • (id2 n : Fin n → Fin n → ℝ)) from rfl]
  rw [lqk_frobT_affine (A := A) ((n : ℝ) - 2) (trT A)]
  ring


lemma lqk_traceless_eq (A : Fin n → Fin n → ℝ) :
    traceless A = (1 : ℝ) • A + (-(trT A / (n : ℝ))) • (id2 n) := by
  funext i j
  rw [lqk_traceless_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma lqk_sqT_traceless (A : Fin n → Fin n → ℝ) :
    sqT (traceless A) = sqT A - (2 * trT A / (n : ℝ)) • A + ((trT A / (n : ℝ)) ^ 2) • (id2 n) := by
  rw [lqk_traceless_eq A, lqk_sqT_affine (A := A) (1 : ℝ) (-(trT A / (n : ℝ)))]
  funext i j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma lqk_frobT_traceless (A : Fin n → Fin n → ℝ) (hn : (n : ℝ) ≠ 0) :
    frobT (traceless A) = frobT A - trT A ^ 2 / (n : ℝ) := by
  rw [lqk_traceless_eq A, lqk_frobT_affine (A := A) (1 : ℝ) (-(trT A / (n : ℝ)))]
  field_simp
  ring

lemma lqk_ric_knProd (A : Fin n → Fin n → ℝ) :
    ric (knProd A (id2 n)) = trT A • (id2 n) + ((n : ℝ) - 2) • A := by
  funext i j
  rw [ric_knProd_id2, trT_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, id2]

lemma lqk_ell_knProd (a b : ℝ) (A : Fin n → Fin n → ℝ) :
    ell a b (knProd A (id2 n))
      = knProd (A + (b * ((n : ℝ) - 2)) • traceless A
          + ((2 * a * ((n : ℝ) - 1) * trT A) / (n : ℝ)) • (id2 n)) (id2 n) := by
  rw [ell, lqk_ric0_knProd, lqk_scalAlg_knProd_id2]
  rw [← knProd_smul_left_linv (b : ℝ) (((n : ℝ) - 2) • traceless A) (id2 n)]
  rw [← knProd_smul_left_linv (a / (n : ℝ) * (2 * (trT A * (n : ℝ) - trT A))) (id2 n) (id2 n)]
  rw [← knProd_add_left_linv, ← knProd_add_left_linv]
  congr 1
  funext i j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring




lemma lqk_ric_knProd_gen (M N : Fin n → Fin n → ℝ) (i j : Fin n) :
    ric (knProd M N) i j = (∑ k, M k k) * N i j - (∑ k, M k j * N i k) - (∑ k, M i k * N k j)
      + (∑ k, N k k) * M i j := by
  rw [ric]
  have hpt : ∀ k : Fin n,
      knProd M N k i k j = M k k * N i j - M k j * N i k - M i k * N k j + M i j * N k k := by
    intro k; simp only [knProd]
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_mul, ← Finset.mul_sum]
  ring

lemma lqk_sqT_id2 : sqT (id2 n) = (id2 n : Fin n → Fin n → ℝ) := by
  funext i j
  rw [sqT_apply, sum_id2_mul_id2]

lemma lqk_sqT_fold (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    (∑ x, A i x * A x j) = sqT A i j := rfl

lemma lqk_sum_A_comm (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    (∑ k, A k j * A i k) = sqT A i j := by
  rw [sqT_apply]
  apply Finset.sum_congr rfl; intro k _
  rw [mul_comm]

lemma lqk_sum_sqT_diag {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) :
    (∑ k, sqT A k k) = frobT A := by
  simp only [frobT_apply, sqT_apply]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro m _
  rw [hA m k]

lemma lqk_sum_id2_mixed (i j : Fin n) :
    (∑ k, id2 n k j * id2 n i k) = id2 n i j := by
  rw [show (∑ k, id2 n k j * id2 n i k) = ∑ k, id2 n j k * id2 n i k from by
    apply Finset.sum_congr rfl; intro k _; rw [id2_symm k j]]
  rw [sum_id2_row j i, id2_symm j i]

lemma lqk_ric_Q_knProd_aux {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) (i j : Fin n) :
    ric (Q (knProd A (id2 n))) i j
      = 2 * (2 * ((n : ℝ) - 2) * trT A * A i j - 2 * ((n : ℝ) - 2) * sqT A i j
             + (trT A ^ 2 + ((n : ℝ) - 2) * frobT A) * id2 n i j) := by
  rw [lqk_Q_knProd n hA]
  rw [two_nsmul]
  simp only [ric_add_linv, ric_sub, ric_smul_linv]
  rw [lqk_ric_knProd_gen A A i j, lqk_ric_knProd_gen A (id2 n) i j,
      lqk_ric_knProd_gen (sqT A) (id2 n) i j, lqk_ric_knProd_gen (id2 n) (id2 n) i j]
  simp only [trT_apply, lqk_sum_A_comm, lqk_sqT_fold, lqk_sqT_id2, lqk_sum_mul_id2, lqk_sum_mul_id2',
    lqk_sum_sqT_diag hA, lqk_sum_id2_mixed, sum_id2_mul_id2, lqk_sum_delta_diag]
  ring


lemma lqk_ric0_Q_knProd {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) (i j : Fin n) :
    ric0 (Q (knProd A (id2 n))) i j
      = (-4 * ((n : ℝ) - 2)) * sqT A i j + (4 * ((n : ℝ) - 2) * trT A) * A i j
        + (2 * (trT A ^ 2 + ((n : ℝ) - 2) * frobT A)
            - 2 * (((3 : ℝ) * (n : ℝ) - 4) * trT A ^ 2 + ((n : ℝ) - 2) ^ 2 * frobT A)
                / (n : ℝ)) * id2 n i j := by
  rw [ric0, lqk_ric_Q_knProd_aux hA, lqk_scalAlg_Q_knProd hA]
  simp only [Pi.sub_apply, Pi.mul_apply, id2]
  ring

lemma lqk_ric0_Q_knProd_fun {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) :
    ric0 (Q (knProd A (id2 n)))
      = (-4 * ((n : ℝ) - 2)) • sqT A + (4 * ((n : ℝ) - 2) * trT A) • A
        + (2 * (trT A ^ 2 + ((n : ℝ) - 2) * frobT A)
            - 2 * (((3 : ℝ) * (n : ℝ) - 4) * trT A ^ 2 + ((n : ℝ) - 2) ^ 2 * frobT A)
                / (n : ℝ)) • (id2 n) := by
  funext i j
  rw [lqk_ric0_Q_knProd hA i j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end Work.Diff.Alg.Pinch
