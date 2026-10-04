import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The matrix `bmat v (id2 ∧ id2)` is `2(∑vᵢ²)·id − 2·v⊗v`

`knProd (id2 n) (id2 n) = 2 • Iso n` is twice the identity curvature operator, so contracting two
of its indices with a vector `v` gives the `(0,2)`-tensor `2(∑ᵢ vᵢ²)·δ − 2 v⊗v`.

Concretely, `knProd (id2 n) (id2 n) i p j q = 2 (δ_{ip} δ_{jq} − δ_{iq} δ_{pj})`, and the two
Kronecker contractions evaluate to `δ_{pq} ∑ᵢ vᵢ²` and `v_q v_p` respectively.
-/

namespace Work.Diff.Alg.Pinch

open Finset

theorem bmat_knProd_id2_id2 (n : ℕ) (v : Fin n → ℝ) (p q : Fin n) :
    Work.Diff.Alg.Pinch.bmat v (Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.id2 n)
        (Work.Diff.Alg.Pinch.id2 n)) p q
      = 2 * (∑ i, v i * v i) * (if p = q then 1 else 0) - 2 * v p * v q := by
  -- Components of `knProd (id2 n) (id2 n)`.
  have hT : ∀ i j : Fin n,
      knProd (id2 n) (id2 n) i p j q
      = 2 * ((if i = j then (1:ℝ) else 0) * (if p = q then (1:ℝ) else 0)
          - (if i = q then (1:ℝ) else 0) * (if p = j then (1:ℝ) else 0)) := by
    intro i j
    simp only [knProd, id2]
    split_ifs <;> ring
  -- Kronecker contractions.
  have hdeltaL : ∀ (w : Fin n → ℝ) (a : Fin n),
      (∑ i, w i * (if i = a then (1:ℝ) else 0)) = w a := by
    intro w a
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp only [hb, ite_false, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hdeltaR : ∀ (w : Fin n → ℝ) (a : Fin n),
      (∑ i, w i * (if a = i then (1:ℝ) else 0)) = w a := by
    intro w a
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp only [show ¬ (a = b) from fun h => hb h.symm, ite_false, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  -- The two contracted sums.
  have hX : (∑ i : Fin n, ∑ j : Fin n,
        v i * v j * ((if i = j then (1:ℝ) else 0) * (if p = q then (1:ℝ) else 0)))
      = (∑ i, v i * v i) * (if p = q then (1:ℝ) else 0) := by
    rw [show (∑ i : Fin n, ∑ j : Fin n,
          v i * v j * ((if i = j then (1:ℝ) else 0) * (if p = q then (1:ℝ) else 0)))
        = ∑ i : Fin n,
            (∑ j, v i * v j * (if i = j then (1:ℝ) else 0))
              * (if p = q then (1:ℝ) else 0) from by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; ring]
    have hinner : ∀ i : Fin n,
        (∑ j, v i * v j * (if i = j then (1:ℝ) else 0)) = v i * v i :=
      fun i => hdeltaR (fun j => v i * v j) i
    simp only [hinner]
    rw [Finset.sum_mul]
  have hY : (∑ i : Fin n, ∑ j : Fin n,
        v i * v j * ((if i = q then (1:ℝ) else 0) * (if p = j then (1:ℝ) else 0)))
      = v q * v p := by
    have hinner : ∀ i : Fin n,
        (∑ j, v i * v j * ((if i = q then (1:ℝ) else 0) * (if p = j then (1:ℝ) else 0)))
        = (v i * (if i = q then (1:ℝ) else 0)) * v p := by
      intro i
      rw [show (∑ j, v i * v j * ((if i = q then (1:ℝ) else 0) * (if p = j then (1:ℝ) else 0)))
          = (v i * (if i = q then (1:ℝ) else 0))
              * (∑ j, v j * (if p = j then (1:ℝ) else 0)) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring]
      rw [hdeltaR v p]
    simp only [hinner]
    rw [← Finset.sum_mul, hdeltaL v q]
  -- Split the inner sum into the two Kronecker pieces.
  have hstep : ∀ i : Fin n,
      (∑ j, v i * v j * (2 * ((if i = j then (1:ℝ) else 0) * (if p = q then (1:ℝ) else 0)
          - (if i = q then (1:ℝ) else 0) * (if p = j then (1:ℝ) else 0))))
      = 2 * (∑ j, v i * v j * ((if i = j then (1:ℝ) else 0)
            * (if p = q then (1:ℝ) else 0)))
        - 2 * (∑ j, v i * v j * ((if i = q then (1:ℝ) else 0)
            * (if p = j then (1:ℝ) else 0))) := by
    intro i
    rw [show (∑ j, v i * v j * (2 * ((if i = j then (1:ℝ) else 0)
            * (if p = q then (1:ℝ) else 0)
          - (if i = q then (1:ℝ) else 0) * (if p = j then (1:ℝ) else 0))))
        = ∑ j, (2 * (v i * v j * ((if i = j then (1:ℝ) else 0)
              * (if p = q then (1:ℝ) else 0)))
            - 2 * (v i * v j * ((if i = q then (1:ℝ) else 0)
              * (if p = j then (1:ℝ) else 0)))) from by
      apply Finset.sum_congr rfl; intro j _; ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [bmat, hT]
  simp only [hstep]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hX, hY]
  ring

end Work.Diff.Alg.Pinch
