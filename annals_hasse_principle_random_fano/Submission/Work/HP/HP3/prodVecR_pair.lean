import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HP3.VeroProdDefs
import Submission.Work.HP.HP3.VeroProdExtra
import Submission.Work.HP.HP3.cond_iff_eq_addE

/-!
# The coefficient vector of `X^m · ⟨c,X⟩` on a difference of two coordinate vectors

`Work.HP.prodVec d n m c` is the coefficient vector of the degree-`d` form `X^m · ⟨c,X⟩`.  This
file records its behaviour on the two-term vector `Pi.single j a - Pi.single i₀ b`: the result is
the two-term vector `a • e_{m+e_j} - b • e_{m+e_i₀}` in the monomial basis.

The proof is a short computation from the explicit description of `prodVec` (see
`Work.HP.HP3.cond_iff_eq_addE`) plus the fact that `prodVec` is additive in `c`.
-/

namespace Work.HP.HP3

set_option linter.unusedVariables false

open Finset

/-- The `m'`-coordinate of `prodVec d n m c` is `c k` when `m' = m + e_k` and `0` otherwise.  This
rewrites the "test condition" appearing in the definition of `prodVec` as the equality
`m' = addE d n hd m k`. -/
lemma prodVec_apply (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) (c : Fin (n + 1) → ℤ)
    (m' : Mon d n) :
    prodVec d n m c m' = ∑ k : Fin (n + 1), if m' = addE d n hd m k then c k else 0 := by
  unfold prodVec
  exact Finset.sum_congr rfl fun k _ => by
    simp only [cond_iff_eq_addE d n hd m k m']

/-- `prodVec` on a coordinate vector `Pi.single j a` (i.e. `X^m · a X_j`) is the coordinate vector
`a • e_{m+e_j}`. -/
lemma prodVec_single (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) (j : Fin (n + 1)) (a : ℤ)
    (m' : Mon d n) :
    prodVec d n m (Pi.single j a) m' = if m' = addE d n hd m j then a else 0 := by
  rw [prodVec_apply d n hd m (Pi.single j a) m']
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `prodVec` is additive in the linear form `c`. -/
lemma prodVec_sub (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) (c c' : Fin (n + 1) → ℤ)
    (m' : Mon d n) :
    prodVec d n m (c - c') m' = prodVec d n m c m' - prodVec d n m c' m' := by
  rw [prodVec_apply d n hd m (c - c') m', prodVec_apply d n hd m c m',
    prodVec_apply d n hd m c' m', ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : m' = addE d n hd m k
  · simp [h]
  · simp [h]

theorem prodVecR_pair (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) (x : Fin (n + 1) → ℤ)
    (i₀ j : Fin (n + 1)) (hji : j ≠ i₀) :
    prodVecR d n m (Pi.single j (x i₀) - Pi.single i₀ (x j))
      = (x i₀ : ℝ) • Pi.single (addE d n hd m j) (1 : ℝ)
        - (x j : ℝ) • Pi.single (addE d n hd m i₀) (1 : ℝ) := by
  funext m'
  simp only [prodVecR, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [prodVec_sub d n hd m (Pi.single j (x i₀)) (Pi.single i₀ (x j)) m']
  rw [prodVec_single d n hd m j (x i₀) m', prodVec_single d n hd m i₀ (x j) m']
  by_cases hA : m' = addE d n hd m j <;> by_cases hB : m' = addE d n hd m i₀ <;>
    simp_all

end Work.HP.HP3
