import Mathlib
import Submission.Work.WilCrux.SphereChoiceDefs
import Submission.Work.WilG0.API
import Submission.Work.WilCrux.omega_poly_le_two

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-!
# The "radius bound" set of the sphere-choice problem

`SphereChoiceLeTail` states that the set
`{y : ℝ^{m+1} | ‖Fin.tail y‖ ≤ y 0}` — a point `(τ, z)` with `‖z‖ ≤ τ` — is `Ω`-definable
with format `m + 5` and degree `2m + 2`.

The norm on `Fin m → ℝ` is the sup norm, so for `τ ≥ 0`

`‖z‖ ≤ τ  ↔  ∀ i, |z i| ≤ τ  ↔  τ ≥ 0 ∧ ∀ i, (z i)² ≤ τ²`.

Accordingly the set is the intersection of

* the closed half-space `{y | 0 ≤ y 0}` (a *linear* sublevel set), and
* for each of the `m` tail coordinates, the cone piece `{y | (y (Fin.succ i))² ≤ (y 0)²}`,
  a *quadratic* sublevel set.

Each of these `m + 1` sets lies in `S.Ω (m + 3) 2 (m + 1)`
(`omega_poly_le_two`: format `n + 2 = m + 3`, degree `2`; note that the naive bound
`Omega.omega_poly_le` would charge `totalDegree + 2 = 4` per factor and overshoot the degree
budget by a factor of two — the whole point of the tighter `n + 2` / `2` bound).  The
intersection over the `m` tail coordinates costs one format (giving `m + 4`) and sums the
degrees (giving `2m`), and intersecting with the half-space costs one more format and degree
`2`, giving exactly `Ω (m + 5) (2m + 2) (m + 1)`.
-/

/-- The set of points `(τ, z) ∈ ℝ^{m+1}` with `‖z‖ ≤ τ` is `Ω`-definable with format `m + 5`
and degree `2m + 2`. -/
theorem SphereChoiceLeTail (S : WilkiesDesign.SOMin) (m : ℕ) :
    {y : Fin (m + 1) → ℝ | ‖Fin.tail y‖ ≤ y 0} ∈ S.Ω (m + 5) (2 * m + 2) (m + 1) := by
  -- the closed half-space `{0 ≤ y 0}`
  have hB1 : {y : Fin (m + 1) → ℝ | 0 ≤ y 0} ∈ S.Ω ((m + 1) + 2) 2 (m + 1) := by
    have h := omega_poly_le_two S (m + 1) (- MvPolynomial.X (0 : Fin (m + 1)))
      (by rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_X]; norm_num)
    have hset : {x : Fin (m + 1) → ℝ |
          (- MvPolynomial.X (0 : Fin (m + 1)) : MvPolynomial (Fin (m + 1)) ℝ).eval x ≤ 0}
        = {y : Fin (m + 1) → ℝ | 0 ≤ y 0} := by
      ext x
      simp only [Set.mem_ofPred_eq, MvPolynomial.eval_neg, MvPolynomial.eval_X]
      constructor <;> intro h <;> linarith
    rwa [hset] at h
  -- the cone pieces `{(y (succ i))² ≤ (y 0)²}`
  have hFi : ∀ i : Fin m,
      {y : Fin (m + 1) → ℝ | (y (Fin.succ i)) ^ 2 ≤ (y 0) ^ 2} ∈ S.Ω ((m + 1) + 2) 2 (m + 1) := by
    intro i
    have hdeg : (MvPolynomial.X (Fin.succ i) ^ 2 -
        MvPolynomial.X (0 : Fin (m + 1)) ^ 2 : MvPolynomial (Fin (m + 1)) ℝ).totalDegree ≤ 2 := by
      refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_) <;>
        rw [MvPolynomial.totalDegree_X_pow]
    have h := omega_poly_le_two S (m + 1)
      (MvPolynomial.X (Fin.succ i) ^ 2 - MvPolynomial.X (0 : Fin (m + 1)) ^ 2) hdeg
    have hset : {x : Fin (m + 1) → ℝ | (MvPolynomial.X (Fin.succ i) ^ 2 -
          MvPolynomial.X (0 : Fin (m + 1)) ^ 2 : MvPolynomial (Fin (m + 1)) ℝ).eval x ≤ 0}
        = {y : Fin (m + 1) → ℝ | (y (Fin.succ i)) ^ 2 ≤ (y 0) ^ 2} := by
      ext x
      simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
        MvPolynomial.eval_X]
      constructor <;> intro h <;> linarith
    rwa [hset] at h
  -- intersect the `m` cone pieces
  have hB2 : (⋂ i : Fin m, {y : Fin (m + 1) → ℝ | (y (Fin.succ i)) ^ 2 ≤ (y 0) ^ 2})
      ∈ S.Ω ((m + 1) + 3) (2 * m) (m + 1) := by
    have h := S.inter (F := (m + 1) + 2) (n := m + 1) (k := m) (fun _ : Fin m => 2)
      (fun i : Fin m => {y : Fin (m + 1) → ℝ | (y (Fin.succ i)) ^ 2 ≤ (y 0) ^ 2})
      (fun i => hFi i)
    have hsum : (∑ _ : Fin m, (2 : ℕ)) = 2 * m := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]
    rw [hsum] at h
    exact h
  -- the half-space, at the common format
  have hB1' : {y : Fin (m + 1) → ℝ | 0 ≤ y 0} ∈ S.Ω ((m + 1) + 3) 2 (m + 1) :=
    Work.WilG0.Omega_mono_F (S := S) (by omega) hB1
  have hinter := Work.WilG0.Omega_inter2 (S := S) hB1' hB2
  -- the two descriptions agree
  have hset : {y : Fin (m + 1) → ℝ | 0 ≤ y 0} ∩
      (⋂ i : Fin m, {y : Fin (m + 1) → ℝ | (y (Fin.succ i)) ^ 2 ≤ (y 0) ^ 2})
      = {y : Fin (m + 1) → ℝ | ‖Fin.tail y‖ ≤ y 0} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · -- `‖z‖ ≤ τ` from `τ ≥ 0` and the coordinate bounds `(z i)² ≤ τ²`
      rintro ⟨h0, htail⟩
      rw [pi_norm_le_iff_of_nonneg h0]
      intro i
      have h2 : ‖Fin.tail y i‖ = |y (Fin.succ i)| := by rw [Real.norm_eq_abs]; rfl
      rw [h2]
      have hsq : |y (Fin.succ i)| ^ 2 ≤ |y 0| ^ 2 := by
        rw [sq_abs, sq_abs]
        exact htail i
      have h5 : |y (Fin.succ i)| ≤ |y 0| := by
        simpa only [abs_abs] using sq_le_sq.mp hsq
      exact le_trans h5 (le_of_eq (abs_of_nonneg h0))
    · -- conversely `‖z‖ ≤ τ` gives `τ ≥ 0` and every coordinate bound
      intro h
      have h0 : 0 ≤ y 0 := le_trans (norm_nonneg (Fin.tail y)) h
      refine ⟨h0, fun i => ?_⟩
      have h1 : ‖Fin.tail y i‖ ≤ ‖Fin.tail y‖ := norm_le_pi_norm _ i
      have h2 : ‖Fin.tail y i‖ = |y (Fin.succ i)| := by rw [Real.norm_eq_abs]; rfl
      have h3 : |y (Fin.succ i)| ≤ y 0 := by rw [h2] at h1; linarith
      have h4 : |y (Fin.succ i)| ^ 2 ≤ (y 0) ^ 2 := by
        simpa only [sq] using mul_self_le_mul_self (abs_nonneg (y (Fin.succ i))) h3
      rwa [sq_abs] at h4
  rw [hset] at hinter
  exact Work.WilG0.Omega_mono_FD (S := S) (by omega) (by omega) hinter

end Work.WilCrux
