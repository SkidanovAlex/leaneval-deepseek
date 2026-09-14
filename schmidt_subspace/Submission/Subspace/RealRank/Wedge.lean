import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.det_norm_le_factorial_prod
import Submission.Commons.LinearAlgebra.Matrix.det_compound_ne_zero

/-!
# The wedge (compound) box: bounds for the values of the compound forms

Let `M : Matrix (Fin N) (Fin N) ℝ` be an invertible real system, `V : Matrix (Fin N) (Fin N) ℝ`
a matrix of "straightened" real vectors, and `lam c : Fin N → ℝ` with `lam ≥ 0`, `C ≥ 0`,
`Q > 0` such that

`|∑ i, M t i * V i j| ≤ C * min (lam t) (lam j) * Q ^ (c t)`

for all `t j` (the conclusion of the straightening lemma `graded_basis_real`).  This file proves
the corresponding bound for the entries of the compound (wedge) matrix `compound r (M * V)`:
for `r`-element index sets `T`, `S`,

`|det ((M*V).submatrix T S)| ≤ r! * C^r * (∏_{t ∈ T} lam t) * Q ^ (∑_{t ∈ T} c t)`,

and the sharpened version for the case that the minima on `T` are all `≥ low` while some index
of `S` has minimum `≤ high` (the product gains a factor `high / low`; in the application
`low = λ_{k+1}`, `high = λ_k`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Matrix

namespace Submission.Subspace.RealRank

variable {N : ℕ}

private lemma sign_abs_eq_one (r : ℕ) (σ : Equiv.Perm (Fin r)) :
    |(((Equiv.Perm.sign σ : ℤ) : ℝ))| = 1 := by
  rw [← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]

/-- **The Leibniz bound for a compound entry.** -/
theorem compound_det_abs_le {r : ℕ}
    (M V : Matrix (Fin N) (Fin N) ℝ) (lam c : Fin N → ℝ)
    (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C) (hlam0 : ∀ t, 0 ≤ lam t)
    (hbound : ∀ t j : Fin N, |∑ i, M t i * V i j| ≤ C * min (lam t) (lam j) * Q ^ (c t))
    (T S : Finset (Fin N)) (hT : T.card = r) (hS : S.card = r) :
    |((M * V).submatrix (T.orderEmbOfFin hT) (S.orderEmbOfFin hS)).det| ≤
      (Nat.factorial r : ℝ) * C ^ r * (∏ a : Fin r, lam (T.orderEmbOfFin hT a)) *
        Q ^ (∑ a : Fin r, c (T.orderEmbOfFin hT a)) := by
  classical
  set e := T.orderEmbOfFin hT with he
  set f := S.orderEmbOfFin hS with hf
  set B : ℝ := C ^ r * (∏ a : Fin r, lam (e a)) * Q ^ (∑ a : Fin r, c (e a)) with hB
  have hmem : ∀ (a b : Fin r),
      (((M * V).submatrix e f) a b) = ∑ i : Fin N, M (e a) i * V i (f b) := by
    intro a b
    rw [Matrix.submatrix_apply, Matrix.mul_apply]
  have hterm : ∀ σ : Equiv.Perm (Fin r),
      |(((Equiv.Perm.sign σ : ℤ) : ℝ)) *
        ∏ i : Fin r, (((M * V).submatrix e f) (σ i) i)| ≤ B := by
    intro σ
    rw [abs_mul, sign_abs_eq_one r σ, one_mul, Finset.abs_prod]
    have hstep : ∀ i : Fin r,
        |((M * V).submatrix e f) (σ i) i|
          ≤ C * min (lam (e (σ i))) (lam (f i)) * Q ^ (c (e (σ i))) := by
      intro i
      rw [hmem]
      exact hbound _ _
    calc ∏ i : Fin r, |((M * V).submatrix e f) (σ i) i|
        ≤ ∏ i : Fin r, (C * min (lam (e (σ i))) (lam (f i)) * Q ^ (c (e (σ i)))) :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hstep i)
      _ = C ^ r * (∏ i : Fin r, min (lam (e (σ i))) (lam (f i))) *
            Q ^ (∑ i : Fin r, c (e (σ i))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin, Real.rpow_sum_of_pos hQ]
      _ ≤ C ^ r * (∏ i : Fin r, lam (e i)) * Q ^ (∑ i : Fin r, c (e i)) := by
          have hCpow : 0 ≤ C ^ r := pow_nonneg hC r
          have hQexp : 0 < Q ^ (∑ i : Fin r, c (e i)) := Real.rpow_pos_of_pos hQ _
          have hmin : (∏ i : Fin r, min (lam (e (σ i))) (lam (f i)))
              ≤ ∏ i : Fin r, lam (e i) := by
            calc ∏ i : Fin r, min (lam (e (σ i))) (lam (f i))
                ≤ ∏ i : Fin r, lam (e (σ i)) :=
                  Finset.prod_le_prod (fun i _ => le_min (hlam0 _) (hlam0 _))
                    (fun i _ => min_le_left _ _)
              _ = ∏ i : Fin r, lam (e i) := Equiv.prod_comp σ (fun i => lam (e i))
          have hcsum : (∑ i : Fin r, c (e (σ i))) = ∑ i : Fin r, c (e i) :=
            Equiv.sum_comp σ (fun i => c (e i))
          rw [hcsum]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmin hCpow) (le_of_lt hQexp)
      _ = B := rfl
  rw [Matrix.det_apply']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun σ _ => hterm σ)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    hB]
  refine le_of_eq (by ring)

/-- **The sharpened Leibniz bound.**  If the minima on the index set `T` are all at least `low`
and some index in `S` has minimum at most `high`, then the product of minima in the Leibniz
expansion of the compound entry gains a factor `high / low`. -/
theorem compound_det_abs_le_sharp {r : ℕ}
    (M V : Matrix (Fin N) (Fin N) ℝ) (lam c : Fin N → ℝ)
    (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C) (hlam0 : ∀ t, 0 ≤ lam t)
    (hbound : ∀ t j : Fin N, |∑ i, M t i * V i j| ≤ C * min (lam t) (lam j) * Q ^ (c t))
    (T S : Finset (Fin N)) (hT : T.card = r) (hS : S.card = r)
    (low high : ℝ) (hlow : 0 < low)
    (hTlow : ∀ a : Fin r, low ≤ lam (T.orderEmbOfFin hT a))
    (hShigh : ∃ s ∈ S, lam s ≤ high) :
    |((M * V).submatrix (T.orderEmbOfFin hT) (S.orderEmbOfFin hS)).det| ≤
      (Nat.factorial r : ℝ) * C ^ r * (high / low) *
        (∏ a : Fin r, lam (T.orderEmbOfFin hT a)) *
        Q ^ (∑ a : Fin r, c (T.orderEmbOfFin hT a)) := by
  classical
  set e := T.orderEmbOfFin hT with he
  set f := S.orderEmbOfFin hS with hf
  set P : ℝ := ∏ a : Fin r, lam (e a) with hP
  set B : ℝ := C ^ r * (high / low) * P * Q ^ (∑ a : Fin r, c (e a)) with hB
  have hmem : ∀ (a b : Fin r),
      (((M * V).submatrix e f) a b) = ∑ i : Fin N, M (e a) i * V i (f b) := by
    intro a b
    rw [Matrix.submatrix_apply, Matrix.mul_apply]
  obtain ⟨s, hsS, hslow⟩ := hShigh
  obtain ⟨b, hb⟩ : ∃ b : Fin r, f b = s := by
    have h1 : s ∈ Set.range (⇑(S.orderEmbOfFin hS)) := by
      rw [Finset.range_orderEmbOfFin]; exact hsS
    exact h1
  have hterm : ∀ σ : Equiv.Perm (Fin r),
      |(((Equiv.Perm.sign σ : ℤ) : ℝ)) *
        ∏ i : Fin r, (((M * V).submatrix e f) (σ i) i)| ≤ B := by
    intro σ
    rw [abs_mul, sign_abs_eq_one r σ, one_mul, Finset.abs_prod]
    have hstep : ∀ i : Fin r,
        |((M * V).submatrix e f) (σ i) i|
          ≤ C * min (lam (e (σ i))) (lam (f i)) * Q ^ (c (e (σ i))) := by
      intro i
      rw [hmem]
      exact hbound _ _
    have hP0 : 0 ≤ P := by rw [hP]; exact Finset.prod_nonneg (fun i _ => hlam0 _)
    have hmin : (∏ i : Fin r, min (lam (e (σ i))) (lam (f i))) ≤ (high / low) * P := by
      rw [hP]
      have hprod := Finset.prod_erase_mul (Finset.univ : Finset (Fin r))
        (fun i => min (lam (e (σ i))) (lam (f i))) (Finset.mem_univ b)
      rw [← hprod]
      have h1 : min (lam (e (σ b))) (lam (f b)) ≤ high := by
        rw [hb]
        exact le_trans (min_le_right _ _) hslow
      have h2 : (∏ i ∈ Finset.univ.erase b, min (lam (e (σ i))) (lam (f i)))
          ≤ (∏ a : Fin r, lam (e a)) / low := by
        have h3 : (∏ i ∈ Finset.univ.erase b, min (lam (e (σ i))) (lam (f i)))
            ≤ ∏ i ∈ Finset.univ.erase b, lam (e (σ i)) :=
          Finset.prod_le_prod (fun i _ => le_min (hlam0 _) (hlam0 _))
            (fun i _ => min_le_left _ _)
        refine h3.trans ?_
        have h4 : (∏ i ∈ Finset.univ.erase b, lam (e (σ i)))
            = (∏ a : Fin r, lam (e a)) / lam (e (σ b)) := by
          have h5 := Finset.prod_erase_mul (Finset.univ : Finset (Fin r))
            (fun i => lam (e (σ i))) (Finset.mem_univ b)
          have h6 : (∏ i : Fin r, lam (e (σ i))) = ∏ a : Fin r, lam (e a) :=
            Equiv.prod_comp σ (fun i => lam (e i))
          rw [h6] at h5
          have hne : lam (e (σ b)) ≠ 0 := ne_of_gt (lt_of_lt_of_le hlow (hTlow (σ b)))
          rw [eq_div_iff hne]
          exact h5
        rw [h4]
        exact div_le_div_of_nonneg_left (by rw [← hP]; exact hP0) hlow (hTlow (σ b))
      have hhigh0 : 0 ≤ high := le_trans (hlam0 s) hslow
      calc (∏ i ∈ Finset.univ.erase b, min (lam (e (σ i))) (lam (f i))) *
            min (lam (e (σ b))) (lam (f b))
          ≤ ((∏ a : Fin r, lam (e a)) / low) * high :=
            mul_le_mul h2 h1 (le_min (hlam0 (e (σ b))) (hlam0 (f b)))
              (div_nonneg (Finset.prod_nonneg (fun i _ => hlam0 _)) (le_of_lt hlow))
        _ = (high / low) * (∏ a : Fin r, lam (e a)) := by ring
    calc ∏ i : Fin r, |((M * V).submatrix e f) (σ i) i|
        ≤ ∏ i : Fin r, (C * min (lam (e (σ i))) (lam (f i)) * Q ^ (c (e (σ i)))) :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hstep i)
      _ = C ^ r * (∏ i : Fin r, min (lam (e (σ i))) (lam (f i))) *
            Q ^ (∑ i : Fin r, c (e (σ i))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin, Real.rpow_sum_of_pos hQ]
      _ ≤ C ^ r * ((high / low) * P) * Q ^ (∑ i : Fin r, c (e i)) := by
          have hcsum : (∑ i : Fin r, c (e (σ i))) = ∑ i : Fin r, c (e i) :=
            Equiv.sum_comp σ (fun i => c (e i))
          rw [hcsum]
          have hCpow : 0 ≤ C ^ r := pow_nonneg hC r
          have hQexp : 0 < Q ^ (∑ i : Fin r, c (e i)) := Real.rpow_pos_of_pos hQ _
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmin hCpow) (le_of_lt hQexp)
      _ = B := by rw [hB]; ring
  rw [Matrix.det_apply']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun σ _ => hterm σ)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    hB]
  refine le_of_eq (by ring)

end Submission.Subspace.RealRank
