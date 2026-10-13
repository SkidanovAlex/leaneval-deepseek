/-
  Work.WilE2 — area E2.  Degree bookkeeping for the Khovanskii–Rolle elimination.

  The symbolic derivative `ESys.d` is a derivation, and it never raises the total degree.
  This is what makes the elimination terminate: each elimination step replaces one chain
  function by a new coordinate and adds one equation, raising degrees in a controlled way.
-/
import Submission.Work.WilE2.Defs
import Mathlib.Algebra.MvPolynomial.Degrees

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Classical
namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {σ : Type*} {n r : ℕ}

/-! ## §1. Auxiliary monomial-degree lemmas -/

/-- `X i * ∂ᵢ Q` is a "diagonal" operator in the monomial basis:
its coefficient at `m` is `m i` times the coefficient of `Q` at `m`. -/
theorem coeff_X_mul_pderiv [DecidableEq σ] (j : σ) (Q : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    (MvPolynomial.X j * MvPolynomial.pderiv j Q).coeff m = (m j : ℝ) * Q.coeff m := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial m0 a =>
    rw [MvPolynomial.X_mul_pderiv_monomial, MvPolynomial.smul_monomial,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h; rw [nsmul_eq_mul]
    · simp
  | add p q hp hq =>
    rw [map_add, mul_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]
    ring

/-- Hence `support (X i * ∂ᵢ Q) ⊆ support Q`. -/
theorem support_X_mul_pderiv_subset [DecidableEq σ] (j : σ) (Q : MvPolynomial σ ℝ) :
    (MvPolynomial.X j * MvPolynomial.pderiv j Q).support ⊆ Q.support := by
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  rw [coeff_X_mul_pderiv] at hm
  exact fun h => hm (by rw [h, mul_zero])

/-- `X i * ∂ᵢ Q` does not raise the total degree. -/
theorem totalDegree_X_mul_pderiv_le [DecidableEq σ] (j : σ) (Q : MvPolynomial σ ℝ) :
    (MvPolynomial.X j * MvPolynomial.pderiv j Q).totalDegree ≤ Q.totalDegree :=
  MvPolynomial.totalDegree_le_of_support_subset (support_X_mul_pderiv_subset j Q)

/-- `(m + single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1`. -/
theorem sum_add_single_one (m : σ →₀ ℕ) (i : σ) [DecidableEq σ] :
    (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
  rw [Finsupp.sum_add_index]
  · rw [Finsupp.sum_single_index]; simp
  · intro a _; simp
  · intro a _ b₁ b₂; simp

/-- Differentiating lowers the total degree. -/
theorem pderiv_totalDegree_le [DecidableEq σ] (i : σ) (P : MvPolynomial σ ℝ) :
    (MvPolynomial.pderiv i P).totalDegree ≤ P.totalDegree := by
  rw [MvPolynomial.totalDegree_eq]
  refine Finset.sup_le fun m hm => ?_
  have hm' : m + Finsupp.single i 1 ∈ P.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0
    rw [MvPolynomial.mem_support_iff] at hm
    exact hm (by rw [MvPolynomial.coeff_pderiv, h0, zero_mul])
  have hle := MvPolynomial.le_totalDegree hm'
  rw [sum_add_single_one] at hle
  rw [Finsupp.card_toMultiset]
  have : m.sum (fun x => id) = m.sum (fun _ e => e) := rfl
  rw [this]
  omega

/-! ## §2. `ESys.d` is a derivation and does not raise degree -/

theorem ESys.d_C (S : ESys n r) (i : Fin n) (c : ℝ) :
    S.d i (MvPolynomial.C c) = 0 := by
  simp [ESys.d]

theorem ESys.d_zero (S : ESys n r) (i : Fin n) : S.d i (0 : EPoly n r) = 0 := by
  simp [ESys.d]

theorem ESys.d_add (S : ESys n r) (i : Fin n) (P Q : EPoly n r) :
    S.d i (P + Q) = S.d i P + S.d i Q := by
  simp only [ESys.d, map_add, mul_add, Finset.sum_add_distrib]
  ac_rfl

theorem ESys.d_mul (S : ESys n r) (i : Fin n) (P Q : EPoly n r) :
    S.d i (P * Q) = S.d i P * Q + P * S.d i Q := by
  have key : ∀ (u v : EPoly n r),
      (∑ j : Fin r, MvPolynomial.C (S.a j i) * MvPolynomial.X (Sum.inr j) *
          MvPolynomial.pderiv (Sum.inr j) (u * v)) =
      (∑ j : Fin r, MvPolynomial.C (S.a j i) * MvPolynomial.X (Sum.inr j) *
          MvPolynomial.pderiv (Sum.inr j) u) * v +
      u * (∑ j : Fin r, MvPolynomial.C (S.a j i) * MvPolynomial.X (Sum.inr j) *
          MvPolynomial.pderiv (Sum.inr j) v) := by
    intro u v
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.pderiv_mul]
    ring
  have hp : MvPolynomial.pderiv (Sum.inl i) (P * Q) =
      MvPolynomial.pderiv (Sum.inl i) P * Q + P * MvPolynomial.pderiv (Sum.inl i) Q :=
    MvPolynomial.pderiv_mul
  rw [ESys.d, ESys.d, ESys.d, hp, key P Q]
  ring

theorem ESys.d_inl (S : ESys n r) (i : Fin n) (j : Fin n) :
    S.d i (MvPolynomial.X (Sum.inl j) : EPoly n r) = if i = j then 1 else 0 := by
  classical
  have hz : ∀ l : Fin r, MvPolynomial.pderiv (Sum.inr l)
      (MvPolynomial.X (Sum.inl j) : EPoly n r) = 0 :=
    fun l => MvPolynomial.pderiv_X_of_ne (by simp)
  rw [ESys.d]
  by_cases h : i = j
  · subst h
    rw [MvPolynomial.pderiv_X_self]
    simp [hz]
  · rw [MvPolynomial.pderiv_X_of_ne (by rintro hh; exact h (Sum.inl.inj hh).symm)]
    simp [hz, h]

theorem ESys.d_inr (S : ESys n r) (i : Fin n) (j : Fin r) :
    S.d i (MvPolynomial.X (Sum.inr j) : EPoly n r) =
      MvPolynomial.C (S.a j i) * MvPolynomial.X (Sum.inr j) := by
  classical
  rw [ESys.d, MvPolynomial.pderiv_X_of_ne (show Sum.inr j ≠ Sum.inl i by simp), zero_add,
    Finset.sum_eq_single j]
  · rw [MvPolynomial.pderiv_X_self]; ring
  · intro l _ hl
    rw [MvPolynomial.pderiv_X_of_ne (by rintro hh; exact hl (Sum.inr.inj hh).symm)]
    simp
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The key degree bound.**  The symbolic derivative never raises the total degree. -/
theorem ESys.d_totalDegree_le (S : ESys n r) (i : Fin n) (Q : EPoly n r) :
    (S.d i Q).totalDegree ≤ Q.totalDegree := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le (pderiv_totalDegree_le _ Q) ?_)
  refine (MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_).trans (le_refl _)
  rw [mul_assoc]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, Nat.zero_add]
  exact totalDegree_X_mul_pderiv_le (Sum.inr j) Q

/-- Iterating `d` keeps the degree bounded. -/
theorem ESys.d_iterate_totalDegree_le (S : ESys n r) (i : Fin n) (k : ℕ) (Q : EPoly n r) :
    ((S.d i)^[k] Q).totalDegree ≤ Q.totalDegree := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (ESys.d_totalDegree_le S i _).trans ih

end Work.WilE2
