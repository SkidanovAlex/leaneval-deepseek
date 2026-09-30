import Mathlib
import Submission.Work.BMF.adi_lagrange
import Submission.Work.BMF.unit_nodes_prod_inv_le
import Submission.Work.BMF.node_arith_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A crude Markov-type derivative bound for polynomials

For a real polynomial `Q` of degree `≤ k` bounded by `A` on `[-1,1]`, the derivative at the
centre is bounded by `((k+1)^(2k+4) * A) / 2`.  The proof is a Lagrange-interpolation
argument: `Q'(0)` is a linear combination of the values `Q(v r)` at the `k+1` equally spaced
nodes `v r = -1 + 2r/k`, with coefficients the derivatives of the Lagrange basis at `0`,
which are bounded by `k·(k/2)^k` each.  Summing over the `k+1` nodes and comparing with the
very generous constant `(k+1)^(2k+4)` gives the claim.

The result is then transported to an arbitrary interval `[c - lam/2, c + lam/2]` by an
affine substitution, yielding the stated `poly_deriv_bound`.
-/

namespace Work.BMF

open Polynomial Finset

/-- A product of reals each lying in `[0,1]` is at most `1`. -/
lemma prod_le_one_real {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have ha1 := h1 a (Finset.mem_insert_self a s)
      have hps := Finset.prod_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      have hs := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
                     (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      calc f a * ∏ i ∈ s, f i ≤ 1 * ∏ i ∈ s, f i := mul_le_mul_of_nonneg_right ha1 hps
        _ = ∏ i ∈ s, f i := one_mul _
        _ ≤ 1 := hs

/-- The derivative at `0` of the nodal polynomial `∏_{m ≠ r} (X - v m)` is bounded by the
number of nodes, provided all nodes lie in `[-1,1]`. -/
lemma deriv_prod_X_sub_C_bound {n : ℕ} {v : Fin (n+1) → ℝ} (r : Fin (n+1))
    (hv : ∀ m, |v m| ≤ 1) :
    |((∏ m ∈ Finset.univ.erase r, (X - C (v m)) : ℝ[X]).derivative).eval 0| ≤ (n:ℝ) := by
  rw [derivative_prod_finset]
  rw [eval_finsetSum]
  simp only [derivative_X_sub_C, mul_one, eval_prod, eval_sub, eval_X, eval_C]
  calc |∑ x ∈ univ.erase r, ∏ y ∈ (univ.erase r).erase x, (0 - v y)|
      ≤ ∑ x ∈ univ.erase r, |∏ y ∈ (univ.erase r).erase x, (0 - v y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ univ.erase r, (1:ℝ) := by
        refine Finset.sum_le_sum fun a ha => ?_
        rw [abs_prod]
        simp only [zero_sub, abs_neg]
        exact prod_le_one_real (fun b hb => abs_nonneg _) (fun b hb => hv b)
    _ = (n:ℝ) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ r),
          Finset.card_univ, Fintype.card_fin]
        simp

/-- **Derivative via Lagrange interpolation.**  If `Q` has degree `≤ n` and `v` is injective,
the derivative of `Q` at any point is the corresponding combination of the values `Q (v r)`
with the derivatives of the Lagrange basis polynomials. -/
lemma lagrange_deriv_eval {n : ℕ} {v : Fin (n+1) → ℝ} (hv : Function.Injective v) {Q : ℝ[X]}
    (hdeg : Q.natDegree ≤ n) (x : ℝ) :
    Q.derivative.eval x = ∑ r, Q.eval (v r) * (lagrangeBasis v r).derivative.eval x := by
  conv_lhs => rw [lagrange_eq hv hdeg]
  rw [derivative_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [derivative_C_mul, eval_mul, eval_C]

/-- Bound on the derivative at `0` of a Lagrange basis polynomial in terms of the nodal
distances. -/
lemma lagrangeBasis_deriv_bound {n : ℕ} {v : Fin (n+1) → ℝ} (r : Fin (n+1))
    (hv : ∀ m, |v m| ≤ 1) :
    |(lagrangeBasis v r).derivative.eval 0| ≤
      (n:ℝ) * (∏ m ∈ Finset.univ.erase r, |v r - v m|)⁻¹ := by
  classical
  have hP := deriv_prod_X_sub_C_bound (n := n) (v := v) r hv
  unfold lagrangeBasis
  rw [derivative_mul, derivative_C, mul_zero, add_zero, eval_mul, eval_C]
  rw [abs_mul, abs_inv, ← abs_prod]
  exact mul_le_mul_of_nonneg_right hP (by positivity)

/-- The equally spaced nodes `-1 + 2 r / n` in `[-1,1]`. -/
noncomputable def unitNodes (n : ℕ) : Fin (n+1) → ℝ := fun r => -1 + 2 * (r:ℝ) / n

theorem unit_nodes_injective {n : ℕ} (hn : 1 ≤ n) :
    Function.Injective (fun r : Fin (n+1) => (-1 : ℝ) + 2 * (r:ℝ) / n) := by
  intro r m h
  have h1 : (r:ℝ) = (m:ℝ) := by
    have h' : 2 * (r:ℝ)/n = 2 * (m:ℝ)/n := by linarith [h]
    field_simp at h'
    linarith
  exact Fin.ext (by exact_mod_cast h1)

theorem unit_nodes_abs_le {n : ℕ} (hn : 1 ≤ n) (m : Fin (n+1)) :
    |(-1 : ℝ) + 2 * (m:ℝ) / n| ≤ 1 := by
  have hn0 : (0:ℝ) < n := by positivity
  have hmn : (m:ℝ) ≤ n := by
    have : (m:ℕ) ≤ n := by have := m.isLt; omega
    exact_mod_cast this
  have hle : 2 * (m:ℝ) / n ≤ 2 := by rw [div_le_iff₀ hn0]; linarith
  rw [abs_le]
  constructor <;> [linarith [show (0:ℝ) ≤ 2 * (m:ℝ) / n by positivity]; linarith]

/-- **Unit-interval derivative bound.**  A degree-`≤ k` polynomial bounded by `A` on `[-1,1]`
has derivative at the centre bounded by `((k+1)^(2k+4) A)/2`. -/
lemma deriv_center_unit {k : ℕ} {Q : ℝ[X]} (hdeg : Q.natDegree ≤ k) {A : ℝ} (hA : 0 ≤ A)
    (hbd : ∀ x ∈ Set.Icc (-1:ℝ) 1, |Q.eval x| ≤ A) :
    |Q.derivative.eval 0| ≤ ((k:ℝ)+1)^(2*k+4) * A / 2 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hQc : Q = C (Q.coeff 0) := eq_C_of_natDegree_le_zero hdeg
    rw [hQc, derivative_C]
    simp only [eval_zero, abs_zero]
    positivity
  · have hvabs : ∀ m, |unitNodes k m| ≤ 1 := fun m => unit_nodes_abs_le hk m
    have hvinj : Function.Injective (unitNodes k) := unit_nodes_injective hk
    have hderiv := lagrange_deriv_eval hvinj hdeg (0:ℝ)
    rw [hderiv]
    have hterm : ∀ r : Fin (k+1),
        |Q.eval (unitNodes k r) * (lagrangeBasis (unitNodes k) r).derivative.eval 0|
          ≤ A * ((k:ℝ) * ((k:ℝ)/2)^k) := by
      intro r
      have hr_in : unitNodes k r ∈ Set.Icc (-1:ℝ) 1 := by
        rw [Set.mem_Icc]; exact abs_le.mp (hvabs r)
      have h1 : |Q.eval (unitNodes k r)| ≤ A := hbd _ hr_in
      have h2 : |(lagrangeBasis (unitNodes k) r).derivative.eval 0|
          ≤ (k:ℝ) * ((k:ℝ)/2)^k := by
        refine le_trans (lagrangeBasis_deriv_bound (v := unitNodes k) r hvabs) ?_
        have hprod := unit_nodes_prod_inv_le hk r
        exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hA
    calc |∑ r : Fin (k+1),
            Q.eval (unitNodes k r) * (lagrangeBasis (unitNodes k) r).derivative.eval 0|
        ≤ ∑ r : Fin (k+1),
            |Q.eval (unitNodes k r) * (lagrangeBasis (unitNodes k) r).derivative.eval 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r : Fin (k+1), A * ((k:ℝ) * ((k:ℝ)/2)^k) :=
          Finset.sum_le_sum (fun r _ => hterm r)
      _ = A * ((k:ℝ) * ((k:ℝ)+1) * ((k:ℝ)/2)^k) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
      _ ≤ A * (((k:ℝ)+1)^(2*k+4) / 2) :=
          mul_le_mul_of_nonneg_left (node_arith_bound hk) hA
      _ = ((k:ℝ)+1)^(2*k+4) * A / 2 := by ring

/-- Affine reduction of an interval bound to the unit interval.  The composite
`Q = E.comp (C (lam/2) * X + C c)` still has degree `≤ k`, is bounded by `A` on `[-1,1]`,
and `E'(c) = (2/lam) * Q'(0)`. -/
lemma reduce_to_unit {k : ℕ} {E : ℝ[X]} (hdeg : E.natDegree ≤ k) {A c lam : ℝ}
    (hlam : 0 < lam)
    (hbd : ∀ t ∈ Set.Icc (c - lam/2) (c + lam/2), |E.eval t| ≤ A) :
    (E.comp (C (lam/2) * X + C c)).natDegree ≤ k ∧
      (∀ x ∈ Set.Icc (-1:ℝ) 1, |(E.comp (C (lam/2) * X + C c)).eval x| ≤ A) ∧
      |E.derivative.eval c| = (2/lam) * |(E.comp (C (lam/2) * X + C c)).derivative.eval 0| := by
  have hq_nat : (C (lam/2) * X + C c : ℝ[X]).natDegree ≤ 1 := by
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans (natDegree_mul_le) ?_
      rw [natDegree_C, zero_add, natDegree_X]
    · rw [natDegree_C]; norm_num
  have hq_eval : ∀ x : ℝ, (C (lam/2) * X + C c : ℝ[X]).eval x = lam/2 * x + c := by
    intro x; simp [eval_add, eval_mul]
  have hder : (E.comp (C (lam/2) * X + C c)).derivative.eval 0
      = (lam/2) * E.derivative.eval c := by
    rw [derivative_comp, eval_mul, eval_comp]
    have hq0 : (C (lam/2) * X + C c : ℝ[X]).eval 0 = c := by rw [hq_eval]; ring
    have hdq0 : (C (lam/2) * X + C c : ℝ[X]).derivative.eval 0 = lam/2 := by
      rw [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_C]
      simp
    rw [hq0, hdq0]
  refine ⟨?_, ?_, ?_⟩
  · calc (E.comp (C (lam/2) * X + C c)).natDegree
        ≤ E.natDegree * (C (lam/2) * X + C c).natDegree := natDegree_comp_le
      _ ≤ k * 1 := Nat.mul_le_mul hdeg hq_nat
      _ = k := Nat.mul_one k
  · intro x hx
    rw [eval_comp, hq_eval]
    apply hbd
    rw [Set.mem_Icc] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    constructor <;> nlinarith [hlam]
  · rw [hder, abs_mul, abs_of_pos (by positivity : (0:ℝ) < lam/2)]
    field_simp

theorem poly_deriv_bound {k : ℕ} {E : ℝ[X]} (hdeg : E.natDegree ≤ k) {A c lam : ℝ}
    (hA : 0 ≤ A) (hlam : 0 < lam)
    (hbd : ∀ t ∈ Set.Icc (c - lam / 2) (c + lam / 2), |E.eval t| ≤ A) :
    |E.derivative.eval c| ≤ ((k : ℝ) + 1) ^ (2 * k + 4) * A / lam := by
  obtain ⟨hQdeg, hQbd, hQderiv⟩ := reduce_to_unit hdeg hlam hbd
  have hcenter := deriv_center_unit hQdeg hA hQbd
  rw [hQderiv]
  calc (2/lam) * |(E.comp (C (lam/2) * X + C c)).derivative.eval 0|
      ≤ (2/lam) * (((k:ℝ)+1)^(2*k+4) * A / 2) :=
        mul_le_mul_of_nonneg_left hcenter (by positivity)
    _ = ((k:ℝ)+1)^(2*k+4) * A / lam := by field_simp

end Work.BMF
