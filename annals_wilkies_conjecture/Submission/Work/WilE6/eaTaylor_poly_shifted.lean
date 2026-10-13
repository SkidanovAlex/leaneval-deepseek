/-
  WilE6 (area E6): the Taylor polynomial as a polynomial in the shift `u = x - z`.

  `eaTaylor_poly_shifted`: for an EA chain `c`, an EA polynomial `Q` and an order `N`,
  the function `(z, u) ↦ eaTaylor c Q N z (z + u)` is the evaluation of ONE polynomial `P`
  in the variables `(u, (z, h(z)))`, with `P.totalDegree ≤ Q.totalDegree + N`.

  The construction is the explicit Taylor sum: the coefficient of `u^m` is
  `∂^m Q(z, h(z)) / m!`, and the symbolic derivative `∂^m Q` does not raise the total degree
  (`eaDmulti_totalDegree_le`, obtained from the corresponding statement for `Work.WilE2.ESys`).
-/
import Mathlib
import Submission.Work.WilE6.Base
import Submission.Work.WilE2.Degree

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {k r : ℕ}

/-! ## §1. The index set of the Taylor sum -/

/-- The finite set of multi-indices `m : Fin k → ℕ` of total size `≤ N` that occur in the
order-`N` Taylor polynomial. -/
def taylorIdx (k N : ℕ) : Finset (Fin k → ℕ) :=
  ((Finset.univ : Finset (Fin k → Fin (N + 1))).image (fun m i => (m i : ℕ))).filter
    (fun m => ∑ i, m i ≤ N)

/-- `eaTaylor` is the sum over `taylorIdx` (definitional unfolding). -/
theorem eaTaylor_eq_sum (c : EAChain k r) (Q : EAPoly k r) (N : ℕ) (y x : Fin k → ℝ) :
    eaTaylor c Q N y x =
      ∑ m ∈ taylorIdx k N,
        eaEval c (eaDmulti c m Q) y * ∏ i, (x i - y i) ^ m i / ((m i).factorial : ℝ) := by
  simp only [eaTaylor, taylorIdx]

/-- The `(z,h)`-block, viewed as the last `k + r` coordinates of the combined space. -/
def inrVar (k r : ℕ) : Fin (k + r) → Fin k ⊕ Fin (k + r) := fun l => Sum.inr l

/-! ## §2. Degree bounds for the symbolic derivative -/

/-- The symbolic derivative does not raise the total degree (transported from
`Work.WilE2.ESys.d_totalDegree_le`). -/
theorem eaD_totalDegree_le (c : EAChain k r) (i : Fin k) (Q : EAPoly k r) :
    (eaD c i Q).totalDegree ≤ Q.totalDegree :=
  Work.WilE2.ESys.d_totalDegree_le (Work.WilE2.ESys.ofChain c) i Q

/-- The iterated symbolic derivative does not raise the total degree. -/
theorem eaD_iterate_totalDegree_le (c : EAChain k r) (i : Fin k) (n : ℕ) (Q : EAPoly k r) :
    ((eaD c i)^[n] Q).totalDegree ≤ Q.totalDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (eaD_totalDegree_le c i (((eaD c i)^[n]) Q)).trans ih

/-- The ordered iterated symbolic derivative does not raise the total degree. -/
theorem foldr_eaD_totalDegree_le (c : EAChain k r) (m : Fin k → ℕ) (Q : EAPoly k r)
    (l : List (Fin k)) :
    (l.foldr (fun i g => (eaD c i)^[m i] g) Q).totalDegree ≤ Q.totalDegree := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.foldr_cons]
    exact (eaD_iterate_totalDegree_le c a (m a) _).trans ih

/-- `eaDmulti` does not raise the total degree. -/
theorem eaDmulti_totalDegree_le (c : EAChain k r) (m : Fin k → ℕ) (Q : EAPoly k r) :
    (eaDmulti c m Q).totalDegree ≤ Q.totalDegree :=
  foldr_eaD_totalDegree_le c m Q (List.finRange k)

/-! ## §3. The shifted Taylor polynomial -/

/-- Evaluation of a `(z,h)`-polynomial at `(z, h(z))`, after embedding its variables in the
last block of the `(u, (z,h))`-space. -/
theorem eval_rename_inrVar (c : EAChain k r) (R : MvPolynomial (Fin (k + r)) ℝ)
    (z u : Fin k → ℝ) :
    MvPolynomial.eval (Sum.elim u (graphPt c z)) (MvPolynomial.rename (inrVar k r) R) =
      MvPolynomial.eval (graphPt c z) R := by
  rw [MvPolynomial.eval_rename]
  rw [show (Sum.elim u (graphPt c z)) ∘ (inrVar k r) = graphPt c z from by
    funext l; simp only [Function.comp_apply, inrVar, Sum.elim_inr]]

/-- One summand of the shifted Taylor polynomial: `∂^m Q(z,h(z)) / m! · u^m`. -/
def taylorTerm (c : EAChain k r) (Q : EAPoly k r) (m : Fin k → ℕ) :
    MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ :=
  MvPolynomial.C ((∏ i, ((m i).factorial : ℝ))⁻¹) *
    (MvPolynomial.rename (inrVar k r) (toCombined (eaDmulti c m Q)) *
      ∏ i, MvPolynomial.X (Sum.inl i) ^ (m i))

/-- The shifted Taylor polynomial of `Q` of order `N`: a polynomial in the variables
`(u, (z,h))`. -/
def eaTaylorPoly (c : EAChain k r) (Q : EAPoly k r) (N : ℕ) :
    MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ :=
  ∑ m ∈ taylorIdx k N, taylorTerm c Q m

/-- Evaluating one summand at `(u, (z, h(z)))`. -/
theorem eval_taylorTerm (c : EAChain k r) (Q : EAPoly k r) (m : Fin k → ℕ) (z u : Fin k → ℝ) :
    MvPolynomial.eval (Sum.elim u (graphPt c z)) (taylorTerm c Q m) =
      eaEval c (eaDmulti c m Q) z * ∏ i, ((z + u) i - z i) ^ m i / ((m i).factorial : ℝ) := by
  have hsub : ∀ i : Fin k, (z + u) i - z i = u i := fun i => by
    rw [Pi.add_apply, add_sub_cancel_left]
  have hprod : (∏ i : Fin k, ((z + u) i - z i) ^ m i / ((m i).factorial : ℝ)) =
      (∏ i : Fin k, ((m i).factorial : ℝ))⁻¹ * ∏ i : Fin k, u i ^ m i := by
    refine (Finset.prod_congr rfl (fun i _ => by rw [hsub i])).trans ?_
    rw [Finset.prod_div_distrib, div_eq_mul_inv, mul_comm]
  simp only [taylorTerm, map_mul, map_prod, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X,
    eval_rename_inrVar, ← eaEval_eq_eval_graphPt, Sum.elim_inl, hprod]
  ring

/-- The degree of one summand. -/
theorem totalDegree_taylorTerm_le (c : EAChain k r) (Q : EAPoly k r) (N : ℕ)
    (m : Fin k → ℕ) (hm : ∑ i, m i ≤ N) :
    (taylorTerm c Q m).totalDegree ≤ Q.totalDegree + N := by
  have h1 : (MvPolynomial.rename (inrVar k r) (toCombined (eaDmulti c m Q))).totalDegree ≤
      Q.totalDegree :=
    (MvPolynomial.totalDegree_rename_le _ _).trans
      ((totalDegree_toCombined _).trans (eaDmulti_totalDegree_le c m Q))
  have h2 : (∏ i, MvPolynomial.X (Sum.inl i) ^ (m i) :
      MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ).totalDegree ≤ N := by
    refine (MvPolynomial.totalDegree_finsetProd Finset.univ
      (fun i : Fin k => (MvPolynomial.X (Sum.inl i) :
        MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) ^ (m i))).trans ?_
    refine (Finset.sum_le_sum (fun i _ => ?_)).trans hm
    rw [MvPolynomial.totalDegree_X_pow]
  rw [taylorTerm]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, Nat.zero_add]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  exact Nat.add_le_add h1 h2

/-- The degree bound for the shifted Taylor polynomial. -/
theorem eaTaylorPoly_totalDegree_le (c : EAChain k r) (Q : EAPoly k r) (N : ℕ) :
    (eaTaylorPoly c Q N).totalDegree ≤ Q.totalDegree + N := by
  refine MvPolynomial.totalDegree_finsetSum_le (fun m hm => ?_)
  exact totalDegree_taylorTerm_le c Q N m (Finset.mem_filter.mp hm).2

/-- The shifted Taylor polynomial evaluates to `eaTaylor` evaluated at the shifted point. -/
theorem eval_eaTaylorPoly (c : EAChain k r) (Q : EAPoly k r) (N : ℕ) (z u : Fin k → ℝ) :
    MvPolynomial.eval (Sum.elim u (graphPt c z)) (eaTaylorPoly c Q N) =
      eaTaylor c Q N z (z + u) := by
  rw [eaTaylor_eq_sum c Q N z (z + u)]
  rw [eaTaylorPoly, map_sum]
  exact Finset.sum_congr rfl (fun m _ => eval_taylorTerm c Q m z u)

/-! ## §4. The main statement -/

theorem eaTaylor_poly_shifted {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Q : WilkiesDesign.E.EAPoly k r) (N : ℕ) :
    ∃ P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ,
      (∀ z u : Fin k → ℝ, WilkiesDesign.E.eaTaylor c Q N z (z + u) =
        MvPolynomial.eval (Sum.elim u (Work.WilE6.graphPt c z)) P) ∧
      P.totalDegree ≤ Q.totalDegree + N :=
  ⟨eaTaylorPoly c Q N, fun z u => (eval_eaTaylorPoly c Q N z u).symm,
    eaTaylorPoly_totalDegree_le c Q N⟩

end Work.WilE6
