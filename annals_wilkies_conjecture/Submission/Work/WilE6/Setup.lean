/-
  WilE6: the vocabulary of the closure assembly.

  * `mergeEq B` : the single equation `∑_{f ∈ B.eqs} f²` whose zero set is that of `B.eqs`
    (this is what turns a list of equations into the single polynomial `P` of `critSA`).
  * `Pof c B κ`, `Gsof c B κ` : the Taylor polynomials (in the shifted variables `(u, (z,h))`)
    of the merged equation and of the positivity atoms, at order `κ²` resp. `κ`.
  * `critUnion hp κ X` : the `SA`-set which is the disjunction, over the basic sets `B` of `X`
    and the attained-index pieces `j : Fin (k+1)`, of `critSA hp κ (Pof X.c B κ) (Gsof X.c B κ)`.
  * `kappa K D p` : the uniform cut-off `K.eval (3D + 2p + 1) + 1` used for every `B` (so that
    `K.eval B''.deg < kappa` holds for the merged frozen basic set `B''` of every `B`).
  * `critUnionOf K X` : `critUnion` instantiated with `κ = kappa K X.deg p`.
-/
import Submission.Work.WilE6.Block
import Submission.Work.WilE6.CritSA
import Submission.Work.WilE6.eaTaylor_poly_shifted

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {k r p q : ℕ}

/-- The single equation `∑_{f ∈ B.eqs} f²`, whose zero set is `{f = 0 : f ∈ B.eqs}`. -/
def mergeEq (B : Basic k r) : EAPoly k r := (B.eqs.map (fun f => f ^ 2)).sum

theorem totalDegree_list_sum_le {σ : Type*} (l : List (MvPolynomial σ ℝ)) :
    l.sum.totalDegree ≤ (l.map MvPolynomial.totalDegree).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.sum_cons, List.map_cons, List.sum_cons]
      exact le_trans (MvPolynomial.totalDegree_add a t.sum) (by omega)

theorem sum_map_mul_const (l : List ℕ) (c : ℕ) :
    (l.map (fun x => c * x)).sum = c * l.sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem totalDegree_mergeEq_le (B : Basic k r) : (mergeEq B).totalDegree ≤ 2 * B.deg := by
  have h1 : (mergeEq B).totalDegree ≤
      ((B.eqs.map (fun f => f ^ 2)).map MvPolynomial.totalDegree).sum :=
    totalDegree_list_sum_le _
  rw [mergeEq] at h1
  refine h1.trans ?_
  have h2 : ((B.eqs.map (fun f => f ^ 2)).map MvPolynomial.totalDegree).sum
      = (B.eqs.map (fun f => (f ^ 2).totalDegree)).sum := by
    rw [List.map_map]; rfl
  rw [h2]
  refine (List.sum_le_sum fun f _ => MvPolynomial.totalDegree_pow f 2).trans ?_
  have h3 : (B.eqs.map (fun f => 2 * f.totalDegree)).sum
      = 2 * (B.eqs.map MvPolynomial.totalDegree).sum := by
    have hm : (B.eqs.map (fun f => 2 * f.totalDegree))
        = (B.eqs.map MvPolynomial.totalDegree).map (fun x => 2 * x) := by
      rw [List.map_map]; rfl
    rw [hm, sum_map_mul_const]
  rw [h3]
  have h4 : (B.eqs.map MvPolynomial.totalDegree).sum ≤ (B.eqs.map atomDeg).sum :=
    List.sum_le_sum fun f _ => by simp only [atomDeg]; omega
  have h5 : (B.eqs.map atomDeg).sum ≤ B.deg := by
    simp only [Basic.deg, List.map_append, List.sum_append]; omega
  omega

theorem eaEval_add (c : EAChain k r) (Q Q' : EAPoly k r) (z : Fin k → ℝ) :
    eaEval c (Q + Q') z = eaEval c Q z + eaEval c Q' z := by
  show MvPolynomial.eval (Sum.elim z fun j => Real.exp (c.ell j z)) (Q + Q') =
    MvPolynomial.eval (Sum.elim z fun j => Real.exp (c.ell j z)) Q +
      MvPolynomial.eval (Sum.elim z fun j => Real.exp (c.ell j z)) Q'
  rw [MvPolynomial.eval_add]

theorem eaEval_pow (c : EAChain k r) (Q : EAPoly k r) (n : ℕ) (z : Fin k → ℝ) :
    eaEval c (Q ^ n) z = eaEval c Q z ^ n := by
  show MvPolynomial.eval (Sum.elim z fun j => Real.exp (c.ell j z)) (Q ^ n) =
    MvPolynomial.eval (Sum.elim z fun j => Real.exp (c.ell j z)) Q ^ n
  rw [MvPolynomial.eval_pow]

theorem eaEval_list_sum_sq (c : EAChain k r) (l : List (EAPoly k r)) (z : Fin k → ℝ) :
    eaEval c (l.map (fun f => f ^ 2)).sum z = (l.map (fun f => eaEval c f z ^ 2)).sum := by
  induction l with
  | nil => simp [eaEval]
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      rw [eaEval_add, eaEval_pow, ih]

theorem sum_sq_eq_zero_iff {l : List ℝ} :
    (l.map (fun x => x ^ 2)).sum = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have hnn : 0 ≤ (t.map (fun x => x ^ 2)).sum :=
        List.sum_nonneg fun y hy => by
          obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy
          positivity
      rw [List.map_cons, List.sum_cons, List.forall_mem_cons]
      constructor
      · intro h
        have ha2 : a ^ 2 = 0 := by linarith [sq_nonneg a]
        have ht2 : (t.map (fun x => x ^ 2)).sum = 0 := by linarith [sq_nonneg a]
        exact ⟨sq_eq_zero_iff.mp ha2, ih.mp ht2⟩
      · rintro ⟨ha, ht⟩
        have ht2 : (t.map (fun x => x ^ 2)).sum = 0 := ih.mpr ht
        rw [ha, ht2]; norm_num

theorem mergeEq_holds_iff (c : EAChain k r) (B : Basic k r) (z : Fin k → ℝ) :
    (eaEval c (mergeEq B) z = 0) ↔ ∀ f ∈ B.eqs, eaEval c f z = 0 := by
  rw [mergeEq, eaEval_list_sum_sq]
  rw [show (B.eqs.map (fun f => eaEval c f z ^ 2))
      = (B.eqs.map (fun f => eaEval c f z)).map (fun x => x ^ 2) from by
    rw [List.map_map]; rfl]
  rw [sum_sq_eq_zero_iff]
  constructor
  · intro h f hf
    exact h (eaEval c f z) (List.mem_map.mpr ⟨f, hf, rfl⟩)
  · intro h x hx
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    exact h f hf

/-- The Taylor polynomial of the merged equation, in the shifted variables `(u, (z,h))`. -/
def Pof (c : EAChain k r) (B : Basic k r) (κ : ℕ) :
    MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ :=
  eaTaylorPoly c (mergeEq B) (κ ^ 2)

/-- The Taylor polynomials of the positivity atoms, in the shifted variables `(u, (z,h))`. -/
def Gsof (c : EAChain k r) (B : Basic k r) (κ : ℕ) :
    List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) :=
  B.pos.map (fun g => eaTaylorPoly c g κ)

/-- The union of the criterion pieces of all basic sets of `X`. -/
def critUnion (hp : p ≤ k) (κ : ℕ) (X : SemiPf k) : SA (BP k X.r + FQ k p) :=
  ⟨X.basics.flatMap (fun B =>
    (List.finRange (k + 1)).map (fun j =>
      critBasic (p := p) hp κ (Pof X.c B κ) (Gsof X.c B κ) j))⟩

/-- The uniform cut-off: `K.eval (3D + 2p + 1) + 1`. -/
def kappa (K : Polynomial ℕ) (D p : ℕ) : ℕ := K.eval (3 * D + 2 * p + 1) + 1

/-- `critUnion` instantiated with the uniform cut-off. -/
def critUnionOf {p q : ℕ} (K : Polynomial ℕ) (X : SemiPf (p + q)) :
    SA (BP (p + q) X.r + FQ (p + q) p) :=
  critUnion (p := p) (by omega : p ≤ p + q) (kappa K X.deg p) X

end Work.WilE6
