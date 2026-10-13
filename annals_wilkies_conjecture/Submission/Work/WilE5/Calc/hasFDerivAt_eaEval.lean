/-
  WilE5.Calc — the derivative of `eaEval`.

  `eaEval c Q x` is the evaluation of the EA-polynomial `Q` at the point
  `(x, exp(ℓ_j x))`. The symbolic operator `eaD c i` is the total derivative of `eaEval`
  along the `i`-th coordinate; this file proves that it computes the Fréchet derivative:

      `HasFDerivAt (eaEval c Q) (∑ i, eaEval c (eaD c i Q) x • proj i) x`.

  The proof is an induction on `Q` (`MvPolynomial.induction_on`), the only analytic inputs
  being the derivative of a coordinate projection and the chain rule for `Real.exp` along
  the affine form `ℓ_j`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec

open WilkiesDesign.E

namespace Work.WilE5.Calc

/-! ## §1. Evaluation lemmas for `eaEval` -/

theorem eaEval_add' {k r : ℕ} (c : EAChain k r) (p q : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (p + q) x = eaEval c p x + eaEval c q x := by simp [eaEval]

theorem eaEval_mul' {k r : ℕ} (c : EAChain k r) (p q : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (p * q) x = eaEval c p x * eaEval c q x := by simp [eaEval]

theorem eaEval_C' {k r : ℕ} (c : EAChain k r) (a : ℝ) (x : Fin k → ℝ) :
    eaEval c (MvPolynomial.C a) x = a := by simp [eaEval]

theorem eaEval_X_inl' {k r : ℕ} (c : EAChain k r) (i : Fin k) (x : Fin k → ℝ) :
    eaEval c (MvPolynomial.X (Sum.inl i)) x = x i := by simp [eaEval]

theorem eaEval_X_inr' {k r : ℕ} (c : EAChain k r) (j : Fin r) (x : Fin k → ℝ) :
    eaEval c (MvPolynomial.X (Sum.inr j)) x = Real.exp (c.ell j x) := by simp [eaEval]

/-! ## §2. Algebraic identities for the symbolic derivative `eaD` -/

theorem eaD_C' {k r : ℕ} (c : EAChain k r) (i : Fin k) (a : ℝ) :
    eaD c i (MvPolynomial.C a) = 0 := by simp [eaD]

theorem eaD_add' {k r : ℕ} (c : EAChain k r) (i : Fin k) (p q : EAPoly k r) :
    eaD c i (p + q) = eaD c i p + eaD c i q := by
  simp only [eaD, map_add, mul_add, Finset.sum_add_distrib]
  simp only [mul_assoc, mul_comm]
  ring

/-- Leibniz rule for `eaD`: it is a derivation, so it satisfies the product rule. -/
theorem eaD_mul_X {k r : ℕ} (c : EAChain k r) (i : Fin k) (p : EAPoly k r)
    (n : Fin k ⊕ Fin r) :
    eaD c i (p * MvPolynomial.X n) = eaD c i p * MvPolynomial.X n + p * eaD c i (MvPolynomial.X n) := by
  simp only [eaD, MvPolynomial.pderiv_mul, mul_add, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  ring

theorem eaD_X_inl' {k r : ℕ} (c : EAChain k r) (l i : Fin k) :
    eaD c l (MvPolynomial.X (Sum.inl i)) = if l = i then 1 else 0 := by
  have hsum : (∑ j : Fin r, MvPolynomial.C (c.a j l) * MvPolynomial.X (Sum.inr j) *
      (MvPolynomial.pderiv (Sum.inr j)) (MvPolynomial.X (Sum.inl i))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [MvPolynomial.pderiv_X_of_ne]
    · ring
    · exact Sum.inl_ne_inr
  simp only [eaD]
  rw [hsum, add_zero]
  rw [MvPolynomial.pderiv_X]
  by_cases h : l = i
  · subst h; simp
  · rw [Pi.single_eq_of_ne]
    · simp [h]
    · simp only [ne_eq, Sum.inl.injEq]; exact fun h' => h h'.symm

theorem eaD_X_inr' {k r : ℕ} (c : EAChain k r) (l : Fin k) (j : Fin r) :
    eaD c l (MvPolynomial.X (Sum.inr j)) = MvPolynomial.C (c.a j l) * MvPolynomial.X (Sum.inr j) := by
  have hsum : (∑ b : Fin r, MvPolynomial.C (c.a b l) * MvPolynomial.X (Sum.inr b) *
      (MvPolynomial.pderiv (Sum.inr b)) (MvPolynomial.X (Sum.inr j : Fin k ⊕ Fin r))) =
      MvPolynomial.C (c.a j l) * MvPolynomial.X (Sum.inr j : Fin k ⊕ Fin r) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [MvPolynomial.pderiv_X_of_ne]
      · ring
      · simp only [ne_eq, Sum.inr.injEq]
        exact fun h => hb h.symm
    · intro h; exact absurd (Finset.mem_univ j) h
  simp only [eaD]
  rw [hsum]
  rw [MvPolynomial.pderiv_X_of_ne]
  · ring
  · exact Sum.inr_ne_inl

/-! ## §3. The candidate derivative `eaEvalD`, and list-combination identities -/

/-- The candidate Fréchet derivative of `eaEval c Q ·`. -/
noncomputable def eaEvalD {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ) :
    (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i, (eaEval c (eaD c i Q) x) • ContinuousLinearMap.proj i

/-- The linear form `z ↦ ∑ i, c.a j i * z i` associated to the affine form `ℓ_j`. -/
noncomputable def ellLin {k r : ℕ} (c : EAChain k r) (j : Fin r) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i, c.a j i • ContinuousLinearMap.proj i

theorem sum_smul_combine {ι : Type*} [Fintype ι] {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (v : ι → M) (b d : ι → ℝ) (a cc : ℝ) :
    (∑ i, (a * b i + cc * d i) • v i) = a • (∑ i, b i • v i) + cc • (∑ i, d i • v i) := by
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_smul, smul_smul, smul_smul]

theorem sum_mul_smul {ι : Type*} [Fintype ι] {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (v : ι → M) (a : ι → ℝ) (e : ℝ) :
    (∑ i, (a i * e) • v i) = e • (∑ i, a i • v i) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, mul_comm]

/-! ## §4. The derivative along the affine forms `ℓ_j` -/

theorem ell_eq {k r : ℕ} (c : EAChain k r) (j : Fin r) (z : Fin k → ℝ) :
    c.ell j z = c.b j + (ellLin c j) z := by
  simp only [EAChain.ell, ellLin, sum_apply, smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  ring

theorem ell_hasFDerivAt {k r : ℕ} (c : EAChain k r) (j : Fin r) (x : Fin k → ℝ) :
    HasFDerivAt (fun z => c.ell j z) (ellLin c j) x := by
  rw [show (fun z : Fin k → ℝ => c.ell j z) = fun z => c.b j + (ellLin c j) z from
    funext fun z => ell_eq c j z]
  exact (ContinuousLinearMap.hasFDerivAt (ellLin c j) (x := x)).const_add (c.b j)

/-! ## §5. Additivity, constants and the Leibniz rule for `eaEvalD` -/

theorem eaEvalD_C {k r : ℕ} (c : EAChain k r) (a : ℝ) (x : Fin k → ℝ) :
    eaEvalD c (MvPolynomial.C a) x = 0 := by
  simp only [eaEvalD, eaD_C', eaEval]
  simp

theorem eaEvalD_add {k r : ℕ} (c : EAChain k r) (p q : EAPoly k r) (x : Fin k → ℝ) :
    eaEvalD c (p + q) x = eaEvalD c p x + eaEvalD c q x := by
  simp only [eaEvalD, eaD_add', eaEval_add', add_smul, Finset.sum_add_distrib]

/-- `eaEvalD` satisfies the Leibniz rule with respect to multiplication by a variable. -/
theorem eaEvalD_mul_X {k r : ℕ} (c : EAChain k r) (p : EAPoly k r) (n : Fin k ⊕ Fin r)
    (x : Fin k → ℝ) :
    eaEvalD c (p * MvPolynomial.X n) x = eaEval c p x • eaEvalD c (MvPolynomial.X n) x +
      eaEval c (MvPolynomial.X n) x • eaEvalD c p x := by
  simp only [eaEvalD]
  simp only [show ∀ i, eaEval c (eaD c i (p * MvPolynomial.X n)) x =
      eaEval c p x * eaEval c (eaD c i (MvPolynomial.X n)) x +
        eaEval c (MvPolynomial.X n) x * eaEval c (eaD c i p) x from fun i => by
    rw [eaD_mul_X, eaEval_add', eaEval_mul', eaEval_mul']; ring]
  rw [sum_smul_combine]

/-! ## §6. `eaEvalD` at the variables and the base case of the induction -/

theorem eaEvalD_X_inl {k r : ℕ} (c : EAChain k r) (i : Fin k) (x : Fin k → ℝ) :
    eaEvalD c (MvPolynomial.X (Sum.inl i)) x = ContinuousLinearMap.proj i := by
  rw [eaEvalD, Finset.sum_eq_single i]
  · rw [eaD_X_inl']; simp [eaEval]
  · intro l _ hl
    rw [eaD_X_inl']; simp [eaEval, hl]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem eaEvalD_X_inr {k r : ℕ} (c : EAChain k r) (j : Fin r) (x : Fin k → ℝ) :
    eaEvalD c (MvPolynomial.X (Sum.inr j)) x = Real.exp (c.ell j x) • ellLin c j := by
  simp only [eaEvalD, eaD_X_inr', eaEval_mul', eaEval_C', eaEval_X_inr', ellLin]
  rw [sum_mul_smul]

theorem hasFDerivAt_X {k r : ℕ} (c : EAChain k r) (n : Fin k ⊕ Fin r) (x : Fin k → ℝ) :
    HasFDerivAt (fun z => eaEval c (MvPolynomial.X n) z) (eaEvalD c (MvPolynomial.X n) x) x := by
  rcases n with i | j
  · rw [eaEvalD_X_inl]
    have hfun : (fun z : Fin k → ℝ => eaEval c (MvPolynomial.X (Sum.inl i)) z) = fun z => z i := by
      funext z; rw [eaEval_X_inl']
    rw [hfun]
    exact ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ) (x := x)
  · rw [eaEvalD_X_inr]
    have hfun : (fun z : Fin k → ℝ => eaEval c (MvPolynomial.X (Sum.inr j)) z) =
        fun z => Real.exp (c.ell j z) := by
      funext z; rw [eaEval_X_inr']
    rw [hfun]
    exact (ell_hasFDerivAt c j x).exp

/-! ## §7. The main statement -/

theorem hasFDerivAt_eaEval {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (Q : WilkiesDesign.E.EAPoly k r) (x : Fin k → ℝ) :
    HasFDerivAt (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Q z)
      ((∑ i : Fin k, (WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Q) x) • ContinuousLinearMap.proj i) :
        (Fin k → ℝ) →L[ℝ] ℝ) x := by
  show HasFDerivAt (fun z : Fin k → ℝ => eaEval c Q z) (eaEvalD c Q x) x
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [eaEvalD_C]
    rw [show (fun z : Fin k → ℝ => eaEval c (MvPolynomial.C a) z) = fun _ => a from
      funext fun z => eaEval_C' c a z]
    exact hasFDerivAt_const a x
  | add p q hp hq =>
    rw [eaEvalD_add]
    refine (hp.add hq).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp only [eaEval_add', Pi.add_apply]
  | mul_X p n hp =>
    have hXn := hasFDerivAt_X c n x
    rw [eaEvalD_mul_X]
    refine (hp.mul hXn).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp only [eaEval_mul', Pi.mul_apply]

end Work.WilE5.Calc
