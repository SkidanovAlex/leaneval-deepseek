import Mathlib
import Submission.Work.WilE3.Defs

namespace Work.WilE3.API

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

noncomputable section

variable {k r : ℕ}

/-! ## Auxiliary lemmas for `hasFDerivAt_eaEval`

`eaEval c Q` is the composition of the polynomial function `eval` with the parametrisation
`x ↦ Sum.elim x (fun j => exp (c.ell j x))`.  The claimed derivative is the symbolic gradient
`eaDeriv c Q x = ∑ i, eaEval c (eaD c i Q) x • proj i`.  We prove this by induction on `Q`,
using that `eaD` is a derivation on `EAPoly`. -/

/-- `eaEval` is multiplicative in the polynomial variable. -/
private lemma eaEval_add (c : EAChain k r) (p q : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (p + q) x = eaEval c p x + eaEval c q x := by
  simp only [eaEval, MvPolynomial.eval_add]

private lemma eaEval_mul (c : EAChain k r) (p q : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (p * q) x = eaEval c p x * eaEval c q x := by
  simp only [eaEval, MvPolynomial.eval_mul]

/-- `eaD` is additive. -/
private lemma eaD_add (c : EAChain k r) (i : Fin k) (p q : EAPoly k r) :
    eaD c i (p + q) = eaD c i p + eaD c i q := by
  simp only [eaD, map_add, mul_add, Finset.sum_add_distrib]
  ring_nf

/-- `eaD` is a derivation (Leibniz rule). -/
private lemma eaD_mul (c : EAChain k r) (i : Fin k) (p q : EAPoly k r) :
    eaD c i (p * q) = eaD c i p * q + p * eaD c i q := by
  simp only [eaD, MvPolynomial.pderiv_mul, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul, mul_add, add_mul]
  ring_nf

private lemma eaD_C (c : EAChain k r) (i : Fin k) (a : ℝ) :
    eaD c i (MvPolynomial.C a : EAPoly k r) = 0 := by
  simp only [eaD, MvPolynomial.pderiv_C, mul_zero]
  simp

/-- `eaD` at a variable of the first kind. -/
private lemma eaD_X_inl_self (c : EAChain k r) (i : Fin k) :
    eaD c i (MvPolynomial.X (Sum.inl i) : EAPoly k r) = 1 := by
  simp only [eaD, MvPolynomial.pderiv_X_self]
  have h2 : ∀ j : Fin r, MvPolynomial.pderiv (Sum.inr j)
      (MvPolynomial.X (Sum.inl i) : EAPoly k r) = 0 :=
    fun j => MvPolynomial.pderiv_X_of_ne (Sum.inl_ne_inr)
  simp only [h2, mul_zero]
  simp

private lemma eaD_X_inl_ne (c : EAChain k r) {i i₀ : Fin k} (h : i ≠ i₀) :
    eaD c i (MvPolynomial.X (Sum.inl i₀) : EAPoly k r) = 0 := by
  simp only [eaD]
  rw [MvPolynomial.pderiv_X_of_ne (i := Sum.inl i) (j := Sum.inl i₀)
    (fun hh => h (Sum.inl_injective hh).symm)]
  have h2 : ∀ j : Fin r, MvPolynomial.pderiv (Sum.inr j)
      (MvPolynomial.X (Sum.inl i₀) : EAPoly k r) = 0 :=
    fun j => MvPolynomial.pderiv_X_of_ne (Sum.inl_ne_inr)
  simp only [h2, mul_zero, zero_add]
  simp

/-- `eaD` at a variable of the second kind. -/
private lemma eaD_X_inr (c : EAChain k r) (i : Fin k) (j₀ : Fin r) :
    eaD c i (MvPolynomial.X (Sum.inr j₀) : EAPoly k r)
      = MvPolynomial.C (c.a j₀ i) * MvPolynomial.X (Sum.inr j₀) := by
  simp only [eaD]
  rw [MvPolynomial.pderiv_X_of_ne (i := Sum.inl i) (j := Sum.inr j₀) Sum.inr_ne_inl,
    zero_add]
  calc (∑ j : Fin r, MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) *
          MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.X (Sum.inr j₀) : EAPoly k r))
      = MvPolynomial.C (c.a j₀ i) * MvPolynomial.X (Sum.inr j₀) *
          MvPolynomial.pderiv (Sum.inr j₀) (MvPolynomial.X (Sum.inr j₀) : EAPoly k r) :=
        Finset.sum_eq_single j₀
          (fun j _ hj => by
            rw [MvPolynomial.pderiv_X_of_ne (i := Sum.inr j) (j := Sum.inr j₀)
              (fun hh => hj (Sum.inr_injective hh).symm)]
            ring)
          (fun h => absurd (Finset.mem_univ j₀) h)
    _ = MvPolynomial.C (c.a j₀ i) * MvPolynomial.X (Sum.inr j₀) := by
        rw [MvPolynomial.pderiv_X_self, mul_one]

private lemma eaEval_eaD_X_inl (c : EAChain k r) (i i₀ : Fin k) (x : Fin k → ℝ) :
    eaEval c (eaD c i (MvPolynomial.X (Sum.inl i₀) : EAPoly k r)) x
      = if i = i₀ then 1 else 0 := by
  by_cases h : i = i₀
  · rw [h, eaD_X_inl_self]
    simp [eaEval]
  · rw [eaD_X_inl_ne c h]
    simp [eaEval, h]

private lemma eaEval_eaD_X_inr (c : EAChain k r) (i : Fin k) (j₀ : Fin r) (x : Fin k → ℝ) :
    eaEval c (eaD c i (MvPolynomial.X (Sum.inr j₀) : EAPoly k r)) x
      = c.a j₀ i * Real.exp (c.ell j₀ x) := by
  rw [eaD_X_inr]
  simp [eaEval]

/-- The symbolic gradient of `Q` at `x`, the announced derivative of `eaEval c Q`. -/
private def eaDeriv (c : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin k, (eaEval c (eaD c i Q) x) • (ContinuousLinearMap.proj i)

private lemma eaDeriv_add (c : EAChain k r) (p q : EAPoly k r) (x : Fin k → ℝ) :
    eaDeriv c (p + q) x = eaDeriv c p x + eaDeriv c q x := by
  simp only [eaDeriv, eaD_add, eaEval_add]
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma eaDeriv_mul (c : EAChain k r) (p q : EAPoly k r) (x : Fin k → ℝ) :
    eaDeriv c (p * q) x
      = (eaEval c p x) • eaDeriv c q x + (eaEval c q x) • eaDeriv c p x := by
  simp only [eaDeriv, eaD_mul, eaEval_add, eaEval_mul]
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma eaDeriv_X_inl (c : EAChain k r) (i₀ : Fin k) (x : Fin k → ℝ) :
    eaDeriv c (MvPolynomial.X (Sum.inl i₀) : EAPoly k r) x = ContinuousLinearMap.proj i₀ := by
  rw [eaDeriv]
  calc (∑ i : Fin k, (eaEval c (eaD c i (MvPolynomial.X (Sum.inl i₀) : EAPoly k r)) x) •
          (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ))
      = (eaEval c (eaD c i₀ (MvPolynomial.X (Sum.inl i₀) : EAPoly k r)) x) •
          (ContinuousLinearMap.proj i₀ : (Fin k → ℝ) →L[ℝ] ℝ) :=
        Finset.sum_eq_single i₀
          (fun i _ hi => by rw [eaEval_eaD_X_inl, if_neg hi, zero_smul])
          (fun h => absurd (Finset.mem_univ i₀) h)
    _ = (ContinuousLinearMap.proj i₀ : (Fin k → ℝ) →L[ℝ] ℝ) := by
        rw [eaEval_eaD_X_inl, if_pos rfl, one_smul]

private lemma eaDeriv_X_inr (c : EAChain k r) (j₀ : Fin r) (x : Fin k → ℝ) :
    eaDeriv c (MvPolynomial.X (Sum.inr j₀) : EAPoly k r) x
      = Real.exp (c.ell j₀ x) •
          (∑ i : Fin k, c.a j₀ i • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) := by
  rw [eaDeriv, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [eaEval_eaD_X_inr, smul_smul, mul_comm (c.a j₀ i) (Real.exp (c.ell j₀ x))]

/-- Derivative of the affine form `c.ell j`. -/
private lemma ell_hasFDerivAt (c : EAChain k r) (j : Fin r) (x : Fin k → ℝ) :
    HasFDerivAt (fun y : Fin k → ℝ => c.ell j y)
      (∑ i : Fin k, c.a j i • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) x := by
  have h1 : HasFDerivAt (fun y : Fin k → ℝ => ∑ i : Fin k, c.a j i * y i)
      (∑ i : Fin k, c.a j i • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) x := by
    have h := HasFDerivAt.sum (u := Finset.univ)
      (A := fun i (y : Fin k → ℝ) => c.a j i * y i)
      (A' := fun i => c.a j i • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ))
      (fun i _ => (hasFDerivAt_apply i x).const_mul (c.a j i))
    have key : (∑ i : Fin k, (fun y : Fin k → ℝ => c.a j i * y i))
        = (fun y : Fin k → ℝ => ∑ i : Fin k, c.a j i * y i) := by
      funext y
      simp only [Finset.sum_apply]
    rw [key] at h
    exact h
  have h2 := h1.add_const (c.b j)
  have key : (fun y : Fin k → ℝ => (∑ i : Fin k, c.a j i * y i) + c.b j)
      = (fun y : Fin k → ℝ => c.ell j y) := by
    funext y
    simp only [EAChain.ell]
  rw [key] at h2
  exact h2

private lemma hasFDerivAt_X_inl (c : EAChain k r) (i₀ : Fin k) (x : Fin k → ℝ) :
    HasFDerivAt (eaEval c (MvPolynomial.X (Sum.inl i₀) : EAPoly k r))
      (eaDeriv c (MvPolynomial.X (Sum.inl i₀) : EAPoly k r) x) x := by
  have hfun : eaEval c (MvPolynomial.X (Sum.inl i₀) : EAPoly k r)
      = (fun y : Fin k → ℝ => y i₀) := by
    funext y
    simp [eaEval]
  rw [hfun, eaDeriv_X_inl]
  exact hasFDerivAt_apply i₀ x

private lemma hasFDerivAt_X_inr (c : EAChain k r) (j₀ : Fin r) (x : Fin k → ℝ) :
    HasFDerivAt (eaEval c (MvPolynomial.X (Sum.inr j₀) : EAPoly k r))
      (eaDeriv c (MvPolynomial.X (Sum.inr j₀) : EAPoly k r) x) x := by
  have hfun : eaEval c (MvPolynomial.X (Sum.inr j₀) : EAPoly k r)
      = (fun y : Fin k → ℝ => Real.exp (c.ell j₀ y)) := by
    funext y
    simp [eaEval]
  rw [hfun, eaDeriv_X_inr]
  exact (ell_hasFDerivAt c j₀ x).exp

private lemma hasFDerivAt_X (c : EAChain k r) (n : Fin k ⊕ Fin r) (x : Fin k → ℝ) :
    HasFDerivAt (eaEval c (MvPolynomial.X n : EAPoly k r))
      (eaDeriv c (MvPolynomial.X n : EAPoly k r) x) x := by
  cases n with
  | inl i₀ => exact hasFDerivAt_X_inl c i₀ x
  | inr j₀ => exact hasFDerivAt_X_inr c j₀ x

private lemma eaEvalHasFDerivAt (c : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ) :
    HasFDerivAt (eaEval c Q) (eaDeriv c Q x) x := by
  revert x
  refine MvPolynomial.induction_on
    (motive := fun Q => ∀ x : Fin k → ℝ, HasFDerivAt (eaEval c Q) (eaDeriv c Q x) x) Q ?_ ?_ ?_
  · intro a x
    have hC : eaEval c (MvPolynomial.C a) = (fun _ : Fin k → ℝ => a) := by
      funext y
      simp [eaEval]
    have hD : eaDeriv c (MvPolynomial.C a : EAPoly k r) x = 0 := by
      simp [eaDeriv, eaD_C, eaEval]
    rw [hC, hD]
    exact hasFDerivAt_const a x
  · intro p q hp hq x
    have h : eaEval c (p + q) = eaEval c p + eaEval c q := by
      funext y
      simp [eaEval]
    rw [h, eaDeriv_add]
    exact (hp x).add (hq x)
  · intro p n hp x
    have h : eaEval c (p * MvPolynomial.X n) = eaEval c p * eaEval c (MvPolynomial.X n) := by
      funext y
      simp [eaEval]
    rw [h, eaDeriv_mul]
    exact (hp x).mul (hasFDerivAt_X c n x)

end

theorem hasFDerivAt_eaEval {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ) :
    HasFDerivAt (eaEval c Q)
      ((∑ i : Fin k, (eaEval c (eaD c i Q) x) •
        (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)) : (Fin k → ℝ) →L[ℝ] ℝ) x := by
  simpa only [eaDeriv] using eaEvalHasFDerivAt c Q x

end Work.WilE3.API
