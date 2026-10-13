import Mathlib
import Submission.Work.WilE3.Defs

namespace Work.WilE3.API

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical Topology
open WilkiesDesign.E
open Work.WilE3

noncomputable section

/-! ## Auxiliary lemmas: the derivative of `eaEvalC` -/

/-- The chain coordinates of `eaEvalC`: variable `Sum.inl i` is `z i` and variable `Sum.inr j`
is `exp (∑ i, a j i * z i + b j)`. -/
def eaPsi {k r : ℕ} (c : EAChain k r) (z : Fin k → ℂ) : Fin k ⊕ Fin r → ℂ :=
  Sum.elim z fun j => Complex.exp (∑ i, (c.a j i : ℂ) * z i + (c.b j : ℂ))

lemma eaEvalC_eq {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (z : Fin k → ℂ) :
    eaEvalC c Q z = MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) (eaPsi c z) Q := rfl

/-- `dEvalC c Q z` is the candidate derivative of `eaEvalC c Q` at `z`. -/
def dEvalC {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (z : Fin k → ℂ) :
    (Fin k → ℂ) →L[ℂ] ℂ :=
  ∑ i : Fin k, (eaEvalC c (eaD c i Q) z) •
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)

/-! ### Algebraic identities for `eaD` -/

lemma eaD_C {k r : ℕ} (c : EAChain k r) (i : Fin k) (a : ℝ) :
    eaD c i (MvPolynomial.C a) = 0 := by
  simp [eaD]

lemma eaD_add {k r : ℕ} (c : EAChain k r) (i : Fin k) (Q Q' : EAPoly k r) :
    eaD c i (Q + Q') = eaD c i Q + eaD c i Q' := by
  simp only [eaD, map_add, mul_add]
  rw [Finset.sum_add_distrib]
  ac_rfl

lemma eaD_mul {k r : ℕ} (c : EAChain k r) (i : Fin k) (Q Q' : EAPoly k r) :
    eaD c i (Q * Q') = eaD c i Q * Q' + Q * eaD c i Q' := by
  have key : ∀ j : Fin r,
      MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) *
          MvPolynomial.pderiv (Sum.inr j) (Q * Q')
        = MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) *
              MvPolynomial.pderiv (Sum.inr j) Q * Q'
          + Q * (MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) *
              MvPolynomial.pderiv (Sum.inr j) Q') := by
    intro j
    rw [MvPolynomial.pderiv_mul]
    ring
  have hsum_eq : (∑ j : Fin r, MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) *
          MvPolynomial.pderiv (Sum.inr j) (Q * Q'))
      = ∑ j : Fin r, (MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) *
              MvPolynomial.pderiv (Sum.inr j) Q * Q'
          + Q * (MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) *
              MvPolynomial.pderiv (Sum.inr j) Q')) := by
    apply Finset.sum_congr rfl
    intro j _
    exact key j
  simp only [eaD]
  rw [MvPolynomial.pderiv_mul, hsum_eq, Finset.sum_add_distrib]
  rw [add_mul, Finset.sum_mul, mul_add, Finset.mul_sum]
  ac_rfl

lemma eaD_X_inl {k r : ℕ} (c : EAChain k r) (i i₀ : Fin k) :
    eaD c i (MvPolynomial.X (Sum.inl i₀)) = if i = i₀ then 1 else 0 := by
  simp only [eaD, MvPolynomial.pderiv_X]
  simp only [Pi.single_eq_of_ne (Sum.inl_ne_inr), mul_zero, Finset.sum_const_zero, add_zero]
  rw [Pi.single_apply]
  simp [eq_comm]

lemma eaD_X_inr {k r : ℕ} (c : EAChain k r) (i : Fin k) (j₀ : Fin r) :
    eaD c i (MvPolynomial.X (Sum.inr j₀)) =
      MvPolynomial.C (c.a j₀ i) * MvPolynomial.X (Sum.inr j₀) := by
  simp only [eaD, MvPolynomial.pderiv_X]
  simp only [Pi.single_eq_of_ne (Sum.inr_ne_inl), zero_mul, zero_add, Finset.sum_const_zero]
  rw [Finset.sum_eq_single j₀]
  · rw [Pi.single_eq_same, mul_one]
  · intro b _ hb
    rw [Pi.single_eq_of_ne (by intro h; exact hb (Sum.inr_injective h).symm)]
    simp
  · intro h; exact absurd (Finset.mem_univ j₀) h

/-! ### Basic evaluation identities -/

lemma eaEvalC_add {k r : ℕ} (c : EAChain k r) (Q Q' : EAPoly k r) (z : Fin k → ℂ) :
    eaEvalC c (Q + Q') z = eaEvalC c Q z + eaEvalC c Q' z := by
  simp only [eaEvalC, MvPolynomial.eval₂_add]

lemma eaEvalC_mul {k r : ℕ} (c : EAChain k r) (Q Q' : EAPoly k r) (z : Fin k → ℂ) :
    eaEvalC c (Q * Q') z = eaEvalC c Q z * eaEvalC c Q' z := by
  simp only [eaEvalC, MvPolynomial.eval₂_mul]

lemma eaEvalC_C {k r : ℕ} (c : EAChain k r) (a : ℝ) (z : Fin k → ℂ) :
    eaEvalC c (MvPolynomial.C a) z = (a : ℂ) := by
  simp [eaEvalC, MvPolynomial.eval₂_C]

lemma eaEvalC_zero {k r : ℕ} (c : EAChain k r) (z : Fin k → ℂ) :
    eaEvalC c (0 : EAPoly k r) z = 0 := by
  rw [eaEvalC_eq]; simp

lemma eaEvalC_one {k r : ℕ} (c : EAChain k r) (z : Fin k → ℂ) :
    eaEvalC c (1 : EAPoly k r) z = 1 := by
  rw [eaEvalC_eq]; simp

lemma eaEvalC_X_inl {k r : ℕ} (c : EAChain k r) (i : Fin k) (z : Fin k → ℂ) :
    eaEvalC c (MvPolynomial.X (Sum.inl i)) z = z i := by
  simp only [eaEvalC, MvPolynomial.eval₂_X, Sum.elim_inl]

lemma eaEvalC_X_inr {k r : ℕ} (c : EAChain k r) (j : Fin r) (z : Fin k → ℂ) :
    eaEvalC c (MvPolynomial.X (Sum.inr j)) z =
      Complex.exp (∑ i, (c.a j i : ℂ) * z i + (c.b j : ℂ)) := by
  simp only [eaEvalC, MvPolynomial.eval₂_X, Sum.elim_inr]

lemma eaEvalC_C_fun {k r : ℕ} (c : EAChain k r) (a : ℝ) :
    eaEvalC c (MvPolynomial.C a) = fun _ => (a : ℂ) := by
  funext z
  exact eaEvalC_C c a z

lemma eaEvalC_add_fun {k r : ℕ} (c : EAChain k r) (p q : EAPoly k r) :
    eaEvalC c (p + q) = eaEvalC c p + eaEvalC c q := by
  funext z
  simp only [Pi.add_apply]
  exact eaEvalC_add c p q z

lemma eaEvalC_mul_fun {k r : ℕ} (c : EAChain k r) (p q : EAPoly k r) :
    eaEvalC c (p * q) = eaEvalC c p * eaEvalC c q := by
  funext z
  simp only [Pi.mul_apply]
  exact eaEvalC_mul c p q z

lemma eaEvalC_eaD_X_inl {k r : ℕ} (c : EAChain k r) (i i₀ : Fin k) (z : Fin k → ℂ) :
    eaEvalC c (eaD c i (MvPolynomial.X (Sum.inl i₀))) z = if i = i₀ then 1 else 0 := by
  rw [eaD_X_inl]
  by_cases h : i = i₀
  · simp [h, eaEvalC_one]
  · simp [h, eaEvalC_zero]

lemma eaEvalC_eaD_X_inr {k r : ℕ} (c : EAChain k r) (i : Fin k) (j₀ : Fin r)
    (z : Fin k → ℂ) :
    eaEvalC c (eaD c i (MvPolynomial.X (Sum.inr j₀))) z
      = (c.a j₀ i : ℂ) * eaEvalC c (MvPolynomial.X (Sum.inr j₀)) z := by
  rw [eaD_X_inr, eaEvalC_mul, eaEvalC_C]

/-- Pull a scalar out of a finite sum of scalar multiples. -/
lemma sum_mul_smul_sum {ι : Type*} [Fintype ι] (A : ι → ℂ) (b : ℂ)
    {M : Type*} [AddCommMonoid M] [Module ℂ M] (L : ι → M) :
    (∑ i, (A i * b) • L i) = b • (∑ i, A i • L i) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (A i) b, smul_smul]

/-- Variant of `sum_mul_smul_sum` with the scalar on the left. -/
lemma sum_scalar_mul_smul_sum {ι : Type*} [Fintype ι] (b : ℂ) (A : ι → ℂ)
    {M : Type*} [AddCommMonoid M] [Module ℂ M] (L : ι → M) :
    (∑ i, (b * A i) • L i) = b • (∑ i, A i • L i) := by
  rw [← sum_mul_smul_sum A b L]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

/-! ### `dEvalC` identities used in the induction -/

lemma dEvalC_C {k r : ℕ} (c : EAChain k r) (a : ℝ) (z : Fin k → ℂ) :
    dEvalC c (MvPolynomial.C a) z = 0 := by
  simp only [dEvalC]
  rw [Finset.sum_eq_zero]
  intro i _
  rw [eaD_C, eaEvalC_zero]
  exact zero_smul ℂ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)

lemma dEvalC_add {k r : ℕ} (c : EAChain k r) (p q : EAPoly k r) (z : Fin k → ℂ) :
    dEvalC c (p + q) z = dEvalC c p z + dEvalC c q z := by
  have hsum_eq : (∑ i : Fin k, (eaEvalC c (eaD c i (p + q)) z) •
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i))
      = ∑ i : Fin k, ((eaEvalC c (eaD c i p) z) •
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)
          + (eaEvalC c (eaD c i q) z) •
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [eaD_add, eaEvalC_add]
    exact add_smul (eaEvalC c (eaD c i p) z) (eaEvalC c (eaD c i q) z)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)
  simp only [dEvalC]
  rw [hsum_eq, Finset.sum_add_distrib]

lemma dEvalC_mul_X {k r : ℕ} (c : EAChain k r) (p : EAPoly k r) (n : Fin k ⊕ Fin r)
    (z : Fin k → ℂ) :
    dEvalC c (p * MvPolynomial.X n) z
      = (eaEvalC c p z) • dEvalC c (MvPolynomial.X n) z
        + (eaEvalC c (MvPolynomial.X n) z) • dEvalC c p z := by
  have hsum_eq : (∑ i : Fin k, (eaEvalC c (eaD c i (p * MvPolynomial.X n)) z) •
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i))
      = ∑ i : Fin k, ((eaEvalC c (eaD c i p) z * eaEvalC c (MvPolynomial.X n) z) •
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)
          + (eaEvalC c p z * eaEvalC c (eaD c i (MvPolynomial.X n)) z) •
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [eaD_mul, eaEvalC_add, eaEvalC_mul, eaEvalC_mul]
    exact add_smul (eaEvalC c (eaD c i p) z * eaEvalC c (MvPolynomial.X n) z)
      (eaEvalC c p z * eaEvalC c (eaD c i (MvPolynomial.X n)) z)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)
  simp only [dEvalC]
  rw [hsum_eq, Finset.sum_add_distrib]
  simp only [sum_mul_smul_sum, sum_scalar_mul_smul_sum]
  rw [add_comm]

/-! ### Analyticity and derivative of the coordinate functions -/

lemma eaEvalC_X_coord {k r : ℕ} (c : EAChain k r) (n : Fin k ⊕ Fin r) (z : Fin k → ℂ) :
    AnalyticAt ℂ (fun z => eaEvalC c (MvPolynomial.X n) z) z ∧
    HasFDerivAt (fun z => eaEvalC c (MvPolynomial.X n) z)
      ((∑ i : Fin k, (eaEvalC c (eaD c i (MvPolynomial.X n)) z) •
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)) :
        (Fin k → ℂ) →L[ℂ] ℂ) z := by
  cases n with
  | inl i₀ =>
    have hfun : (fun z : Fin k → ℂ => eaEvalC c (MvPolynomial.X (Sum.inl i₀)) z)
        = ⇑(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i₀) := by
      funext z
      simp only [eaEvalC, MvPolynomial.eval₂_X, Sum.elim_inl, ContinuousLinearMap.proj_apply]
    have hsum : (∑ i : Fin k, (eaEvalC c (eaD c i (MvPolynomial.X (Sum.inl i₀))) z) •
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i))
        = ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i₀ := by
      have h1 : (∑ i : Fin k, (eaEvalC c (eaD c i (MvPolynomial.X (Sum.inl i₀))) z) •
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i))
          = ∑ i : Fin k, (if i = i₀ then (1 : ℂ) else 0) •
              (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [eaEvalC_eaD_X_inl]
      rw [h1, Finset.sum_eq_single i₀]
      · rw [if_pos rfl]
        exact one_smul ℂ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i₀)
      · intro b _ hb
        rw [if_neg hb]
        exact zero_smul ℂ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) b)
      · intro h; exact absurd (Finset.mem_univ i₀) h
    rw [hfun, hsum]
    exact ⟨(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i₀).analyticAt z,
           (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i₀).hasFDerivAt⟩
  | inr j₀ =>
    have hfun : (fun z : Fin k → ℂ => eaEvalC c (MvPolynomial.X (Sum.inr j₀)) z)
        = fun z => Complex.exp (∑ i, (c.a j₀ i : ℂ) * z i + (c.b j₀ : ℂ)) := by
      funext z
      simp only [eaEvalC, MvPolynomial.eval₂_X, Sum.elim_inr]
    have hG : HasFDerivAt (fun z : Fin k → ℂ => (∑ i, (c.a j₀ i : ℂ) * z i) + (c.b j₀ : ℂ))
        (∑ i : Fin k, (c.a j₀ i : ℂ) •
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)) z := by
      have h1 : HasFDerivAt (fun z : Fin k → ℂ => ∑ i, (c.a j₀ i : ℂ) * z i)
          (∑ i : Fin k, (c.a j₀ i : ℂ) •
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)) z :=
        HasFDerivAt.fun_sum (u := Finset.univ)
          (A := fun (i : Fin k) (z : Fin k → ℂ) => (c.a j₀ i : ℂ) * z i)
          (A' := fun i => (c.a j₀ i : ℂ) •
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i))
          (x := z)
          (fun i _ => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i).hasFDerivAt.const_smul (c.a j₀ i : ℂ))
      have h2 : HasFDerivAt (fun _ : Fin k → ℂ => (c.b j₀ : ℂ)) (0 : (Fin k → ℂ) →L[ℂ] ℂ) z :=
        hasFDerivAt_const _ z
      have hh := h1.add h2
      rw [add_zero] at hh
      exact hh
    have hExp : HasFDerivAt
        (fun z : Fin k → ℂ => Complex.exp (∑ i, (c.a j₀ i : ℂ) * z i + (c.b j₀ : ℂ)))
        (Complex.exp (∑ i, (c.a j₀ i : ℂ) * z i + (c.b j₀ : ℂ)) •
          (∑ i : Fin k, (c.a j₀ i : ℂ) •
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i))) z := by
      exact hG.cexp
    have hsum : (∑ i : Fin k, (eaEvalC c (eaD c i (MvPolynomial.X (Sum.inr j₀))) z) •
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i))
        = Complex.exp (∑ i, (c.a j₀ i : ℂ) * z i + (c.b j₀ : ℂ)) •
          (∑ i : Fin k, (c.a j₀ i : ℂ) •
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)) := by
      have hc : ∀ i : Fin k, eaEvalC c (eaD c i (MvPolynomial.X (Sum.inr j₀))) z
          = (c.a j₀ i : ℂ) * Complex.exp (∑ i, (c.a j₀ i : ℂ) * z i + (c.b j₀ : ℂ)) := by
        intro i
        rw [eaEvalC_eaD_X_inr, eaEvalC_X_inr]
      have h1 : (∑ i : Fin k, (eaEvalC c (eaD c i (MvPolynomial.X (Sum.inr j₀))) z) •
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i))
          = ∑ i : Fin k, ((c.a j₀ i : ℂ) *
                Complex.exp (∑ i, (c.a j₀ i : ℂ) * z i + (c.b j₀ : ℂ))) •
              (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hc i]
      rw [h1]
      exact sum_mul_smul_sum (fun i => (c.a j₀ i : ℂ))
        (Complex.exp (∑ i, (c.a j₀ i : ℂ) * z i + (c.b j₀ : ℂ)))
        (fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i)
    rw [hfun]
    refine ⟨?_, ?_⟩
    · have hGa : AnalyticAt ℂ (fun z : Fin k → ℂ => ∑ i, (c.a j₀ i : ℂ) * z i) z := by
        have h : ∀ i ∈ (Finset.univ : Finset (Fin k)),
            AnalyticAt ℂ (fun z : Fin k → ℂ => (c.a j₀ i : ℂ) * z i) z := fun i _ =>
          analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i).analyticAt z)
        have h' := Finset.analyticAt_sum (Finset.univ : Finset (Fin k)) h
        have hfn : (∑ i : Fin k, (fun z : Fin k → ℂ => (c.a j₀ i : ℂ) * z i))
            = fun z : Fin k → ℂ => ∑ i, (c.a j₀ i : ℂ) * z i :=
          Finset.sum_fn Finset.univ _
        rw [hfn] at h'
        exact h'
      exact (hGa.add analyticAt_const).cexp'
    · rw [hsum]
      exact hExp

end

theorem eaEvalC_fderiv_analytic {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r)
    (z : Fin k → ℂ) :
    AnalyticAt ℂ (Work.WilE3.eaEvalC c Q) z ∧
    HasFDerivAt (Work.WilE3.eaEvalC c Q)
      ((∑ i : Fin k, (Work.WilE3.eaEvalC c (eaD c i Q) z) •
        (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℂ) i)) : (Fin k → ℂ) →L[ℂ] ℂ) z := by
  change AnalyticAt ℂ (eaEvalC c Q) z ∧ HasFDerivAt (eaEvalC c Q) (dEvalC c Q z) z
  induction Q using MvPolynomial.induction_on with
  | C a =>
    exact ⟨by rw [eaEvalC_C_fun]; exact analyticAt_const,
           by rw [eaEvalC_C_fun, dEvalC_C]; exact hasFDerivAt_const (a : ℂ) z⟩
  | add p q hp hq =>
    refine ⟨?_, ?_⟩
    · rw [eaEvalC_add_fun]; exact hp.1.add hq.1
    · rw [eaEvalC_add_fun, dEvalC_add]; exact hp.2.add hq.2
  | mul_X p n hp =>
    refine ⟨?_, ?_⟩
    · rw [eaEvalC_mul_fun]
      exact hp.1.mul (eaEvalC_X_coord c n z).1
    · rw [eaEvalC_mul_fun, dEvalC_mul_X]
      exact hp.2.mul (eaEvalC_X_coord c n z).2

end Work.WilE3.API
