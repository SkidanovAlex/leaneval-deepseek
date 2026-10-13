/-
  Work.WilE2 — the bridge between the symbolic derivative `ESys.d` and the Fréchet
  derivative of the evaluated EA polynomial.

  The main theorem is `ev_hasFDerivAt`: for a chain `S` and an EA polynomial `P`, the
  evaluated function `x ↦ S.ev P x` is (Fréchet) differentiable at every point `x`, with
  derivative the "gradient" continuous linear functional
  `S.grad P x = ∑ a, (S.ev (S.d a P) x) • proj a` of `Grad.lean`.

  The proof is an induction on the polynomial `P` in the generators `C`, `+`, `· X`:
  the derivative of `C c` is `0`; the derivative of a sum is the sum of the derivatives
  (`S.d` and `S.ev` are additive); and the derivative of `P * X s` is the Leibniz rule,
  which is exactly the statement that `S.d` is a derivation (`ESys.d_mul`, proved in
  `Degree.lean`) together with the fact that `S.ev` is a ring homomorphism.

  The only two "primitive" derivatives needed are those of `x ↦ x j` (the coordinate
  projection, a continuous linear map) and of the chain function
  `S.psi j = exp ∘ S.ell j` (exponential of an affine function), for which we use the
  auxiliary continuous linear map `ESys.ellGrad`.
-/
import Mathlib
import Submission.Work.WilE2.Grad

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Classical
namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

section Helpers

variable {n r : ℕ}

/-! ## §1. `S.ev` as a ring homomorphism in the polynomial variable -/

theorem ESys.ev_zero (S : ESys n r) : S.ev (0 : EPoly n r) = fun _ => 0 := by
  funext x; simp [ESys.ev]

theorem ESys.ev_one (S : ESys n r) : S.ev (1 : EPoly n r) = fun _ => 1 := by
  funext x; simp [ESys.ev]

theorem ESys.ev_C (S : ESys n r) (c : ℝ) : S.ev (MvPolynomial.C c) = fun _ => c := by
  funext x; simp [ESys.ev]

theorem ESys.ev_add (S : ESys n r) (P Q : EPoly n r) :
    S.ev (P + Q) = S.ev P + S.ev Q := by
  funext x; simp [ESys.ev, map_add]

theorem ESys.ev_mul (S : ESys n r) (P Q : EPoly n r) :
    S.ev (P * Q) = S.ev P * S.ev Q := by
  funext x; simp [ESys.ev, map_mul]

theorem ESys.ev_X_inl (S : ESys n r) (j : Fin n) :
    S.ev (MvPolynomial.X (Sum.inl j)) = fun x => x j := by
  funext x; simp [ESys.ev]

theorem ESys.ev_X_inr (S : ESys n r) (j : Fin r) :
    S.ev (MvPolynomial.X (Sum.inr j)) = S.psi j := by
  funext x; simp [ESys.ev]

/-! ## §2. The gradient is additive and satisfies the Leibniz rule -/

theorem ESys.grad_C (S : ESys n r) (c : ℝ) (x : Fin n → ℝ) :
    S.grad (MvPolynomial.C c) x = 0 := by
  ext v
  simp [ESys.grad_apply, ESys.d_C, ESys.ev_zero]

theorem ESys.grad_add (S : ESys n r) (P Q : EPoly n r) (x : Fin n → ℝ) :
    S.grad (P + Q) x = S.grad P x + S.grad Q x := by
  ext v
  rw [ESys.grad_apply, ContinuousLinearMap.add_apply, ESys.grad_apply, ESys.grad_apply]
  simp only [ESys.d_add, ESys.ev_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem ESys.grad_mul (S : ESys n r) (P Q : EPoly n r) (x : Fin n → ℝ) :
    S.grad (P * Q) x = S.ev Q x • S.grad P x + S.ev P x • S.grad Q x := by
  ext v
  rw [ESys.grad_apply]
  simp only [ESys.d_mul, ESys.ev_add, ESys.ev_mul, Pi.add_apply, Pi.mul_apply]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, ESys.grad_apply, ESys.grad_apply, smul_eq_mul, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ## §3. Derivatives of the generators -/

/-- The derivative of the affine exponent `S.ell j`: it is the continuous linear
functional `v ↦ ∑ a, S.a j a * v a`. -/
def ESys.ellGrad (S : ESys n r) (j : Fin r) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ a : Fin n, S.a j a • ContinuousLinearMap.proj a

theorem ESys.ellGrad_apply (S : ESys n r) (j : Fin r) (v : Fin n → ℝ) :
    S.ellGrad j v = ∑ a : Fin n, S.a j a * v a := by
  simp [ESys.ellGrad, ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem ESys.grad_X_inl (S : ESys n r) (j : Fin n) (x : Fin n → ℝ) :
    S.grad (MvPolynomial.X (Sum.inl j)) x = ContinuousLinearMap.proj j := by
  ext v
  rw [ESys.grad_apply]
  have hterm : ∀ b : Fin n, S.ev (if b = j then (1:EPoly n r) else 0) x * v b
      = (if b = j then (1:ℝ) else 0) * v b := by
    intro b; split_ifs <;> simp [ESys.ev_one, ESys.ev_zero]
  have h1 : (∑ a : Fin n, S.ev (S.d a (MvPolynomial.X (Sum.inl j))) x * v a)
      = ∑ b : Fin n, (if b = j then (1:ℝ) else 0) * v b := by
    simp only [ESys.d_inl]
    exact Finset.sum_congr rfl fun b _ => hterm b
  rw [h1, Finset.sum_eq_single j]
  · simp [ContinuousLinearMap.proj_apply]
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem ESys.grad_X_inr (S : ESys n r) (j : Fin r) (x : Fin n → ℝ) :
    S.grad (MvPolynomial.X (Sum.inr j)) x = S.psi j x • S.ellGrad j := by
  ext v
  rw [ESys.grad_apply]
  have hterm : ∀ a : Fin n, S.ev (S.d a (MvPolynomial.X (Sum.inr j))) x * v a
      = S.psi j x * (S.a j a * v a) := by
    intro a
    rw [ESys.d_inr]
    simp only [ESys.ev_mul, ESys.ev_C, ESys.ev_X_inr, Pi.mul_apply]
    ring
  have h1 : (∑ a : Fin n, S.ev (S.d a (MvPolynomial.X (Sum.inr j))) x * v a)
      = ∑ a : Fin n, S.psi j x * (S.a j a * v a) :=
    Finset.sum_congr rfl fun a _ => hterm a
  rw [h1, ← Finset.mul_sum]
  simp [ESys.ellGrad_apply, smul_eq_mul]

/-- The affine exponent is differentiable with derivative `S.ellGrad j`. -/
theorem ESys.hasFDerivAt_ell (S : ESys n r) (j : Fin r) (x : Fin n → ℝ) :
    HasFDerivAt (S.ell j) (S.ellGrad j) x := by
  have hFun : S.ell j = fun y : Fin n → ℝ => S.ellGrad j y + S.b j := by
    funext y
    rw [ESys.ell, ESys.ellGrad_apply]
  rw [hFun]
  exact (ContinuousLinearMap.hasFDerivAt (S.ellGrad j)).add_const (S.b j)

theorem ESys.hasFDerivAt_ev_C (S : ESys n r) (c : ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (S.ev (MvPolynomial.C c)) (S.grad (MvPolynomial.C c) x) x := by
  rw [ESys.grad_C, ESys.ev_C]
  exact hasFDerivAt_const c x

theorem ESys.hasFDerivAt_ev_X_inl (S : ESys n r) (j : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (S.ev (MvPolynomial.X (Sum.inl j))) (S.grad (MvPolynomial.X (Sum.inl j)) x) x := by
  rw [ESys.grad_X_inl, ESys.ev_X_inl]
  exact ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) (x := x)

/-- The chain function `S.psi j = exp (S.ell j)` has derivative
`S.psi j x • S.ellGrad j`. -/
theorem ESys.hasFDerivAt_psi (S : ESys n r) (j : Fin r) (x : Fin n → ℝ) :
    HasFDerivAt (S.psi j) (S.psi j x • S.ellGrad j) x :=
  (ESys.hasFDerivAt_ell S j x).exp

theorem ESys.hasFDerivAt_ev_X_inr (S : ESys n r) (j : Fin r) (x : Fin n → ℝ) :
    HasFDerivAt (S.ev (MvPolynomial.X (Sum.inr j))) (S.grad (MvPolynomial.X (Sum.inr j)) x) x := by
  rw [ESys.grad_X_inr, ESys.ev_X_inr]
  exact ESys.hasFDerivAt_psi S j x

theorem ESys.hasFDerivAt_ev_X (S : ESys n r) (s : Fin n ⊕ Fin r) (x : Fin n → ℝ) :
    HasFDerivAt (S.ev (MvPolynomial.X s)) (S.grad (MvPolynomial.X s) x) x := by
  rcases s with j | j
  · exact ESys.hasFDerivAt_ev_X_inl S j x
  · exact ESys.hasFDerivAt_ev_X_inr S j x

end Helpers

/-! ## §4. The main theorem -/

theorem ev_hasFDerivAt {n r : ℕ} (S : ESys n r) (P : EPoly n r) (x : Fin n → ℝ) : HasFDerivAt (S.ev P) (S.grad P x) x := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ESys.hasFDerivAt_ev_C S c x
  | add P Q hP hQ =>
      have h := hP.add hQ
      rw [← ESys.ev_add S P Q, ← ESys.grad_add S P Q x] at h
      exact h
  | mul_X P s hP =>
      have h := hP.mul (ESys.hasFDerivAt_ev_X S s x)
      rw [← ESys.ev_mul S P (MvPolynomial.X s)] at h
      refine h.congr_fderiv ?_
      rw [ESys.grad_mul S P (MvPolynomial.X s) x]
      exact add_comm _ _

end Work.WilE2
