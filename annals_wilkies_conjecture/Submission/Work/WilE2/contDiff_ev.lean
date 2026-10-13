/-
  Work.WilE2 — smoothness of the evaluation of an EA polynomial along an exp-affine chain.

  `S.ev P` is the function `x ↦ MvPolynomial.eval (Sum.elim x (fun j => exp (S.ell j x))) P`:
  a polynomial in the coordinates `x i` and in the chain functions `ψ_j x = exp (S.ell j x)`.
  Each of the `n + r` "coordinate" functions is `C^∞` (the coordinates are continuous linear
  maps, and `ψ_j` is the exponential of an affine function), and `MvPolynomial.eval` turns
  sums and products of `C^N` functions into `C^N` functions.  Hence `S.ev P` is `C^N` for every
  order `N : WithTop ℕ∞`, in particular `C^k` for every `k : ℕ`.
-/
import Mathlib
import Submission.Work.WilE2.Defs

set_option autoImplicit false

noncomputable section
open Classical
namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n r : ℕ}

/-! ## §1. Smoothness of the generators -/

/-- The linear part `v ↦ ∑ i, a j i * v i` of the affine exponent `S.ell j`, as a
continuous linear functional. -/
def ESys.ellL (S : ESys n r) (j : Fin r) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ a : Fin n, S.a j a • ContinuousLinearMap.proj a

theorem ESys.ellL_apply (S : ESys n r) (j : Fin r) (v : Fin n → ℝ) :
    S.ellL j v = ∑ a : Fin n, S.a j a * v a := by
  simp [ESys.ellL, ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The affine exponent is its linear part plus the constant `b j`. -/
theorem ESys.ell_eq_ellL (S : ESys n r) (j : Fin r) :
    S.ell j = fun x : Fin n → ℝ => S.ellL j x + S.b j := by
  funext x
  rw [ESys.ell, ESys.ellL_apply]

theorem ESys.contDiff_ell (S : ESys n r) (j : Fin r) (N : WithTop ℕ∞) :
    ContDiff ℝ N (S.ell j) := by
  rw [ESys.ell_eq_ellL]
  simpa using (S.ellL j).contDiff.add (contDiff_const (c := S.b j))

theorem ESys.contDiff_psi (S : ESys n r) (j : Fin r) (N : WithTop ℕ∞) :
    ContDiff ℝ N (S.psi j) :=
  (Real.contDiff_exp.of_le le_top).comp (ESys.contDiff_ell S j N)

/-- Each of the `n + r` "coordinate" functions of the substitution is `C^N`. -/
theorem ESys.contDiff_ev_X (S : ESys n r) (s : Fin n ⊕ Fin r) (N : WithTop ℕ∞) :
    ContDiff ℝ N (S.ev (MvPolynomial.X s)) := by
  rcases s with j | j
  · have h : S.ev (MvPolynomial.X (Sum.inl j)) = fun x : Fin n → ℝ => x j := by
      funext x; simp [ESys.ev]
    rw [h]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).contDiff
  · have h : S.ev (MvPolynomial.X (Sum.inr j)) = S.psi j := by
      funext x; simp [ESys.ev, ESys.psi]
    rw [h]
    exact ESys.contDiff_psi S j N

/-! ## §2. Main theorem -/

/-- `S.ev` is a polynomial expression in the substitution `Sum.elim x (fun j => S.psi j x)`,
so it is `C^N` for every order `N`. -/
theorem ESys.contDiff_ev_of (S : ESys n r) (N : WithTop ℕ∞) (P : EPoly n r) :
    ContDiff ℝ N (S.ev P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have h : S.ev (MvPolynomial.C c) = fun _ : Fin n → ℝ => c := by
        funext x; simp [ESys.ev]
      rw [h]
      exact contDiff_const
  | add P Q hP hQ =>
      have h : S.ev (P + Q) = S.ev P + S.ev Q := by
        funext x; simp [ESys.ev, map_add]
      rw [h]
      exact hP.add hQ
  | mul_X P s hP =>
      have h : S.ev (P * MvPolynomial.X s) = S.ev P * S.ev (MvPolynomial.X s) := by
        funext x; simp [ESys.ev, map_mul]
      rw [h]
      exact hP.mul (ESys.contDiff_ev_X S s N)

theorem contDiff_ev {n r : ℕ} (S : ESys n r) (P : EPoly n r) (k : ℕ) :
    ContDiff ℝ (k : WithTop ℕ∞) (S.ev P) :=
  ESys.contDiff_ev_of S (k : WithTop ℕ∞) P

end Work.WilE2
