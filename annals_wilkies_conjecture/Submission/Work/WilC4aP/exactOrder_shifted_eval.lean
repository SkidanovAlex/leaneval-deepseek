/-
  annals_wilkies_conjecture, hole `C4a_puiseux` (`PuiseuxReal`): the order of vanishing of the
  fibre polynomial `Pz P 0` at a root `α` seen through the shifted function
  `w ↦ (Pz P 0).eval (w + α)`.

  Mathematically: if `p` is a nonzero polynomial over `ℂ`, `α` a point and
  `p.rootMultiplicity α = k`, then `w ↦ p.eval (w + α)` vanishes to order exactly `k` at `0`.
  Concretely the `j`-th derivative at `0` is `p^{(j)}(α) = j! · [X^j] (taylor α p)`, and the
  shifted polynomial is `X^k` times a factor whose constant term is `p`'s "cofactor" evaluated
  at `α`, which is nonzero because the multiplicity is exactly `k`.

  The file proves the general polynomial statement together with the analytic/algebraic bridge
  `iteratedDeriv n (w ↦ p.eval (w + α)) 0 = p^{(n)}(α)`, then specialises to `p = Pz P 0`,
  which is monic (hence nonzero) because `P` is.
-/
import Mathlib
import Submission.Work.WilC4aP.Basic

set_option autoImplicit false

noncomputable section

open Polynomial

namespace Work.WilC4aP

/-! ### The analytic/algebraic bridge -/

/-- The `n`-th derivative of the polynomial function `z ↦ p.eval z` is the `n`-th formal
derivative of `p`. -/
private theorem aux_iteratedDeriv_eval_self (p : Polynomial ℂ) (n : ℕ) (x : ℂ) :
    iteratedDeriv n (fun z : ℂ => p.eval z) x = (Polynomial.derivative^[n] p).eval x := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    have hd : deriv (fun z : ℂ => p.eval z) = fun z : ℂ => p.derivative.eval z := by
      funext z
      exact (p.hasDerivAt z).deriv
    rw [iteratedDeriv_succ', hd, ih p.derivative, Function.iterate_succ_apply]

/-- Shifting the argument: the `n`-th derivative at `0` of `w ↦ p.eval (w + α)` is the `n`-th
formal derivative of `p` evaluated at `α`. -/
private theorem aux_iteratedDeriv_shift (p : Polynomial ℂ) (α : ℂ) (n : ℕ) :
    iteratedDeriv n (fun w : ℂ => p.eval (w + α)) 0 = (Polynomial.derivative^[n] p).eval α := by
  rw [iteratedDeriv_comp_add_const (n := n) (s := α) (f := fun z : ℂ => p.eval z)]
  simp only [zero_add]
  exact aux_iteratedDeriv_eval_self p n α

/-! ### The Taylor coefficient form -/

/-- `p^{(n)}(α)` is `n!` times the `n`-th coefficient of the Taylor shift `taylor α p`. -/
private theorem aux_eval_derivative_taylor (p : Polynomial ℂ) (α : ℂ) (n : ℕ) :
    (Polynomial.derivative^[n] p).eval α = (n.factorial : ℂ) * (taylor α p).coeff n := by
  have h1 : (n.factorial • Polynomial.hasseDeriv n p) = Polynomial.derivative^[n] p := by
    have := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) n) p
    simpa using this
  rw [← h1, nsmul_eq_mul, Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.taylor_coeff]

/-- The Taylor shift of `X - C α` is `X`. -/
private theorem aux_taylor_X_sub_C (α : ℂ) : taylor α (X - C α : Polynomial ℂ) = X := by
  rw [Polynomial.taylor_apply, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  simp

/-- If `p = (X - C α)^k * q`, the Taylor shift of `p` is divisible by `X^k`. -/
private theorem aux_taylor_coeff_eq_zero {p q : Polynomial ℂ} {α : ℂ} {k j : ℕ}
    (h : p = (X - C α) ^ k * q) (hj : j < k) : (taylor α p).coeff j = 0 := by
  subst h
  rw [Polynomial.taylor_mul, Polynomial.taylor_pow, aux_taylor_X_sub_C]
  exact (Polynomial.X_pow_dvd_iff.mp ⟨taylor α q, rfl⟩) j hj

/-- If `p = (X - C α)^k * q`, the `k`-th coefficient of the Taylor shift of `p` is `q.eval α`. -/
private theorem aux_taylor_coeff_eq {p q : Polynomial ℂ} {α : ℂ} {k : ℕ}
    (h : p = (X - C α) ^ k * q) : (taylor α p).coeff k = q.eval α := by
  subst h
  rw [Polynomial.taylor_mul, Polynomial.taylor_pow, aux_taylor_X_sub_C,
    Polynomial.coeff_X_pow_mul']
  simp [Polynomial.taylor_coeff_zero]

/-! ### The statement -/

theorem exactOrder_shifted_eval (P : Polynomial (ℂ → ℂ)) (hmon : P.Monic) {α : ℂ} {k : ℕ}
    (hroot : (Work.WilC4aP.Pz P 0).rootMultiplicity α = k) :
    (∀ j < k, iteratedDeriv j (fun w : ℂ => (Work.WilC4aP.Pz P 0).eval (w + α)) 0 = 0) ∧
      iteratedDeriv k (fun w : ℂ => (Work.WilC4aP.Pz P 0).eval (w + α)) 0 ≠ 0 := by
  have hpmon : (Pz P 0).Monic := hmon.map _
  have hp0 : (Pz P 0) ≠ 0 := hpmon.ne_zero
  obtain ⟨q, hfac, hndvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (Pz P 0) hp0 α
  rw [hroot] at hfac
  -- the cofactor does not vanish at `α`, because `α` is a root of multiplicity exactly `k`
  have hqα : q.eval α ≠ 0 := fun h =>
    hndvd ((Polynomial.dvd_iff_isRoot).mpr (Polynomial.IsRoot.def.mpr h))
  -- the `j`-th derivative at `0` is `j!` times the `j`-th Taylor coefficient
  have key : ∀ j : ℕ, iteratedDeriv j (fun w : ℂ => (Pz P 0).eval (w + α)) 0
      = (j.factorial : ℂ) * (taylor α (Pz P 0)).coeff j := fun j =>
    (aux_iteratedDeriv_shift (Pz P 0) α j).trans (aux_eval_derivative_taylor (Pz P 0) α j)
  constructor
  · intro j hj
    rw [key j, aux_taylor_coeff_eq_zero hfac hj, mul_zero]
  · rw [key k, aux_taylor_coeff_eq hfac]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)) hqα

end Work.WilC4aP
