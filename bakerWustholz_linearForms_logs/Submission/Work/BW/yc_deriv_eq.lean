import Mathlib
import Submission.Work.BW.yc_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- Hasse derivative of the affine substitution `X ↦ aX + c`: the `n`-th Hasse derivative of
`q(X)` composed with `X ↦ aX + c` is `a^n` times the `n`-th Hasse derivative of `q` evaluated
at `aX + c`.  Proved via the iterated ordinary derivative. -/
lemma hasseDeriv_comp_affine_aux (q : ℂ[X]) (a c : ℂ) (n : ℕ) :
    Polynomial.hasseDeriv n (q.comp (Polynomial.C a * Polynomial.X + Polynomial.C c))
      = Polynomial.C (a ^ n) *
        (Polynomial.hasseDeriv n q).comp (Polynomial.C a * Polynomial.X + Polynomial.C c) := by
  have iter : (Polynomial.derivative)^[n] (q.comp (Polynomial.C a * Polynomial.X + Polynomial.C c))
      = Polynomial.C (a ^ n) * ((Polynomial.derivative)^[n] q).comp
          (Polynomial.C a * Polynomial.X + Polynomial.C c) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      rw [Polynomial.derivative_C_mul, Polynomial.derivative_comp]
      have hd : Polynomial.derivative (Polynomial.C a * Polynomial.X + Polynomial.C c)
          = Polynomial.C a := by simp
      have hiter : Polynomial.derivative ((Polynomial.derivative)^[n] q)
          = (Polynomial.derivative)^[n.succ] q :=
        (Function.iterate_succ_apply' Polynomial.derivative n q).symm
      rw [hd, hiter, ← mul_assoc, ← Polynomial.C_mul, ← pow_succ]
  have hfac : ∀ (p : ℂ[X]),
      Polynomial.hasseDeriv n p = Polynomial.C (((n.factorial : ℂ))⁻¹) * (Polynomial.derivative)^[n] p := by
    intro p
    have h : Polynomial.C (((n.factorial : ℂ))) * Polynomial.hasseDeriv n p
        = (Polynomial.derivative)^[n] p := by
      have h0 := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) n) p
      rw [← Nat.cast_smul_eq_nsmul ℂ n.factorial (Polynomial.hasseDeriv n)] at h0
      rw [LinearMap.smul_apply] at h0
      simpa only [Polynomial.smul_eq_C_mul] using h0
    have hnz : ((n.factorial : ℂ)) ≠ 0 := by simp [Nat.factorial_ne_zero]
    rw [← h, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hnz, Polynomial.C_1, one_mul]
  rw [hfac (q.comp (Polynomial.C a * Polynomial.X + Polynomial.C c)), hfac q, iter]
  rw [Polynomial.mul_comp, Polynomial.C_comp]
  ring

/-- `hasseDeriv` commutes with left multiplication by a constant. -/
lemma hasseDeriv_C_mul' (t : ℕ) (R : ℂ) (P : ℂ[X]) :
    Polynomial.hasseDeriv t (Polynomial.C R * P)
      = Polynomial.C R * Polynomial.hasseDeriv t P := by
  rw [← Polynomial.smul_eq_C_mul, LinearMap.map_smul, Polynomial.smul_eq_C_mul]

/-- The `t`-th Hasse derivative of `ycP h d 0` is `ycP h d t`. -/
lemma ycP_hasseDeriv (h d t : ℕ) :
    Polynomial.hasseDeriv t (ycP h d 0) = ycP h d t := by
  simp only [ycP, Polynomial.hasseDeriv_zero, LinearMap.id_coe, id_eq,
    Polynomial.hasseDeriv_map]

/-- The `t₀`-th Hasse derivative of the `Y₀`-shadow `ycY0 h d 0 a c` is `a^{t₀}` times
`ycY0 h d t₀ a c`. -/
lemma ycY0_hasseDeriv (h d t0 : ℕ) (a c : ℂ) :
    Polynomial.hasseDeriv t0 (ycY0 h d 0 a c)
      = Polynomial.C (a ^ t0) * ycY0 h d t0 a c := by
  have h1 := hasseDeriv_comp_affine_aux (ycP h d 0) a c t0
  simp only [ycY0] at h1 ⊢
  rw [h1, ycP_hasseDeriv]

/-- The twist `Q^{(J)}_μ(·;t0,0)` is, up to the scalar `(ulcm h)^{t0}`, the `t0`-th Hasse
derivative of the univariate shadow of `Q^{(J)}_μ(·;0)` (with `ycQ` as defined in `yc_defs`). -/
theorem yc_deriv_eq {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) :
    Polynomial.C ((ulcm h : ℂ) ^ t0) * Polynomial.hasseDeriv t0 (ycQ φ h D0 Dj p J μ 0)
      = Polynomial.C ((((2 : ℂ) ^ J)⁻¹) ^ t0) * ycQ φ h D0 Dj p J μ t0 := by
  classical
  unfold ycQ
  rw [Finset.mul_sum]
  rw [map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lm _
  by_cases hc : (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
  · rw [if_pos hc, if_pos hc]
    rw [hasseDeriv_C_mul', ycY0_hasseDeriv]
    simp only [Polynomial.C_mul, pow_zero, mul_one]
    ring
  · rw [if_neg hc, if_neg hc]
    simp

end Work.BW
