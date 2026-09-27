import Mathlib
import Submission.Work.EQ.Defs

/-!
# Polynomials attached to the equichordal "endgame" identity

Given a polynomial `D` over `ℂ` and a complex number `lam` (which will be `eqLam a`), we attach
the three polynomials appearing in the cleared germ identity

`(D(u/λ) - D(u)/λ)² (λD(u) - D(λu))² = a² (c²u² + D(u)²) (λD(u/λ) - D(λu)/λ)²`:

* `eP lam D = D(u/λ) - D(u)/λ`,
* `eQ lam D = λD(u) - D(λu)`,
* `eR lam D = λD(u/λ) - D(λu)/λ`,
* `eE c D  = c²u² + D(u)²`.

The main content is `endgame_poly_identity`: the hypothesis of `Work.EQ.eq_endgame`, which is an
identity of *values* for all `u : ℂ`, upgrades to an identity of polynomials.
-/

namespace Work.EQ

open Polynomial

noncomputable def eP (lam : ℂ) (D : ℂ[X]) : ℂ[X] := D.comp (C lam⁻¹ * X) - C lam⁻¹ * D
noncomputable def eQ (lam : ℂ) (D : ℂ[X]) : ℂ[X] := C lam * D - D.comp (C lam * X)
noncomputable def eR (lam : ℂ) (D : ℂ[X]) : ℂ[X] :=
  C lam * D.comp (C lam⁻¹ * X) - C lam⁻¹ * D.comp (C lam * X)
noncomputable def eE (c : ℂ) (D : ℂ[X]) : ℂ[X] := C (c^2) * X^2 + D^2

lemma coeff_eP (lam : ℂ) (D : ℂ[X]) (k : ℕ) :
    (eP lam D).coeff k = D.coeff k * ((lam⁻¹)^k - lam⁻¹) := by
  simp [eP, coeff_sub, coeff_C_mul] <;> ring_nf

lemma coeff_eQ (lam : ℂ) (D : ℂ[X]) (k : ℕ) :
    (eQ lam D).coeff k = D.coeff k * (lam - lam^k) := by
  simp [eQ, coeff_sub, coeff_C_mul] <;> ring_nf

lemma coeff_eR (lam : ℂ) (D : ℂ[X]) (k : ℕ) :
    (eR lam D).coeff k = D.coeff k * (lam * (lam⁻¹)^k - lam⁻¹ * lam^k) := by
  simp [eR, coeff_sub, coeff_C_mul] <;> ring_nf

lemma eval_eP (lam : ℂ) (D : ℂ[X]) (u : ℂ) :
    (eP lam D).eval u = D.eval (u / lam) - D.eval u / lam := by
  simp [eP, eval_comp, div_eq_mul_inv] <;> ring_nf

lemma eval_eQ (lam : ℂ) (D : ℂ[X]) (u : ℂ) :
    (eQ lam D).eval u = lam * D.eval u - D.eval (lam * u) := by
  simp [eQ, eval_comp] <;> ring_nf

lemma eval_eR (lam : ℂ) (D : ℂ[X]) (u : ℂ) :
    (eR lam D).eval u = lam * D.eval (u / lam) - D.eval (lam * u) / lam := by
  simp [eR, eval_comp, div_eq_mul_inv] <;> ring_nf

lemma eval_eE (c : ℂ) (D : ℂ[X]) (u : ℂ) :
    (eE c D).eval u = c^2*u^2 + (D.eval u)^2 := by
  simp [eE] <;> ring_nf

/-- The value identity of `Work.EQ.eq_endgame` upgraded to a polynomial identity. -/
theorem endgame_poly_identity {a : ℝ} {c : ℂ} {D : ℂ[X]}
    (hEND : ∀ u : ℂ,
      (D.eval (u / (eqLam a : ℂ)) - D.eval u / (eqLam a : ℂ)) ^ 2 *
        ((eqLam a : ℂ) * D.eval u - D.eval ((eqLam a : ℂ) * u)) ^ 2
      = ((a : ℂ)) ^ 2 * (c ^ 2 * u ^ 2 + D.eval u ^ 2) *
        ((eqLam a : ℂ) * D.eval (u / (eqLam a : ℂ)) -
          D.eval ((eqLam a : ℂ) * u) / (eqLam a : ℂ)) ^ 2) :
    eP (eqLam a : ℂ) D ^ 2 * eQ (eqLam a : ℂ) D ^ 2
      = C ((a:ℂ)^2) * eE c D * eR (eqLam a : ℂ) D ^ 2 := by
  apply Polynomial.funext
  intro u
  simp only [eval_mul, eval_pow, eval_C, eval_eP, eval_eQ, eval_eE, eval_eR]
  linear_combination hEND u

/-! ## Elementary facts about `eqLam` -/

lemma endgame_lam_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; exact div_pos (by linarith) (by linarith)

lemma endgame_lam_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

/-- `a (1 + λ) = 1 - λ` for `λ = eqLam a` (needs `a ≠ -1`; we use `0 < a`). -/
lemma endgame_lam_rel {a : ℝ} (ha : (0:ℝ) < a) :
    (a : ℂ) * (1 + (eqLam a : ℂ)) = 1 - (eqLam a : ℂ) := by
  have hreal : a * (1 + eqLam a) = 1 - eqLam a := by
    rw [eqLam]
    have h1a : (1 : ℝ) + a ≠ 0 := by linarith
    field_simp
    ring
  exact_mod_cast hreal

/-- `a² (1 + λ)² = (1 - λ)²` for `λ = eqLam a`. -/
lemma endgame_lam_sq_rel {a : ℝ} (ha : (0:ℝ) < a) :
    (a : ℂ)^2 * (1 + (eqLam a : ℂ))^2 = (1 - (eqLam a : ℂ))^2 := by
  have h := congr_arg (fun z : ℂ => z^2) (endgame_lam_rel ha)
  rw [mul_pow] at h
  exact h

end Work.EQ
