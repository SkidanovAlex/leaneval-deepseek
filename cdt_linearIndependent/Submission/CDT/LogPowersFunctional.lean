import Submission.CDT.LogPowersIndependence

/-!
# The powers of `log(1 − x)` are `ℚ(x)`-linearly independent, functional form

The paper's Lemma `seven` begins with the observation that `1`, `log(1−x)`, `log²(1−x)` are
linearly independent over `ℚ(x)`, "since `log(1−x)` is transcendental over `ℚ(x)`".  The
transcendence statement is a function-field Lindemann–Weierstrass theorem; here we obtain the
*linear independence of the functions* without it, by evaluating a hypothetical relation at the
points `x = 1 − 1/n` (`n ≥ 2`), where `log(1/n)` is a *number* to which the classical
Lindemann–Weierstrass theorem applies (`Submission.Transcendence.transcendental_log_rat`),
through the sampled form `Submission.CDT.log_powers_linearIndependent`.

Deliverable: `log_powers_independent_on_Ioo`.
-/

open scoped BigOperators

noncomputable section

namespace Submission.CDT

open Polynomial

/-- **The powers of `log(1 − x)` are `ℚ[x]`-linearly independent on `(0,1)`.**  If the polynomial
combination `Σ_i p_i(x)·log(1 − x)^i` vanishes for every `x ∈ (0,1)`, then every `p_i = 0`. -/
theorem log_powers_independent_on_Ioo (K : ℕ) (p : Fin K → Polynomial ℚ)
    (h : ∀ x : ℝ, 0 < x → x < 1 →
      ∑ i : Fin K, Polynomial.aeval x (p i) * (Real.log (1 - x)) ^ (i : ℕ) = 0) :
    ∀ i, p i = 0 := by
  refine log_powers_linearIndependent K p (fun n hn => ?_)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlt : 1 - (n : ℝ)⁻¹ < 1 := by
    have hpos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hn0
    linarith
  have hgt : 0 < 1 - (n : ℝ)⁻¹ := by
    have hle : (n : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hn1
    linarith
  have hx := h (1 - (n : ℝ)⁻¹) hgt hlt
  rw [show (1 : ℝ) - (1 - (n : ℝ)⁻¹) = (n : ℝ)⁻¹ by ring] at hx
  have hbridge1 : ∀ i : Fin K,
      ((Polynomial.eval (1 - ((n : ℚ))⁻¹) (p i) : ℚ) : ℝ)
        = Polynomial.aeval (1 - (n : ℝ)⁻¹) (p i) := by
    intro i
    have hhom := Polynomial.hom_eval₂ (p i) (RingHom.id ℚ) (algebraMap ℚ ℝ) (1 - ((n : ℚ))⁻¹)
    rw [Polynomial.eval₂_id, RingHom.comp_id] at hhom
    rw [show (algebraMap ℚ ℝ) (1 - ((n : ℚ))⁻¹) = 1 - (n : ℝ)⁻¹ by
      push_cast
      ring] at hhom
    rw [Polynomial.aeval_def, ← hhom]
    rfl
  have hbridge2 : ((Real.log ((((n : ℚ))⁻¹ : ℚ) : ℝ)) : ℝ) = Real.log ((n : ℝ)⁻¹) := by
    congr 1
    push_cast
    ring
  have hterm : ∀ i : Fin K,
      (((p i).eval (1 - ((n : ℚ))⁻¹) : ℚ) : ℂ)
          * (((Real.log ((((n : ℚ))⁻¹ : ℚ) : ℝ)) : ℝ) : ℂ) ^ (i : ℕ)
        = ((Polynomial.aeval (1 - (n : ℝ)⁻¹) (p i)
            * (Real.log ((n : ℝ)⁻¹)) ^ (i : ℕ) : ℝ) : ℂ) := by
    intro i
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
    norm_cast
    rw [hbridge1 i, hbridge2]
  calc ∑ i : Fin K, (((p i).eval (1 - ((n : ℚ))⁻¹) : ℚ) : ℂ)
          * (((Real.log ((((n : ℚ))⁻¹ : ℚ) : ℝ)) : ℝ) : ℂ) ^ (i : ℕ)
      = ∑ i : Fin K, ((Polynomial.aeval (1 - (n : ℝ)⁻¹) (p i)
          * (Real.log ((n : ℝ)⁻¹)) ^ (i : ℕ) : ℝ) : ℂ) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ((∑ i : Fin K, Polynomial.aeval (1 - (n : ℝ)⁻¹) (p i)
          * (Real.log ((n : ℝ)⁻¹)) ^ (i : ℕ) : ℝ) : ℂ) := (Complex.ofReal_sum _ _).symm
    _ = 0 := by rw [hx, Complex.ofReal_zero]

end Submission.CDT
