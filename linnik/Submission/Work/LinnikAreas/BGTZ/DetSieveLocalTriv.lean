import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup

/-!
# The sieve function at the trivial character equals its value at the quadratic character

`G(s,χ) = Σ_{d,e ≤ R} θ_d θ_e ∏_{p | [d,e]} (u_p(1+χ₁(p)) - χ₁(p)u_p²)`, `u_p = χ(p)p^{-s}`
(`sieveLocal χ₁ χ s p`), is a function of `χ` only through the local factors at the primes
`p ≤ R`.  For a *quadratic* character `χ₁` (`χ₁² = 1`) these local factors at the principal
character `χ₀ = 1` and at `χ = χ₁` coincide:

* if `p | q` then `χ₀(p) = χ₁(p) = 0` and both local factors vanish;
* if `p ∤ q` then `χ₀(p) = 1` and `χ₁(p) ∈ {1,-1}` with `χ₁(p)² = 1`, and the two local factors
  are `(1+x)p^{-s} - x p^{-2s}` with `x = χ₁(p)`: they agree because `(1+x)x = x + x² = x + 1`.

This is the elementary starting point of the detector argument: the principal character is the
one for which `G(1,χ₀)` is bounded by Graham's sieve lemma, while the sum that the detector
actually multiplies is the one at `χ₁` (see `DetectorDefs`).
-/

open DirichletCharacter Complex
open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

/-- A quadratic character (`χ₁² = 1`) of level `q` is real-valued: its value at `p` is the
real number `(χ₁ p).re`. -/
private lemma re_eq_of_sq_eq_one {q : ℕ} (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    (p : ℕ) :
    ((χ₁ (p : ZMod q)).re : ℂ) = χ₁ (p : ZMod q) := by
  have hquad : χ₁.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hχ₁
  rcases hquad (p : ZMod q) with h | h | h <;> rw [h] <;> simp

/-- **The local factors at the principal character and at the quadratic character `χ₁` agree.**
For `p | q` both characters vanish (both local factors are `0`); for `p ∤ q` the trivial
character has value `1`, `χ₁(p)² = 1`, and the two expressions
`(1+x)p^{-s} - x p^{-2s}` and `(1+x)x p^{-s} - x·x² p^{-2s}` coincide because `(1+x)x = 1+x`. -/
private lemma sieveLocal_triv {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ^ 2 = 1) (s : ℂ) (p : ℕ) :
    sieveLocal χ₁ (1 : DirichletCharacter ℂ q) s p = sieveLocal χ₁ χ₁ s p := by
  have hreal := re_eq_of_sq_eq_one χ₁ hχ₁ p
  by_cases hp : IsUnit (p : ZMod q)
  · have ht : (1 : DirichletCharacter ℂ q) (p : ZMod q) = 1 := MulChar.one_apply hp
    have hx2 : χ₁ (p : ZMod q) ^ 2 = 1 := by
      rw [← MulChar.pow_apply' χ₁ two_ne_zero, hχ₁, MulChar.one_apply hp]
    have hxx : (1 + χ₁ (p : ZMod q)) * χ₁ (p : ZMod q) = 1 + χ₁ (p : ZMod q) := by
      have h1 : χ₁ (p : ZMod q) * χ₁ (p : ZMod q) = 1 := by rw [← pow_two]; exact hx2
      rw [add_mul, one_mul, h1, add_comm]
    rw [sieveLocal, sieveLocal, hreal, ht, hx2, hxx]
    ring
  · have ht : (1 : DirichletCharacter ℂ q) (p : ZMod q) = 0 := MulChar.map_nonunit _ hp
    have hx : χ₁ (p : ZMod q) = 0 := MulChar.map_nonunit χ₁ hp
    rw [sieveLocal, sieveLocal, hreal, ht, hx]

theorem DetSieveLocalTriv {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    (R : ℕ) (θw : ℕ → ℝ) (s : ℂ) :
    Work.LinnikAreas.BGTZ.sieveG χ₁ R θw s (1 : DirichletCharacter ℂ q)
      = Work.LinnikAreas.BGTZ.sieveG χ₁ R θw s χ₁ := by
  unfold sieveG
  refine Finset.sum_congr rfl (fun d _ => ?_)
  refine Finset.sum_congr rfl (fun e _ => ?_)
  congr 1
  exact Finset.prod_congr rfl (fun p _ => sieveLocal_triv χ₁ hχ₁ s p)

end Work.LinnikAreas.BGTZ
