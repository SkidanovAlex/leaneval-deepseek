import Mathlib
import Submission.Work.TMComp.Duality.Defs

/-!
# Aubry duality: the twist intertwines `suspA` with `suspA` at the inverted coupling

Aubry duality (Avila--Jitomirskaya, *The Ten Martini Problem*, §1.1) is a unitary
equivalence between the almost Mathieu operator at coupling `λ` and the one at
coupling `1/λ`.  At the level of the *suspension* `suspA α lam` on `ℓ²(ℤ × ℤ)` this
is implemented by the "twist"

`(U f) (m, n) = e^{2πi α m n} f (n, -m)`,

and the precise relation needed is

`twistU α * suspA α lam = (lam : ℂ) • (suspA α lam⁻¹ * twistU α)`.

The identity is proved coordinatewise: both sides are `ℂ`-valued functions of `p`
and the equality reduces to the multiplicativity of the phase character
`ph α : ℤ → ℂ`, `ph α (a + b) = ph α a * ph α b`, together with `lam * lam⁻¹ = 1`.
-/

namespace Work.TMComp.Duality

theorem twistU_intertwines (α lam : ℝ) (hlam : lam ≠ 0) :
    Work.TMComp.Duality.twistU α * Work.TMComp.Duality.suspA α lam =
      (lam : ℂ) • (Work.TMComp.Duality.suspA α lam⁻¹ * Work.TMComp.Duality.twistU α) := by
  refine coord_ext fun f p => ?_
  obtain ⟨m, n⟩ := p
  -- Expand both sides into coordinates.
  rw [mul_apply_eq_comp, smul_apply]
  simp only [mul_apply_eq_comp]
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [twistU_coord, suspA_coord, suspA_coord,
    twistU_coord, twistU_coord, twistU_coord, twistU_coord]
  -- Normalise the index expressions appearing in the two `f`-values that are
  -- indexed differently on the two sides, and the exponent `-(-m)`.
  rw [show (-(m - 1) : ℤ) = -m + 1 from by ring,
      show (-(m + 1) : ℤ) = -m - 1 from by ring,
      show ph α (- -m) = ph α m from by congr 1; ring]
  -- Multiplicativity of the character identifies the four coefficients.
  have h1 : ph α (m * (n + 1)) = ph α (m * n) * ph α m := by
    rw [← ph_add]; congr 1; ring
  have h2 : ph α (m * (n - 1)) = ph α (m * n) * ph α (-m) := by
    rw [← ph_add]; congr 1; ring
  have hw : ∀ X : ℂ, (↑(lam⁻¹) : ℂ) * ph α n * (ph α ((m - 1) * n) * X)
      = (↑(lam⁻¹) : ℂ) * (ph α (m * n) * X) := by
    intro X
    have hh : ph α n * ph α ((m - 1) * n) = ph α (m * n) := by
      rw [← ph_add]; congr 1; ring
    rw [← hh]; ring
  have hz : ∀ X : ℂ, (↑(lam⁻¹) : ℂ) * ph α (-n) * (ph α ((m + 1) * n) * X)
      = (↑(lam⁻¹) : ℂ) * (ph α (m * n) * X) := by
    intro X
    have hh : ph α (-n) * ph α ((m + 1) * n) = ph α (m * n) := by
      rw [← ph_add]; congr 1; ring
    rw [← hh]; ring
  rw [h1, h2, hw, hz]
  -- Reduce the remaining identity in the field `ℂ` using `lam * lam⁻¹ = 1`.
  rw [Complex.ofReal_inv]
  have hlamC : (↑lam : ℂ) ≠ 0 := by simpa using hlam
  field_simp
  ring

end Work.TMComp.Duality
