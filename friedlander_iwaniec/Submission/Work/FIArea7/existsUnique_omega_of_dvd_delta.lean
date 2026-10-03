/-
# `Submission.Work.FIArea7.existsUnique_omega_of_dvd_delta` — the `ω`-congruence (19.7)

*FI* §19 attaches to a pair `z₁, z₂` of Gaussian integers and a modulus `q` (with `(q, |z₂|²) = 1`)
the congruence `z₁ ≡ ω z₂ (mod q)`, i.e. the two rational congruences

  `r₁ ≡ ω r₂`,  `s₁ ≡ ω s₂   (mod q)`,

and needs that `ω` exists and is unique precisely when `q ∣ Δ(z₁,z₂) = r₁s₂ − r₂s₁`.  The
existence half is (19.7) of the paper (see `FIArea7.dvd_delta_iff_exists_omega`); here we prove
the *unique existence* form, which is the shape used downstream (the map `z ↦ ω` is well
defined).

Since `(r₂² + s₂², q) = 1`, the element `r₂² + s₂²` is a unit of `ZMod q`, and the only candidate
is the "complex quotient"

  `ω = (r₁r₂ + s₁s₂)·(r₂² + s₂²)⁻¹`,

which maps to `r₁`, `s₁` exactly because `r₂² + s₂² ≡ 0 (mod q)` forces the two linear
congruences to be compatible (`q ∣ Δ`), and whose uniqueness is immediate from the invertibility
of `r₂² + s₂²`.

Everything is elementary: `Delta_eq` unfolds `Δ` in coordinates, `ZMod.intCast_eq_intCast_iff`
turns the `ZMod q`-identities into integer congruences, and the coprimality hypothesis is
converted to the unit `ZMod.isUnit_iff_coprime`.
-/
import Mathlib
import Submission.Work.FIArea7.FIsymbols

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

open scoped BigOperators

/-- **The `ω`-congruence, unique-existence form.**  For `q > 0` and `(q, |z₂|²) = 1`, if
`q ∣ Δ(z₁,z₂)` then there is exactly one `ω ∈ ZMod q` with `r₁ ≡ ω r₂` and `s₁ ≡ ω s₂ (mod q)`;
concretely `ω = (r₁r₂ + s₁s₂)/(r₂² + s₂²)` in `ZMod q`. -/
theorem existsUnique_omega_of_dvd_delta {q : ℕ} (hq : 0 < q) (z1 z2 : GaussianInt)
    (hcop : Nat.Coprime (Work.FIPlan.gnorm z2) q)
    (hD : (q : ℤ) ∣ Work.FIPlan.Delta z1 z2) :
    ∃! ω : ZMod q, (z1.re : ZMod q) = ω * (z2.re : ZMod q)
      ∧ (z1.im : ZMod q) = ω * (z2.im : ZMod q) := by
  -- `Δ` in coordinates
  have hDelta : Work.FIPlan.Delta z1 z2 = z1.re * z2.im - z2.re * z1.im := by
    simp only [Work.FIPlan.Delta, Zsqrtd.im_mul, Zsqrtd.im_star, Zsqrtd.re_star]
    ring
  have hΔ : (q : ℤ) ∣ z1.re * z2.im - z2.re * z1.im := by rwa [hDelta] at hD
  -- `|z₂|² = r₂² + s₂²` is a unit of `ZMod q`
  have hu : IsUnit (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod q) :=
    (ZMod.isUnit_iff_coprime (Work.FIPlan.gnorm z2) q).mpr hcop
  obtain ⟨U, hU⟩ := hu
  have hDcast : ((Work.FIPlan.gnorm z2 : ℕ) : ZMod q)
      = (z2.re : ZMod q)^2 + (z2.im : ZMod q)^2 := by
    have h : ((Work.FIPlan.gnorm z2 : ℤ) : ZMod q)
        = (z2.re : ZMod q)^2 + (z2.im : ZMod q)^2 := by
      rw [norm_eq]; push_cast; ring
    simpa using h
  -- `(r₁r₂ + s₁s₂) r₂ ≡ r₁ (r₂² + s₂²)` and likewise for `s₂`; both use `q ∣ Δ`
  have hA : ((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) * (z2.re : ZMod q)
      = (z1.re : ZMod q) * ((Work.FIPlan.gnorm z2 : ℕ) : ZMod q) := by
    have key : (((z1.re * z2.re + z1.im * z2.im) * z2.re : ℤ) : ZMod q)
        = ((z1.re * ((Work.FIPlan.gnorm z2 : ℤ)) : ℤ) : ZMod q) := by
      rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
      have hrw : (z1.re * ((Work.FIPlan.gnorm z2 : ℤ))
            - (z1.re * z2.re + z1.im * z2.im) * z2.re)
          = z2.im * (z1.re * z2.im - z2.re * z1.im) := by
        rw [norm_eq]; ring
      rw [hrw]
      exact dvd_mul_of_dvd_right hΔ z2.im
    calc ((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) * (z2.re : ZMod q)
        = (((z1.re * z2.re + z1.im * z2.im) * z2.re : ℤ) : ZMod q) := by push_cast; ring
      _ = ((z1.re * ((Work.FIPlan.gnorm z2 : ℤ)) : ℤ) : ZMod q) := key
      _ = (z1.re : ZMod q) * ((Work.FIPlan.gnorm z2 : ℕ) : ZMod q) := by push_cast; ring
  have hB : ((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) * (z2.im : ZMod q)
      = (z1.im : ZMod q) * ((Work.FIPlan.gnorm z2 : ℕ) : ZMod q) := by
    have key : (((z1.re * z2.re + z1.im * z2.im) * z2.im : ℤ) : ZMod q)
        = ((z1.im * ((Work.FIPlan.gnorm z2 : ℤ)) : ℤ) : ZMod q) := by
      rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
      have hrw : (z1.im * ((Work.FIPlan.gnorm z2 : ℤ))
            - (z1.re * z2.re + z1.im * z2.im) * z2.im)
          = (-z2.re) * (z1.re * z2.im - z2.re * z1.im) := by
        rw [norm_eq]; ring
      rw [hrw]
      exact dvd_mul_of_dvd_right hΔ (-z2.re)
    calc ((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) * (z2.im : ZMod q)
        = (((z1.re * z2.re + z1.im * z2.im) * z2.im : ℤ) : ZMod q) := by push_cast; ring
      _ = ((z1.im * ((Work.FIPlan.gnorm z2 : ℤ)) : ℤ) : ZMod q) := key
      _ = (z1.im : ZMod q) * ((Work.FIPlan.gnorm z2 : ℕ) : ZMod q) := by push_cast; ring
  refine ⟨((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) * ↑U⁻¹, ?_, ?_⟩
  · -- the candidate indeed represents `z₁`
    constructor
    · have hr : (((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) * ↑U⁻¹) * (z2.re : ZMod q)
          = (z1.re : ZMod q) := by
        calc (((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) * ↑U⁻¹) * (z2.re : ZMod q)
            = (((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) * (z2.re : ZMod q)) * ↑U⁻¹ := by
              ring
          _ = ((z1.re : ZMod q) * (↑U : ZMod q)) * ↑U⁻¹ := by rw [hA, ← hU]
          _ = (z1.re : ZMod q) := by rw [mul_assoc, Units.mul_inv, mul_one]
      exact hr.symm
    · have hs : (((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) * ↑U⁻¹) * (z2.im : ZMod q)
          = (z1.im : ZMod q) := by
        calc (((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) * ↑U⁻¹) * (z2.im : ZMod q)
            = (((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) * (z2.im : ZMod q)) * ↑U⁻¹ := by
              ring
          _ = ((z1.im : ZMod q) * (↑U : ZMod q)) * ↑U⁻¹ := by rw [hB, ← hU]
          _ = (z1.im : ZMod q) := by rw [mul_assoc, Units.mul_inv, mul_one]
      exact hs.symm
  · -- uniqueness: any solution satisfies `ω'·U = r₁r₂ + s₁s₂`
    intro ω' hω'
    obtain ⟨hr', hs'⟩ := hω'
    have key : ω' * ↑U = ((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) := by
      rw [hU, hDcast]
      calc ω' * ((z2.re : ZMod q)^2 + (z2.im : ZMod q)^2)
          = (ω' * (z2.re : ZMod q)) * (z2.re : ZMod q)
            + (ω' * (z2.im : ZMod q)) * (z2.im : ZMod q) := by ring
        _ = (z1.re : ZMod q) * (z2.re : ZMod q) + (z1.im : ZMod q) * (z2.im : ZMod q) := by
              rw [← hr', ← hs']
        _ = ((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) := by push_cast; ring
    calc ω' = ω' * 1 := (mul_one _).symm
      _ = ω' * (↑U * ↑U⁻¹) := by rw [Units.mul_inv]
      _ = (ω' * ↑U) * ↑U⁻¹ := by ring
      _ = ((z1.re * z2.re + z1.im * z2.im : ℤ) : ZMod q) * ↑U⁻¹ := by rw [key]

end Work.FIArea7
