import Mathlib
import Submission.Work.FIArea7.FIsymbols

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-!
# `Work.FIArea7.dvd_delta_iff_exists_omega`

The determinant `Δ(z₁, z₂) = Im(z̄₁ z₂) = r₁s₂ - s₁r₂` of the paper (6.1) vanishes modulo `q`
exactly when the two Gaussian integers are proportional modulo `q`, *provided* `q` is coprime to
`|z₂|² = r₂² + s₂²`.  Concretely, with `zⱼ = rⱼ + i sⱼ`,

  `q ∣ Δ(z₁,z₂)  ↔  ∃ ω : ZMod q, r₁ = ω r₂  ∧  s₁ = ω s₂`.

The forward direction inverts `|z₂|²` modulo `q` (legitimate by the coprimality hypothesis) and
takes `ω = (r₁r₂ + s₁s₂)·(|z₂|²)⁻¹`; the reverse direction is immediate from `Δ = r₁s₂ - s₁r₂`.
-/

/-- `Δ(z₁,z₂) = r₁s₂ - s₁r₂` in coordinates (paper (6.1)). -/
lemma Delta_eq (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z1 z2 = z1.re * z2.im - z1.im * z2.re := by
  unfold Work.FIPlan.Delta
  rw [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

/-- **Linear-algebra lemma.**  In a commutative ring, if `c² + d²` is a unit and `a d = b c`, then
`(a, b)` is a scalar multiple of `(c, d)`: the scalar is `(ac + bd)·(c²+d²)⁻¹`.

This is the algebraic content of the result studied here: the determinant `ad - bc` vanishes and
the norm `c² + d²` is invertible. -/
lemma exists_mul_of_eq_mul {R : Type*} [CommRing R] {a b c d : R}
    (h : a * d = b * c) (hu : IsUnit (c ^ 2 + d ^ 2)) :
    ∃ ω : R, ω * c = a ∧ ω * d = b := by
  refine ⟨(a * c + b * d) * ↑hu.unit⁻¹, ?_, ?_⟩
  · have h1 : (a * c + b * d) * c = a * (c ^ 2 + d ^ 2) := by
      linear_combination (-d) * h
    calc ((a * c + b * d) * ↑hu.unit⁻¹) * c
        = ((a * c + b * d) * c) * ↑hu.unit⁻¹ := by ring
      _ = (a * (c ^ 2 + d ^ 2)) * ↑hu.unit⁻¹ := by rw [h1]
      _ = a * ((c ^ 2 + d ^ 2) * ↑hu.unit⁻¹) := by ring
      _ = a * 1 := by rw [hu.mul_val_inv]
      _ = a := by ring
  · have h2 : (a * c + b * d) * d = b * (c ^ 2 + d ^ 2) := by
      linear_combination (c) * h
    calc ((a * c + b * d) * ↑hu.unit⁻¹) * d
        = ((a * c + b * d) * d) * ↑hu.unit⁻¹ := by ring
      _ = (b * (c ^ 2 + d ^ 2)) * ↑hu.unit⁻¹ := by rw [h2]
      _ = b * ((c ^ 2 + d ^ 2) * ↑hu.unit⁻¹) := by ring
      _ = b * 1 := by rw [hu.mul_val_inv]
      _ = b := by ring

theorem dvd_delta_iff_exists_omega {q : ℕ} (hq : 0 < q) (z1 z2 : GaussianInt)
    (hcop : Nat.Coprime (Work.FIPlan.gnorm z2) q) :
    ((q : ℤ) ∣ Work.FIPlan.Delta z1 z2) ↔
      ∃ ω : ZMod q, (z1.re : ZMod q) = ω * (z2.re : ZMod q)
        ∧ (z1.im : ZMod q) = ω * (z2.im : ZMod q) := by
  constructor
  · intro hdvd
    -- `Δ(z₁,z₂) ≡ 0 (mod q)` as an equation in `ZMod q`
    have hzero : ((Work.FIPlan.Delta z1 z2 : ℤ) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (Work.FIPlan.Delta z1 z2) q).mpr hdvd
    rw [Delta_eq] at hzero
    -- in coordinates: `r₁s₂ = s₁r₂` in `ZMod q`
    have hprod : (z1.re : ZMod q) * (z2.im : ZMod q)
        = (z1.im : ZMod q) * (z2.re : ZMod q) := by
      have hh := hzero
      push_cast at hh
      linear_combination hh
    -- `|z₂|² = r₂² + s₂²` is a unit modulo `q`
    have hN : (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod q)
        = (z2.re : ZMod q) ^ 2 + (z2.im : ZMod q) ^ 2 := by
      rw [← Int.cast_natCast, norm_eq]
      push_cast
      ring
    have hu : IsUnit ((z2.re : ZMod q) ^ 2 + (z2.im : ZMod q) ^ 2) := by
      rw [← hN]
      exact (ZMod.isUnit_iff_coprime (Work.FIPlan.gnorm z2) q).mpr hcop
    obtain ⟨ω, hω1, hω2⟩ := exists_mul_of_eq_mul hprod hu
    exact ⟨ω, hω1.symm, hω2.symm⟩
  · rintro ⟨ω, h1, h2⟩
    -- reconstruct `Δ(z₁,z₂) ≡ 0 (mod q)` from the proportionality
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (Work.FIPlan.Delta z1 z2) q).mp
    rw [Delta_eq]
    push_cast
    rw [h1, h2]
    ring

end Work.FIArea7
