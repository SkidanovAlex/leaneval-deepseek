/-
# `Submission.Work.FIArea6.ncGaussAlg` — multiplicativity of the Gaussian norm and determinant

Three elementary algebraic facts about `Work.FIPlan.gnorm` (the norm `|z|² = z.norm.natAbs`),
`Work.FIPlan.Delta` (the determinant `Δ(z₁,z₂) = Im(z̄₁z₂)`) and `Work.FIPlan.absDelta` (its
absolute value `|Δ(z₁,z₂)|`):

* `gnorm` is multiplicative: `gnorm (z*w) = gnorm z * gnorm w`;
* `Delta` is homogeneous in the *first* argument simultaneously for both arguments:
  `Delta (g*u₁) (g*u₂) = (gnorm g : ℤ) * Delta u₁ u₂` — the "common divisor `g`" of (16.1);
* consequently, if `gnorm g` is coprime to `4d` then `4d ∣ |Δ(g u₁, g u₂)|` forces
  `4d ∣ |Δ(u₁, u₂)|` — the cancellation of the `g`-factor used when passing from the pair
  `(g u₁, g u₂)` (as in `Work.FIArea6.Vd`) to the pair `(u₁, u₂)`.

All three are pure `ℤ[i]`-algebra: `z̄z = norm z` is a rational integer, hence central and
invisible in the imaginary part; `natAbs` of a product is the product of `natAbs`; and the
coprime hypothesis lets `4d` cancel the `gnorm g` factor.
-/
import Mathlib
import Submission.Work.FIArea6.S16UDefs

set_option autoImplicit false

namespace Work.FIArea6

open Work.FIPlan

/-- `z̄ z = |z|²` with `|z|²` read as the rational integer `z.norm` inside `ℤ[i]`. -/
private lemma star_mul_self_eq_norm (g : GaussianInt) : star g * g = (g.norm : GaussianInt) := by
  rw [mul_comm, Zsqrtd.norm_eq_mul_conj]

/-- The `ℤ`-cast of `g.norm.natAbs` is `g.norm` (the norm is non-negative). -/
private lemma gnorm_intCast (g : GaussianInt) : (gnorm g : ℤ) = g.norm := by
  simp only [gnorm, GaussianInt.abs_natCast_norm]

/-- **Multiplicativity of `gnorm`** (`|zw|² = |z|²|w|²`). -/
lemma ncga_gnorm_mul (z w : GaussianInt) : gnorm (z * w) = gnorm z * gnorm w := by
  simp only [gnorm]
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]

/-- **Homogeneity of `Delta`**: `Δ(g u₁, g u₂) = |g|² Δ(u₁, u₂)` (paper (6.1) for the pair
`(gu₁, gu₂)`). -/
lemma ncga_Delta_mul (g u1 u2 : GaussianInt) :
    Delta (g * u1) (g * u2) = (gnorm g : ℤ) * Delta u1 u2 := by
  unfold Delta
  -- `z̄₁z₂` for `zᵢ = g uᵢ` is `(ḡg)(ū₁u₂)`, and `ḡg = |g|²` is a rational integer.
  have h : star (g * u1) * (g * u2) = (star g * g) * (star u1 * u2) := by
    rw [star_mul]; ring
  rw [h, star_mul_self_eq_norm, Zsqrtd.im_smul, gnorm_intCast]

/-- **`absDelta` for a pair with a common factor**: `|Δ(g u₁, g u₂)| = |g|² |Δ(u₁, u₂)|`. -/
lemma ncga_absDelta_mul (g u1 u2 : GaussianInt) :
    absDelta (g * u1) (g * u2) = gnorm g * absDelta u1 u2 := by
  unfold absDelta
  rw [ncga_Delta_mul, Int.natAbs_mul, Int.natAbs_natCast]

/-- **The cancellation of the common factor `g` modulo `4d`**: if `(|g|², 4d) = 1` and
`4d ∣ |Δ(g u₁, g u₂)|` then `4d ∣ |Δ(u₁, u₂)|`. -/
lemma ncga_absDelta_dvd_of_mul (g u1 u2 : GaussianInt) (d : ℕ)
    (hcop : Nat.Coprime (gnorm g) (4 * d)) (hdvd : 4 * d ∣ absDelta (g * u1) (g * u2)) :
    4 * d ∣ absDelta u1 u2 := by
  rw [ncga_absDelta_mul] at hdvd
  exact hcop.symm.dvd_of_dvd_mul_left hdvd

theorem ncGaussAlg : (∀ z w : GaussianInt, Work.FIPlan.gnorm (z * w)
      = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w) ∧
    (∀ g u1 u2 : GaussianInt, Work.FIPlan.Delta (g * u1) (g * u2)
      = ((Work.FIPlan.gnorm g : ℕ) : ℤ) * Work.FIPlan.Delta u1 u2) ∧
    (∀ (g u1 u2 : GaussianInt) (d : ℕ), Nat.Coprime (Work.FIPlan.gnorm g) (4 * d) →
      4 * d ∣ Work.FIPlan.absDelta (g * u1) (g * u2) →
      4 * d ∣ Work.FIPlan.absDelta u1 u2) := by
  exact ⟨ncga_gnorm_mul, ncga_Delta_mul, ncga_absDelta_dvd_of_mul⟩

end Work.FIArea6
