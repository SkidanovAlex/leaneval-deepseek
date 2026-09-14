import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Submission.Commons.RingTheory.Ideal.span_singleton_prime_int

open scoped NumberField Pointwise

namespace Commons.NumberTheory.NumberField

noncomputable section

/-- In a Galois number field `K/ℚ`, the stabilizer (decomposition group) of a prime
ideal `𝔓` lying over the rational prime `p₀` has cardinality `e(𝔓/p₀) · f(𝔓/p₀)`,
the ramification index times the inertia degree. -/
theorem stabilizer_card_eq (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (p0 : ℕ) (hp0 : Nat.Prime p0)
    (𝔓 : Ideal (𝓞 K)) [𝔓.IsPrime]
    [𝔓.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ))] :
    Nat.card (MulAction.stabilizer Gal(K/ℚ) 𝔓) =
      𝔓.ramificationIdx ℤ * 𝔓.inertiaDeg ℤ := by
  classical
  let pZ : Ideal ℤ := Ideal.span ({(p0 : ℤ)} : Set ℤ)
  have hpZ : pZ.IsPrime := by
    simpa [pZ] using Commons.RingTheory.Ideal.span_singleton_prime_int hp0
  have hmain := Ideal.card_stabilizer_eq (R := ℤ) (S := 𝓞 K) (G := Gal(K/ℚ))
    (p := pZ) (P := 𝔓)
  rw [hmain]
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := ℤ) (B := 𝓞 K)
    (p := pZ) (P := 𝔓) (G := Gal(K/ℚ))]
  rw [← Ideal.inertiaDegIn_eq_inertiaDeg (A := ℤ) (B := 𝓞 K)
    (p := pZ) (P := 𝔓) (G := Gal(K/ℚ))]

end

end Commons.NumberTheory.NumberField