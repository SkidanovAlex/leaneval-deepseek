import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

namespace Commons.RingTheory.DedekindDomain

/-- If `a : A` is such that `m * a ∈ 1` for every `m` in the inverse of a nonzero ideal `p`
of a Dedekind domain `A`, then `a ∈ p`.

The hypothesis says exactly that `p⁻¹ ≤ (A·a)⁻¹`; multiplying by `p` (invertible because
`p ≠ 0`) gives `A·a ≤ p`. -/
theorem mem_of_forall_mul_inv_mem {A K : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] (p : Ideal A) (hp : p ≠ ⊥) {a : A}
    (h : ∀ m ∈ (p : FractionalIdeal (nonZeroDivisors A) K)⁻¹,
      m * algebraMap A K a ∈ (1 : FractionalIdeal (nonZeroDivisors A) K)) :
    a ∈ p := by
  have hpmul : (p : FractionalIdeal (nonZeroDivisors A) K) *
      (p : FractionalIdeal (nonZeroDivisors A) K)⁻¹ = 1 :=
    FractionalIdeal.coe_ideal_mul_inv p hp
  -- The hypothesis shows that `p⁻¹ * (A·a) ≤ 1`.
  have hpJ : (p : FractionalIdeal (nonZeroDivisors A) K)⁻¹ *
      FractionalIdeal.spanSingleton (nonZeroDivisors A) (algebraMap A K a) ≤ 1 := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    rw [FractionalIdeal.mem_spanSingleton] at hj
    obtain ⟨c, rfl⟩ := hj
    rw [Algebra.smul_def]
    have hmem : i * algebraMap A K a ∈ (1 : FractionalIdeal (nonZeroDivisors A) K) := h i hi
    have key : i * (algebraMap A K c * algebraMap A K a)
        = algebraMap A K c * (i * algebraMap A K a) := by ring
    rw [key, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c hmem
  -- Multiplying by `p` and using `p * p⁻¹ = 1` gives `A·a ≤ p`.
  have hJle : FractionalIdeal.spanSingleton (nonZeroDivisors A) (algebraMap A K a) ≤
      (p : FractionalIdeal (nonZeroDivisors A) K) := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors A) (algebraMap A K a)
        = 1 * FractionalIdeal.spanSingleton (nonZeroDivisors A) (algebraMap A K a) := by
          rw [one_mul]
      _ = (p : FractionalIdeal (nonZeroDivisors A) K) *
            (p : FractionalIdeal (nonZeroDivisors A) K)⁻¹ *
            FractionalIdeal.spanSingleton (nonZeroDivisors A) (algebraMap A K a) := by
          rw [hpmul]
      _ = (p : FractionalIdeal (nonZeroDivisors A) K) *
            ((p : FractionalIdeal (nonZeroDivisors A) K)⁻¹ *
              FractionalIdeal.spanSingleton (nonZeroDivisors A) (algebraMap A K a)) := by
          rw [mul_assoc]
      _ ≤ (p : FractionalIdeal (nonZeroDivisors A) K) * 1 := mul_le_mul_right hpJ _
      _ = (p : FractionalIdeal (nonZeroDivisors A) K) := mul_one _
  have hxmem : algebraMap A K a ∈ (p : FractionalIdeal (nonZeroDivisors A) K) :=
    hJle (FractionalIdeal.mem_spanSingleton_self _ _)
  obtain ⟨a', ha', hmap⟩ := (FractionalIdeal.mem_coeIdeal (nonZeroDivisors A)).mp hxmem
  rwa [IsFractionRing.injective A K hmap] at ha'

end Commons.RingTheory.DedekindDomain