import Mathlib
import Submission.Work.AUTL2.Defs

namespace Work.AUTL2.Norm

/-- In a finite field `𝔽_{p^k}` of odd characteristic, every ring automorphism `σ` of order
dividing `2` (indeed every ring automorphism at all) satisfies: `d * σ d` is a square.

The reason: any ring automorphism of `GaloisField p k` is a power of the arithmetic Frobenius
`x ↦ x ^ (p ^ i)` (`FiniteField.exists_forall_apply_eq_pow`), so
`d * σ d = d ^ (1 + p ^ i) = (d ^ ((1 + p ^ i) / 2)) ^ 2`, valid because `p` is odd and hence
`1 + p ^ i` is even. -/
theorem square (p k : ℕ) [Fact p.Prime] (hp : Odd p)
    (σ : GaloisField p k ≃+* GaloisField p k) (hσ : σ * σ = 1) (hne : σ ≠ 1) (d : GaloisField p k) :
    ∃ c : GaloisField p k, c ^ 2 = d * σ d := by
  -- `σ` fixes the prime field `𝔽_p`, so it is a `ZMod p`-algebra automorphism.
  have hf : ∀ x : ZMod p, σ (algebraMap (ZMod p) (GaloisField p k) x) =
      algebraMap (ZMod p) (GaloisField p k) x := by
    intro x
    have hx : ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_zmod_val x
    have e : algebraMap (ZMod p) (GaloisField p k) x = ((x.val : ℕ) : GaloisField p k) := by
      conv_lhs => rw [← hx]
      exact map_natCast (algebraMap (ZMod p) (GaloisField p k)) x.val
    rw [e]
    exact map_natCast σ x.val
  let σA : GaloisField p k ≃ₐ[ZMod p] GaloisField p k := AlgEquiv.ofRingEquiv (f := σ) hf
  -- Every automorphism of a finite field is a power of the Frobenius.
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod p) p (GaloisField p k) σA
  refine ⟨d ^ ((1 + p ^ i) / 2), ?_⟩
  have hσd : σ d = d ^ (p ^ i) := by
    have h := hi d
    simp only [Nat.card_zmod] at h
    rwa [show σA d = σ d from rfl] at h
  rw [hσd, ← pow_mul, mul_comm]
  have hm : 2 * ((1 + p ^ i) / 2) = 1 + p ^ i := by
    have h : 2 ∣ 1 + p ^ i := by
      have hpi : Odd (p ^ i) := hp.pow
      simpa [add_comm] using even_iff_two_dvd.mp hpi.add_one
    exact Nat.mul_div_cancel' h
  rw [hm, pow_add, pow_one]

end Work.AUTL2.Norm
