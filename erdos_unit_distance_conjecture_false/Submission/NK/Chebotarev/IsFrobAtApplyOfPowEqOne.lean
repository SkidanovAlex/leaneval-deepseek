import Mathlib
import Submission.NK.Chebotarev.Basic

namespace NK.Chebotarev

/-- **The Frobenius acts on roots of unity by the residue-field cardinality.**

If `σ : Gal(L/K)` is an arithmetic Frobenius at a prime `P` of `𝓞 L` lying over `p`, and `ζ` is a
root of unity of order dividing `m` with `m` invertible at `P`, then the action of `σ` on `ζ` is
exactly raising to the power `#(𝓞 K ⧸ p)`. -/
theorem IsFrobAtApplyOfPowEqOne {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal L}
    (hP : P.asIdeal.LiesOver p.asIdeal) {σ : Gal(L/K)} (h : NK.Chebotarev.IsFrobAt P σ)
    {ζ : NumberField.RingOfIntegers L} {m : ℕ} (hζ : ζ ^ m = 1)
    (hm : (m : NumberField.RingOfIntegers L) ∉ P.asIdeal) :
    galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ ζ =
      ζ ^ Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) := by
  have h' := h.apply_of_pow_eq_one hζ hm
  rw [← hP.over] at h'
  exact h'

end NK.Chebotarev
