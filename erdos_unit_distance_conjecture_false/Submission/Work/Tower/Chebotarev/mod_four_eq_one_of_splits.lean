import Mathlib
import Submission.Work.Tower.Chebotarev.Defs

namespace Work.Tower.Chebotarev

open NumberField Ideal
open scoped Classical nonZeroDivisors NumberField

/-- If `q` splits completely in a number field `M` and some algebraic integer `u : 𝓞 M` satisfies
`u * u = -1`, then `q ≡ 1 (mod 4)`: the residue field `𝔽_q` of a prime above `q` then contains a
square root of `-1`. -/
theorem mod_four_eq_one_of_splits {M : Type} [Field M] [NumberField M] {q : ℕ}
    (hq : Nat.Prime q) (hq2 : q ≠ 2) (h : Work.Tower.Splits q M) {P : Ideal (𝓞 M)}
    (hP : P.IsPrime) (hPq : (q : 𝓞 M) ∈ P) {u : 𝓞 M} (hu : u * u = -1) : q % 4 = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  -- Since `q` splits completely, the residue field of `P` is `ZMod q`.
  obtain ⟨e⟩ := h.residue_of_isPrime hP hPq
  -- The image of `u` in the residue field is a square root of `-1`.
  have h1 : (Ideal.Quotient.mk P u : 𝓞 M ⧸ P) * (Ideal.Quotient.mk P u) = -1 := by
    rw [← map_mul, hu, map_neg, map_one]
  -- Transport it to `ZMod q` along the residue field isomorphism.
  have h2 := congrArg e h1
  rw [map_mul, map_neg, map_one] at h2
  -- Hence `-1` is a square in `ZMod q`, so `q ≢ 3 (mod 4)`.
  have hsq : IsSquare (-1 : ZMod q) := ⟨_, h2.symm⟩
  have hmod : q % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
  -- As `q` is an odd prime, this forces `q ≡ 1 (mod 4)`.
  obtain ⟨k, hk⟩ := Nat.Prime.odd_of_ne_two hq hq2
  omega

end Work.Tower.Chebotarev
