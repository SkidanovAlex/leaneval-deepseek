import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

namespace Work.MotC2

/-- In `L(X) = Frac L[X]`, a square root of `d` times a rational function lies in `L[X]` when `d`
is squarefree.  Proof route: `(w * d) ^ 2 = (w ^ 2 * d) * d` lies in the image of `L[X]`, so
`w * d` is integral over `L[X]` (root of the monic `X ^ 2 - (w ^ 2 d) * d`); `IsIntegrallyClosed`
for `Polynomial L` (`IsIntegrallyClosed.isIntegral_iff`) gives `w * d = u` with `u ∈ L[X]`.  Then
`u ^ 2 = w ^ 2 d ^ 2 = (w ^ 2 * d) * d` is divisible by `d`, so `d ∣ u ^ 2`, and
`Squarefree.dvd_pow_iff_dvd` gives `d ∣ u`, say `u = d * v`; then `w = (d * v) / d = v` is in the
image of `L[X]`. -/
lemma NeTwoRatFuncSqMul (L : Type*) [Field L] (d : Polynomial L) (hd : Squarefree d)
    (w : RatFunc L)
    (h : w ^ 2 * algebraMap (Polynomial L) (RatFunc L) d ∈
      Set.range (algebraMap (Polynomial L) (RatFunc L))) :
    w ∈ Set.range (algebraMap (Polynomial L) (RatFunc L)) := by
  obtain ⟨p, hp⟩ := h
  have hd0 : d ≠ 0 := hd.ne_zero
  have hinj : Function.Injective (algebraMap (Polynomial L) (RatFunc L)) :=
    IsFractionRing.injective (Polynomial L) (RatFunc L)
  -- `(w * d) ^ 2` is the image of `p * d`, hence integral over `L[X]`.
  have key : (w * algebraMap (Polynomial L) (RatFunc L) d) ^ 2
      = algebraMap (Polynomial L) (RatFunc L) (p * d) := by
    rw [map_mul, hp]
    first | refl_ring1 | ring
  have hint : IsIntegral (Polynomial L) ((w * algebraMap (Polynomial L) (RatFunc L) d) ^ 2) := by
    rw [key]; exact isIntegral_algebraMap
  -- `Polynomial L` is integrally closed, so `w * d` is a polynomial.
  obtain ⟨u, hu⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := Polynomial L) (K := RatFunc L) (n := 2) (by norm_num) hint
  have hu2 : u ^ 2 = p * d := by
    apply hinj
    rw [map_pow, hu, key]
  -- hence `d ∣ u ^ 2`, and `d` squarefree gives `d ∣ u`.
  have hdvd : d ∣ u ^ 2 := ⟨p, by rw [hu2, mul_comm]⟩
  obtain ⟨c, hc⟩ := (hd.dvd_pow_iff_dvd (n := 2) (by norm_num)).mp hdvd
  refine ⟨c, ?_⟩
  have hdne : algebraMap (Polynomial L) (RatFunc L) d ≠ 0 := by
    simpa using hinj.ne hd0
  have h1 : w * algebraMap (Polynomial L) (RatFunc L) d
      = algebraMap (Polynomial L) (RatFunc L) c * algebraMap (Polynomial L) (RatFunc L) d := by
    rw [← hu, hc, map_mul]
    first | refl_ring1 | ring
  exact (mul_right_cancel₀ hdne h1).symm

end Work.MotC2
