import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTdualControl

/-- For a prime `p` and a primitive `p`-th root of unity `ζ` in a field `Ω` over a field `K`,
the degree `[K(ζ) : K]` is not divisible by `p`.

Indeed `K(ζ)/K` is obtained by adjoining a root of the `p`-th cyclotomic polynomial,
so `K(ζ)` has degree `natDegree (minpoly K ζ)` over `K`, which is positive and at most
`p.totient = p - 1 < p`; a positive integer `< p` is not divisible by the prime `p`. -/
theorem not_dvd_finrank_adjoin_isPrimitiveRoot (p : ℕ) [Fact p.Prime] {K Ω : Type} [Field K]
    [Field Ω] [Algebra K Ω] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) :
    ¬ p ∣ Module.finrank K ↥(IntermediateField.adjoin K {ζ} : IntermediateField K Ω) := by
  have hp : p.Prime := Fact.out
  have hppos : 0 < p := hp.pos
  -- `ζ` is integral over `K`, being a root of the monic polynomial `X^p - 1`; this is what
  -- lets us identify the degree with `natDegree (minpoly K ζ)`.
  have hint : IsIntegral K ζ := by
    apply IsIntegral.of_pow (n := p) hppos
    rw [hζ.pow_eq_one]
    exact isIntegral_one
  rw [IntermediateField.adjoin.finrank hint]
  intro hd
  have hpos : 0 < (minpoly K ζ).natDegree := minpoly.natDegree_pos hint
  -- `minpoly K ζ` divides the `p`-th cyclotomic polynomial over `K`.
  have hdvd : minpoly K ζ ∣ Polynomial.cyclotomic p K := by
    rw [minpoly.dvd_iff]
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic,
      ← Polynomial.IsRoot.def]
    exact hζ.isRoot_cyclotomic hppos
  have hle : (minpoly K ζ).natDegree ≤ p - 1 := by
    calc (minpoly K ζ).natDegree ≤ (Polynomial.cyclotomic p K).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd (Polynomial.cyclotomic_ne_zero p K)
      _ = p.totient := Polynomial.natDegree_cyclotomic p K
      _ = p - 1 := Nat.totient_prime hp
  -- A positive divisor of `natDegree` would be `≤ natDegree ≤ p - 1 < p`, contradicting `p ∣ ·`.
  have := Nat.le_of_dvd hpos hd
  omega

end Work.SSGRoute.PTdualControl
