import Submission.Work.Tower.CMAdjoin.Basic

/-!
# The local splitting of a prime of `𝓞 L` in `L(i)`

For the class-field tower step (paper Proposition 3.8, Step 4) one needs to know that an odd
prime `𝔮` of `𝓞 L` whose residue field is `𝔽_q` splits in `K = L(i)` into exactly two primes,
both with residue field `𝔽_q`.  This file fixes that property as a predicate so that it can be
stated, proved and used independently of the global `Work.Defs.SplitsCompletely`.

## Main definitions

* `Work.Tower.CMAdjoin.SplitsIntoTwo L q 𝔮`: the prime `𝔮` of `𝓞 L` splits into two primes of
  `𝓞 (L(i))` with residue field `𝔽_q`.

-/

open Polynomial
open NumberField

open scoped Classical nonZeroDivisors

namespace Work
namespace Tower
namespace CMAdjoin

/-- A prime `𝔮` of `𝓞 L` **splits into two primes** in `K = L(i)`: the extension `𝔮 𝓞 K` is the
product of two distinct primes `𝔔₀ ≠ 𝔔₁`, each lying over `𝔮` and with residue field `𝔽_q`. -/
def SplitsIntoTwo (L : Type*) [Field L] [NumberField L] [NumberField.IsTotallyReal L]
    (q : ℕ) (𝔮 : Ideal (𝓞 L)) : Prop :=
  ∃ 𝔔₀ 𝔔₁ : Ideal (𝓞 (cmAdjoin L)),
    𝔔₀.IsPrime ∧ 𝔔₁.IsPrime ∧ 𝔔₀ ≠ 𝔔₁ ∧ 𝔔₀.LiesOver 𝔮 ∧ 𝔔₁.LiesOver 𝔮 ∧
    Nonempty ((𝓞 (cmAdjoin L)) ⧸ 𝔔₀ ≃+* ZMod q) ∧
    Nonempty ((𝓞 (cmAdjoin L)) ⧸ 𝔔₁ ≃+* ZMod q) ∧
    𝔮.map (algebraMap (𝓞 L) (𝓞 (cmAdjoin L))) = 𝔔₀ * 𝔔₁

end CMAdjoin
end Tower
end Work
