import Mathlib
import Submission.Vdw.SplittingField
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_isGaloisGroup
import Submission.Commons.NumberTheory.NumberField.stabilizer_card_eq

open Polynomial
open scoped NumberField Pointwise

set_option autoImplicit false

/-!
# Galois-side ramification facts for the splitting field (item (b) of the fiber count)

The fiber count `fiberCard` (`Contraction.lean`) needs the Galois-group side
of the prime data in `L = p.SplittingField` (normal over `ℚ`, with
`p.Gal = Gal(L/ℚ)` acting on the primes of `𝒪 L` over `p0`):

* `splGaloisGroup` (instance): `IsGaloisGroup p.Gal ℤ (𝓞 L)` — the Galois
  action of `p.Gal` on the ring of integers of the splitting field
  (built with `IsIntegralClosure.MulSemiringAction` +
  `IsGaloisGroup.of_isFractionRing`, following
  `NumberTheory.NumberField.ExistsRamified`);
* `stabilizer_card_spl`: the decomposition group of a prime `𝔓` of `𝒪 L`
  over `p0` has order `e(𝔓/p0)·f(𝔓/p0)` (`Ideal.card_stabilizer_eq` +
  the `ramificationIdxIn`/`inertiaDegIn` identifications).
-/

namespace Submission.Vdw

noncomputable section

open Polynomial


/-- The splitting field of a polynomial over `ℚ` is normal over `ℚ`
(usable via `haveI := spl_normal p` — typeclass search does not find it). -/
theorem spl_normal (p : ℚ[X]) : Normal ℚ p.SplittingField :=
  Polynomial.SplittingField.instNormal p

/-- The splitting field of an irreducible polynomial over `ℚ` is Galois
over `ℚ` (normal by `spl_normal`, separable in characteristic zero). -/
theorem spl_galois (p : ℚ[X]) [Fact (Irreducible p)] : IsGalois ℚ p.SplittingField := by
  classical
  refine {
    to_isSeparable := (inferInstance : Algebra.IsSeparable ℚ p.SplittingField)
    to_normal := spl_normal p }

/-! **Item (b) status.**  The generic (variable-`K`) facts are now in the
commons (both PROVED by the fleet): `ringOfIntegers_isGaloisGroup`
(`IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K)` for `[NumberField K] [IsGalois ℚ K]`) and
`stabilizer_card_eq` (`Nat.card (MulAction.stabilizer Gal(K/ℚ) 𝔓) =
e(𝔓/p0)·f(𝔓/p0)`).  Both are proved for variable `K`; applying them at the
concrete `K = p.SplittingField` works once `IsGalois` is supplied locally
(`spl_galois p`) — see `stabilizer_card_spl` below.  The reason typeclass
search does not find these global instances for the concrete
`p.SplittingField` is that `SplittingField` is a noncomputable def that
instance search cannot unfold. -/

/-- **Decomposition-group order for the splitting field.**  For a prime
`𝔓` of `𝒪 L` over `p₀`, the stabilizer of `𝔓` in `p.Gal = Gal(L/ℚ)` (the
decomposition group `D(𝔓)`) has order `e(𝔓/p₀)·f(𝔓/p₀)`.
(Generic-K version proved in the commons:
`Commons.NumberTheory.NumberField.stabilizer_card_eq`; this is its
instantiation at `K = p.SplittingField`, with `IsGalois` supplied via
`spl_galois`.) -/
theorem stabilizer_card_spl (p : ℚ[X]) [Fact (Irreducible p)]
    [IsGalois ℚ p.SplittingField]
    (p0 : ℕ) (hp0 : Nat.Prime p0)
    (𝔓 : Ideal (𝓞 p.SplittingField)) [𝔓.IsPrime]
    [𝔓.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ))] :
    Nat.card (MulAction.stabilizer p.Gal 𝔓) =
      𝔓.ramificationIdx ℤ * 𝔓.inertiaDeg ℤ := by
  classical
  exact Commons.NumberTheory.NumberField.stabilizer_card_eq
    (K := p.SplittingField) p0 hp0 𝔓

end
end Submission.Vdw
