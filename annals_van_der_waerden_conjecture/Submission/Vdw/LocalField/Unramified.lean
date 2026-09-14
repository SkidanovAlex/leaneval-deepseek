import Mathlib
import Submission.Commons.NumberTheory.NumberField.natCard_quotient_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
import Submission.Vdw.LocalField.Completion
import Submission.Vdw.LocalField.BaseAlgebra

open scoped NumberField
open IsDedekindDomain

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (stone 3): the maximal unramified subfield `W` of `K_P/ℚ_p`

With `K_P := Completion.kpAdic p P` a `ℚ_p`-algebra (stone 2), stone 3
constructs the **maximal unramified subfield** `W ⊆ K_P`: the unique
unramified extension of `ℚ_p` inside `K_P` with the same residue field, of
degree `f := P.inertiaDeg ℤ` over `ℚ_p`.  `K_P/W` is then totally ramified
of degree `e := P.ramificationIdx ℤ` — the input of the local trace identity
(stone 4).

**Construction route (recorded):** the residue field is `κ := 𝓞 K / P`, a
finite field of cardinality `p^f` (this module: `kResidue`, `residue_card`,
from the commons `natCard_quotient_eq_pow_inertiaDeg`).  The valuation ring
`𝒪_{K_P}` of the completion is a complete DVR with residue field `κ`
(isomorphic to `𝓞K/P` — fleet L96 `adicCompletion_residueField_equiv_exists`,
in flight).  By Hensel's lemma / Teichmüller lifts
(`RingTheory/Teichmuller.lean`, lifts of `Perfection κ p`; `κ` finite is
perfect, so the lifts land in `𝒪_{K_P}`), the multiplicative group `κ^×`
lifts to roots of unity of order `p^f − 1` in `𝒪_{K_P}`; adjoining a
generator gives `W := ℚ_p[ζ]`, the unramified extension of degree `f`.
Goals (next stones): (a) `W` of degree `f` and unramified over `ℚ_p`;
(b) `[K_P : W] = e` with `K_P/W` totally ramified; (c) trace identity.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The residue field `κ := 𝓞 K / P` of the prime `P`. -/
abbrev kResidue (P : Ideal (𝓞 K)) : Type u := 𝓞 K ⧸ P

/-- Membership of a maximal ideal over `(p)` in the primes-over-`(p)` Finset. -/
lemma mem_primesOverFinset_of_maximal_liesOver (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K) := by
  classical
  have hp0 : (Ideal.span ({(p : ℤ)} : Set ℤ)) ≠ ⊥ := by
    intro hz
    have hp0' : (p : ℤ) = 0 := (Ideal.span_singleton_eq_bot.mp hz)
    exact (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)) (by omega)
  exact (IsDedekindDomain.mem_primesOverFinset_iff (p := Ideal.span ({(p : ℤ)} : Set ℤ))
    (B := 𝓞 K) hp0).mpr ⟨‹P.IsMaximal›.isPrime, ‹P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))›⟩

/-- **Residue field cardinality**: `|𝓞K/P| = p^f`, `f := P.inertiaDeg ℤ` —
the degree of the residue extension over `𝔽_p` (from the commons
`natCard_quotient_eq_pow_inertiaDeg`). -/
theorem residue_card (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Nat.card (kResidue P) = p ^ P.inertiaDeg ℤ := by
  classical
  simpa [kResidue] using (Commons.NumberTheory.NumberField.natCard_quotient_eq_pow_inertiaDeg
    (K := K) p P (mem_primesOverFinset_of_maximal_liesOver p P))

/-- **The residue field of the completion `K_P` is the residue field of the
base prime** (fleet L96 `adicCompletion_residueField_equiv_exists`,
instantiated at `kprime p P`; with `kprime_asIdeal` the codomain is
`kResidue P`, so `|residue(K_P)| = p^f` by `residue_card`).  Together these
pin the residue data `(κ, f)` that the unramified subfield `W` (stone 3)
must carry. -/
theorem completion_residueField_equiv (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Nonempty ((kpInt p P ⧸ IsLocalRing.maximalIdeal (kpInt p P)) ≃+*
      (𝓞 K ⧸ (kprime p P).asIdeal)) := by
  classical
  simpa [kpInt] using (Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
    (K := K) (V := kprime p P))

end
end Submission.Vdw.LocalField