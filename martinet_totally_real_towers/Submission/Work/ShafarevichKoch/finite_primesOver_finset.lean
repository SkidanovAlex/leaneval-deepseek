import Mathlib

/-!
# `Work.ShafarevichKoch.finite_primesOver_finset` -- finitely many primes over a finite set of
rational primes

The subtype of primes `𝔮` of `𝓞 F` (a number field) with `∃ q ∈ S, 𝔮.LiesOver (span {q})` is
finite: it is the finite union over `q ∈ S` of the primes over the single ideal `span {q}`, and
`𝓞 F` is quasi-finite over `ℤ` (`QuasiFinite.finite_primesOver`).

This is the index set of the inertia generators of `Work.ShafarevichKoch.InertiaCount`; it is what
makes the count "one generator per prime of `F` above `S`" a *finite* statement.
-/

set_option linter.unusedVariables false

open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

theorem finite_primesOver_finset {F : Type} [Field F] [NumberField F] (S : Finset ℕ) :
    Finite {𝔮 : Ideal (NumberField.RingOfIntegers F) // 𝔮.IsPrime ∧
      ∃ q ∈ S, 𝔮.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))} := by
  classical
  have h : ({𝔮 : Ideal (NumberField.RingOfIntegers F) |
      𝔮.IsPrime ∧ ∃ q ∈ S, 𝔮.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))} :
      Set (Ideal (NumberField.RingOfIntegers F))) =
      ⋃ q ∈ (S : Set ℕ),
        (Ideal.span ({(q : ℤ)} : Set ℤ)).primesOver (NumberField.RingOfIntegers F) := by
    ext 𝔮
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h1, q, hq, hl⟩
      exact ⟨q, hq, h1, hl⟩
    · rintro ⟨q, hq, h1, hl⟩
      exact ⟨h1, q, hq, hl⟩
  have hfin : (⋃ q ∈ (S : Set ℕ),
      (Ideal.span ({(q : ℤ)} : Set ℤ)).primesOver (NumberField.RingOfIntegers F)).Finite :=
    Set.Finite.biUnion S.finite_toSet fun q _ =>
      Algebra.QuasiFinite.finite_primesOver (R := ℤ) (S := NumberField.RingOfIntegers F)
        (Ideal.span ({(q : ℤ)} : Set ℤ))
  exact (h ▸ hfin).to_subtype

end Work.ShafarevichKoch
