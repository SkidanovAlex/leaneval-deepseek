import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.ArtinReciprocityIdeal.AbelianReduction
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_cyclic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymbolKillsPrincipal_cyclic

namespace NK.CFTLib.ArtinReciprocityIdeal

open NumberField
open scoped NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The ramification bookkeeping of a conductor.**  If `m` satisfies the product condition of a
conductor (`NK.CFTLib.artinKillsPrincipal K L m`), then the multiple
`m * N(𝔡_{L/K})` is a conductor for `L/K`: every prime not dividing it is unramified, and the
product condition survives by `NK.CFTLib.artinKillsPrincipal.mono`. -/
theorem artinConductor_of_artinKillsPrincipal {m : ℕ} (hm : 0 < m)
    (h : NK.CFTLib.artinKillsPrincipal K L m) :
    NK.CFTLib.artinConductor K L (m * Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L))) := by
  have hdiff_ne : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ≠ 0 := by
    rw [Ideal.absNorm_ne_zero_iff]
    exact Ring.HasFiniteQuotients.finiteQuotient
      (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))
  refine ⟨Nat.mul_pos hm (Nat.pos_of_ne_zero hdiff_ne), ?_, ?_⟩
  · intro p hp
    refine NK.CFTLib.ramificationIdxIn_eq_one_of_absNorm_differentIdeal_notMem p ?_
    intro hmem
    apply hp
    push_cast
    exact p.asIdeal.mul_mem_left _ hmem
  · exact h.mono (dvd_mul_right m _)

/-- **The cyclic case of the conductor theorem (Lang, ANT, Ch. X §2, Theorem 2).**  For a finite
cyclic extension `L/K` of number fields there is a positive integer `m` (a conductor) such that
every prime `p ∤ m` is unramified in `L` and the ideal-theoretic Artin symbol kills every principal
ideal `(a)` with `a ≡ 1 mod m` totally positive.

Together with `NK.CFTLib.ArtinReciprocityIdeal_of_cyclicCase` this gives the ideal-theoretic
reciprocity law `NK.CFTLib.ArtinReciprocityIdeal`. -/
theorem artinConductor_cyclic (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L/K))] :
    ∃ m : ℕ, NK.CFTLib.artinConductor K L m := by
  obtain ⟨m, hm, h⟩ := artinKillsPrincipal_cyclic K L
  exact ⟨_, artinConductor_of_artinKillsPrincipal hm h⟩

end NK.CFTLib.ArtinReciprocityIdeal
