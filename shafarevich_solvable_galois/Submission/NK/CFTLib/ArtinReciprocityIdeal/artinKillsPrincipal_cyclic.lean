import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.ArtinReciprocityIdeal.AbelianReduction
import Submission.NK.CFTLib.ArtinReciprocityIdeal.CyclotomicSubextension
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
import Submission.NK.CFTLib.ARL.artinReciprocity_cyclotomic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_span_eq_one_of_kernelLe_of_relIndex
import Submission.NK.CFTLib.ArtinReciprocityIdeal.langCyclicKernelLe_byArtinLemma
import Submission.NK.CFTLib.ArtinReciprocityIdeal.langCyclicRelIndex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.ArtinReciprocityIdeal

open NK.Chebotarev
open NumberField
open scoped NumberField IsMulCommutative

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The product condition, in terms of the Artin symbol of a principal ideal.**  For `m ≥ 0`,
`ArtinSymbolKillsPrincipal m` says that the Artin symbol of every principal ideal `(a)` with
`a ≡ 1 mod m` and `a` totally positive is trivial.

This is the form in which the reciprocity law is proved and used: it is equivalent to
`NK.CFTLib.artinKillsPrincipal K L m` as soon as the primes dividing `(m)` include all the
primes ramified in `L/K` (`artinKillsPrincipal_of_artinSymbolKillsPrincipal`). -/
def ArtinSymbolKillsPrincipal (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (Gal(L/K))]
    (m : ℕ) : Prop :=
  ∀ a : 𝓞 K, a - 1 ∈ Ideal.span {(m : 𝓞 K)} → (∀ φ : K →+* ℝ, 0 < φ (a : K)) →
    artinSymbol (K := K) (L := L) (Ideal.span {a}) = 1

/-- **The product condition from the Artin symbol form.**  If every ramified prime of `L/K`
divides `(m)`, then `ArtinSymbolKillsPrincipal K L m` implies `artinKillsPrincipal K L m`: the
product of *any* choice of Frobenius elements at the primes of a factorisation of `(a)` agrees
with the Artin symbol of `(a)` (`NK.CFTLib.frobAtPrime_prod_irrel`). -/
theorem artinKillsPrincipal_of_artinSymbolKillsPrincipal [IsMulCommutative (Gal(L/K))] (m : ℕ)
    (hram : ∀ p : PrimeIdeal K, ¬ IsUnramified (K := K) (L := L) p →
      (m : 𝓞 K) ∈ p.asIdeal)
    (h : ArtinSymbolKillsPrincipal K L m) :
    artinKillsPrincipal K L m := by
  intro a ha hpos s e σ hs hfac hfrob
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := IsMulCommutative.is_comm.comm
  have hunr : ∀ p ∈ s, IsUnramified (K := K) (L := L) p := fun p hp => by
    by_contra hcon
    exact hs p hp (hram p hcon)
  calc (s.toList.map (fun p => σ p ^ e p)).prod
      = (s.toList.map (fun p => (frobAtPrime (K := K) (L := L) p) ^ e p)).prod :=
        frobAtPrime_prod_irrel (K := K) (L := L) hcomm s e σ hunr hfrob
    _ = ∏ p ∈ s, (frobAtPrime (K := K) (L := L) p) ^ e p :=
        toList_map_prod_eq_finset_prod s _
    _ = ∏ p ∈ s, (frobSymbol (K := K) (L := L) p.asIdeal) ^ e p := by
        refine Finset.prod_congr rfl fun p hp => ?_
        show (frobAtPrime (K := K) (L := L) p) ^ e p
          = (frobSymbol (K := K) (L := L) p.asIdeal) ^ e p
        rw [← frobSymbol_eq (K := K) (L := L) p (hunr p hp)]
    _ = artinSymbol (K := K) (L := L) (∏ p ∈ s, p.asIdeal ^ e p) :=
        (artinSymbol_finset_prod (K := K) (L := L) s e).symm
    _ = artinSymbol (K := K) (L := L) (Ideal.span {a}) := by rw [← hfac]
    _ = 1 := h a ha hpos

/-- **The main theorem from its Artin-symbol form.** -/
theorem artinKillsPrincipal_cyclic_of_exists [IsMulCommutative (Gal(L/K))]
    (h : ∃ m : ℕ, 0 < m ∧
      (∀ p : PrimeIdeal K, ¬ IsUnramified (K := K) (L := L) p → (m : 𝓞 K) ∈ p.asIdeal) ∧
      ArtinSymbolKillsPrincipal K L m) :
    ∃ m : ℕ, 0 < m ∧ artinKillsPrincipal K L m := by
  obtain ⟨m, hm, hram, hkill⟩ := h
  exact ⟨m, hm, artinKillsPrincipal_of_artinSymbolKillsPrincipal m hram hkill⟩

/-- **Lang, *Algebraic Number Theory*, Chapter X §2, Theorem 2 (cyclic case)**: the product
condition of the ideal-theoretic reciprocity law for a cyclic extension.  See
`Submission/Work/CFTLib/ArtinReciprocityIdeal/NOTES.md` for the roadmap (surjectivity of the Artin
symbol from `NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem`; the ideal-form
norm index equality `[I(m) : P_m·𝔑(m)] = n` from the idèle-form
`NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`; the Auxiliary-Field/Arttin-trick argument for
`ker ψ ⊆ P_m·𝔑(m)`, using the already-proved cyclotomic case
`NK.CFTLib.ARL.artinReciprocity_cyclotomic` and
`NK.CFTLib.artinKillsPrincipal_of_le_isCyclotomicExtension`). -/
theorem artinKillsPrincipal_cyclic (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L/K))] :
    ∃ m : ℕ, 0 < m ∧ NK.CFTLib.artinKillsPrincipal K L m := by
  haveI : IsMulCommutative (Gal(L/K)) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    rw [← zpow_add, ← zpow_add, add_comm m n]
  obtain ⟨m, hm, hram, hkill⟩ :=
    artinSymbol_span_eq_one_of_kernelLe_of_relIndex K L
      (langCyclicKernelLe_byArtinLemma K L)
      (fun m hm hram hadm => langCyclicRelIndex K L m hm hram hadm)
  exact ⟨m, hm, artinKillsPrincipal_of_artinSymbolKillsPrincipal m hram hkill⟩

end NK.CFTLib.ArtinReciprocityIdeal
