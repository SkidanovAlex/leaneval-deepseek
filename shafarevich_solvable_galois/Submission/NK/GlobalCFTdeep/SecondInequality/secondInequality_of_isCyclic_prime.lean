import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.SecondInequality.index_le_finrank_of_kummerCase
import Submission.NK.GlobalCFTdeep.SecondInequality.secondInequality_of_isCyclic_prime_kummerCase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The second inequality of global class field theory for a cyclic extension of prime degree

Target: `NK.GlobalCFTdeep.SecondInequality.secondInequality_of_isCyclic_prime`:

for `L / K` a number field extension which is Galois and such that `Gal(L/K)` is cyclic of prime
order `p`, the norm class subgroup has index `≤ [L : K] = p`, i.e.

`[C_K : N_{L/K} C_L] ≤ p`.

## Proof architecture

The proof is the classical *algebraic* one (Milne, *Class Field Theory*, VII §6), which for
cyclic `L/K` of prime degree `p` is equivalent to Hasse's norm theorem in that case, and
which also underlies the first inequality.

1. **Reduction to `Ĥ¹`** (proved below, `index_le_finrank_of_subsingleton_tateOne`): the
   `H⁰`-computation `NK.GlobalCFT.H0Computation.index_eq_natCard` and the Herbrand-quotient
   computation `NK.GlobalCFTdeep.cyclicHerbrandQuotient.herbrand`,
   `|Ĥ⁰(G, C_L)| = [L:K] · |Ĥ¹(G, C_L)|`, give `index ≤ [L:K]` as soon as `Ĥ¹(G, C_L) = 0`.

2. **Milne 6.1** (`index_le_finrank_of_kummerCase`, delegated in this directory): base change to
   `K' = K(ζ_p)`, `L' = L·K'`.  `[K':K] = m ∣ p-1`, `L'/K'` is cyclic of prime degree `p`, and
   `index_K ∣ index_{K'}`, so it suffices to treat the Kummer case `μ_p ⊆ K`.

3. **Milne VII §6** (`secondInequality_of_isCyclic_prime_kummerCase`, delegated in this
   directory): with `ζ_p ∈ K` one takes a Kummer generator `L = K(α^{1/p})`, a finite set `S` of
   places containing the infinite places, the primes over `p`, the places where `α` is not a unit
   and a generating set for `Cl(K)`, puts `M := K(U(S)^{1/p})` (so `[M:K] = p^{|S|}`, by
   `finrank_kummerAdjoin`), chooses `|S|-1` primes `T` outside `S` splitting completely in `L`
   whose Frobenius elements generate `Gal(M/L)` (`frobeniusGenerateTop_of_notMem`), and computes
   the index of `Kˣ·E` for Milne's subgroup
   `E := ∏_{v∈S}K_v^{×p} · ∏_{v∈T}K_v^× · ∏_{v∉S∪T}U_v` (defined below as `milneE`), using
   `index_sup_mul_index_inf` (Milne 6.5), `pow_mem_normGroup_adicCompletion` (Milne 6.4),
   Lemma 4.5 (`finrank_eq_one_of_le_normImage`) and the `S`-unit theorem (`finrank_tUnits`).
   Since `E ⊆ N_{L/K} 𝕀_L`, the index of the norm class subgroup divides `[𝕀_K : KˣE] = p`.

The file below only *assembles* this: the mathematical content lives in the two delegated lemmas,
which reduce to the tools of the delivered chapter (`NK.GlobalCFT`) and of the Herbrand
development (`NK.GlobalCFTdeep.Herbrand`).
-/

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality

open NK.GlobalCFT

/-- **Step 1: the reduction to `Ĥ¹`.**  If the first Tate cohomology of the idèle class group
vanishes, then the norm class subgroup has index at most `[L : K]`: the `H⁰`-computation
identifies the index with `|Ĥ⁰(G, C_L)|` and the Herbrand-quotient computation gives
`|Ĥ⁰(G, C_L)| = [L:K] · |Ĥ¹(G, C_L)| = [L:K]`. -/
theorem index_le_finrank_of_subsingleton_tateOne {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (h : Subsingleton (tateCohomology (IdeleClassGroup.rep K L) 1)) :
    (Idele.normClassSubgroup K L).index ≤ Module.finrank K L := by
  have h0 : (Idele.normClassSubgroup K L).index =
      Nat.card (tateCohomology (IdeleClassGroup.rep K L) 0) :=
    NK.GlobalCFT.H0Computation.index_eq_natCard (globalCFT_H0Computation (K := K) (L := L))
  rw [h0]
  have hh : Nat.card (tateCohomology (IdeleClassGroup.rep K L) 0) =
      Module.finrank K L * Nat.card (tateCohomology (IdeleClassGroup.rep K L) 1) :=
    (NK.GlobalCFTdeep.cyclicHerbrandQuotient.herbrand (K := K) (L := L)).herbrand
  rw [hh]
  have h1 : Nat.card (tateCohomology (IdeleClassGroup.rep K L) 1) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨h, ⟨0⟩⟩
  rw [h1, mul_one]

/-! ## The target -/

/-- **The second inequality of global class field theory for a cyclic extension of prime degree**
(Milne, *Class Field Theory*, VII §6). -/
theorem secondInequality_of_isCyclic_prime {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] [Fact (Nat.Prime (Nat.card (L ≃ₐ[K] L)))] :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index ≤ Module.finrank K L := by
  refine index_le_finrank_of_kummerCase (K := K) (L := L) ?_
  intro K' L' hfield hnum hfield' hnum' halg hfin hgal hcyc p hp hcard ζ hζ
  exact secondInequality_of_isCyclic_prime_kummerCase (K := K') (L := L') hp hcard hζ

end NK.GlobalCFTdeep.SecondInequality
