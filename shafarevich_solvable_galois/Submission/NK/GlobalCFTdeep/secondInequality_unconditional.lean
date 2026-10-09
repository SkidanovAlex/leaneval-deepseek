import Mathlib
import Submission.NK.GlobalCFTdeep.Inequalities
import Submission.NK.GlobalCFTdeep.AbstractH0
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFTdeep.SecondInequality.factorization_natCard_H0_le
import Submission.NK.GlobalCFTdeep.SecondInequality.natCard_H0_eq_of_mulEquiv
import Submission.NK.GlobalCFTdeep.SecondInequality.normClassSubgroup_index_eq_natCard_H0
import Submission.NK.GlobalCFTdeep.SecondInequality.normClassSubgroup_fixedField_index_eq_natCard_H0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT
open NK.GlobalCFTdeep.SecondInequality

/-! ## The reduction to the `p`-primary parts

The second inequality `[C_K : N_{L/K}C_L] ≤ [L : K]` is proved by showing that the index divides
`Nat.card (Gal(L/K)) = [L : K]`.  Since the norm index is finite
(`NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero`) and every subgroup of a finite group has
nonzero index, it suffices by `Nat.factorization_le_iff_dvd` to bound the `p`-primary part for
every prime `p`. -/

/-- **The index bound from the `p`-primary parts.**  If the `q`-primary part of the norm index is
bounded by that of `[L : K]` for every prime `q`, then the norm index divides `[L : K]`. -/
theorem index_le_finrank_of_factorization_le {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h : ∀ q, q.Prime → ((Idele.normClassSubgroup K L).index).factorization q ≤
      (Nat.card (L ≃ₐ[K] L)).factorization q) :
    (Idele.normClassSubgroup K L).index ≤ Module.finrank K L := by
  have hidx0 : (Idele.normClassSubgroup K L).index ≠ 0 :=
    normClassSubgroup_index_ne_zero
  have hcard0 : Nat.card (L ≃ₐ[K] L) ≠ 0 := by
    rw [Nat.card_ne_zero]; exact ⟨⟨1⟩, inferInstance⟩
  have hfac : (Idele.normClassSubgroup K L).index.factorization ≤
      (Nat.card (L ≃ₐ[K] L)).factorization := by
    rw [Finsupp.le_def]
    intro q
    by_cases hq : q.Prime
    · exact h q hq
    · rw [Nat.factorization_eq_zero_of_not_prime _ hq]
      exact Nat.zero_le _
  have hdvd : (Idele.normClassSubgroup K L).index ∣ Nat.card (L ≃ₐ[K] L) :=
    (Nat.factorization_le_iff_dvd hidx0 hcard0).mp hfac
  calc (Idele.normClassSubgroup K L).index ≤ Nat.card (L ≃ₐ[K] L) :=
        Nat.le_of_dvd Nat.card_pos hdvd
    _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L

/-- **The `p`-primary bound for a subgroup `S ≤ Gal(L/K)` which is a `p`-group** (a Sylow
`p`-subgroup in the application).  The index of `N_{L/K}C_L` is compared with the index of the
norm subgroup of the sub-extension `L / L^S` — whose `p`-part is bounded by `[L : L^S] = |S|` by
the second inequality for the solvable (indeed nilpotent) extension `L / L^S` — using the fact
that restriction `Ĥ⁰(Gal(L/K), C_L) → Ĥ⁰(S, C_L)` is injective on `p`-primary parts when
`p ∤ [G : S]`. -/
theorem factorization_index_le_of_subgroup {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (q : ℕ) (hq : q.Prime) (S : Subgroup (L ≃ₐ[K] L)) [Fintype ↥S]
    (hSpg : IsPGroup q ↥S) (hSnd : ¬ q ∣ S.index)
    (hScard : Nat.card ↥S = q ^ (Nat.card (L ≃ₐ[K] L)).factorization q) :
    ((Idele.normClassSubgroup K L).index).factorization q ≤
      (Nat.card (L ≃ₐ[K] L)).factorization q := by
  -- the index of `N_{L/K}C_L` is the order of `Ĥ⁰(Gal(L/K), C_L)`
  have hK : ((Idele.normClassSubgroup K L).index).factorization q =
      ((Nat.card (H0 (L ≃ₐ[K] L) (IdeleClassGroup L)))).factorization q := by
    rw [normClassSubgroup_index_eq_natCard_H0 (K := K) (L := L)]
  -- both `Ĥ⁰` groups are finite
  have hG : Nat.card (H0 (L ≃ₐ[K] L) (IdeleClassGroup L)) ≠ 0 := by
    rw [← normClassSubgroup_index_eq_natCard_H0 (K := K) (L := L)]
    exact normClassSubgroup_index_ne_zero
  have hH : Nat.card (H0 ↥S (IdeleClassGroup L)) ≠ 0 := by
    rw [← normClassSubgroup_fixedField_index_eq_natCard_H0 (K := K) (L := L) (S := S)]
    exact normClassSubgroup_index_ne_zero
  -- restriction is injective on `q`-primary parts
  have hcomp := factorization_natCard_H0_le (G := L ≃ₐ[K] L) (M := IdeleClassGroup L)
    (H := S) hq hSnd hG hH
  -- the subgroup side is bounded by the order of the Sylow `q`-subgroup
  have hbnd : Nat.card (H0 ↥S (IdeleClassGroup L)) ≤ Nat.card ↥S := by
    rw [← normClassSubgroup_fixedField_index_eq_natCard_H0 (K := K) (L := L) (S := S)]
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : Group.IsSolvable (L ≃ₐ[↥(IntermediateField.fixedField S)] L) := by
      haveI hpg : IsPGroup q (L ≃ₐ[↥(IntermediateField.fixedField S)] L) :=
        IsPGroup.of_equiv hSpg (IntermediateField.subgroupEquivAlgEquiv S)
      haveI : Group.IsNilpotent (L ≃ₐ[↥(IntermediateField.fixedField S)] L) :=
        IsPGroup.isNilpotent hpg
      infer_instance
    calc (Idele.normClassSubgroup ↥(IntermediateField.fixedField S) L).index
        ≤ Module.finrank ↥(IntermediateField.fixedField S) L := index_le_finrank_of_isSolvable
      _ = Nat.card (L ≃ₐ[↥(IntermediateField.fixedField S)] L) :=
          (IsGalois.card_aut_eq_finrank ↥(IntermediateField.fixedField S) L).symm
      _ = Nat.card ↥S :=
          (Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv S).toEquiv).symm
  calc ((Idele.normClassSubgroup K L).index).factorization q
      = (Nat.card (H0 (L ≃ₐ[K] L) (IdeleClassGroup L))).factorization q := hK
    _ ≤ (Nat.card (H0 ↥S (IdeleClassGroup L))).factorization q := hcomp
    _ ≤ (Nat.card (L ≃ₐ[K] L)).factorization q := by
        refine Nat.factorization_le_of_le_pow ?_
        rw [← hScard]
        exact hbnd

/-- **The second inequality for every finite Galois extension of number fields.**  For each prime
`q`, a Sylow `q`-subgroup `S` of `Gal(L/K)` has `q`-part `q ^ v_q([L : K])` and index coprime to
`q`, so the previous lemma bounds the `q`-primary part of the norm index by `v_q([L : K])`; hence
the norm index divides `[L : K]`. -/
theorem index_le_finrank_of_isGalois {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    (Idele.normClassSubgroup K L).index ≤ Module.finrank K L :=
  index_le_finrank_of_factorization_le fun q hq => by
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨S⟩ : Nonempty (Sylow q (L ≃ₐ[K] L)) := Sylow.nonempty
    haveI : Fintype ↥(S : Subgroup (L ≃ₐ[K] L)) := Fintype.ofFinite _
    exact factorization_index_le_of_subgroup (K := K) (L := L) q hq
      (S : Subgroup (L ≃ₐ[K] L)) S.isPGroup' (Sylow.not_dvd_index S)
      (Sylow.card_eq_multiplicity S)

/-- **The second inequality of global class field theory for every finite Galois extension of
number fields**, unconditionally: `[C_K : N_{L/K}C_L] ≤ [L : K]`.

This is Milne, *Class Field Theory*, Theorem 5.1(a).  The statement is the structure
`NK.GlobalCFTdeep.SecondInequality` (defined in `Submission/Work/GlobalCFTdeep/Inequalities.lean`),
whose single field `index_le` is the inequality for every finite Galois `L/K`.

Proof plan (the classical one of Milne 5.3–5.4, using the two cases that are already
unconditional in this chapter):

* **cyclic** `G`: `NK.GlobalCFTdeep.index_le_finrank_of_isCyclic` (Kummer-theoretic cyclic prime
  case + the tower inequality);
* **solvable** `G`: `NK.GlobalCFTdeep.index_le_finrank_of_isSolvable`;
* **general** `G`: let `S ≤ G` be a Sylow `p`-subgroup and `K' = L^S`.  Then
  `index_K = Nat.card (tateCohomology (IdeleClassGroup.rep K L) 0)` and
  `index_{K'} = Nat.card (tateCohomology (IdeleClassGroup.rep K' L) 0)`
  (`NK.GlobalCFT.H0Computation.index_eq_natCard`), and the restriction map
  `Ĥ⁰(G, C_L) → Ĥ⁰(S, C_L)` is injective on `p`-primary parts: in the model
  `Ĥ⁰(G,M) ≅ M^G/N_G M` (`Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso`) the
  restriction is the identity on `M^G` while `cor(y) = ∑_i g_i y` for coset representatives `g_i`,
  so `cor (res x) = [G:S] • x`; an element killed by restriction is therefore annihilated by
  `[G:S]`, which is coprime to `p`.  Since `index_{K'} ≤ |S|` (the `p`-group case), this gives
  `p ^ (index_K).factorization p ≤ p ^ (Nat.card G).factorization p` for every prime `p`, hence
  `index_K ∣ Nat.card G = [L:K]`, hence `index_K ≤ [L:K]`.
  Finiteness (`index_K ≠ 0`, needed because `Nat.card` of an infinite type is `0`) is
  `NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero` (the norm index of *every* finite extension
  of number fields is finite), and `Nat.card G = [L:K]` is `IsGalois.card_aut_eq_finrank`. -/
theorem secondInequality_unconditional : NK.GlobalCFTdeep.SecondInequality :=
  ⟨fun {K L} _ _ _ _ _ _ _ => index_le_finrank_of_isGalois (K := K) (L := L)⟩

end NK.GlobalCFTdeep
