import Mathlib
import Submission.Work.TorsorExistence.Defs
import Submission.Work.TorsorExistence.ArtinSchreier.Basic
import Submission.Work.TorsorExistence.ArtinSchreier.Irreducible
import Submission.Work.TorsorExistence.ArtinSchreier.SplittingField
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.TorsorExistence

universe u

open Polynomial

/-- **Artin–Schreier theory, degree five.**  Over a field `𝕜` of characteristic `5`, if
`a ∈ 𝕜` is not of the form `b ^ 5 - b`, then `X ^ 5 - X - a` is irreducible over `𝕜` and its
root field is a cyclic extension of degree `5` of `𝕜`. -/
theorem existsCyclicExtension_of_charP_five {𝕜 : Type u} [Field 𝕜] [CharP 𝕜 5] (a : 𝕜)
    (ha : ¬ ∃ b : 𝕜, b ^ 5 - b = a) : Nonempty (CyclicExtension 𝕜 5) := by
  classical
  have hIrr : Irreducible (X ^ 5 - X - C a : 𝕜[X]) :=
    ArtinSchreier.irreducible_X_pow_five_sub_X_sub_C a ha
  haveI hFact : Fact (Irreducible (X ^ 5 - X - C a : 𝕜[X])) := ⟨hIrr⟩
  let L := AdjoinRoot (X ^ 5 - X - C a : 𝕜[X])
  have hnat : (X ^ 5 - X - C a : 𝕜[X]).natDegree = 5 := by
    have h : (X ^ 5 - X - C a : 𝕜[X]) = (X ^ 5 - C a) - X := by ring
    rw [h, natDegree_sub_eq_left_of_natDegree_lt]
    · exact natDegree_X_pow_sub_C
    · rw [natDegree_X, natDegree_X_pow_sub_C]; norm_num
  have hf0 : (X ^ 5 - X - C a : 𝕜[X]) ≠ 0 := by
    intro h; rw [h] at hnat; simp at hnat
  -- the root of `f` in `L`
  have hαeval : aeval (AdjoinRoot.root (X ^ 5 - X - C a : 𝕜[X]))
      (X ^ 5 - X - C a : 𝕜[X]) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hα : (AdjoinRoot.root (X ^ 5 - X - C a : 𝕜[X])) ^ 5
      - AdjoinRoot.root (X ^ 5 - X - C a : 𝕜[X]) = algebraMap 𝕜 L a := by
    have h := hαeval
    simp only [map_sub, map_pow, aeval_X, aeval_C] at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  -- `L` is a splitting field of `f`
  haveI hSplit : IsSplittingField 𝕜 L (X ^ 5 - X - C a : 𝕜[X]) :=
    ArtinSchreier.isSplittingField_adjoin_of_pow_five_sub_self a hα AdjoinRoot.adjoinRoot_eq_top
  haveI : FiniteDimensional 𝕜 L :=
    IsSplittingField.finiteDimensional L (X ^ 5 - X - C a : 𝕜[X])
  -- `f` is separable, with derivative `-1`
  have hderiv : derivative (X ^ 5 - X - C a : 𝕜[X]) = -1 := by
    rw [derivative_sub, derivative_sub, derivative_X, derivative_C, derivative_X_pow,
      C_eq_algebraMap, map_natCast (algebraMap 𝕜 𝕜[X]) 5, CharP.cast_eq_zero 𝕜[X] 5,
      zero_mul]
    first | refl_ring1 | ring
  have hsep : (X ^ 5 - X - C a : 𝕜[X]).Separable := by
    rw [separable_def, hderiv]
    exact ⟨0, -1, by ring⟩
  haveI : IsGalois 𝕜 L := IsGalois.of_separable_splitting_field hsep
  -- the degree is `5`
  have hfin : Module.finrank 𝕜 L = 5 := by
    change Module.finrank 𝕜 (AdjoinRoot (X ^ 5 - X - C a : 𝕜[X])) = 5
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis (f := (X ^ 5 - X - C a : 𝕜[X])) hf0),
      AdjoinRoot.powerBasis_dim (f := (X ^ 5 - X - C a : 𝕜[X])) hf0, hnat]
  -- the Galois group is cyclic of order `5`
  have hcard : Nat.card (L ≃ₐ[𝕜] L) = 5 := by
    rw [IsGalois.card_aut_eq_finrank 𝕜 L, hfin]
  haveI : Fintype (L ≃ₐ[𝕜] L) := AlgEquiv.fintype 𝕜 L
  haveI : Finite (L ≃ₐ[𝕜] L) := Finite.of_fintype _
  haveI : Nontrivial (L ≃ₐ[𝕜] L) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]; norm_num
  obtain ⟨g, hg⟩ := exists_ne (1 : L ≃ₐ[𝕜] L)
  have hgord : orderOf g = 5 := by
    have hdvd : orderOf g ∣ 5 := by
      simpa only [hcard] using orderOf_dvd_natCard g
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hg
    · exact h
  haveI : IsCyclic (L ≃ₐ[𝕜] L) := isCyclic_of_orderOf_eq_card g (by rw [hgord, hcard])
  obtain ⟨gen, hgen⟩ := IsCyclic.exists_generator (α := L ≃ₐ[𝕜] L)
  have hgenord : orderOf gen = 5 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, hcard]
  refine ⟨{ L := L
            finrank_eq := hfin
            gen := gen
            gen_generator := ?_
            orderOf_gen := hgenord }⟩
  intro g'
  have hmem : g' ∈ Submonoid.powers gen :=
    (isOfFinOrder_of_finite gen).mem_powers_iff_mem_zpowers.mpr (hgen g')
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff g' gen).mp hmem
  exact ⟨k, hk.symm⟩

end Work.TorsorExistence
