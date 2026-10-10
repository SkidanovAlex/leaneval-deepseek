import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.FunLike.Fintype
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.GlobalCFTdeep.Inequalities
import Submission.NK.GlobalCFTdeep.SecondInequality.card_le_finrank_of_bound
import Submission.NK.GlobalCFTdeep.SecondInequality.index_normClassSubgroup_eq_card_rayClassGroup
import Submission.NK.GlobalCFTdeep.SecondInequality.log_norm_eulerProduct_one_le
import Submission.NK.GlobalCFTdeep.SecondInequality.mul_trivialClassSum_le
import Submission.NK.GlobalCFTdeep.SecondInequality.primeClass_eq_one_of_splitsCompletely
import Submission.NK.GlobalCFTdeep.SecondInequality.primeClass_eq_one_of_splitsCompletely_of_le
import Submission.NK.GlobalCFTdeep.SecondInequality.sum_log_norm_eulerProduct_nontrivial_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The second inequality of global class field theory

This file assembles the analytic proof of the **second inequality**

  `[C_K : N_{L/K} C_L] ≤ [L : K]`   for every finite Galois extension of number fields

from the chapter's named analytic input (`HeckeRegularity`, Hecke's theorem that the Hecke
`L`-series of a non-trivial ray class character is regular at `s = 1`) and the completely-split
primes' density `1/[L:K]` (proved in the shared library).  This is Milne, *Class Field Theory*,
Chapter VI: Theorem 4.8 (the density of the primes in a congruence subgroup) and Theorem 4.9 (the
second inequality).

The mathematical organisation is:

* (`mul_trivialClassSum_le_log`) Milne VI.4.8: for a finite abelian group `B`, a class map
  `b : PrimeIdeal K → B` and Euler products `L(χ,s) = ∏_{𝔭∉S} (1 - χ(b𝔭)N𝔭^{-s})⁻¹` that are
  regular at `s = 1` for `χ ≠ 1`, one has
  `|B| · ∑_{b𝔭 = 1} N𝔭^{-s} ≤ log (1/(s-1)) + C` near `s = 1⁺`.
* (`card_le_finrank_of_bound`) since the completely split primes are among those with `b𝔭 = 1`
  and have density `1/[L:K]`, this forces `|B| ≤ [L:K]`.
* (`index_le_finrank_of_heckeRegularity`) instantiate with `B = 𝕀 K ⧸ (Kˣ ⊔ N_{L/K} 𝕀 L)`, the
  ray class group modulo the norm subgroup, using that a completely split prime is a norm
  (`primeClass_eq_one_of_splitsCompletely_of_le`), and translate back through
  `index_normClassSubgroup_eq_card_rayClassGroup`.

Everything is `sorry`-free; the only named classical input is `HeckeRegularity`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain Filter
open scoped BigOperators Topology

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality

open NK.GlobalCFT

/-- **Milne VI.4.8, the analytic bound.**  For a finite abelian group `B`, a class map
`b : PrimeIdeal K → B` and Euler products regular at `s = 1` for every non-trivial `χ`, the sum of
the weights of the primes with trivial class is at most `|B|⁻¹ · log (1/(s-1))` up to a constant.

The proof combines `mul_trivialClassSum_le` (`|B| · ∑_{b𝔭=1} N𝔭^{-s}` bounded by
`∑_χ log ‖L(χ,s)‖`), `log_norm_eulerProduct_one_le` (the trivial character contributes
`log (1/(s-1)) + O(1)`) and `sum_log_norm_eulerProduct_nontrivial_le` (the non-trivial characters
contribute `O(1)`). -/
theorem mul_trivialClassSum_le_log {K : Type} [Field K] [NumberField K] {B : Type}
    [CommGroup B] [Fintype B] [DecidableEq B] (b : PrimeIdeal K → B) (S : Finset (PrimeIdeal K))
    (hreg : ∀ χ : B →* ℂˣ, χ ≠ 1 → ∃ v : ℂ,
      Filter.Tendsto (eulerProduct b S χ) (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds v)) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      (Nat.card B : ℝ) * trivialClassSum b S s ≤ Real.log (1 / (s - 1)) + C := by
  obtain ⟨C₁, h₁⟩ := mul_trivialClassSum_le b S
  obtain ⟨C₂, h₂⟩ := log_norm_eulerProduct_one_le b S
  obtain ⟨C₃, h₃⟩ := sum_log_norm_eulerProduct_nontrivial_le b S hreg
  refine ⟨C₁ + C₂ + C₃, ?_⟩
  filter_upwards [self_mem_nhdsWithin, h₂, h₃] with s hs hs₂ hs₃
  have hsplit : (∑ χ : B →* ℂˣ, Real.log ‖eulerProduct b S χ s‖)
      = (∑ χ ∈ Finset.univ.erase (1 : B →* ℂˣ), Real.log ‖eulerProduct b S χ s‖)
        + Real.log ‖eulerProduct b S 1 s‖ := by
    rw [(Finset.sum_erase_add (Finset.univ : Finset (B →* ℂˣ))
      (fun χ => Real.log ‖eulerProduct b S χ s‖) (Finset.mem_univ (1 : B →* ℂˣ))).symm]
  have hmain := h₁ s hs
  rw [hsplit] at hmain
  linarith

/-- **Hecke's theorem, as the analytic input of the second inequality** (E. Hecke, *Eine neue Art
von Zetafunktionen*, 1917): for a finite extension `L/K` of number fields, every non-trivial
character of the ray class group `𝕀 K ⧸ (Kˣ · N_{L/K} 𝕀 L)` modulo the norm subgroup has an
`L`-series which is regular at `s = 1` (a finite limit).

This is a specific classical theorem.  Its satisfiability is independent of class field theory:
the characters in question are trivial on the norm subgroup, which has finite index in `𝕀 K`
(the local norm groups have finite index in the local multiplicative groups), so they are
characters of a finite quotient of the idèle class group, i.e. Hecke characters of some modulus.

The *non-vanishing* of the `L`-series at `s = 1` is deliberately **not** assumed: as in Milne's
proof of Theorem 4.8, it is a consequence of the density argument (`mul_trivialClassSum_le_log`
only needs regularity). -/
structure HeckeRegularity : Prop where
  /-- regularity of the Hecke `L`-series of every non-trivial character modulo the norm subgroup. -/
  regular : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (S : Finset (PrimeIdeal K))
    (χ : HeckeL.RayChar K (Idele.normImage K L)), χ ≠ 1 →
      ∃ v : ℂ, Filter.Tendsto (fun s : ℝ => HeckeL.heckeLSeries K (Idele.normImage K L) S χ s)
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds v)

/-- **The second inequality** `[C_K : N_{L/K}C_L] ≤ [L:K]`, from Hecke's regularity input.

This is Milne, *Class Field Theory*, Theorem 4.9 (proved in Chapter VI from the density of the
primes in a congruence subgroup, Theorem 4.8). -/
theorem index_le_finrank_of_heckeRegularity (hH : HeckeRegularity)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (Idele.normClassSubgroup K L).index ≤ Module.finrank K L := by
  classical
  rw [index_normClassSubgroup_eq_card_rayClassGroup (K := K) (L := L)]
  by_cases hfin : Nat.card (IdeleClassGroup.rayClassGroup K (Idele.normImage K L)) = 0
  · rw [hfin]; exact Nat.zero_le _
  · haveI : Finite (IdeleClassGroup.rayClassGroup K (Idele.normImage K L)) :=
      (Nat.card_ne_zero.mp hfin).2
    haveI : Fintype (IdeleClassGroup.rayClassGroup K (Idele.normImage K L)) :=
      Fintype.ofFinite _
    have hbound : ∃ C : ℝ, ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1),
        (Nat.card (IdeleClassGroup.rayClassGroup K (Idele.normImage K L)) : ℝ)
          * trivialClassSum (HeckeL.primeClass K (Idele.normImage K L)) ∅ s
          ≤ Real.log (1 / (s - 1)) + C := by
      apply mul_trivialClassSum_le_log
      intro χ hχ
      obtain ⟨v, hv⟩ := hH.regular (K := K) (L := L) ∅ χ hχ
      refine ⟨v, hv.congr' ?_⟩
      have heq : HeckeL.heckeLSeries K (Idele.normImage K L) ∅ χ
          =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)]
            eulerProduct (HeckeL.primeClass K (Idele.normImage K L)) ∅ χ := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [HeckeL.Series.heckeLSeries_eq_heckeEulerProduct (Idele.normImage K L) ∅ χ hs]
        rfl
      exact heq
    exact card_le_finrank_of_bound (HeckeL.primeClass K (Idele.normImage K L)) ∅
      (fun 𝔭 _ h𝔭 => primeClass_eq_one_of_splitsCompletely_of_le le_rfl 𝔭 h𝔭) hbound

/-- **The second inequality of global class field theory**, as the `Prop`-structure
`NK.GlobalCFTdeep.SecondInequality` consumed by the rest of the chapter. -/
theorem secondInequality_of_heckeRegularity (hH : HeckeRegularity) :
    NK.GlobalCFTdeep.SecondInequality where
  index_le := fun {K L} _ _ _ _ _ _ _ =>
    index_le_finrank_of_heckeRegularity hH

end NK.GlobalCFTdeep.SecondInequality
