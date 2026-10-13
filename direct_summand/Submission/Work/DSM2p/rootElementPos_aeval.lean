import Mathlib
import Submission.Work.DSM2p.ConstructionPos
import Submission.Work.DSM2p.adicCompletion_eq_zero_of_mem_pow

/-!
# DSM2p — the roots clause for the positive-degree index set

This module proves the analogue of `Work.DSM2p.rootElement_aeval` for the repaired
Česnavičius–Scholze construction of `ConstructionPos.lean`, whose index set is the set
`MonicPolysPos A` of *positive-degree* monic polynomials:

  `Polynomial.aeval (rootElementPos A p ϖ F) F.1 = 0`.

The proof is the same computation as for the unrestricted index set.  Write `R = A'` for
`CSIntegralClosurePos A p ϖ` (the `p`-integral closure of `A_∞` in `Λ[1/ϖ]`) and
`y = T_F ∈ R`.  Since `A_∞` contains `F(T_F)/ϖ^m` for every `m`, and `ϖ ^ p = p · u` with
`u` a unit, one gets `(p)^n ∣ F(y)` in `R` for every `n`; hence `F(y)` dies in the
`p`-adic completion `B = AdicCompletion (p) R` by `adicCompletion_eq_zero_of_mem_pow`.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-- The inclusion `A' ⊆ Λ[1/ϖ]` for the positive-degree construction, as an `A`-algebra
homomorphism.  The `A`-algebra structure on `A' = CSIntegralClosurePos A p ϖ` is the one
defined in `ConstructionPos.lean` (the restriction of `A → Λ → Λ[1/ϖ]`), so the subtype
inclusion is an `A`-algebra map. -/
noncomputable def csInclAlgHomPos (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) :
    CSIntegralClosurePos A p ϖ →ₐ[A] RootAlgLocPos A p ϖ where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  map_zero' := rfl
  map_add' := fun _ _ => rfl
  commutes' := fun _ => rfl

/-- `F(T_F)`, computed in `Λ[1/ϖ]`, agrees with the base change of `F(T_F)` computed in `Λ`. -/
theorem aeval_rootVarLocPos_eq (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : MonicPolysPos A) :
    (algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ))
        (Polynomial.aeval (rootVarPos A p F) F.1)
      = Polynomial.aeval (rootVarLocPos A p ϖ F) F.1 := by
  rw [rootVarLocPos]
  exact (Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom A (RootAlgPos A p) (RootAlgLocPos A p ϖ)) (rootVarPos A p F)
    F.1).symm

/-- `F(T_F)`, computed in `A'` and then mapped into `Λ[1/ϖ]`, agrees with `F(T_F)` computed
directly in `Λ[1/ϖ]`. -/
theorem aeval_rootVarInClosurePos_val (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : MonicPolysPos A) :
    ((Polynomial.aeval (rootVarInClosurePos A p ϖ F) F.1 : CSIntegralClosurePos A p ϖ)
        : RootAlgLocPos A p ϖ)
      = Polynomial.aeval (rootVarLocPos A p ϖ F) F.1 :=
  (Polynomial.aeval_algHom_apply (csInclAlgHomPos A p ϖ) (rootVarInClosurePos A p ϖ F)
    F.1).symm

/-- `F(T_F) / ϖ^m` lies in `A_∞ = CSAlgPos A p ϖ ⊆ Λ[1/ϖ]` for every `m`. -/
theorem aeval_rootVarLocPos_mul_invSelf_pow_mem_CSAlgPos (A : Type u) [CommRing A] (p : ℕ)
    (ϖ : A) (F : MonicPolysPos A) (m : ℕ) :
    Polynomial.aeval (rootVarLocPos A p ϖ F) F.1 *
        (IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ)) ^ m ∈ CSAlgPos A p ϖ := by
  rw [← aeval_rootVarLocPos_eq A p ϖ F, CSAlgPos]
  refine Subring.subset_closure (Set.mem_union_right _ ?_)
  exact ⟨(F, m), rfl⟩

/-- **The divisibility that makes `F(T_F)` vanish in the `p`-adic completion.**  If
`ϖ ^ p = p · u` with `u` a unit, then `p ^ n` divides `F(T_F)` in `A'` for every `n`. -/
theorem p_pow_dvd_aeval_rootVarInClosurePos (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (hunit : ∃ u : Aˣ, ϖ ^ p = (p : A) * u) (F : MonicPolysPos A) (n : ℕ) :
    (p : CSIntegralClosurePos A p ϖ) ^ n ∣
      Polynomial.aeval (rootVarInClosurePos A p ϖ F) F.1 := by
  obtain ⟨u, hu⟩ := hunit
  -- `p = ϖ ^ p · u⁻¹` in `A`.
  have hpA : (p : A) = ϖ ^ p * (↑(u⁻¹) : A) := by
    rw [hu, mul_assoc, Units.mul_inv, mul_one]
  have hmemR : Polynomial.aeval (rootVarLocPos A p ϖ F) F.1 *
      (IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ)) ^ (p * n)
      ∈ CSIntegralClosurePos A p ϖ :=
    CSAlgPos_le_CSIntegralClosurePos A p ϖ
      (aeval_rootVarLocPos_mul_invSelf_pow_mem_CSAlgPos A p ϖ F (p * n))
  refine dvd_def.mpr ⟨(algebraMap A (CSIntegralClosurePos A p ϖ) (↑u : A)) ^ n *
      ⟨Polynomial.aeval (rootVarLocPos A p ϖ F) F.1 *
        (IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ)) ^ (p * n), hmemR⟩, ?_⟩
  apply Subtype.ext
  rw [aeval_rootVarInClosurePos_val A p ϖ F]
  push_cast
  rw [show ((p : RootAlgLocPos A p ϖ)) = algebraMap A (RootAlgLocPos A p ϖ) (p : A)
      from (map_natCast _ p).symm]
  rw [show (↑((algebraMap A (CSIntegralClosurePos A p ϖ) (↑u : A))) : RootAlgLocPos A p ϖ)
      = algebraMap A (RootAlgLocPos A p ϖ) (↑u : A) from rfl]
  have hsinv : algebraMap A (RootAlgLocPos A p ϖ) ϖ *
      IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) = 1 := by
    rw [IsScalarTower.algebraMap_apply A (RootAlgPos A p) (RootAlgLocPos A p ϖ) ϖ]
    exact IsLocalization.Away.mul_invSelf _
  have huL : algebraMap A (RootAlgLocPos A p ϖ) (↑(u⁻¹) : A) *
      algebraMap A (RootAlgLocPos A p ϖ) (↑u : A) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [hpA, map_mul, map_pow, mul_pow, ← pow_mul]
  have hbc : (algebraMap A (RootAlgLocPos A p ϖ) (↑(u⁻¹) : A)) ^ n *
      (algebraMap A (RootAlgLocPos A p ϖ) (↑u : A)) ^ n = 1 := by
    rw [← mul_pow, huL, one_pow]
  have hai : (algebraMap A (RootAlgLocPos A p ϖ) ϖ) ^ (p * n) *
      (IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ)) ^ (p * n) = 1 := by
    rw [← mul_pow, hsinv, one_pow]
  rw [show (algebraMap A (RootAlgLocPos A p ϖ) ϖ) ^ (p * n) *
        (algebraMap A (RootAlgLocPos A p ϖ) (↑(u⁻¹) : A)) ^ n *
        ((algebraMap A (RootAlgLocPos A p ϖ) (↑u : A)) ^ n *
          (Polynomial.aeval (rootVarLocPos A p ϖ F) F.1 *
           (IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ)) ^ (p * n)))
      = ((algebraMap A (RootAlgLocPos A p ϖ) ϖ) ^ (p * n) *
         (IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ)) ^ (p * n)) *
        ((algebraMap A (RootAlgLocPos A p ϖ) (↑(u⁻¹) : A)) ^ n *
         (algebraMap A (RootAlgLocPos A p ϖ) (↑u : A)) ^ n) *
        Polynomial.aeval (rootVarLocPos A p ϖ F) F.1 from by ring]
  rw [hai, hbc, mul_one, one_mul]

/-- **The roots clause of the Česnavičius–Scholze construction** for the positive-degree
index set.  In `B = AdicCompletion (p) A'` the image of `T_F` is a root of `F`. -/
theorem rootElementPos_aeval (A : Type*) [CommRing A] (p : ℕ) (ϖ : A)
    (hunit : ∃ u : Aˣ, ϖ ^ p = (p : A) * u) (F : MonicPolysPos A) :
    Polynomial.aeval (rootElementPos A p ϖ F) F.1 = 0 := by
  have hmain : ∀ n : ℕ, Polynomial.aeval (rootVarInClosurePos A p ϖ F) F.1 ∈
      (Ideal.span {(p : CSIntegralClosurePos A p ϖ)}) ^ n := by
    intro n
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact p_pow_dvd_aeval_rootVarInClosurePos A p ϖ hunit F n
  have hzero : AdicCompletion.of (Ideal.span {(p : CSIntegralClosurePos A p ϖ)})
      (CSIntegralClosurePos A p ϖ) (Polynomial.aeval (rootVarInClosurePos A p ϖ F) F.1) = 0 :=
    adicCompletion_eq_zero_of_mem_pow _ hmain
  rw [rootElementPos]
  have hbridge : Polynomial.aeval (algebraMap (CSIntegralClosurePos A p ϖ)
        (CSCompletionPos A p ϖ) (rootVarInClosurePos A p ϖ F)) F.1
      = AdicCompletion.of (Ideal.span {(p : CSIntegralClosurePos A p ϖ)})
        (CSIntegralClosurePos A p ϖ)
        (Polynomial.aeval (rootVarInClosurePos A p ϖ F) F.1) := by
    trans (IsScalarTower.toAlgHom A (CSIntegralClosurePos A p ϖ) (CSCompletionPos A p ϖ))
        (Polynomial.aeval (rootVarInClosurePos A p ϖ F) F.1)
    · exact Polynomial.aeval_algHom_apply
        (IsScalarTower.toAlgHom A (CSIntegralClosurePos A p ϖ) (CSCompletionPos A p ϖ))
        (rootVarInClosurePos A p ϖ F) F.1
    · show algebraMap (CSIntegralClosurePos A p ϖ) (CSCompletionPos A p ϖ)
        (Polynomial.aeval (rootVarInClosurePos A p ϖ F) F.1) = _
      rw [AdicCompletion.algebraMap_apply]
      rfl
  rw [hbridge]
  exact hzero

end Work.DSM2p
