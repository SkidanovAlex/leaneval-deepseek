import Mathlib
import Submission.Vdw.BlockPoly
import Submission.Vdw.GaloisRamification
import Submission.Vdw.CaseI
import Submission.Commons.NumberTheory.NumberField.card_algHom_eq_finrank

open Polynomial
open scoped Pointwise

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-!
# The structural dictionary of the imprimitive slice, II: the transfer to `ℂ`

`BlockPolyGalois` develops the dictionary inside the splitting field
`E = p.SplittingField`.  The counting argument of the imprimitive slice,
however, lives over `ℂ` (Mahler measures, conjugates, algebraic integers).
This module performs the first half of the transfer:

* `isIntegral_of_aeval_map_monic` — an element of an `ℤ`-algebra that is a root
  of `f.map (algebraMap ℤ E)` for a monic `f : ℤ[X]` is integral over `ℤ`;
* `exists_algHom_complex` — a `ℚ`-algebra embedding `p.SplittingField →ₐ[ℚ] ℂ`;
* `isIntegral_coeff_prod_X_sub_C`, `isIntegral_coeff_blockPoly` — the
  coefficients of a product of `X - C a` with integral `a`, hence the
  coefficients of the block polynomial, are integral over `ℤ`;
* `blockPolyC` — the complex block polynomial `(blockPoly p hsep B).map ι`,
  with `blockPolyC_monic`, `blockPolyC_natDegree`, `blockPolyC_coeff`, and
  `isIntegral_coeff_blockPolyC` (its coefficients are complex algebraic
  integers, the input to `minpoly`/Mahler-measure counting).

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **Integrality from a monic integer polynomial.**  If `f : ℤ[X]` is monic and
`x` is a root of its image in an `ℤ`-algebra `E`, then `x` is integral over
`ℤ`. -/
theorem isIntegral_of_aeval_map_monic {E : Type*} [Field E] [Algebra ℤ E] {x : E}
    {f : ℤ[X]} (hm : f.Monic) (h : aeval x (f.map (algebraMap ℤ E)) = 0) :
    IsIntegral ℤ x := by
  refine ⟨f, hm, ?_⟩
  simpa only [Polynomial.aeval_def, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq ℤ E E]
    using h

/-- **A complex embedding of the splitting field.** -/
theorem exists_algHom_complex (p : ℚ[X]) : Nonempty (p.SplittingField →ₐ[ℚ] ℂ) := by
  haveI : Algebra.IsSeparable ℚ p.SplittingField := inferInstance
  exact Fintype.card_pos_iff.mp (by
    rw [Commons.NumberTheory.NumberField.card_algHom_eq_finrank]
    exact Module.finrank_pos)

/-- **The coefficients of a product of `X - C a` with integral `a` are
integral.** -/
lemma isIntegral_coeff_prod_X_sub_C {E : Type*} [Field E] [Algebra ℤ E] {ι : Type*}
    (s : Finset ι) (a : ι → E) (ha : ∀ i, IsIntegral ℤ (a i)) :
    ∀ n, IsIntegral ℤ ((∏ i ∈ s, (X - C (a i)) : E[X]).coeff n) := by
  classical
  have hX : ∀ c : E, IsIntegral ℤ c → ∀ k : ℕ,
      IsIntegral ℤ ((X - C c : E[X]).coeff k) := by
    intro c hc k
    rcases eq_or_ne k 0 with hk | hk
    · subst hk
      simpa using IsIntegral.neg hc
    rcases eq_or_ne k 1 with hk1 | hk1
    · subst hk1
      simpa using isIntegral_one (R := ℤ) (B := E)
    · rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C,
        if_neg (Ne.symm hk1), if_neg hk, sub_zero]
      exact isIntegral_zero
  induction s using Finset.induction_on with
  | empty =>
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simpa using isIntegral_one (R := ℤ) (B := E)
      · rw [Finset.prod_empty, Polynomial.coeff_one, if_neg (by omega)]
        exact isIntegral_zero
  | insert j s hj ih =>
      intro n
      rw [Finset.prod_insert hj, Polynomial.coeff_mul]
      exact IsIntegral.sum _ fun k _ => IsIntegral.mul (hX (a j) (ha j) k.1) (ih k.2)

/-- **The indexed roots of `f.map φℚ` are integral over `ℤ`** (`f` monic). -/
theorem isIntegral_rootOf (f : ℤ[X]) (hm : f.Monic) (hsep : (f.map φℚ).Separable)
    (i : Fin (f.map φℚ).natDegree) :
    IsIntegral ℤ (rootOf (f.map φℚ) hsep i) := by
  have h0 : aeval (rootOf (f.map φℚ) hsep i) (f.map φℚ) = 0 :=
    aeval_eq_zero_of_mem_rootSet ((rootFinEquiv (f.map φℚ) hsep).symm i).2
  have h2 : f.map (algebraMap ℤ (f.map φℚ).SplittingField) =
      (f.map φℚ).map (algebraMap ℚ (f.map φℚ).SplittingField) := by
    rw [Polynomial.map_map, IsScalarTower.algebraMap_eq ℤ ℚ (f.map φℚ).SplittingField]
    simp only [φℚ]
  have h : aeval (rootOf (f.map φℚ) hsep i)
      (f.map (algebraMap ℤ (f.map φℚ).SplittingField)) = 0 := by
    rw [h2, Polynomial.aeval_def, Polynomial.eval₂_map,
      ← IsScalarTower.algebraMap_eq ℚ (f.map φℚ).SplittingField (f.map φℚ).SplittingField,
      ← Polynomial.aeval_def]
    exact h0
  exact isIntegral_of_aeval_map_monic hm h

/-- **The coefficients of the block polynomial are integral over `ℤ`.** -/
theorem isIntegral_coeff_blockPoly (f : ℤ[X]) (hm : f.Monic) (hsep : (f.map φℚ).Separable)
    (B : Finset (Fin (f.map φℚ).natDegree)) (n : ℕ) :
    IsIntegral ℤ ((blockPoly (f.map φℚ) hsep B).coeff n) := by
  rw [blockPoly]
  exact isIntegral_coeff_prod_X_sub_C B (rootOf (f.map φℚ) hsep)
    (isIntegral_rootOf f hm hsep) n

/-- The complex block polynomial: the image of `blockPoly p hsep B` under a
`ℚ`-algebra embedding of the splitting field into `ℂ`. -/
def blockPolyC (p : ℚ[X]) (hsep : p.Separable) (B : Finset (Fin p.natDegree))
    (ι : p.SplittingField →ₐ[ℚ] ℂ) : ℂ[X] :=
  (blockPoly p hsep B).map ι.toRingHom

lemma blockPolyC_monic (p : ℚ[X]) (hsep : p.Separable) (B : Finset (Fin p.natDegree))
    (ι : p.SplittingField →ₐ[ℚ] ℂ) : (blockPolyC p hsep B ι).Monic :=
  (blockPoly_monic p hsep B).map ι.toRingHom

lemma blockPolyC_natDegree (p : ℚ[X]) (hsep : p.Separable) (B : Finset (Fin p.natDegree))
    (ι : p.SplittingField →ₐ[ℚ] ℂ) : (blockPolyC p hsep B ι).natDegree = B.card := by
  rw [blockPolyC, (blockPoly_monic p hsep B).natDegree_map ι.toRingHom, blockPoly_natDegree]

lemma blockPolyC_coeff (p : ℚ[X]) (hsep : p.Separable) (B : Finset (Fin p.natDegree))
    (ι : p.SplittingField →ₐ[ℚ] ℂ) (n : ℕ) :
    (blockPolyC p hsep B ι).coeff n = ι ((blockPoly p hsep B).coeff n) :=
  Polynomial.coeff_map _ _

/-- **The coefficients of the complex block polynomial are algebraic
integers.** -/
theorem isIntegral_coeff_blockPolyC (f : ℤ[X]) (hm : f.Monic)
    (hsep : (f.map φℚ).Separable) (B : Finset (Fin (f.map φℚ).natDegree))
    (ι : (f.map φℚ).SplittingField →ₐ[ℚ] ℂ) (n : ℕ) :
    IsIntegral ℤ ((blockPolyC (f.map φℚ) hsep B ι).coeff n) := by
  rw [blockPolyC_coeff]
  exact (isIntegral_coeff_blockPoly f hm hsep B n).map ι

end

end Submission.Vdw
