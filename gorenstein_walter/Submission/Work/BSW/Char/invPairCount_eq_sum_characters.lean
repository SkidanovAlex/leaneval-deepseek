import Mathlib
import Submission.Work.BSW.Char.Setup
import Submission.Work.BSW.Char.sum_char_div_eq_sum_char_inv
import Submission.Work.BSW.Char.invPairCount_eq_coeff_classSum_mul_self

namespace Work.BSW.Char

open scoped MonoidAlgebra
open OddOrder.GroupTheory.CenterClassSum
open OddOrder.RepresentationTheory

/-- **The involution-product formula** (Gorenstein 9.4.21; Bender 1974 §2, p. 230).

If all involutions of `G` are conjugate to the involution `t` (condition (iv) of `BSWHyps2`), then
the number of ordered pairs `(u, v)` of involutions with `u * v = x` is
`|G| / |C_G(t)|² * Σ_χ χ(t)² χ(x) / χ(1)`, the sum running over the irreducible complex characters
of `G`.  (Numerically checked on `A₅`: `x = 1` gives `15`, `x = t` gives `2`, `x` a 3-cycle gives
`3`, `x` a 5-cycle gives `5`, all matching the direct counts.)

Route: `OddOrder.RepresentationTheory.classSum_mul_apply` (the coefficient of a product of class
sums at `w` counts the factorizations `w = u * v`) together with
`OddOrder.RepresentationTheory.classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter`
(Gorenstein 4.2.12), applied to the involution class `ConjClasses.mk t`.  The cited result carries
`χ(x⁻¹)`; the passage to `χ(x)` uses that the sum is real (`χ ↦ χ̄` permutes the irreducible
characters and `χ(t)`, `χ(1)` are real), not termwise reality of `χ(x)`. -/
theorem invPairCount_eq_sum_characters {G : Type} [Group G] [Fintype G] {t : G}
    (ht : orderOf t = 2) (hconj : ∀ x : G, orderOf x = 2 → IsConj x t) (x : G) :
    (Work.BSW.invPairCount G x : ℂ) =
      (Nat.card G : ℂ) / (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 *
        ∑ χ : OddOrder.RepresentationTheory.IrreducibleCharacter G,
          (((χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) t) ^ 2 *
            (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) x) /
          (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) 1 := by
  classical
  set Ct : ConjClasses G := ConjClasses.mk t with hCt
  set Cs : ConjClasses G := ConjClasses.mk x with hCs
  set A : ℕ := Nat.card { y : G // ConjClasses.mk y = Ct } with hA
  set B : ℕ := Nat.card { y : G // ConjClasses.mk y = Cs } with hB
  set Z : ℕ := Nat.card (Subgroup.centralizer ({t} : Set G)) with hZ
  set Zx : ℕ := Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) with hZx
  set S : ℂ := ∑ χ : IrreducibleCharacter G,
          (((χ : ClassFunction G ℂ) t) ^ 2 * (χ : ClassFunction G ℂ) x) /
          (χ : ClassFunction G ℂ) 1 with hS
  have ht2 : t * t = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two ht
  -- ### the pair count is the coefficient of the square of the class sum of `t`
  have hpairs : (Work.BSW.invPairCount G x : ℂ)
      = (classSum Ct * classSum Ct : ℂ[G]).coeff x := invPairCount_eq_coeff_classSum_mul_self ht hconj x
  -- ### class sum coefficients
  have hout : (classSum Ct * classSum Ct : ℂ[G]).coeff Cs.out
      = (classSum Ct * classSum Ct : ℂ[G]).coeff x := by
    rw [hCs]
    exact (classSum_mul_apply_out Ct Ct x).symm
  have hcoeff : (classSumCoeff Ct Ct Cs : ℂ)
      = (classSum Ct * classSum Ct : ℂ[G]).coeff x * (B : ℂ) := by
    rw [← coeff_mul_card_eq_classSumCoeff Ct Ct Cs, hout, hB]
  -- ### the character-theoretic structure-constant formula
  have hform := classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter (G := G) Ct Ct Cs
  have hmain : (classSum Ct * classSum Ct : ℂ[G]).coeff x * (B : ℂ) * (Zx : ℂ)
      = ∑ χ : IrreducibleCharacter G,
          ((A : ℂ) * (χ : ClassFunction G ℂ) Ct.out *
              ((A : ℂ) * (χ : ClassFunction G ℂ) Ct.out)) /
            (χ : ClassFunction G ℂ) 1 * (χ : ClassFunction G ℂ) Cs.out⁻¹ := by
    rw [← hcoeff]
    exact hform
  -- ### character values at the class representatives
  have hχt (χ : IrreducibleCharacter G) :
      (χ : ClassFunction G ℂ) Ct.out = (χ : ClassFunction G ℂ) t :=
    ClassFunction.of_isConj (χ : ClassFunction G ℂ) (ConjClasses.mk_eq_mk_iff_isConj.mp
      (by rw [conjClass_mk_out Ct, hCt]))
  have hχx (χ : IrreducibleCharacter G) :
      (χ : ClassFunction G ℂ) Cs.out⁻¹ = (χ : ClassFunction G ℂ) x⁻¹ := by
    refine ClassFunction.of_isConj (χ : ClassFunction G ℂ) ?_
    have h1 : IsConj Cs.out x := ConjClasses.mk_eq_mk_iff_isConj.mp
      (by rw [conjClass_mk_out Cs, hCs])
    obtain ⟨c, hc⟩ := isConj_iff.mp h1
    exact isConj_iff.mpr ⟨c, by rw [← hc]; group⟩
  have hterm (χ : IrreducibleCharacter G) :
      ((A : ℂ) * (χ : ClassFunction G ℂ) Ct.out *
            ((A : ℂ) * (χ : ClassFunction G ℂ) Ct.out)) /
          (χ : ClassFunction G ℂ) 1 * (χ : ClassFunction G ℂ) Cs.out⁻¹
        = (A : ℂ) ^ 2 * (((χ : ClassFunction G ℂ) t) ^ 2 * (χ : ClassFunction G ℂ) x⁻¹ /
            (χ : ClassFunction G ℂ) 1) := by
    rw [hχt χ, hχx χ]
    ring
  -- ### passing from `χ(x⁻¹)` to `χ(x)` in the sum
  have hT : (∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) t) ^ 2 * (χ : ClassFunction G ℂ) x⁻¹ /
          (χ : ClassFunction G ℂ) 1) = S := by
    rw [hS]
    exact (sum_char_div_eq_sum_char_inv ht2).symm
  have hsum : (∑ χ : IrreducibleCharacter G,
          ((A : ℂ) * (χ : ClassFunction G ℂ) Ct.out *
              ((A : ℂ) * (χ : ClassFunction G ℂ) Ct.out)) /
            (χ : ClassFunction G ℂ) 1 * (χ : ClassFunction G ℂ) Cs.out⁻¹)
      = (A : ℂ) ^ 2 * S := by
    rw [Finset.sum_congr rfl (fun χ _ => hterm χ), ← Finset.mul_sum, hT]
  -- ### orbit-stabilizer
  have h1B : Nat.card { y : G // ConjClasses.mk y = Cs }
      = (Subgroup.centralizer ({Cs.out} : Set G)).index := by
    have h := card_class_eq_index_centralizer (G := G) Cs.out
    rwa [conjClass_mk_out Cs] at h
  have hBZnat : B * Zx = Nat.card G := by
    rw [hB, hZx, h1B]
    exact Subgroup.index_mul_card _
  have h1A : Nat.card { y : G // ConjClasses.mk y = Ct }
      = (Subgroup.centralizer ({t} : Set G)).index := by
    have h := card_class_eq_index_centralizer (G := G) t
    rwa [← hCt] at h
  have hAZnat : A * Z = Nat.card G := by
    rw [hA, hZ, h1A]
    exact Subgroup.index_mul_card _
  have hBZ : (B : ℂ) * (Zx : ℂ) = (Nat.card G : ℂ) := by
    rw [← Nat.cast_mul, hBZnat]
  have hAZc : (A : ℂ) * (Z : ℂ) = (Nat.card G : ℂ) := by
    rw [← Nat.cast_mul, hAZnat]
  have hNgc : (Nat.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne'
  have hAc : (A : ℂ) ≠ 0 := fun h => hNgc (by rw [← hAZc, h, zero_mul])
  have hZc : (Z : ℂ) ≠ 0 := fun h => hNgc (by rw [← hAZc, h, mul_zero])
  -- ### the key numeric identity
  have hkey : (Work.BSW.invPairCount G x : ℂ) * (Nat.card G : ℂ) = (A : ℂ) ^ 2 * S := by
    calc (Work.BSW.invPairCount G x : ℂ) * (Nat.card G : ℂ)
        = (Work.BSW.invPairCount G x : ℂ) * ((B : ℂ) * (Zx : ℂ)) := by rw [hBZ]
      _ = (classSum Ct * classSum Ct : ℂ[G]).coeff x * (B : ℂ) * (Zx : ℂ) := by
            rw [hpairs]; ring
      _ = (A : ℂ) ^ 2 * S := by rw [hmain, hsum]
  have hfinal : (Work.BSW.invPairCount G x : ℂ) * (Z : ℂ) ^ 2
      = (Nat.card G : ℂ) * S := by
    refine mul_left_cancel₀ hAc ?_
    calc (A : ℂ) * ((Work.BSW.invPairCount G x : ℂ) * (Z : ℂ) ^ 2)
        = (Work.BSW.invPairCount G x : ℂ) * ((A : ℂ) * (Z : ℂ)) * (Z : ℂ) := by ring
      _ = (Work.BSW.invPairCount G x : ℂ) * (Nat.card G : ℂ) * (Z : ℂ) := by rw [hAZc]
      _ = (A : ℂ) ^ 2 * S * (Z : ℂ) := by rw [hkey]
      _ = (A : ℂ) * ((Nat.card G : ℂ) * S) := by rw [← hAZc]; ring
  rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hZc)]
  exact hfinal

end Work.BSW.Char
