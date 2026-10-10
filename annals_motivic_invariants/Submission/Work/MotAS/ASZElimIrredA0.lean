/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotAS
-/
import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.ASZElimSigmaIrr
import Submission.Work.MotAS.P_homog
import Submission.Work.MotAS.MvPolyAffineIrred
import Submission.Work.MotAS.MvPolyAffineNotAssociated
import Submission.Work.TorsorExistence.ArtinSchreier.Irreducible
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASZElimIrredA0`

The `a = 0` case of the irreducibility of the eliminant `P a b g` of the residual chart of the
characteristic-`5` Crauder–Katz link: for `K` of characteristic `5`, `b ≠ 0` and `g ∉ ℘(K)`,
`P 0 b g` is irreducible over `K`.

`P` is homogeneous of degree `5` in `(a,b)`, so `P 0 b g = b^5 * P 0 1 g`; over the
Artin–Schreier root field `L = K[θ]/(θ^5 - θ - g)` the latter is the norm of a linear form, hence
factors into the five conjugates of that form under `θ ↦ θ + 1`, and the Galois-orbit argument
(`ASZElimSigmaIrr`) gives irreducibility over `K`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Work.MotAS

open MvPolynomial

section RingData
variable {K : Type*} [Field K]

/-- `c X 0^a X 1^b X 2^d X 3^e`, a monomial helper for the (large) correction polynomial. -/
noncomputable def ASZmz (c : ℤ) (a b d e : ℕ) : MvPolynomial (Fin 4) K :=
  (c : MvPolynomial (Fin 4) K) * X 0 ^ a * X 1 ^ b * X 2 ^ d * X 3 ^ e

/-- The `n`-th of the five factors of the norm identity, with `X 3` playing the role of `g`. -/
noncomputable def ASZfac (n : ℕ) : MvPolynomial (Fin 4) K :=
  X 3 * X 0 + 2 * X 3 * (X 2 + (n : MvPolynomial (Fin 4) K)) * X 1
    + 4 * ((X 2 + (n : MvPolynomial (Fin 4) K)) ^ 3 + (X 2 + (n : MvPolynomial (Fin 4) K)))

/-- `P 0 1 (X 3)`. -/
noncomputable def ASZPhat : MvPolynomial (Fin 4) K :=
    ASZmz 2 5 0 0 2 + ASZmz 1 3 1 0 1 + ASZmz 2 3 0 0 0 - ASZmz 1 2 0 0 0
    - ASZmz 2 1 4 0 2 - ASZmz 1 1 3 0 1 - ASZmz 2 1 2 0 0 - ASZmz 1 0 5 0 3
    - ASZmz 2 0 3 0 1 - ASZmz 2 0 2 0 0 - ASZmz 2 0 0 0 0

/-- The quotient of the division of the norm identity by `X 2 ^ 5 - X 2 - X 3`, reduced mod `5`. -/
noncomputable def ASZQhat : MvPolynomial (Fin 4) K :=
    ASZmz 3 0 0 10 2 + ASZmz 4 0 0 6 2 + ASZmz 3 0 0 5 3 + ASZmz 3 0 0 2 2
    + ASZmz 2 0 0 1 3 + ASZmz 4 2 0 0 4 + ASZmz 4 0 5 0 7 + ASZmz 3 0 3 0 5
    + ASZmz 3 0 2 0 4 + ASZmz 3 0 0 0 4

/-- The `5`-correction: the remainder of the division, divided by `5`. -/
noncomputable def ASZShat : MvPolynomial (Fin 4) K :=
    ASZmz 409 0 0 15 2 + ASZmz 12288 0 0 14 2 + ASZmz 1024 0 1 13 3 + ASZmz 167936 0 0 13 2
    + ASZmz 512 1 0 12 3 + ASZmz 26624 0 1 12 3 + ASZmz 1384448 0 0 12 2 + ASZmz 12288 1 0 11 3
    + ASZmz 1024 0 2 11 4 + ASZmz 314368 0 1 11 3 + ASZmz 7689011 0 0 11 2 + ASZmz 1024 1 1 10 4
    + ASZmz 135680 1 0 10 3 + ASZmz 22528 0 2 10 4 + ASZmz 2230272 0 1 10 3 + ASZmz 30457856 0 0 10 2
    + ASZmz 256 2 0 9 4 + ASZmz 20480 1 1 9 4 + ASZmz 911360 1 0 9 3 + ASZmz 512 0 3 9 5
    + ASZmz 223232 0 2 9 4 + ASZmz 10605568 0 1 9 3 + ASZmz 88977408 0 0 9 2 + ASZmz 4608 2 0 8 4
    + ASZmz 768 1 2 8 5 + ASZmz 187392 1 1 8 4 + ASZmz 4154880 1 0 8 3 + ASZmz 9216 0 3 8 5
    + ASZmz 1314816 0 2 8 4 + ASZmz 35727360 0 1 8 3 + ASZmz 195846144 0 0 8 2 + ASZmz 384 2 1 7 5
    + ASZmz 38784 2 0 7 4 + ASZmz 12288 1 2 7 5 + ASZmz 1032192 1 1 7 4 + ASZmz 13590528 1 0 7 3
    + ASZmz 128 0 4 7 6 + ASZmz 73216 0 3 7 5 + ASZmz 5113344 0 2 7 4 + ASZmz 87897088 0 1 7 3
    + ASZmz 329770189 0 0 7 2 + ASZmz 64 3 0 6 5 + ASZmz 5376 2 1 6 5 + ASZmz 198912 2 0 6 4
    + ASZmz 256 1 3 6 6 + ASZmz 88320 1 2 6 5 + ASZmz 3793920 1 1 6 4 + ASZmz 32867840 1 0 6 3
    + ASZmz 1792 0 4 6 6 + ASZmz 336896 0 3 6 5 + ASZmz 13784064 0 2 6 4 + ASZmz 160421888 0 1 6 3
    + ASZmz 1 0 0 6 3 + ASZmz 429871104 0 0 6 2 + ASZmz 768 3 0 5 5 + ASZmz 192 2 2 5 6
    + ASZmz 34752 2 1 5 5 + ASZmz 685516 2 0 5 4 + ASZmz 3072 1 3 5 6 + ASZmz 371712 1 2 5 5
    + ASZmz 9744384 1 1 5 4 + ASZmz 59590656 1 0 5 3 + ASZmz 12 0 5 5 7 + ASZmz 10496 0 4 5 6
    + ASZmz 985241 0 3 5 5 + ASZmz 26247577 0 2 5 4 + ASZmz 218023936 0 1 5 3 + ASZmz 437272576 0 0 5 2
    + ASZmz 64 3 1 4 6 + ASZmz 4448 3 0 4 5 + ASZmz 1920 2 2 4 6 + ASZmz 132480 2 1 4 5
    + ASZmz 1651200 2 0 4 4 + ASZmz 32 1 4 4 7 + ASZmz 15616 1 3 4 6 + ASZmz 997248 1 2 4 5
    + ASZmz 17741824 1 1 4 4 + ASZmz 80918528 1 0 4 3 + ASZmz 128 0 5 4 7 + ASZmz 33280 0 4 4 6
    + ASZmz 1881600 0 3 4 5 + ASZmz 35123200 0 2 4 4 + ASZmz 218238976 0 1 4 3 + ASZmz 345899008 0 0 4 2
    + ASZmz 8 4 0 3 6 + ASZmz 512 3 1 3 6 + ASZmz 15104 3 0 3 5 + ASZmz 32 2 3 3 7
    + ASZmz 8352 2 2 3 6 + ASZmz 319680 2 1 3 5 + ASZmz 2788480 2 0 3 4 + ASZmz 256 1 4 3 7
    + ASZmz 43008 1 3 3 6 + ASZmz 1735680 1 2 3 5 + ASZmz 22593536 1 1 3 4 + ASZmz 80625664 1 0 3 3
    + ASZmz 448 0 5 3 7 + ASZmz 60032 0 4 3 6 + ASZmz 2295040 0 3 3 5 + ASZmz 31835648 0 2 3 4
    + ASZmz 154968064 0 1 3 3 + ASZmz 205669991 0 0 3 2 + ASZmz 48 4 0 2 6 + ASZmz 16 3 2 2 7
    + ASZmz 1888 3 1 2 6 + ASZmz 31840 3 0 2 5 + ASZmz 192 2 3 2 7 + ASZmz 19392 2 2 2 6
    + ASZmz 486528 2 1 2 5 + ASZmz 3189504 2 0 2 4 + ASZmz 672 1 4 2 7 + ASZmz 64896 1 3 2 6
    + ASZmz 1875072 1 2 2 5 + ASZmz 19061760 1 1 2 4 + ASZmz 55756800 1 0 2 3 + ASZmz 640 0 5 2 7
    + ASZmz 57088 0 4 2 6 + ASZmz 1621504 0 3 2 5 + ASZmz 17671168 0 2 2 4 + ASZmz 70696960 0 1 2 3
    + ASZmz 1 0 0 2 3 + ASZmz 82788352 0 0 2 2 + ASZmz 4 4 1 1 7 + ASZmz 152 4 0 1 6
    + ASZmz 64 3 2 1 7 + ASZmz 3456 3 1 1 6 + ASZmz 39296 3 0 1 5 + ASZmz 336 2 3 1 7
    + ASZmz 22176 2 2 1 6 + ASZmz 419328 2 1 1 5 + ASZmz 2212148 2 0 1 4 + ASZmz 640 1 4 1 7
    + ASZmz 46592 1 3 1 6 + ASZmz 1085952 1 2 1 5 + ASZmz 9269248 1 1 1 4 + ASZmz 23404544 1 0 1 3
    + ASZmz 308 0 5 1 7 + ASZmz 21504 0 4 1 6 + ASZmz 495207 0 3 1 5 + ASZmz 4494951 0 2 1 4
    + ASZmz 15532032 0 1 1 3 + ASZmz 1 0 0 1 4 + ASZmz 16711680 0 0 1 2 + ASZmz 8 4 1 0 7
    + ASZmz 176 4 0 0 6 + ASZmz 56 3 2 0 7 + ASZmz 2291 3 1 0 6 + ASZmz 20710 3 0 0 5
    + ASZmz 160 2 3 0 7 + ASZmz 9024 2 2 0 6 + ASZmz 147456 2 1 0 5 + ASZmz 1 2 0 0 5
    + ASZmz 676864 2 0 0 4 + ASZmz 154 1 4 0 7 + ASZmz 10445 1 3 0 6 + ASZmz 226714 1 2 0 5
    + ASZmz 1794048 1 1 0 4 + ASZmz 4177920 1 0 0 3 + ASZmz 1 0 5 0 8 + ASZmz 1 0 3 0 6
    + ASZmz 1 0 2 0 5 + ASZmz 1 0 0 0 5

/-- **The norm identity**, over `ℤ` (hence in every commutative ring): the product of the five
`X 3`-scaled linear factors, minus `X 3 ^ 5 * P 0 1 (X 3)`, equals `(X 2 ^ 5 - X 2 - X 3) * Q` plus
the explicit `5`-correction `5 * ASZShat`. -/
theorem ASZkey :
    (2 : MvPolynomial (Fin 4) K) * X 3 ^ 2 *
        (ASZfac 0 * ASZfac 1 * ASZfac 2 * ASZfac 3 * ASZfac 4)
      - X 3 ^ 5 * ASZPhat
      = (X 2 ^ 5 - X 2 - X 3) * ASZQhat + 5 * ASZShat := by
  simp only [ASZfac, ASZPhat, ASZQhat, ASZShat, ASZmz]
  first | refl_ring1 | ring

end RingData

section Helpers
variable {K : Type*} [Field K]

/-- `C (2 : K) = 2` in `K[X 0, X 1]`. -/
theorem ASZC2 : (C (2 : K) : MvPolynomial (Fin 2) K) = 2 := by
  rw [show (2 : K) = 1 + 1 by norm_num, MvPolynomial.C_add, MvPolynomial.C_1]
  norm_num

/-- `C (2 x ^ 2) = 2 C x ^ 2`. -/
theorem ASZC2sq (x : K) : (C (2 * x ^ 2) : MvPolynomial (Fin 2) K) = 2 * C x ^ 2 := by
  rw [MvPolynomial.C_mul, MvPolynomial.C_pow, ASZC2]

/-- **`P 0 1 g` in explicit form.** -/
theorem ASZP01 (g : K) :
    ASZElim.P 0 1 g = 2 * C g ^ 2 * X 0 ^ 5 + C g * X 0 ^ 3 * X 1 + 2 * X 0 ^ 3 - X 0 ^ 2
      - 2 * C g ^ 2 * X 0 * X 1 ^ 4 - C g * X 0 * X 1 ^ 3 - 2 * X 0 * X 1 ^ 2
      - C g ^ 3 * X 1 ^ 5 - 2 * C g * X 1 ^ 3 - 2 * X 1 ^ 2 - 2 := by
  simp only [ASZElim.P]
  simp only [MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_add, MvPolynomial.C_neg,
    MvPolynomial.C_0, MvPolynomial.C_1, ASZC2]
  refl_ring1

end Helpers

section Prod

/-- The product over `ZMod 5` expanded in the order `0,1,2,3,4`. -/
theorem prod_univ_zmod_five {M : Type*} [CommMonoid M] (f : ZMod 5 → M) :
    ∏ i : ZMod 5, f i = f 0 * (f 1 * (f 2 * (f 3 * f 4))) := by
  have h : (Finset.univ : Finset (ZMod 5)) = ({0, 1, 2, 3, 4} : Finset (ZMod 5)) := by decide
  rw [h]
  rw [Finset.prod_insert (by decide : (0 : ZMod 5) ∉ ({1, 2, 3, 4} : Finset (ZMod 5)))]
  rw [Finset.prod_insert (by decide : (1 : ZMod 5) ∉ ({2, 3, 4} : Finset (ZMod 5)))]
  rw [Finset.prod_insert (by decide : (2 : ZMod 5) ∉ ({3, 4} : Finset (ZMod 5)))]
  rw [Finset.prod_insert (by decide : (3 : ZMod 5) ∉ ({4} : Finset (ZMod 5)))]
  rw [Finset.prod_singleton]

end Prod

section ASZRoot

variable {K : Type*} [Field K]

/-- The Artin–Schreier polynomial `X ^ 5 - X - g`. -/
noncomputable def ASZF (g : K) : Polynomial K :=
  Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g

/-- `C (n : K) = n` in `K[X 0, X 1]`. -/
theorem ASZCnat (n : ℕ) :
    (C (n : K) : MvPolynomial (Fin 2) K) = (n : MvPolynomial (Fin 2) K) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, Nat.cast_succ, MvPolynomial.C_add, MvPolynomial.C_1, ih]

end ASZRoot

section Aux

variable {K : Type} [Field K] [CharP K 5]

/-- **The Artin–Schreier automorphism** `θ ↦ θ + 1` of `K[θ]/(θ^5 - θ - g)`, for the
literal polynomial `X ^ 5 - X - g`. -/
private theorem ASZadjoinAutLit (g : K) :
    ∃ σ : AdjoinRoot (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial K) ≃ₐ[K]
        AdjoinRoot (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial K),
      σ (AdjoinRoot.root _) = AdjoinRoot.root _ + 1 := by
  set F : Polynomial K := Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g with hF
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hroot : Polynomial.aeval (AdjoinRoot.root F) F = 0 := by
    have h := AdjoinRoot.aeval_eq (f := F) F
    rw [AdjoinRoot.mk_self] at h
    exact h
  have ht1 : F.comp ((Polynomial.X : Polynomial K) + 1) = F := by
    rw [hF]
    simp only [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.add_comp,
      Polynomial.C_comp]
    have hp : ((Polynomial.X : Polynomial K) + 1) ^ 5 = Polynomial.X ^ 5 + 1 := by
      rw [add_pow_char (Polynomial.X : Polynomial K) 1 5]
      norm_num
    rw [hp]
    refl_ring1
  have htm1 : F.comp ((Polynomial.X : Polynomial K) - 1) = F := by
    rw [hF]
    simp only [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.C_comp]
    have hp : ((Polynomial.X : Polynomial K) - 1) ^ 5 = Polynomial.X ^ 5 - 1 := by
      rw [sub_pow_char (Polynomial.X : Polynomial K) 1]
      norm_num
    rw [hp]
    refl_ring1
  have hroot1 : Polynomial.aeval (AdjoinRoot.root F + 1) F = 0 := by
    have hx : Polynomial.aeval (AdjoinRoot.root F + 1) F
        = Polynomial.aeval ((Polynomial.aeval (AdjoinRoot.root F))
            ((Polynomial.X : Polynomial K) + 1)) F := by
      rw [show (Polynomial.aeval (AdjoinRoot.root F)) ((Polynomial.X : Polynomial K) + 1)
        = AdjoinRoot.root F + 1 from by simp]
    rw [hx, ← Polynomial.aeval_comp (p := F) (q := (Polynomial.X : Polynomial K) + 1)
      (AdjoinRoot.root F), ht1, hroot]
  have hrootm1 : Polynomial.aeval (AdjoinRoot.root F - 1) F = 0 := by
    have hx : Polynomial.aeval (AdjoinRoot.root F - 1) F
        = Polynomial.aeval ((Polynomial.aeval (AdjoinRoot.root F))
            ((Polynomial.X : Polynomial K) - 1)) F := by
      rw [show (Polynomial.aeval (AdjoinRoot.root F)) ((Polynomial.X : Polynomial K) - 1)
        = AdjoinRoot.root F - 1 from by simp]
    rw [hx, ← Polynomial.aeval_comp (p := F) (q := (Polynomial.X : Polynomial K) - 1)
      (AdjoinRoot.root F), htm1, hroot]
  let φ : AdjoinRoot F →ₐ[K] AdjoinRoot F :=
    AdjoinRoot.liftAlgHom F (Algebra.ofId K (AdjoinRoot F)) (AdjoinRoot.root F + 1) hroot1
  let ψ : AdjoinRoot F →ₐ[K] AdjoinRoot F :=
    AdjoinRoot.liftAlgHom F (Algebra.ofId K (AdjoinRoot F)) (AdjoinRoot.root F - 1) hrootm1
  have hφ : φ (AdjoinRoot.root F) = AdjoinRoot.root F + 1 :=
    AdjoinRoot.liftAlgHom_root F _ _ hroot1
  have hψ : ψ (AdjoinRoot.root F) = AdjoinRoot.root F - 1 :=
    AdjoinRoot.liftAlgHom_root F _ _ hrootm1
  refine ⟨AlgEquiv.ofAlgHom φ ψ ?_ ?_, ?_⟩
  · apply AdjoinRoot.algHom_ext
    show φ (ψ (AdjoinRoot.root F)) = AdjoinRoot.root F
    rw [hψ, map_sub, map_one, hφ]
    refl_ring1
  · apply AdjoinRoot.algHom_ext
    show ψ (φ (AdjoinRoot.root F)) = AdjoinRoot.root F
    rw [hφ, map_add, map_one, hψ]
    refl_ring1
  · rw [AlgEquiv.ofAlgHom_apply]
    exact hφ

/-- **The Artin–Schreier automorphism** `θ ↦ θ + 1` of `K[θ]/(θ^5 - θ - g)`. -/
theorem ASZadjoinAut (g : K) :
    ∃ σ : AdjoinRoot (ASZF g) ≃ₐ[K] AdjoinRoot (ASZF g),
      σ (AdjoinRoot.root (ASZF g)) = AdjoinRoot.root (ASZF g) + 1 :=
  ASZadjoinAutLit g

/-- **The defining relation of the Artin–Schreier root** in `K[θ]/(X^5 - X - g)`. -/
private theorem ASZrootRel (K : Type) [Field K] [CharP K 5] (g : K) :
    (AdjoinRoot.root (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial K)) ^ 5
        - AdjoinRoot.root (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial K)
        - algebraMap K
            (AdjoinRoot (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial K)) g = 0 := by
  have h := AdjoinRoot.aeval_eq
    (f := (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial K))
    (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial K)
  rw [AdjoinRoot.mk_self] at h
  rw [map_sub, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h
  exact h

end Aux

section Main

theorem ASZElimIrredA0 (K : Type) [Field K] [CharP K 5] (b g : K)
    (hb : b ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    Irreducible (Work.MotAS.ASZElim.P 0 b g) := by
  classical
  have hg0 : g ≠ 0 := by rintro rfl; exact hg ⟨0, by norm_num⟩
  -- ## the Artin–Schreier root field `K[θ]/(θ^5 - θ - g)`
  have hFirr : Irreducible (ASZF g) := by
    rw [ASZF]
    exact Work.TorsorExistence.ArtinSchreier.irreducible_X_pow_five_sub_X_sub_C g hg
  haveI : Fact (Irreducible (ASZF g)) := ⟨hFirr⟩
  have halg : Function.Injective (algebraMap K (AdjoinRoot (ASZF g))) := by
    intro x y hxy
    have h : algebraMap K (AdjoinRoot (ASZF g)) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hz : x - y = 0 := by
      by_contra hne
      have hu : IsUnit (x - y) := isUnit_iff_ne_zero.mpr hne
      have hu2 : IsUnit (algebraMap K (AdjoinRoot (ASZF g)) (x - y)) := hu.map _
      rw [h] at hu2
      exact not_isUnit_zero hu2
    exact sub_eq_zero.mp hz
  haveI : CharP (AdjoinRoot (ASZF g)) 5 := charP_of_injective_algebraMap halg 5
  have hgg : (algebraMap K (AdjoinRoot (ASZF g)) g) ≠ 0 := by
    intro h
    exact hg0 (halg (by rw [h, map_zero]))
  let θ : AdjoinRoot (ASZF g) := AdjoinRoot.root (ASZF g)
  have hθ : θ ^ 5 - θ - algebraMap K (AdjoinRoot (ASZF g)) g = 0 := ASZrootRel K g
  obtain ⟨σ, hσθ⟩ := ASZadjoinAut (K := K) g
  -- ## the family of the five conjugate factors
  let χ : ZMod 5 →+* K := ZMod.castHom (dvd_refl 5) K
  have hχval : ∀ i : ZMod 5, χ i = (i.val : K) := by
    intro i
    rw [show χ i = ZMod.cast i from ZMod.castHom_apply (h := dvd_refl 5) i, ZMod.cast_eq_val]
  have hχinj : Function.Injective χ := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    intro i j hij
    have h0 : χ (i - j) = 0 := by rw [map_sub, hij, sub_self]
    by_contra hne
    have hu : IsUnit (i - j) := isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)
    have hu2 : IsUnit (χ (i - j)) := hu.map χ
    rw [h0] at hu2
    exact not_isUnit_zero hu2
  let Gfam : ZMod 5 → MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)) := fun i =>
    X 0 + C (2 * (θ + algebraMap K (AdjoinRoot (ASZF g)) (χ i))) * X 1
      + C (4 * (algebraMap K (AdjoinRoot (ASZF g)) g)⁻¹ *
          ((θ + algebraMap K (AdjoinRoot (ASZF g)) (χ i)) ^ 3
            + (θ + algebraMap K (AdjoinRoot (ASZF g)) (χ i))))
  have hirr : ∀ i, Irreducible (Gfam i) := by
    intro i
    simpa only [Gfam] using
      MvPolyAffineIrred (AdjoinRoot (ASZF g)) (2 * (θ + algebraMap K (AdjoinRoot (ASZF g)) (χ i)))
        (4 * (algebraMap K (AdjoinRoot (ASZF g)) g)⁻¹ *
          ((θ + algebraMap K (AdjoinRoot (ASZF g)) (χ i)) ^ 3
            + (θ + algebraMap K (AdjoinRoot (ASZF g)) (χ i))))
  have h1 : (σ : AdjoinRoot (ASZF g) →+* AdjoinRoot (ASZF g)) θ = θ + 1 := hσθ
  have h2all : ∀ x : K, (σ : AdjoinRoot (ASZF g) →+* AdjoinRoot (ASZF g))
      (algebraMap K (AdjoinRoot (ASZF g)) x) = algebraMap K (AdjoinRoot (ASZF g)) x :=
    fun x => σ.commutes x
  have hconj : ∀ i, MvPolynomial.map (σ : AdjoinRoot (ASZF g) →+* AdjoinRoot (ASZF g)) (Gfam i)
      = Gfam (i + 1) := by
    intro i
    simp only [Gfam, map_add, map_mul, map_pow, map_inv₀, map_ofNat, map_one,
      MvPolynomial.map_C, MvPolynomial.map_X, h1, h2all]
    refl_ring1
  have hne : ∀ i j, i ≠ j → ¬ Associated (Gfam i) (Gfam j) := by
    intro i j hij
    have h2 : (2 : AdjoinRoot (ASZF g)) ≠ 0 := by
      intro hz
      have hz' : ((2 : ℕ) : AdjoinRoot (ASZF g)) = 0 := by
        rw [Nat.cast_ofNat]; exact hz
      rw [CharP.cast_eq_zero_iff (AdjoinRoot (ASZF g)) 5] at hz'
      norm_num at hz'
    have hslope : 2 * (θ + algebraMap K (AdjoinRoot (ASZF g)) (χ i))
        ≠ 2 * (θ + algebraMap K (AdjoinRoot (ASZF g)) (χ j)) := by
      intro heq
      have h3 : θ + algebraMap K (AdjoinRoot (ASZF g)) (χ i)
          = θ + algebraMap K (AdjoinRoot (ASZF g)) (χ j) := mul_left_cancel₀ h2 heq
      have h4 : algebraMap K (AdjoinRoot (ASZF g)) (χ i)
          = algebraMap K (AdjoinRoot (ASZF g)) (χ j) := add_left_cancel h3
      exact hij (hχinj (halg h4))
    simpa only [Gfam] using
      MvPolyAffineNotAssociated (AdjoinRoot (ASZF g)) (2 * (θ + algebraMap K (AdjoinRoot (ASZF g)) (χ i)))
        (4 * (algebraMap K (AdjoinRoot (ASZF g)) g)⁻¹ *
          ((θ + algebraMap K (AdjoinRoot (ASZF g)) (χ i)) ^ 3
            + (θ + algebraMap K (AdjoinRoot (ASZF g)) (χ i))))
        (2 * (θ + algebraMap K (AdjoinRoot (ASZF g)) (χ j)))
        (4 * (algebraMap K (AdjoinRoot (ASZF g)) g)⁻¹ *
          ((θ + algebraMap K (AdjoinRoot (ASZF g)) (χ j)) ^ 3
            + (θ + algebraMap K (AdjoinRoot (ASZF g)) (χ j))))
        hslope
  -- ## the norm identity, transported to `θ`
  let psim : Fin 4 → MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)) :=
    Fin.cases (X 0)
      (Fin.cases (X 1) (Fin.cases (C θ) (fun _ => C (algebraMap K (AdjoinRoot (ASZF g)) g))))
  let ψ : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)) :=
    MvPolynomial.aeval psim
  have hψ0 : ψ (X 0) = X 0 := by
    rw [show ψ (X 0) = psim 0 from MvPolynomial.aeval_X psim 0]; rfl
  have hψ1 : ψ (X 1) = X 1 := by
    rw [show ψ (X 1) = psim 1 from MvPolynomial.aeval_X psim 1]; rfl
  have hψ2 : ψ (X 2) = C θ := by
    rw [show ψ (X 2) = psim 2 from MvPolynomial.aeval_X psim 2]; rfl
  have hψ3 : ψ (X 3) = C (algebraMap K (AdjoinRoot (ASZF g)) g) := by
    rw [show ψ (X 3) = psim 3 from MvPolynomial.aeval_X psim 3]; rfl
  have hkey' : 2 * (C (algebraMap K (AdjoinRoot (ASZF g)) g)) ^ 2 *
        (ψ (ASZfac 0) * ψ (ASZfac 1) * ψ (ASZfac 2) * ψ (ASZfac 3) * ψ (ASZfac 4))
      = (C (algebraMap K (AdjoinRoot (ASZF g)) g)) ^ 5 * ψ ASZPhat := by
    have hL : ψ (2 * X 3 ^ 2 *
          (ASZfac 0 * ASZfac 1 * ASZfac 2 * ASZfac 3 * ASZfac 4) - X 3 ^ 5 * ASZPhat)
        = 2 * (C (algebraMap K (AdjoinRoot (ASZF g)) g)) ^ 2 *
            (ψ (ASZfac 0) * ψ (ASZfac 1) * ψ (ASZfac 2) * ψ (ASZfac 3) * ψ (ASZfac 4))
          - (C (algebraMap K (AdjoinRoot (ASZF g)) g)) ^ 5 * ψ ASZPhat := by
      simp only [map_sub, map_mul, map_pow, map_ofNat, hψ3]
    have hR : ψ ((X 2 ^ 5 - X 2 - X 3) * ASZQhat + 5 * ASZShat) = 0 := by
      simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, hψ2, hψ3]
      have hθ0 : (C θ : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g))) ^ 5 - C θ
          - C (algebraMap K (AdjoinRoot (ASZF g)) g) = 0 := by
        rw [← MvPolynomial.C_pow, ← MvPolynomial.C_sub, ← MvPolynomial.C_sub, hθ,
          MvPolynomial.C_0]
      rw [hθ0, zero_mul, zero_add,
        show (5 : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g))) = 0 from CharP.cast_eq_zero _ 5,
        zero_mul]
    have h := congrArg ψ (ASZkey (K := K))
    rw [hL, hR] at h
    linear_combination (norm := refl_ring1) h
  have hψP : ψ ASZPhat
      = MvPolynomial.map (algebraMap K (AdjoinRoot (ASZF g))) (ASZElim.P 0 1 g) := by
    rw [ASZP01 g]
    simp only [ASZPhat, ASZmz, map_add, map_sub, map_mul, map_pow, map_intCast, map_ofNat,
      MvPolynomial.map_C, MvPolynomial.map_X, hψ0, hψ1, hψ2, hψ3]
    first | refl_ring1 | ring
  have hχn : ∀ n : ℕ, n < 5 →
      algebraMap K (AdjoinRoot (ASZF g)) (χ (n : ZMod 5)) = (n : AdjoinRoot (ASZF g)) := by
    intro n hn
    rw [hχval, ZMod.val_cast_of_lt hn]
    exact map_natCast (algebraMap K (AdjoinRoot (ASZF g))) n
  have hψF : ∀ n : ℕ, n < 5 →
      ψ (ASZfac n) = C (algebraMap K (AdjoinRoot (ASZF g)) g) * Gfam (n : ZMod 5) := by
    intro n hn
    have hC2 : (C (2 : AdjoinRoot (ASZF g)) : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g))) = 2 :=
      ASZC2
    have hC4 : (C (4 : AdjoinRoot (ASZF g)) : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g))) = 4 :=
      ASZCnat 4
    have hχnn : algebraMap K (AdjoinRoot (ASZF g)) (χ (n : ZMod 5))
        = (n : AdjoinRoot (ASZF g)) := hχn n hn
    have hgg1 : (C (algebraMap K (AdjoinRoot (ASZF g)) g) *
        C (algebraMap K (AdjoinRoot (ASZF g)) g)⁻¹ : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g))) = 1 := by
      rw [← MvPolynomial.C_mul, mul_inv_cancel₀ hgg, MvPolynomial.C_1]
    have e1 : ψ (X 3 * X 0) = C (algebraMap K (AdjoinRoot (ASZF g)) g) * X 0 := by
      simp only [map_mul, hψ0, hψ3]
    have e2 : ψ (2 * X 3 * (X 2 + (n : MvPolynomial (Fin 4) K)) * X 1)
        = C (algebraMap K (AdjoinRoot (ASZF g)) g) *
            (2 * (C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)))) * X 1) := by
      simp only [map_mul, map_ofNat, map_add, map_natCast, map_one, hψ0, hψ1, hψ2, hψ3]
      refl_ring1
    have e3 : ψ (4 * ((X 2 + (n : MvPolynomial (Fin 4) K)) ^ 3
            + (X 2 + (n : MvPolynomial (Fin 4) K))))
        = 4 * ((C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)))) ^ 3
            + (C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g))))) := by
      simp only [map_mul, map_add, map_pow, map_ofNat, map_natCast, map_one, hψ2, hψ3]
    have hexp : Gfam (n : ZMod 5) = X 0 + C (2 * (θ + (n : AdjoinRoot (ASZF g)))) * X 1
        + C (4 * (algebraMap K (AdjoinRoot (ASZF g)) g)⁻¹ *
            ((θ + (n : AdjoinRoot (ASZF g))) ^ 3 + (θ + (n : AdjoinRoot (ASZF g))))) := by
      simp only [Gfam, hχnn]
    have hA : (C (2 * (θ + (n : AdjoinRoot (ASZF g)))) :
          MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)))
        = 2 * (C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)))) := by
      simp only [MvPolynomial.C_mul, MvPolynomial.C_add, hC2, ASZCnat n]
    have hB : (C (4 * (algebraMap K (AdjoinRoot (ASZF g)) g)⁻¹ *
          ((θ + (n : AdjoinRoot (ASZF g))) ^ 3 + (θ + (n : AdjoinRoot (ASZF g))))) :
          MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)))
        = 4 * C (algebraMap K (AdjoinRoot (ASZF g)) g)⁻¹ *
            ((C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)))) ^ 3
              + (C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g))))) := by
      simp only [MvPolynomial.C_mul, MvPolynomial.C_add, MvPolynomial.C_pow, hC4, hC2, ASZCnat n]
    have h4 : ∀ S : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)),
        C (algebraMap K (AdjoinRoot (ASZF g)) g) *
            (4 * C (algebraMap K (AdjoinRoot (ASZF g)) g)⁻¹ * S) = 4 * S := by
      intro S
      rw [show C (algebraMap K (AdjoinRoot (ASZF g)) g) *
              (4 * C (algebraMap K (AdjoinRoot (ASZF g)) g)⁻¹ * S)
            = 4 * (C (algebraMap K (AdjoinRoot (ASZF g)) g) *
                C (algebraMap K (AdjoinRoot (ASZF g)) g)⁻¹) * S from by ring, hgg1]
      refl_ring1
    have hdist : C (algebraMap K (AdjoinRoot (ASZF g)) g) *
          (X 0 + 2 * (C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)))) * X 1
            + 4 * C (algebraMap K (AdjoinRoot (ASZF g)) g)⁻¹ *
              ((C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)))) ^ 3
                + (C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g))))))
        = C (algebraMap K (AdjoinRoot (ASZF g)) g) * X 0
            + C (algebraMap K (AdjoinRoot (ASZF g)) g) *
              (2 * (C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)))) * X 1)
            + 4 * ((C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)))) ^ 3
                + (C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g))))) := by
      linear_combination (norm := refl_ring1) h4 ((C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)))) ^ 3
        + (C θ + (n : MvPolynomial (Fin 2) (AdjoinRoot (ASZF g)))))
    rw [show ASZfac n = X 3 * X 0 + 2 * X 3 * (X 2 + (n : MvPolynomial (Fin 4) K)) * X 1
        + 4 * ((X 2 + (n : MvPolynomial (Fin 4) K)) ^ 3
            + (X 2 + (n : MvPolynomial (Fin 4) K))) from rfl]
    rw [hexp, hA, hB, hdist, map_add, map_add, e1, e2, e3]
  have hprod : ψ (ASZfac 0) * ψ (ASZfac 1) * ψ (ASZfac 2) * ψ (ASZfac 3) * ψ (ASZfac 4)
      = (C (algebraMap K (AdjoinRoot (ASZF g)) g)) ^ 5 * ∏ i : ZMod 5, Gfam i := by
    rw [hψF 0 (by norm_num), hψF 1 (by norm_num), hψF 2 (by norm_num), hψF 3 (by norm_num),
      hψF 4 (by norm_num), prod_univ_zmod_five]
    refl_ring1
  have hmain : MvPolynomial.map (algebraMap K (AdjoinRoot (ASZF g))) (ASZElim.P 0 1 g)
      = 2 * (C (algebraMap K (AdjoinRoot (ASZF g)) g)) ^ 2 * ∏ i : ZMod 5, Gfam i := by
    have hcancel : (C (algebraMap K (AdjoinRoot (ASZF g)) g) :
        MvPolynomial (Fin 2) (AdjoinRoot (ASZF g))) ≠ 0 := by
      rw [Ne, MvPolynomial.C_eq_zero]; exact hgg
    have key : (C (algebraMap K (AdjoinRoot (ASZF g)) g)) ^ 5 *
          MvPolynomial.map (algebraMap K (AdjoinRoot (ASZF g))) (ASZElim.P 0 1 g)
        = (C (algebraMap K (AdjoinRoot (ASZF g)) g)) ^ 5 *
          (2 * (C (algebraMap K (AdjoinRoot (ASZF g)) g)) ^ 2 * ∏ i : ZMod 5, Gfam i) := by
      rw [← hψP]
      have hh := hkey'
      rw [hprod] at hh
      linear_combination (norm := refl_ring1) -1 * hh
    exact mul_left_cancel₀ (pow_ne_zero 5 hcancel) key
  -- ## the Galois-orbit argument over `K`
  have h2ne : (2 : AdjoinRoot (ASZF g)) ≠ 0 := by
    intro hz
    have hz' : ((2 : ℕ) : AdjoinRoot (ASZF g)) = 0 := by
      rw [Nat.cast_ofNat]; exact hz
    rw [CharP.cast_eq_zero_iff (AdjoinRoot (ASZF g)) 5] at hz'
    norm_num at hz'
  have hu : IsUnit (2 * (algebraMap K (AdjoinRoot (ASZF g)) g) ^ 2) := by
    refine isUnit_iff_ne_zero.mpr ?_
    exact mul_ne_zero h2ne (pow_ne_zero 2 hgg)
  have hfac : MvPolynomial.map (algebraMap K (AdjoinRoot (ASZF g))) (ASZElim.P 0 1 g)
      = MvPolynomial.C (2 * (algebraMap K (AdjoinRoot (ASZF g)) g) ^ 2) *
          ∏ i : ZMod 5, Gfam i := by
    rw [hmain, ASZC2sq]
  have h01 : Irreducible (ASZElim.P 0 1 g) :=
    ASZElimSigmaIrr K (AdjoinRoot (ASZF g)) σ (ASZElim.P 0 1 g)
      (2 * (algebraMap K (AdjoinRoot (ASZF g)) g) ^ 2) hu Gfam hirr hconj hfac hne
  -- ## reduce to `b = 1` by homogeneity
  have hPb : ASZElim.P 0 b g = MvPolynomial.C (b ^ 5) * ASZElim.P 0 1 g := by
    have h := P_homog K b 0 1 g
    simpa using h
  have hunit : IsUnit (MvPolynomial.C (b ^ 5) : MvPolynomial (Fin 2) K) := by
    refine MvPolynomial.isUnit_iff_eq_C_of_isReduced.mpr ⟨b ^ 5, ?_, rfl⟩
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero 5 hb)
  rw [hPb]
  exact (Associated.irreducible_iff (associated_unit_mul_left _ _ hunit)).mpr h01

end Main

end Work.MotAS
