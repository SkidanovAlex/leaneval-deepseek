import Mathlib
import Submission.Work.MotAS.ASZResidualChartDefs
import Submission.Work.MotAS.ASZChartSetup
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.AK
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotTDG.Setup
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASResDefs` — the vocabulary of the residual projection `asZOm`

Part of the subproject `Submission/Work/MotAS`, node **`Work.MotAS.ASResidualGen`**
(`Submission/Work/MotAS/ASResidualGen.lean`).

The residual coordinates of the AS Crauder–Katz link are the five elements

  `asZOm 𝕜 D g k = Σ_j phiAS (aK D) (bK D) k j · (asTwY D g j / asTwY D g 0)`

of `Om D = κ(E)` (`Submission/Work/MotAS/ASZResidualChartDefs.lean`).  Because `phiAS` is the
explicit `D⁻¹ p(T₁)` matrix, the first four of them are the *linear* forms

  `z₀ = A·v₁ + B·v₃`,  `z₁ = A·v₂ + C·v₄`,  `z₂ = D·v₃`,  `z₃ = E·v₄`,  `z₄ = 0`

in the projective twisted coordinates `v_j = asTwY D g j / asTwY D g 0`, where

  `A = 3a+b`, `B = 3a+4b`, `C = a+3b`, `D = a+2b`, `E = 4a+3b`.

This file provides

* the entry lemmas `phiAS_ij` for the (explicit) matrix `phiAS`;
* the constants `asZA, …, asZE`, `asZa, asZb, asZc`, `asZmu`, `asZlam`;
* the coordinates `asZv` (`= v`), `asZX` (`= z_{i+1}/z₀`), `asZw1 … asZw4`, `asZw`, i.e. the
  *inverse chart* of the projection:
  `w₃ = X₁/D`, `w₄ = X₂/E`, `w₁ = (1 - B·w₃)/A`, `w₂ = (X₀ - C·w₄)/A`, and `asZw 0 = 0`;
* the identities `asZOm k = …` above, the bridge lemmas `asZA_eq` etc. to the base field, and the
  nonvanishing `asZA, asZD, asZE, asZmu ≠ 0` under `ASGood`;
* the two decompositions of the twisted Pfaffians used by the inversion:
  `kleinPAS_k a b c y = y 0 * (linear part) + kleinPAS_k a b c ![0,y₁,y₂,y₃,y₄]` for `k = 1,3`;
* the characterstic-`5` power sum `Σ_{i<5} (w+i)² = 0`.

All of this is used by the node `ASResidualGen` and by the `asZRecovery`-style inversion lemma.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.MotAS

open Work.MotV

noncomputable section

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-! ## §1 The entries of `phiAS` -/

lemma phiAS_00 {R : Type*} [CommRing R] (a b : R) : phiAS a b 0 0 = 0 := by simp [phiAS]
lemma phiAS_01 {R : Type*} [CommRing R] (a b : R) : phiAS a b 0 1 = 3 * a + b := by simp [phiAS]
lemma phiAS_02 {R : Type*} [CommRing R] (a b : R) : phiAS a b 0 2 = 0 := by simp [phiAS]
lemma phiAS_03 {R : Type*} [CommRing R] (a b : R) : phiAS a b 0 3 = 3 * a + 4 * b := by simp [phiAS]
lemma phiAS_04 {R : Type*} [CommRing R] (a b : R) : phiAS a b 0 4 = 0 := by simp [phiAS]
lemma phiAS_10 {R : Type*} [CommRing R] (a b : R) : phiAS a b 1 0 = 0 := by simp [phiAS]
lemma phiAS_11 {R : Type*} [CommRing R] (a b : R) : phiAS a b 1 1 = 0 := by simp [phiAS]
lemma phiAS_12 {R : Type*} [CommRing R] (a b : R) : phiAS a b 1 2 = 3 * a + b := by simp [phiAS]
lemma phiAS_13 {R : Type*} [CommRing R] (a b : R) : phiAS a b 1 3 = 0 := by simp [phiAS]
lemma phiAS_14 {R : Type*} [CommRing R] (a b : R) : phiAS a b 1 4 = a + 3 * b := by simp [phiAS]
lemma phiAS_20 {R : Type*} [CommRing R] (a b : R) : phiAS a b 2 0 = 0 := by simp [phiAS]
lemma phiAS_21 {R : Type*} [CommRing R] (a b : R) : phiAS a b 2 1 = 0 := by simp [phiAS]
lemma phiAS_22 {R : Type*} [CommRing R] (a b : R) : phiAS a b 2 2 = 0 := by simp [phiAS]
lemma phiAS_23 {R : Type*} [CommRing R] (a b : R) : phiAS a b 2 3 = a + 2 * b := by simp [phiAS]
lemma phiAS_24 {R : Type*} [CommRing R] (a b : R) : phiAS a b 2 4 = 0 := by simp [phiAS]
lemma phiAS_30 {R : Type*} [CommRing R] (a b : R) : phiAS a b 3 0 = 0 := by simp [phiAS]
lemma phiAS_31 {R : Type*} [CommRing R] (a b : R) : phiAS a b 3 1 = 0 := by simp [phiAS]
lemma phiAS_32 {R : Type*} [CommRing R] (a b : R) : phiAS a b 3 2 = 0 := by simp [phiAS]
lemma phiAS_33 {R : Type*} [CommRing R] (a b : R) : phiAS a b 3 3 = 0 := by simp [phiAS]
lemma phiAS_34 {R : Type*} [CommRing R] (a b : R) : phiAS a b 3 4 = 4 * a + 3 * b := by simp [phiAS]
lemma phiAS_40 {R : Type*} [CommRing R] (a b : R) : phiAS a b 4 0 = 0 := by simp [phiAS]
lemma phiAS_41 {R : Type*} [CommRing R] (a b : R) : phiAS a b 4 1 = 0 := by simp [phiAS]
lemma phiAS_42 {R : Type*} [CommRing R] (a b : R) : phiAS a b 4 2 = 0 := by simp [phiAS]
lemma phiAS_43 {R : Type*} [CommRing R] (a b : R) : phiAS a b 4 3 = 0 := by simp [phiAS]
lemma phiAS_44 {R : Type*} [CommRing R] (a b : R) : phiAS a b 4 4 = 0 := by simp [phiAS]

/-! ## §2 The constants of the residual chart -/

/-- `A = 3a+b = phiAS 0 1` with `a = aK D`. -/
def asZA (D : KleinData 𝕜) : Om D := algebraMap (RatFunc 𝕜) (Om D) (phiAS (aK D) (bK D) 0 1)
/-- `B = 3a+4b = phiAS 0 3`. -/
def asZB (D : KleinData 𝕜) : Om D := algebraMap (RatFunc 𝕜) (Om D) (phiAS (aK D) (bK D) 0 3)
/-- `C = a+3b = phiAS 1 4`. -/
def asZC (D : KleinData 𝕜) : Om D := algebraMap (RatFunc 𝕜) (Om D) (phiAS (aK D) (bK D) 1 4)
/-- `D = a+2b = phiAS 2 3`. -/
def asZD (D : KleinData 𝕜) : Om D := algebraMap (RatFunc 𝕜) (Om D) (phiAS (aK D) (bK D) 2 3)
/-- `E = 4a+3b = phiAS 3 4`. -/
def asZE (D : KleinData 𝕜) : Om D := algebraMap (RatFunc 𝕜) (Om D) (phiAS (aK D) (bK D) 3 4)

/-- The Klein coefficient `a`, pushed to `Om D`. -/
def asZa (D : KleinData 𝕜) : Om D :=
  algebraMap (RatFunc 𝕜) (Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.a)
/-- The Klein coefficient `b`, pushed to `Om D`. -/
def asZb (D : KleinData 𝕜) : Om D :=
  algebraMap (RatFunc 𝕜) (Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.b)
/-- The Artin–Schreier parameter `g`, pushed to `Om D`. -/
def asZc (D : KleinData 𝕜) (g : RatFunc 𝕜) : Om D := algebraMap (RatFunc 𝕜) (Om D) g

/-- `μ = 2(a² - ab - b²)`. -/
def asZmu (D : KleinData 𝕜) : Om D :=
  algebraMap (RatFunc 𝕜) (Om D) (2 * (aK D ^ 2 - aK D * bK D - bK D ^ 2))

/-- `λ = μ·B/A + (a² + b²)`, the combination of the `k=1` and `k=3` equations. -/
def asZlam (D : KleinData 𝕜) (g : RatFunc 𝕜) : Om D :=
  asZmu D * asZB D / asZA D + (asZa D ^ 2 + asZb D ^ 2)

/-! ## §3 The projective coordinates of the source curve, and the inverse chart -/

/-- The projective twisted coordinates `v_j = asTwY D g j / asTwY D g 0`. -/
def asZv (D : KleinData 𝕜) (g : RatFunc 𝕜) (j : Fin 5) : Om D :=
  asTwY D g j / asTwY D g 0

/-- The residual chart coordinates `X i = z_{i+1}/z₀`. -/
def asZX (D : KleinData 𝕜) (g : RatFunc 𝕜) (i : Fin 3) : Om D :=
  asZOm 𝕜 D g ⟨i.1 + 1, by omega⟩ / asZOm 𝕜 D g 0

/-- `w₃ = X₁/D`. -/
def asZw3 (D : KleinData 𝕜) (g : RatFunc 𝕜) : Om D := asZX D g 1 / asZD D
/-- `w₄ = X₂/E`. -/
def asZw4 (D : KleinData 𝕜) (g : RatFunc 𝕜) : Om D := asZX D g 2 / asZE D
/-- `w₁ = (1 - B·w₃)/A`. -/
def asZw1 (D : KleinData 𝕜) (g : RatFunc 𝕜) : Om D := (1 - asZB D * asZw3 D g) / asZA D
/-- `w₂ = (X₀ - C·w₄)/A`. -/
def asZw2 (D : KleinData 𝕜) (g : RatFunc 𝕜) : Om D := (asZX D g 0 - asZC D * asZw4 D g) / asZA D

/-- The recovered chart vector `w = (0, w₁, w₂, w₃, w₄)`. -/
def asZw (D : KleinData 𝕜) (g : RatFunc 𝕜) : Fin 5 → Om D :=
  ![0, asZw1 D g, asZw2 D g, asZw3 D g, asZw4 D g]

/-! ## §4 Bridge lemmas: the constants of §2 in the base field -/

lemma asZA_eq (D : KleinData 𝕜) : asZA D = algebraMap 𝕜 (Om D) (3 * D.a + D.b) := by
  have h : 3 * aK D + bK D = algebraMap 𝕜 (RatFunc 𝕜) (3 * D.a + D.b) := by
    rw [aK, bK, map_add, map_mul, map_ofNat]
  simp only [asZA, phiAS_01]
  rw [h, IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Om D) (3 * D.a + D.b)]

lemma asZD_eq (D : KleinData 𝕜) : asZD D = algebraMap 𝕜 (Om D) (D.a + 2 * D.b) := by
  have h : aK D + 2 * bK D = algebraMap 𝕜 (RatFunc 𝕜) (D.a + 2 * D.b) := by
    rw [aK, bK, map_add, map_mul, map_ofNat]
  simp only [asZD, phiAS_23]
  rw [h, IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Om D) (D.a + 2 * D.b)]

lemma asZE_eq (D : KleinData 𝕜) : asZE D = algebraMap 𝕜 (Om D) (4 * D.a + 3 * D.b) := by
  have h : 4 * aK D + 3 * bK D = algebraMap 𝕜 (RatFunc 𝕜) (4 * D.a + 3 * D.b) := by
    rw [aK, bK, map_add, map_mul, map_mul, map_ofNat, map_ofNat]
  simp only [asZE, phiAS_34]
  rw [h, IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Om D) (4 * D.a + 3 * D.b)]

lemma asZmu_eq (D : KleinData 𝕜) :
    asZmu D = algebraMap 𝕜 (Om D) (2 * (D.a ^ 2 - D.a * D.b - D.b ^ 2)) := by
  have h : 2 * (aK D ^ 2 - aK D * bK D - bK D ^ 2)
      = algebraMap 𝕜 (RatFunc 𝕜) (2 * (D.a ^ 2 - D.a * D.b - D.b ^ 2)) := by
    rw [aK, bK]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  simp only [asZmu]
  rw [h, IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Om D)
    (2 * (D.a ^ 2 - D.a * D.b - D.b ^ 2))]

lemma asZa_eq (D : KleinData 𝕜) : asZa D = algebraMap 𝕜 (Om D) D.a :=
  IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Om D) D.a

lemma asZb_eq (D : KleinData 𝕜) : asZb D = algebraMap 𝕜 (Om D) D.b :=
  IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Om D) D.b

/-! ## §5 The residual coordinates as linear forms in `v` -/

lemma asZOm_zero_eq (D : KleinData 𝕜) (g : RatFunc 𝕜) :
    asZOm 𝕜 D g 0 = asZA D * asZv D g 1 + asZB D * asZv D g 3 := by
  simp only [asZOm, asZA, asZB, asZv, Fin.sum_univ_five, phiAS_00, phiAS_01, phiAS_02,
    phiAS_03, phiAS_04, phiAS_10, phiAS_11, phiAS_12, phiAS_13, phiAS_14, map_zero,
    zero_mul, mul_zero, add_zero, zero_add]

lemma asZOm_one_eq (D : KleinData 𝕜) (g : RatFunc 𝕜) :
    asZOm 𝕜 D g 1 = asZA D * asZv D g 2 + asZC D * asZv D g 4 := by
  simp only [asZOm, asZA, asZC, asZv, Fin.sum_univ_five, phiAS_00, phiAS_01, phiAS_02,
    phiAS_03, phiAS_04, phiAS_10, phiAS_11, phiAS_12, phiAS_13, phiAS_14, map_zero,
    zero_mul, mul_zero, add_zero, zero_add]

lemma asZOm_two_eq (D : KleinData 𝕜) (g : RatFunc 𝕜) :
    asZOm 𝕜 D g 2 = asZD D * asZv D g 3 := by
  simp only [asZOm, asZD, asZv, Fin.sum_univ_five, phiAS_20, phiAS_21, phiAS_22, phiAS_23,
    phiAS_24, map_zero, zero_mul, mul_zero, add_zero, zero_add]

lemma asZOm_three_eq (D : KleinData 𝕜) (g : RatFunc 𝕜) :
    asZOm 𝕜 D g 3 = asZE D * asZv D g 4 := by
  simp only [asZOm, asZE, asZv, Fin.sum_univ_five, phiAS_30, phiAS_31, phiAS_32, phiAS_33,
    phiAS_34, map_zero, zero_mul, add_zero, zero_add]

lemma asZOm_four_eq (D : KleinData 𝕜) (g : RatFunc 𝕜) : asZOm 𝕜 D g 4 = 0 := by
  simp only [asZOm, Fin.sum_univ_five, phiAS_40, phiAS_41, phiAS_42, phiAS_43, phiAS_44,
    map_zero, zero_mul, add_zero, zero_add]

/-! ## §6 Nonvanishing of the chart coefficients under `ASGood` -/

/-- In characteristic `5`, `a² - ab - b² = (3a+b)(2a+4b)`. -/
lemma three_mul_add_ne_zero (a b : 𝕜) (hδ : a ^ 2 - a * b - b ^ 2 ≠ 0) : 3 * a + b ≠ 0 := by
  intro h
  have h5 : (5 : 𝕜) = 0 := CharP.cast_eq_zero 𝕜 5
  have hfac : (3 * a + b) * (2 * a + 4 * b) = a ^ 2 - a * b - b ^ 2 := by
    linear_combination (norm := first | refl_ring1 | ring1) (a ^ 2 + 3 * a * b + b ^ 2) * h5
  rw [h, zero_mul] at hfac
  exact hδ hfac.symm

/-- In characteristic `5`, `a² - ab - b² = (a+2b)²`. -/
lemma add_two_mul_ne_zero (a b : 𝕜) (hδ : a ^ 2 - a * b - b ^ 2 ≠ 0) : a + 2 * b ≠ 0 := by
  intro h
  have h5 : (5 : 𝕜) = 0 := CharP.cast_eq_zero 𝕜 5
  have hfac : (a + 2 * b) * (a + 2 * b) = a ^ 2 - a * b - b ^ 2 := by
    linear_combination (norm := first | refl_ring1 | ring1) (a * b + b ^ 2) * h5
  rw [h, zero_mul] at hfac
  exact hδ hfac.symm

/-- In characteristic `5`, `a² - ab - b² = (4a+3b)²`. -/
lemma four_mul_add_three_mul_ne_zero (a b : 𝕜)
    (hδ : a ^ 2 - a * b - b ^ 2 ≠ 0) : 4 * a + 3 * b ≠ 0 := by
  intro h
  have h5 : (5 : 𝕜) = 0 := CharP.cast_eq_zero 𝕜 5
  have hfac : (4 * a + 3 * b) * (4 * a + 3 * b) = a ^ 2 - a * b - b ^ 2 := by
    linear_combination (norm := first | refl_ring1 | ring1) (3 * a ^ 2 + 5 * a * b + 2 * b ^ 2) * h5
  rw [h, zero_mul] at hfac
  exact hδ hfac.symm

lemma asZA_ne_zero (D : KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) : asZA D ≠ 0 := by
  rw [asZA_eq]
  intro h
  exact three_mul_add_ne_zero D.a D.b hD.2.2.2
    ((algebraMap 𝕜 (Om D)).injective (by rw [h, map_zero]))

lemma asZD_ne_zero (D : KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) : asZD D ≠ 0 := by
  rw [asZD_eq]
  intro h
  exact add_two_mul_ne_zero D.a D.b hD.2.2.2
    ((algebraMap 𝕜 (Om D)).injective (by rw [h, map_zero]))

lemma asZE_ne_zero (D : KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) : asZE D ≠ 0 := by
  rw [asZE_eq]
  intro h
  exact four_mul_add_three_mul_ne_zero D.a D.b hD.2.2.2
    ((algebraMap 𝕜 (Om D)).injective (by rw [h, map_zero]))

lemma asZmu_ne_zero (D : KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) : asZmu D ≠ 0 := by
  rw [asZmu_eq]
  intro h
  have h' : (2 : 𝕜) * (D.a ^ 2 - D.a * D.b - D.b ^ 2) = 0 :=
    (algebraMap 𝕜 (Om D)).injective (by rw [h, map_zero])
  have h2 : (2 : 𝕜) ≠ 0 := by
    intro hh
    have h5 : (5 : 𝕜) = 0 := CharP.cast_eq_zero 𝕜 5
    have h32 : (3 : 𝕜) * 2 = 1 := by linear_combination h5
    rw [hh, mul_zero] at h32
    exact one_ne_zero h32.symm
  rcases mul_eq_zero.mp h' with hzero | hd
  · exact absurd hzero h2
  · exact hD.2.2.2 hd

/-! ## §7 The two decompositions of the twisted Pfaffians -/

/-- `kleinPAS1` is `y₀` times an explicit linear form plus its value at `y₀ = 0`. -/
lemma kleinPAS1_decomp {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) :
    kleinPAS1 a b g y
      = y 0 * (2 * (a ^ 2 - a * b - b ^ 2) * y 1 - (a ^ 2 + b ^ 2) * y 3)
        + kleinPAS1 a b g (Function.update y 0 0) := by
  simp only [kleinPAS1, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 5) ≠ 0),
    Function.update_of_ne (by decide : (2 : Fin 5) ≠ 0),
    Function.update_of_ne (by decide : (3 : Fin 5) ≠ 0),
    Function.update_of_ne (by decide : (4 : Fin 5) ≠ 0)]
  first | refl_ring1 | ring

/-- `kleinPAS3` is `y₀` times an explicit linear form plus its value at `y₀ = 0`. -/
lemma kleinPAS3_decomp {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) :
    kleinPAS3 a b g y
      = y 0 * (2 * (a ^ 2 - a * b - b ^ 2) * y 3)
        + kleinPAS3 a b g (Function.update y 0 0) := by
  simp only [kleinPAS3, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 5) ≠ 0),
    Function.update_of_ne (by decide : (2 : Fin 5) ≠ 0),
    Function.update_of_ne (by decide : (3 : Fin 5) ≠ 0),
    Function.update_of_ne (by decide : (4 : Fin 5) ≠ 0)]
  first | refl_ring1 | ring

/-- The `![0,y₁,y₂,y₃,y₄]` form of `kleinPAS1_decomp`. -/
lemma kleinPAS1_decomp_fin {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) :
    kleinPAS1 a b g y
      = y 0 * (2 * (a ^ 2 - a * b - b ^ 2) * y 1 - (a ^ 2 + b ^ 2) * y 3)
        + kleinPAS1 a b g ![0, y 1, y 2, y 3, y 4] := by
  rw [kleinPAS1_decomp]
  congr 1

/-- The `![0,y₁,y₂,y₃,y₄]` form of `kleinPAS3_decomp`. -/
lemma kleinPAS3_decomp_fin {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) :
    kleinPAS3 a b g y
      = y 0 * (2 * (a ^ 2 - a * b - b ^ 2) * y 3)
        + kleinPAS3 a b g ![0, y 1, y 2, y 3, y 4] := by
  rw [kleinPAS3_decomp]
  congr 1

/-- The decomposition of `kleinPAS1` at the vector `![t,w₁,w₂,w₃,w₄]`. -/
lemma kleinPAS1_decomp_u {R : Type*} [CommRing R] (a b g t w1 w2 w3 w4 : R) :
    kleinPAS1 a b g ![t, w1, w2, w3, w4]
      = t * (2 * (a ^ 2 - a * b - b ^ 2) * w1 - (a ^ 2 + b ^ 2) * w3)
        + kleinPAS1 a b g ![0, w1, w2, w3, w4] := by
  have h := kleinPAS1_decomp_fin (a := a) (b := b) (g := g) (y := ![t, w1, w2, w3, w4])
  simpa [Matrix.cons_val_zero] using h

/-- The decomposition of `kleinPAS3` at the vector `![t,w₁,w₂,w₃,w₄]`. -/
lemma kleinPAS3_decomp_u {R : Type*} [CommRing R] (a b g t w1 w2 w3 w4 : R) :
    kleinPAS3 a b g ![t, w1, w2, w3, w4]
      = t * (2 * (a ^ 2 - a * b - b ^ 2) * w3)
        + kleinPAS3 a b g ![0, w1, w2, w3, w4] := by
  have h := kleinPAS3_decomp_fin (a := a) (b := b) (g := g) (y := ![t, w1, w2, w3, w4])
  simpa [Matrix.cons_val_zero] using h

/-! ## §8 The characteristic-`5` power sum -/

lemma sum_five_sq {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (w : R) :
    ∑ i : Fin 5, (w + (i : ℕ)) ^ 2 = 0 := by
  rw [Fin.sum_univ_five]
  norm_num
  ring_nf
  linear_combination (norm := first | refl_ring1 | ring1) (6 + 4 * w + w ^ 2) * h5

end

end Work.MotAS
