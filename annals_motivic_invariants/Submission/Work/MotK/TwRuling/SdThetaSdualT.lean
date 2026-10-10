import Mathlib
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.TwAmbh
import Submission.Work.MotK.TGen.TwCoordGKleinTw
import Submission.Work.MotK.TGen.TwBridge
import Submission.Work.MotK.TwRule.KleinTwRuleEval
import Submission.Work.MotK.TwRuling.KleinNondeg
import Submission.Work.MotK.TwRuling.sdY_curve
import Submission.Work.MotK.TwRuling.sdW_four_ne_zero
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000
set_option autoImplicit false

namespace Work.MotK.TwRuling

open MvPolynomial

/-! ## Elementary polynomial identities for the twisted ruling data -/

/-- Naturality of the inverse-twisted dual secant quintic. -/
theorem kleinTwSDualV_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b h : R)
    (z : Fin 5 → R) :
    φ (Work.MotK.kleinTwSDualV a b h z)
      = Work.MotK.kleinTwSDualV (φ a) (φ b) (φ h) (fun i => φ (z i)) := by
  simp only [Work.MotK.kleinTwSDualV, map_add, map_mul, map_sub, map_pow, map_ofNat]

/-- The inverse-twisted dual secant quintic has no constant term. -/
theorem kleinTwSDualV_zero {R : Type*} [CommRing R] (a b h : R) :
    Work.MotK.kleinTwSDualV a b h (0 : Fin 5 → R) = 0 := by
  simp only [Work.MotK.kleinTwSDualV, Pi.zero_apply]
  first | refl_ring1 | ring

/-- The first ruling vector has vanishing zeroth component. -/
theorem kleinTwRuleA_zero {R : Type*} [CommRing R] (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleA a b h c 0 = 0 := by
  unfold Work.MotK.kleinTwRuleA Work.MotK.kleinTwPolarP Work.MotK.kleinTwP Work.MotK.kleinTwTan
    Work.MotK.kleinTwBilin Work.MotK.kleinTwQ Work.MotK.kleinTwP0 Work.MotK.kleinTwP1
    Work.MotK.kleinTwP2 Work.MotK.kleinTwP3 Work.MotK.kleinTwP4 Work.MotK.kleinE
  simp only [Pi.single_apply, Fin.isValue]
  norm_num
  first | refl_ring1 | ring

/-- The second ruling vector has vanishing zeroth component. -/
theorem kleinTwRuleB_zero {R : Type*} [CommRing R] (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleB a b h c 0 = 0 := by
  unfold Work.MotK.kleinTwRuleB Work.MotK.kleinTwPolarP Work.MotK.kleinTwP Work.MotK.kleinTwTan
    Work.MotK.kleinTwBilin Work.MotK.kleinTwQ Work.MotK.kleinTwP0 Work.MotK.kleinTwP1
    Work.MotK.kleinTwP2 Work.MotK.kleinTwP3 Work.MotK.kleinTwP4 Work.MotK.kleinE
  simp only [Pi.single_apply, Fin.isValue]
  norm_num
  first | refl_ring1 | ring

/-- The fourth component of the first ruling vector. -/
theorem kleinTwRuleA_four {R : Type*} [CommRing R] (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleA a b h c 4
      = 2 * a ^ 3 * b * (c 0) ^ 2 - a ^ 2 * b ^ 2 * h * (c 1) * (c 4) := by
  unfold Work.MotK.kleinTwRuleA Work.MotK.kleinTwPolarP Work.MotK.kleinTwP Work.MotK.kleinTwTan
    Work.MotK.kleinTwBilin Work.MotK.kleinTwQ Work.MotK.kleinTwP0 Work.MotK.kleinTwP1
    Work.MotK.kleinTwP2 Work.MotK.kleinTwP3 Work.MotK.kleinTwP4 Work.MotK.kleinE
  simp only [Pi.single_apply, Fin.isValue]
  norm_num
  first | refl_ring1 | ring

/-- The fourth component of the second ruling vector. -/
theorem kleinTwRuleB_four {R : Type*} [CommRing R] (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleB a b h c 4
      = a ^ 4 * h * (c 1) * (c 3) - 2 * a * b ^ 3 * h * (c 0) * (c 4) := by
  unfold Work.MotK.kleinTwRuleB Work.MotK.kleinTwPolarP Work.MotK.kleinTwP Work.MotK.kleinTwTan
    Work.MotK.kleinTwBilin Work.MotK.kleinTwQ Work.MotK.kleinTwP0 Work.MotK.kleinTwP1
    Work.MotK.kleinTwP2 Work.MotK.kleinTwP3 Work.MotK.kleinTwP4 Work.MotK.kleinE
  simp only [Pi.single_apply, Fin.isValue]
  norm_num
  first | refl_ring1 | ring

/-- Naturality of the fourth component of the first ruling vector. -/
theorem kleinTwRuleA_map_four {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b h : R)
    (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleA (φ a) (φ b) (φ h) (fun i => φ (c i)) 4
      = φ (Work.MotK.kleinTwRuleA a b h c 4) := by
  simp only [kleinTwRuleA_four, map_sub, map_mul, map_pow, map_ofNat]

/-- Naturality of the fourth component of the second ruling vector. -/
theorem kleinTwRuleB_map_four {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b h : R)
    (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleB (φ a) (φ b) (φ h) (fun i => φ (c i)) 4
      = φ (Work.MotK.kleinTwRuleB a b h c 4) := by
  simp only [kleinTwRuleB_four, map_sub, map_mul, map_pow, map_ofNat]

/-- **Transcendence of `RatFunc.X`**: `C a + X * C b` is nonzero as soon as `a ≠ 0`. -/
theorem ratFunc_C_add_X_mul_C_ne_zero {F : Type*} [Field F] {a b : F} (ha : a ≠ 0) :
    RatFunc.C a + RatFunc.X * RatFunc.C b ≠ 0 := by
  intro h0
  have hX : (algebraMap (Polynomial F) (RatFunc F)) Polynomial.X = RatFunc.X :=
    RatFunc.algebraMap_X
  have hCa : (algebraMap (Polynomial F) (RatFunc F)) (Polynomial.C a) = RatFunc.C a := by
    change (algebraMap (Polynomial F) (RatFunc F)) ((algebraMap F (Polynomial F)) a) = RatFunc.C a
    rw [← IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F), RatFunc.algebraMap_eq_C]
  have hCb : (algebraMap (Polynomial F) (RatFunc F)) (Polynomial.C b) = RatFunc.C b := by
    change (algebraMap (Polynomial F) (RatFunc F)) ((algebraMap F (Polynomial F)) b) = RatFunc.C b
    rw [← IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F), RatFunc.algebraMap_eq_C]
  have h2 : (algebraMap (Polynomial F) (RatFunc F))
      (Polynomial.C a + Polynomial.X * Polynomial.C b) = 0 := by
    rw [map_add, map_mul, hCa, hCb, hX, h0]
  have h3 : Polynomial.C a + Polynomial.X * Polynomial.C b = 0 :=
    IsFractionRing.injective (Polynomial F) (RatFunc F) (by rw [h2, map_zero])
  have h4 : (Polynomial.C a + Polynomial.X * Polynomial.C b).coeff 0 = 0 := by
    rw [h3, Polynomial.coeff_zero]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul_zero, add_zero] at h4
  exact ha h4

/-- The zeroth twisted coordinate (in the rational function field of the twist field) is `1`. -/
theorem sdY_zero (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) :
    Work.MotK.TGen.sdY K D h 0 = 1 := by
  have h0 : Work.MotK.twCoordG K D h 0 = 1 := by
    rw [Work.MotK.twCoordG]
    simp only [Fin.val_zero, pow_zero, one_mul]
    exact div_self (hD.coord0_ne (Work.MotK.KbG K))
  have hsub : (⟨Work.MotK.twCoordG K D h 0,
      IntermediateField.subset_adjoin K (Set.range (Work.MotK.twCoordG K D h))
        (Set.mem_range_self 0)⟩ : ↥(Work.MotK.twistFieldTG K D h)) = 1 :=
    Subtype.ext h0
  rw [Work.MotK.TGen.sdY, hsub, map_one]

/-! ## The main theorem -/

theorem SdThetaSdualT (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) (h : K)
    (hh : h ≠ 0) :
    Work.MotK.TGen.sdTheta K D h (Work.MotK.TGen.sdualT D.a D.b h) = 0 := by
  set W := Work.MotK.TGen.sdW K D h with hW
  set Y := Work.MotK.TGen.sdY K D h with hY
  set P := Work.MotK.TGen.sdPhi K D h with hP
  have hcurve : ∀ k : Fin 5,
      Work.MotK.kleinTwP (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h)
        Y k = 0 := by
    intro k
    rw [hY]
    exact sdY_curve K D hD h hh k
  have hW0 : W 0 = 0 := by
    rw [hW]
    simp only [Work.MotK.TGen.sdW, Work.MotK.TGen.sdRuleA, Work.MotK.TGen.sdRuleB]
    rw [kleinTwRuleA_zero, kleinTwRuleB_zero]
    first | refl_ring1 | ring
  have hW4 : W 4 ≠ 0 := by
    rw [hW]
    exact sdW_four_ne_zero K D hD h hh
  have hZe : (fun i => ![0, P 0, P 1, P 2, 1] i) = fun i => W i / W 4 := by
    funext i
    fin_cases i
    · simp [hW0]
    · simp [Work.MotK.TGen.sdPhi, Work.MotK.TGen.sdIdx, hP, hW]
    · simp [Work.MotK.TGen.sdPhi, Work.MotK.TGen.sdIdx, hP, hW]
    · simp [Work.MotK.TGen.sdPhi, Work.MotK.TGen.sdIdx, hP, hW]
    · exact (div_self hW4).symm
  have hZdiv : (fun i => W i / W 4) = fun i => (W 4)⁻¹ * W i := by
    funext i
    rw [div_eq_mul_inv, mul_comm]
  have hsW : Work.MotK.kleinTwSDualV (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
      (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h)
      W = 0 := by
    have hpt : Work.MotK.kleinTwRulePt (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h)
        Y 1 (RatFunc.X) = W := by
      rw [hW, hY]
      funext j
      simp only [Work.MotK.kleinTwRulePt, Work.MotK.TGen.sdW, Work.MotK.TGen.sdRuleA,
        Work.MotK.TGen.sdRuleB]
      first | refl_ring1 | ring
    have hR : Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h) W
        = fun j => Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
            (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
            (algebraMap K (Work.MotK.TGen.sdA K D h) h) W 0 * Y j := by
      funext j
      have hR1 := Work.MotK.TwRule.KleinTwRuleEval K (Work.MotK.TGen.sdA K D h) D.a D.b h 1
        (RatFunc.X) Y hcurve j 0
      rw [hpt] at hR1
      rw [hY, sdY_zero K D hD h, mul_one] at hR1
      exact hR1
    have hWs : ∀ i, Work.MotK.kleinTwSDualV (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h)
        W * W i = 0 := by
      intro i
      have hI2 := Work.MotK.kleinTwP_kleinTwR_V (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h) W i
      rw [← hI2, hR]
      rw [congrFun (Work.MotK.kleinTwP_homog (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h)
        (Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
          (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
          (algebraMap K (Work.MotK.TGen.sdA K D h) h) W 0) Y) i]
      rw [hcurve i, mul_zero]
    by_cases hWz : W = 0
    · rw [hWz, kleinTwSDualV_zero]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hWz
      exact (mul_eq_zero.mp (hWs i)).resolve_right hi
  have h1 : Work.MotK.TGen.sdTheta K D h (Work.MotK.TGen.sdualT D.a D.b h)
      = Work.MotK.kleinTwSDualV (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
          (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
          (algebraMap K (Work.MotK.TGen.sdA K D h) h)
          (fun i => ![0, P 0, P 1, P 2, 1] i) := by
    rw [Work.MotK.TGen.sdTheta, Work.MotK.TGen.sdualT]
    simp only [Work.MotK.kleinTwSDualV, map_add, map_mul, map_sub, map_pow, map_ofNat,
      MvPolynomial.aeval_C]
    simp only [Work.MotK.chart3, MvPolynomial.aeval_X]
    simp [hP]
  rw [h1, hZe, hZdiv, Work.MotK.kleinTwSDualV_homog, hsW, mul_zero]
