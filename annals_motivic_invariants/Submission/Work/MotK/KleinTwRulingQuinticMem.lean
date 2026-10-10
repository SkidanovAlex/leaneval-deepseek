import Mathlib
import Submission.Work.MotK.TwRulingField
import Submission.Work.MotK.KleinTwLink
import Submission.Work.MotK.KleinTwRuleMem
import Submission.Work.MotV.twCoord_eq
import Submission.Work.MotK.TGen.TwBridge
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The ruling lines of the T-twisted link lie in the divisor `{s' = 0}`

`Work.MotK.KleinTwRuleMem` proves the *polynomial* ruling identity of the T-twisted
Crauder--Katz link: for `c` in the twisted Klein curve `C = V(P_0, …, P_4)` the inverse cubic map
`R = kleinTwR` is projectively constant on the ruling line `ℓ_c = ℙ(span(A(c), B(c)))` with value
`c`, i.e. `R_i(ℓ_c)·c_j − R_j(ℓ_c)·c_i ∈ (P_0, …, P_4)`.

This file evaluates that identity at the *base point* `c = y` of the twisted Klein curve, i.e. at
the twisted Klein coordinates `y_j = twCoord D h j` of `Work.MotV`, viewed in the rational function
field `F = RatFunc ↥(twistFieldT D h)`, at the ruling parameters `λ = 1`, `μ = RatFunc.X`.  Since
the base point satisfies the twisted Klein quadrics (`Work.MotV.twCoord_eq`), the evaluation gives

  `R_i(w)·y_j = R_j(w)·y_i`,   `w = A(y) + t·B(y)`,

and with `y_0 = 1` this reads `R(w) = R_0(w) • y`.  Twisted I2
(`Work.MotK.KleinTwI2inv`: `kleinTwP (kleinTwR z) = kleinTwSDualInv z • z`) then gives

  `kleinTwSDualInv w · w_k = kleinTwP (kleinTwR w)_k = R_0(w)^2 · kleinTwP y_k = 0`,

whence `kleinTwSDualInv w = 0` (the case `w = 0` being trivial), which is
`Work.MotK.KleinTwRulingQuinticMem`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

namespace Work.MotK

/-! ## §1 Naturality of the ruling data under a ring homomorphism -/

section Nat

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The standard basis vectors are fixed by every ring homomorphism. -/
theorem kleinE_map_apply (σ : R →+* S) (k i : Fin 5) :
    σ (kleinE (R := R) k i) = kleinE (R := S) k i := by
  simp only [kleinE, Pi.single_apply]
  split <;> simp

/-- Naturality of the polar form `kleinTwBilin` of the twisted quadric. -/
theorem kleinTwBilin_map (σ : R →+* S) (a b h : R) (u v : Fin 5 → R) :
    σ (kleinTwBilin a b h u v)
      = kleinTwBilin (σ a) (σ b) (σ h) (fun i => σ (u i)) (fun i => σ (v i)) := by
  simp only [kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply, map_add, map_mul, map_pow, map_neg,
    map_sub]

/-- Naturality of the tangent vectors `kleinTwTan`. -/
theorem kleinTwTan_map (σ : R →+* S) (a b h : R) (c : Fin 5 → R) (k : Fin 5) :
    (fun i => σ (kleinTwTan a b h c k i))
      = kleinTwTan (σ a) (σ b) (σ h) (fun i => σ (c i)) k := by
  funext i
  simp only [kleinTwTan, map_sub, map_mul, kleinTwBilin_map, kleinE_map_apply]

/-- Naturality of the first ruling vector `kleinTwRuleA`. -/
theorem kleinTwRuleA_map (σ : R →+* S) (a b h : R) (c : Fin 5 → R) :
    (fun i => σ (kleinTwRuleA a b h c i))
      = kleinTwRuleA (σ a) (σ b) (σ h) (fun i => σ (c i)) := by
  funext i
  simp only [kleinTwRuleA, kleinTwPolarP_map_apply, kleinTwTan_map]

/-- Naturality of the second ruling vector `kleinTwRuleB`. -/
theorem kleinTwRuleB_map (σ : R →+* S) (a b h : R) (c : Fin 5 → R) :
    (fun i => σ (kleinTwRuleB a b h c i))
      = kleinTwRuleB (σ a) (σ b) (σ h) (fun i => σ (c i)) := by
  funext i
  simp only [kleinTwRuleB, kleinTwPolarP_map_apply, kleinTwTan_map]

/-- Naturality of the ruling point `kleinTwRulePt`. -/
theorem kleinTwRulePt_map (σ : R →+* S) (a b h : R) (c : Fin 5 → R) (l m : R) :
    (fun i => σ (kleinTwRulePt a b h c l m i))
      = kleinTwRulePt (σ a) (σ b) (σ h) (fun i => σ (c i)) (σ l) (σ m) := by
  funext i
  simp only [kleinTwRulePt, map_add, map_mul]
  rw [show σ (kleinTwRuleA a b h c i)
        = kleinTwRuleA (σ a) (σ b) (σ h) (fun i => σ (c i)) i
        from congrFun (kleinTwRuleA_map σ a b h c) i,
      show σ (kleinTwRuleB a b h c i)
        = kleinTwRuleB (σ a) (σ b) (σ h) (fun i => σ (c i)) i
        from congrFun (kleinTwRuleB_map σ a b h c) i]

/-- Pointwise form of `Work.MotK.KleinTwRMap`. -/
theorem kleinTwR_map_apply (σ : R →+* S) (a b h : R) (z : Fin 5 → R) (i : Fin 5) :
    σ (kleinTwR a b h z i) = kleinTwR (σ a) (σ b) (σ h) (fun i => σ (z i)) i :=
  congrFun (KleinTwRMap σ a b h z) i

/-- Pointwise form of `kleinTwRulePt_map`. -/
theorem kleinTwRulePt_map_apply (σ : R →+* S) (a b h : R) (c : Fin 5 → R) (l m : R)
    (i : Fin 5) :
    σ (kleinTwRulePt a b h c l m i)
      = kleinTwRulePt (σ a) (σ b) (σ h) (fun i => σ (c i)) (σ l) (σ m) i :=
  congrFun (kleinTwRulePt_map σ a b h c l m) i

/-- Evaluation of a constant multivariate polynomial at an algebra homomorphism into the base. -/
theorem aeval_C_apply {A σ : Type*} [CommSemiring A] (c : σ → A) (r : A) :
    MvPolynomial.aeval c (MvPolynomial.C r : MvPolynomial σ A) = r := by
  rw [MvPolynomial.aeval_C, Algebra.algebraMap_self_apply]

/-- Evaluation of a constant multivariate polynomial, in the ring-hom form. -/
theorem aeval_C_apply_ringHom {A σ : Type*} [CommSemiring A] (c : σ → A) (r : A) :
    (MvPolynomial.aeval c).toRingHom (MvPolynomial.C r : MvPolynomial σ A) = r := by
  show MvPolynomial.aeval c (MvPolynomial.C r) = r
  rw [MvPolynomial.aeval_C, Algebra.algebraMap_self_apply]

/-- Evaluation of the variables, in the ring-hom form. -/
theorem aeval_X_ringHom {A σ : Type*} [CommSemiring A] (c : σ → A) (s : σ) :
    (MvPolynomial.aeval c).toRingHom (MvPolynomial.X s : MvPolynomial σ A) = c s := by
  show MvPolynomial.aeval c (MvPolynomial.X s) = c s
  rw [MvPolynomial.aeval_X]

end Nat

/-! ## §2 Evaluating the ruling membership at a point of the twisted Klein curve -/

/-- **The ruling identity evaluated at a point of the twisted Klein curve.**  If `c` satisfies the
five twisted Klein quadrics, then the inverse cubic map `kleinTwR` is projectively constant on the
ruling line `ℓ_c` with value `c`.  This is the evaluated form of `Work.MotK.KleinTwRuleMem`, which
is the form consumed by the link. -/
theorem kleinTwRuleMem_aeval {K A : Type} [Field K] [Field A] [Algebra K A]
    (a b h : K) (l m : A) (c : Fin 5 → A)
    (hc : ∀ k : Fin 5, kleinTwP (algebraMap K A a) (algebraMap K A b) (algebraMap K A h) c k = 0)
    (i j : Fin 5) :
    kleinTwR (algebraMap K A a) (algebraMap K A b) (algebraMap K A h)
        (kleinTwRulePt (algebraMap K A a) (algebraMap K A b) (algebraMap K A h) c l m) i * c j
      = kleinTwR (algebraMap K A a) (algebraMap K A b) (algebraMap K A h)
        (kleinTwRulePt (algebraMap K A a) (algebraMap K A b) (algebraMap K A h) c l m) j * c i := by
  have hmem := KleinTwRuleMem (K := A) (algebraMap K A a) (algebraMap K A b) (algebraMap K A h)
    l m i j
  have hgen : ∀ k : Fin 5,
      MvPolynomial.aeval c (kleinTwP (MvPolynomial.C (algebraMap K A a))
        (MvPolynomial.C (algebraMap K A b)) (MvPolynomial.C (algebraMap K A h))
        (fun t => MvPolynomial.X t) k) = 0 := by
    intro k
    change (MvPolynomial.aeval c).toRingHom
        (kleinTwP (MvPolynomial.C (algebraMap K A a)) (MvPolynomial.C (algebraMap K A b))
          (MvPolynomial.C (algebraMap K A h)) (fun t => MvPolynomial.X t) k) = 0
    rw [KleinTwPMapApply (R := MvPolynomial (Fin 5) A) (S := A)
      (φ := (MvPolynomial.aeval c).toRingHom)]
    simp only [aeval_C_apply_ringHom, aeval_X_ringHom]
    exact hc k
  have hle : Ideal.span (Set.range (fun k : Fin 5 =>
        kleinTwP (MvPolynomial.C (algebraMap K A a)) (MvPolynomial.C (algebraMap K A b))
          (MvPolynomial.C (algebraMap K A h)) (fun t => MvPolynomial.X t) k))
      ≤ RingHom.ker (MvPolynomial.aeval c).toRingHom := by
    rw [Ideal.span_le]
    rintro x ⟨k, rfl⟩
    exact hgen k
  have h0 : (MvPolynomial.aeval c).toRingHom
      (kleinTwR (MvPolynomial.C (algebraMap K A a)) (MvPolynomial.C (algebraMap K A b))
          (MvPolynomial.C (algebraMap K A h))
          (kleinTwRulePt (MvPolynomial.C (algebraMap K A a)) (MvPolynomial.C (algebraMap K A b))
            (MvPolynomial.C (algebraMap K A h)) (fun t => MvPolynomial.X t)
            (MvPolynomial.C l) (MvPolynomial.C m)) i * MvPolynomial.X j
        - kleinTwR (MvPolynomial.C (algebraMap K A a)) (MvPolynomial.C (algebraMap K A b))
          (MvPolynomial.C (algebraMap K A h))
          (kleinTwRulePt (MvPolynomial.C (algebraMap K A a)) (MvPolynomial.C (algebraMap K A b))
            (MvPolynomial.C (algebraMap K A h)) (fun t => MvPolynomial.X t)
            (MvPolynomial.C l) (MvPolynomial.C m)) j * MvPolynomial.X i) = 0 :=
    RingHom.mem_ker.mp (hle hmem)
  simp only [map_sub, map_mul, kleinTwR_map_apply, kleinTwRulePt_map_apply,
    aeval_X_ringHom, aeval_C_apply_ringHom] at h0
  exact sub_eq_zero.mp h0

/-! ## §3 The base point of the twisted Klein curve in the twist field -/

/-- The zeroth twisted Klein coordinate is `w^{-0}·κ_0/κ_0 = 1`. -/
theorem twCoordF_zero (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (hD : D.Good)
    (h : RatFunc 𝕜) : twCoordF 𝕜 D h 0 = 1 := by
  apply Subtype.ext
  rw [twCoordF_coe]
  have hk : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ≠ 0 := hD.coord0_ne (Work.MotV.Kb 𝕜)
  simp only [Work.MotV.twCoord]
  norm_num
  exact hk

/-- The image in the ambient function field of a `𝕜`-constant of the twist field. -/
theorem coe_algebraMap_twistField (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (h : RatFunc 𝕜) (x : 𝕜) :
    algebraMap ↥(Work.MotV.twistFieldT D h) (Work.MotV.Om D)
        (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) x) = algebraMap 𝕜 (Work.MotV.Om D) x := by
  show ((algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) x : ↥(Work.MotV.twistFieldT D h)) :
      Work.MotV.Om D) = algebraMap 𝕜 (Work.MotV.Om D) x
  rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) ↥(Work.MotV.twistFieldT D h) x]
  rw [IntermediateField.coe_algebraMap_apply (Work.MotV.twistFieldT D h)
    (algebraMap 𝕜 (RatFunc 𝕜) x)]
  rw [← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) x]

/-- The image in the ambient function field of the Kummer class `h` in the twist field. -/
theorem coe_algebraMap_twistField_h (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (h : RatFunc 𝕜) :
    algebraMap ↥(Work.MotV.twistFieldT D h) (Work.MotV.Om D)
        (algebraMap (RatFunc 𝕜) ↥(Work.MotV.twistFieldT D h) h)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) h := by
  show ((algebraMap (RatFunc 𝕜) ↥(Work.MotV.twistFieldT D h) h :
      ↥(Work.MotV.twistFieldT D h)) : Work.MotV.Om D) = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) h
  exact IntermediateField.coe_algebraMap_apply (Work.MotV.twistFieldT D h) h

/-- The image in the ambient function field of the twisted coordinates. -/
theorem coe_twCoordF_apply (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (h : RatFunc 𝕜) (j : Fin 5) :
    algebraMap ↥(Work.MotV.twistFieldT D h) (Work.MotV.Om D) (twCoordF 𝕜 D h j)
      = Work.MotV.twCoord D h j :=
  twCoordF_coe 𝕜 D h j

/-- **The twisted Klein quadrics in the twist field**: the twisted Klein coordinates, viewed in
`RatFunc ↥(twistFieldT D h)`, satisfy the twisted Klein equations. -/
theorem kleinTwP_twistField (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (hD : D.Good)
    (h : RatFunc 𝕜) (hh : h ≠ 0) (k : Fin 5) :
    kleinTwP
      (algebraMap ↥(Work.MotV.twistFieldT D h) (RatFunc ↥(Work.MotV.twistFieldT D h))
        (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.a))
      (algebraMap ↥(Work.MotV.twistFieldT D h) (RatFunc ↥(Work.MotV.twistFieldT D h))
        (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.b))
      (algebraMap ↥(Work.MotV.twistFieldT D h) (RatFunc ↥(Work.MotV.twistFieldT D h))
        (algebraMap (RatFunc 𝕜) ↥(Work.MotV.twistFieldT D h) h))
      (fun j => algebraMap ↥(Work.MotV.twistFieldT D h) (RatFunc ↥(Work.MotV.twistFieldT D h))
        (twCoordF 𝕜 D h j)) k = 0 := by
  -- the twisted Klein equations in the ambient function field `Om D`
  have hOm : kleinTwP (algebraMap 𝕜 (Work.MotV.Om D) D.a)
      (algebraMap 𝕜 (Work.MotV.Om D) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) h)
      (Work.MotV.twCoord D h) k = 0 :=
    (Work.MotK.TGen.kleinTw_eq_kleinTwP (algebraMap 𝕜 (Work.MotV.Om D) D.a)
      (algebraMap 𝕜 (Work.MotV.Om D) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) h)
      (Work.MotV.twCoord D h) k).symm.trans (Work.MotV.twCoord_eq_univ0 D hD h hh k)
  -- descend to the twist field `↥(twistFieldT D h)`
  have hK : kleinTwP (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.a)
      (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.b)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV.twistFieldT D h) h)
      (twCoordF 𝕜 D h) k = 0 := by
    apply (algebraMap ↥(Work.MotV.twistFieldT D h) (Work.MotV.Om D)).injective
    rw [map_zero, KleinTwPMapApply (algebraMap ↥(Work.MotV.twistFieldT D h) (Work.MotV.Om D))
      (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.a)
      (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.b)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV.twistFieldT D h) h) (twCoordF 𝕜 D h) k]
    rw [coe_algebraMap_twistField 𝕜 D h D.a, coe_algebraMap_twistField 𝕜 D h D.b,
      coe_algebraMap_twistField_h 𝕜 D h]
    simp only [coe_twCoordF_apply]
    exact hOm
  -- and lift to the rational function field
  rw [← KleinTwPMapApply (algebraMap ↥(Work.MotV.twistFieldT D h)
      (RatFunc ↥(Work.MotV.twistFieldT D h)))
    (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.a)
    (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.b)
    (algebraMap (RatFunc 𝕜) ↥(Work.MotV.twistFieldT D h) h) (twCoordF 𝕜 D h) k]
  rw [hK, map_zero]

/-! ## §4 The abstract argument -/

/-- **The ruling point at the base point lies on the dual secant divisor.**  If `y` is a point of
the twisted Klein curve with `y 0 = 1`, then for any ruling parameters `l, m` the dual secant
quintic `kleinTwSDualInv` vanishes at the ruling point `kleinTwRulePt a b h y l m` (which is the
trivial statement when that point is zero, and follows from I2 and the ruling identity otherwise).
-/
theorem kleinTwSDualInv_rulingPt_eq_zero {F : Type*} [Field F] (a b h l m : F) (y : Fin 5 → F)
    (hy : ∀ k, kleinTwP a b h y k = 0)
    (hR : ∀ i j, kleinTwR a b h (kleinTwRulePt a b h y l m) i * y j
      = kleinTwR a b h (kleinTwRulePt a b h y l m) j * y i)
    (hy0 : y 0 = 1) :
    kleinTwSDualInv a b h (kleinTwRulePt a b h y l m) = 0 := by
  let w : Fin 5 → F := kleinTwRulePt a b h y l m
  change kleinTwSDualInv a b h w = 0
  by_cases hzero : w = 0
  · rw [hzero]
    simp only [kleinTwSDualInv, Pi.zero_apply]
    refl_ring1
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp hzero
    have hR0 : ∀ i, kleinTwR a b h w i = kleinTwR a b h w 0 * y i := by
      intro i
      have h := hR i 0
      rw [hy0, mul_one] at h
      exact h
    have hPeq : kleinTwP a b h (kleinTwR a b h w) k = 0 := by
      have h1 : kleinTwR a b h w = fun i => kleinTwR a b h w 0 * y i := funext hR0
      rw [h1,
        show kleinTwP a b h (fun i => kleinTwR a b h w 0 * y i) k
            = (kleinTwR a b h w 0) ^ 2 * kleinTwP a b h y k
            from congrFun (kleinTwP_homog a b h (kleinTwR a b h w 0) y) k,
        hy k, mul_zero]
    have h2 : kleinTwSDualInv a b h w * w k = 0 := by
      rw [← KleinTwI2inv a b h w k]
      exact hPeq
    exact (mul_eq_zero.mp h2).resolve_right hk

/-! ## §5 The main theorem -/

theorem KleinTwRulingQuinticMem (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (hD : D.Good)
    (h : RatFunc 𝕜) (hh : h ≠ 0) :
    Work.MotK.kleinTwSDualInv
      (algebraMap 𝕜 (RatFunc ↥(Work.MotV.twistFieldT D h)) D.a)
      (algebraMap 𝕜 (RatFunc ↥(Work.MotV.twistFieldT D h)) D.b)
      (algebraMap (RatFunc 𝕜) (RatFunc ↥(Work.MotV.twistFieldT D h)) h)
      (Work.MotK.twRulePtF 𝕜 D h) = 0 := by
  have ha : algebraMap ↥(Work.MotV.twistFieldT D h) (RatFunc ↥(Work.MotV.twistFieldT D h))
        (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.a)
      = algebraMap 𝕜 (RatFunc ↥(Work.MotV.twistFieldT D h)) D.a :=
    IsScalarTower.algebraMap_apply 𝕜 ↥(Work.MotV.twistFieldT D h)
      (RatFunc ↥(Work.MotV.twistFieldT D h)) D.a
  have hb : algebraMap ↥(Work.MotV.twistFieldT D h) (RatFunc ↥(Work.MotV.twistFieldT D h))
        (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.b)
      = algebraMap 𝕜 (RatFunc ↥(Work.MotV.twistFieldT D h)) D.b :=
    IsScalarTower.algebraMap_apply 𝕜 ↥(Work.MotV.twistFieldT D h)
      (RatFunc ↥(Work.MotV.twistFieldT D h)) D.b
  have hh' : algebraMap ↥(Work.MotV.twistFieldT D h) (RatFunc ↥(Work.MotV.twistFieldT D h))
        (algebraMap (RatFunc 𝕜) ↥(Work.MotV.twistFieldT D h) h)
      = algebraMap (RatFunc 𝕜) (RatFunc ↥(Work.MotV.twistFieldT D h)) h :=
    IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(Work.MotV.twistFieldT D h)
      (RatFunc ↥(Work.MotV.twistFieldT D h)) h
  have hy := kleinTwP_twistField 𝕜 D hD h hh
  have hy0 : (fun j => algebraMap ↥(Work.MotV.twistFieldT D h)
      (RatFunc ↥(Work.MotV.twistFieldT D h)) (twCoordF 𝕜 D h j)) 0 = 1 := by
    simp only [twCoordF_zero 𝕜 D hD h, map_one]
  have hR := fun i j => kleinTwRuleMem_aeval
      (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.a)
      (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.b)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV.twistFieldT D h) h)
      (1 : RatFunc ↥(Work.MotV.twistFieldT D h)) RatFunc.X
      (fun j => algebraMap ↥(Work.MotV.twistFieldT D h)
        (RatFunc ↥(Work.MotV.twistFieldT D h)) (twCoordF 𝕜 D h j)) hy i j
  have hkey := kleinTwSDualInv_rulingPt_eq_zero
      (algebraMap ↥(Work.MotV.twistFieldT D h) (RatFunc ↥(Work.MotV.twistFieldT D h))
        (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.a))
      (algebraMap ↥(Work.MotV.twistFieldT D h) (RatFunc ↥(Work.MotV.twistFieldT D h))
        (algebraMap 𝕜 ↥(Work.MotV.twistFieldT D h) D.b))
      (algebraMap ↥(Work.MotV.twistFieldT D h) (RatFunc ↥(Work.MotV.twistFieldT D h))
        (algebraMap (RatFunc 𝕜) ↥(Work.MotV.twistFieldT D h) h))
      (1 : RatFunc ↥(Work.MotV.twistFieldT D h)) RatFunc.X
      (fun j => algebraMap ↥(Work.MotV.twistFieldT D h)
        (RatFunc ↥(Work.MotV.twistFieldT D h)) (twCoordF 𝕜 D h j)) hy hR hy0
  rw [ha, hb, hh'] at hkey
  exact hkey

end Work.MotK
