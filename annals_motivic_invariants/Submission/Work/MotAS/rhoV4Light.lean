import Mathlib
import Submission.Work.MotAS.SdualAS2Defs
import Submission.Work.MotAS.AsCoeff6Defs
import Submission.Work.MotAS.asRulingEval
import Submission.Work.MotAS.asY0_curve
import Submission.Work.MotAS.ASChart3.asTwY_mem_span
import Submission.Work.MotAS.ASChart3.sdBas_mem_span_asTwY
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.MotAS.asRuleMinP_isHomogeneous
import Submission.Work.MotAS.map_asRuleQW
import Submission.Work.MotAS.ASI1Ratio
import Submission.Work.MotAS.aeval_asCoeff6
import Submission.Work.MotAS.asCoeff6_aeval_smul
import Submission.Work.MotAS.asCoeff6_isHomogeneous
import Submission.Work.MotAS.kleinRAS0_asRuleQA_notMem_asIdeal6
import Submission.Work.MotAS.asPhi2_denom
import Submission.Work.MotAS.asKernel6

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.RhoL2.asRuleQW_kleinRAS_ne_zero`

The inverse AS quadro-cubic map `kleinRAS` does not vanish on the ruling line
`asRuleQW a b g c t` over the generic point `c = asY0 D g` of the AS-twisted Klein curve.

## Route

* `asRuleQW a b g c t = A(c) + t·B(c)` with `A = asRuleQA`, `B = asRuleQB` quadratic in `c`
  (`SdualAS2Defs.lean`), so `kleinRAS0 (asRuleQW a b g c t)` is a polynomial of degree `≤ 3` in
  `t`; it suffices to produce one `j` whose `t^j`-coefficient is nonzero.
* The `t^j`-coefficient is `aeval c (asCoeff6 j)` (`aeval_asCoeff6`), where `asCoeff6`
  (`AsCoeff6Defs.lean`) are the degree-6 coefficient forms.
* `asCoeff6` is homogeneous of degree `6` (`asCoeff6_aeval_smul`) and natural in the coefficient
  ring (`map_asCoeff6`); together with `asY0 = asTwY / (asTwY 0)` this carries the non-vanishing of
  one coefficient from the Galois coordinates `asTwY` in `Om D` down to the twist field.
* The non-vanishing in `Om D` is `asCoeff6_notMem` (one of the four forms lies outside the
  degree-6 part of the Pfaffian ideal) together with the kernel statement `asKernel6`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 800000

namespace Work.MotAS.RhoL2

open MvPolynomial

variable {S : Type*} [CommRing S]

/-! ## §1  Naturality of the ruling expression -/

/-- **Naturality of the degree-6 coefficient forms** in the coefficient ring. -/
theorem map_asCoeff6 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b g : R) (j : ℕ) :
    MvPolynomial.map φ (asCoeff6 R a b g j) = asCoeff6 S (φ a) (φ b) (φ g) j := by
  have hA : ∀ k : Fin 5, MvPolynomial.map φ (qAS_A R a b g k)
      = qAS_A S (φ a) (φ b) (φ g) k := by
    intro k
    refine (map_asRuleQA (MvPolynomial.map φ) (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C g) (fun i => MvPolynomial.X i) k).trans ?_
    simp only [qAS_A, MvPolynomial.map_C, MvPolynomial.map_X]
  have hB : ∀ k : Fin 5, MvPolynomial.map φ (qAS_B R a b g k)
      = qAS_B S (φ a) (φ b) (φ g) k := by
    intro k
    refine (map_asRuleQB (MvPolynomial.map φ) (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C g) (fun i => MvPolynomial.X i) k).trans ?_
    simp only [qAS_B, MvPolynomial.map_C, MvPolynomial.map_X]
  have hpoly : (asCoeffPoly R a b g).map (MvPolynomial.map φ)
      = asCoeffPoly S (φ a) (φ b) (φ g) := by
    show Polynomial.mapRingHom (MvPolynomial.map φ) (asCoeffPoly R a b g)
      = asCoeffPoly S (φ a) (φ b) (φ g)
    rw [asCoeffPoly, asCoeffPoly]
    rw [← map_kleinRAS0 (Polynomial.mapRingHom (MvPolynomial.map φ))
      (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
      (Polynomial.C (MvPolynomial.C g))
      (fun k => Polynomial.C (qAS_A R a b g k) + Polynomial.X * Polynomial.C (qAS_B R a b g k))]
    have hv : (fun k => (Polynomial.mapRingHom (MvPolynomial.map φ))
          ((fun k => Polynomial.C (qAS_A R a b g k)
            + Polynomial.X * Polynomial.C (qAS_B R a b g k)) k))
        = fun k => Polynomial.C (qAS_A S (φ a) (φ b) (φ g) k)
            + Polynomial.X * Polynomial.C (qAS_B S (φ a) (φ b) (φ g) k) := by
      funext k
      simp only [Polynomial.coe_mapRingHom, map_add, map_mul, Polynomial.map_C,
        Polynomial.map_X, hA k, hB k]
    rw [hv]
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_C, MvPolynomial.map_C]
  have hmap : MvPolynomial.map φ ((asCoeffPoly R a b g).coeff j)
      = ((asCoeffPoly R a b g).map (MvPolynomial.map φ)).coeff j := by
    rw [Polynomial.coeff_map]
  exact (hmap.trans (congrArg (fun p => p.coeff j) hpoly))

/-- Evaluation of the abstract polynomial `R^AS_0(A + T·B)` under a coefficient map. -/
theorem eval₂_asCoeffPoly {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T) (a b g : R)
    (c : Fin 5 → R) (t : T) :
    (kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
        (fun k => Polynomial.C (asRuleQA a b g c k)
          + Polynomial.X * Polynomial.C (asRuleQB a b g c k))).eval₂ φ t
      = kleinRAS0 (φ a) (φ b) (φ g)
          (fun k => φ (asRuleQA a b g c k) + t * φ (asRuleQB a b g c k)) := by
  have h := map_kleinRAS0 (Polynomial.eval₂RingHom φ t)
    (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
    (fun k => Polynomial.C (asRuleQA a b g c k)
      + Polynomial.X * Polynomial.C (asRuleQB a b g c k))
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_X] at h
  exact h.symm

/-- The same identity over a single ring. -/
theorem eval_asCoeffPoly (a b g : S) (c : Fin 5 → S) (t : S) :
    (kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
        (fun k => Polynomial.C (asRuleQA a b g c k)
          + Polynomial.X * Polynomial.C (asRuleQB a b g c k))).eval t
      = kleinRAS0 a b g (fun k => asRuleQA a b g c k + t * asRuleQB a b g c k) := by
  have h := eval₂_asCoeffPoly (RingHom.id S) a b g c t
  simpa only [RingHom.id_apply, Polynomial.eval₂_id] using h

/-- Naturality of the whole ruling expression under a ring homomorphism. -/
theorem map_kleinRAS0_asRuleQW {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (c : Fin 5 → R) (t : R) :
    kleinRAS0 (φ a) (φ b) (φ g)
      (fun k => asRuleQA (φ a) (φ b) (φ g) (fun i => φ (c i)) k
        + φ t * asRuleQB (φ a) (φ b) (φ g) (fun i => φ (c i)) k)
      = φ (kleinRAS0 a b g (fun k => asRuleQA a b g c k + t * asRuleQB a b g c k)) := by
  rw [← map_kleinRAS0 φ a b g (fun k => asRuleQA a b g c k + t * asRuleQB a b g c k)]
  congr 1
  funext k
  rw [map_add, map_mul, map_asRuleQA, map_asRuleQB]

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- For `P : K[X]`, evaluation at `RatFunc.X` is the canonical image in the fraction field. -/
theorem eval₂_eq_algebraMap_poly (K : Type*) [Field K] (P : Polynomial K) :
    P.eval₂ (algebraMap K (RatFunc K)) (RatFunc.X : RatFunc K)
      = algebraMap (Polynomial K) (RatFunc K) P := by
  have h : (Polynomial.eval₂RingHom (algebraMap K (RatFunc K)) (RatFunc.X : RatFunc K))
      = algebraMap (Polynomial K) (RatFunc K) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · show Polynomial.eval₂ (algebraMap K (RatFunc K)) (RatFunc.X : RatFunc K) (Polynomial.C a)
          = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a)
      rw [Polynomial.eval₂_C, Polynomial.C_eq_algebraMap,
        ← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) a]
    · show Polynomial.eval₂ (algebraMap K (RatFunc K)) (RatFunc.X : RatFunc K) Polynomial.X
          = algebraMap (Polynomial K) (RatFunc K) Polynomial.X
      rw [Polynomial.eval₂_X, RatFunc.algebraMap_X]
  have h2 := congrFun (congrArg DFunLike.coe h) P
  simpa using h2

/-- **Naturality of the ruling parametrisation.**  The point `asRuleQW a b g c t` of the ruling
line is sent by a ring homomorphism `φ` to the point obtained from `φ` applied to the coefficients
`A(c)`, `B(c)`. -/
theorem asRuleQW_vector_eq {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T)
    (a b g : R) (c : Fin 5 → R) (t : T) :
    asRuleQW (φ a) (φ b) (φ g) (fun i => φ (c i)) t
      = fun k => φ (asRuleQA a b g c k) + t * φ (asRuleQB a b g c k) := by
  funext k
  show asRuleQA (φ a) (φ b) (φ g) (fun i => φ (c i)) k
      + t * asRuleQB (φ a) (φ b) (φ g) (fun i => φ (c i)) k
    = φ (asRuleQA a b g c k) + t * φ (asRuleQB a b g c k)
  rw [← map_asRuleQA φ a b g c k, ← map_asRuleQB φ a b g c k]

/-- The `0`-th component of the inverse quadro-cubic map is `kleinRAS0`. -/
theorem kleinRAS_zero {R : Type*} [CommRing R] (a b g : R) (z : Fin 5 → R) :
    kleinRAS a b g z 0 = kleinRAS0 a b g z := rfl

/-- The value of `kleinRAS0` on the ruling line is the evaluation at `t` of the ruling polynomial
`R^AS_0(A + T·B)`. -/
theorem kleinRAS0_asRuleQW_eval₂ {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T)
    (a b g : R) (c : Fin 5 → R) (t : T) :
    kleinRAS0 (φ a) (φ b) (φ g) (asRuleQW (φ a) (φ b) (φ g) (fun i => φ (c i)) t)
      = (kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
          (fun k => Polynomial.C (asRuleQA a b g c k)
            + Polynomial.X * Polynomial.C (asRuleQB a b g c k))).eval₂ φ t := by
  rw [asRuleQW_vector_eq φ a b g c t]
  exact (eval₂_asCoeffPoly φ a b g c t).symm

/-! ## §2  The main theorem -/

theorem asRuleQW_kleinRAS_ne_zero (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    ∃ i : Fin 5,
      Work.MotAS.kleinRAS
        (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.a)
        (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.b)
        (algebraMap (RatFunc 𝕜) (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
          (Work.MotV.fAS 𝕜))
        (Work.MotAS.asRuleQW
          (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.a)
          (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.b)
          (algebraMap (RatFunc 𝕜) (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
            (Work.MotV.fAS 𝕜))
          (fun j => algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
            (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
            (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜) j))
          (RatFunc.X : RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))) i ≠ 0 := by
  classical
  set g : RatFunc 𝕜 := Work.MotV.fAS 𝕜 with hg
  set F : IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) := Work.MotAS.twistFieldAS D g with hF
  set aK : Work.MotV.Kb 𝕜 := algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a with haK
  set bK : Work.MotV.Kb 𝕜 := algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b with hbK
  set gK : Work.MotV.Kb 𝕜 := algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g with hgK
  have ha0 : D.a ≠ 0 := fun h => hD.1.ab_ne (by rw [h, zero_mul])
  have hb0 : D.b ≠ 0 := fun h => hD.1.ab_ne (by rw [h, mul_zero])
  have haK' : aK ≠ 0 := fun h =>
    ha0 (RingHom.injective (algebraMap 𝕜 (Work.MotV.Kb 𝕜)) (by rw [haK] at h; simpa using h))
  have hbK' : bK ≠ 0 := fun h =>
    hb0 (RingHom.injective (algebraMap 𝕜 (Work.MotV.Kb 𝕜)) (by rw [hbK] at h; simpa using h))
  have hαK : aK ^ 2 - aK * bK - bK ^ 2 ≠ 0 := by
    intro h
    apply hD.2.2.2
    apply RingHom.injective (algebraMap 𝕜 (Work.MotV.Kb 𝕜))
    rw [haK, hbK] at h
    rw [map_sub, map_sub, map_mul, map_pow, map_pow, h, map_zero]
  -- the crux: one of the four coefficient forms is outside the degree-6 ideal, hence does not
  -- vanish at the Galois coordinates `asTwY`
  obtain ⟨j, hj⟩ : ∃ j : ℕ, Work.MotAS.asCoeff6 (Work.MotV.Kb 𝕜) aK bK gK j
      ∉ Work.MotAS.asIdeal6 (Work.MotV.Kb 𝕜) aK bK gK :=
    ⟨0, by
      intro hmem
      refine Work.MotAS.kleinRAS0_asRuleQA_notMem_asIdeal6 (Work.MotV.Kb 𝕜) aK bK gK
        haK' hbK' hαK ?_
      have hbridge : Work.MotAS.asCoeff6 (Work.MotV.Kb 𝕜) aK bK gK 0
          = Work.MotAS.kleinRAS0 (MvPolynomial.C aK) (MvPolynomial.C bK) (MvPolynomial.C gK)
              (Work.MotAS.asRuleQA (MvPolynomial.C aK) (MvPolynomial.C bK) (MvPolynomial.C gK)
                (fun i => MvPolynomial.X i)) := by
        have h := Work.MotAS.RhoL2.eval_asCoeffPoly (a := MvPolynomial.C aK)
          (b := MvPolynomial.C bK) (g := MvPolynomial.C gK)
          (c := fun i => MvPolynomial.X i)
          (t := (0 : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)))
        simp only [zero_mul, add_zero] at h
        rw [Work.MotAS.asCoeff6, Work.MotAS.asCoeffPoly, Polynomial.coeff_zero_eq_eval_zero]
        exact h
      rwa [hbridge] at hmem⟩
  have hhom : Work.MotAS.asCoeff6 (Work.MotV.Kb 𝕜) aK bK gK j
      ∈ MvPolynomial.homogeneousSubmodule (Fin 5) (Work.MotV.Kb 𝕜) 6 :=
    Work.MotAS.asCoeff6_isHomogeneous aK bK gK j
  have hcrux : MvPolynomial.aeval (Work.MotAS.asTwY D g)
      (Work.MotAS.asCoeff6 (Work.MotV.Kb 𝕜) aK bK gK j) ≠ 0 := by
    intro h0
    exact hj (Work.MotAS.asKernel6 𝕜 D hD g (Work.MotAS.asCoeff6 (Work.MotV.Kb 𝕜) aK bK gK j)
      hhom h0)
  -- the same non-vanishing with coefficients pushed to `Om D`
  have hmapL : MvPolynomial.map (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D))
      (Work.MotAS.asCoeff6 (Work.MotV.Kb 𝕜) aK bK gK j)
      = Work.MotAS.asCoeff6 (Work.MotV.Om D) (algebraMap 𝕜 (Work.MotV.Om D) D.a)
          (algebraMap 𝕜 (Work.MotV.Om D) D.b)
          (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g) j := by
    rw [Work.MotAS.RhoL2.map_asCoeff6]
    have h1 : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) aK
        = algebraMap 𝕜 (Work.MotV.Om D) D.a := by
      rw [haK]
      exact IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.a
    have h2 : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) bK
        = algebraMap 𝕜 (Work.MotV.Om D) D.b := by
      rw [hbK]
      exact IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.b
    have h3 : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) gK
        = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g := by
      rw [hgK]
      exact IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) g
    rw [h1, h2, h3]
  have hpush : MvPolynomial.aeval (Work.MotAS.asTwY D g)
      (Work.MotAS.asCoeff6 (Work.MotV.Om D) (algebraMap 𝕜 (Work.MotV.Om D) D.a)
        (algebraMap 𝕜 (Work.MotV.Om D) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g) j) ≠ 0 := by
    rw [← hmapL]
    simp only [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval₂Hom_map_hom,
      Algebra.algebraMap_self, RingHom.id_comp]
    simpa only [MvPolynomial.aeval_eq_eval₂Hom] using hcrux
  -- the point `asY0` in `Om D` is the normalisation of `asTwY`
  have hpt : (fun i => algebraMap ↥F (Work.MotV.Om D) (Work.MotAS.asY0 D g i))
      = fun i => (Work.MotAS.asTwY D g 0)⁻¹ * Work.MotAS.asTwY D g i := by
    funext i
    show Work.MotAS.asTwY D g i / Work.MotAS.asTwY D g 0 = _
    rw [div_eq_mul_inv, mul_comm]
  -- the `j`-th coefficient at the normalised point in `Om D`
  have hcoeffL : MvPolynomial.aeval
      (fun i => algebraMap ↥F (Work.MotV.Om D) (Work.MotAS.asY0 D g i))
      (Work.MotAS.asCoeff6 (Work.MotV.Om D) (algebraMap 𝕜 (Work.MotV.Om D) D.a)
        (algebraMap 𝕜 (Work.MotV.Om D) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g) j) ≠ 0 := by
    rw [hpt, Work.MotAS.asCoeff6_aeval_smul]
    exact mul_ne_zero (pow_ne_zero 6
      (inv_ne_zero (Work.MotAS.asTwY_zero_ne_zero D g hD.1))) hpush
  -- the same coefficient computed in the twist field
  have hmapF : MvPolynomial.map (algebraMap ↥F (Work.MotV.Om D))
      (Work.MotAS.asCoeff6 ↥F (algebraMap 𝕜 ↥F D.a) (algebraMap 𝕜 ↥F D.b)
        (algebraMap (RatFunc 𝕜) ↥F g) j)
      = Work.MotAS.asCoeff6 (Work.MotV.Om D) (algebraMap 𝕜 (Work.MotV.Om D) D.a)
          (algebraMap 𝕜 (Work.MotV.Om D) D.b)
          (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g) j := by
    rw [Work.MotAS.RhoL2.map_asCoeff6]
    have h1 : algebraMap ↥F (Work.MotV.Om D) (algebraMap 𝕜 ↥F D.a)
        = algebraMap 𝕜 (Work.MotV.Om D) D.a := by
      first
        | rfl
        | simp only [IntermediateField.algebraMap_apply, Subalgebra.coe_algebraMap]
    have h2 : algebraMap ↥F (Work.MotV.Om D) (algebraMap 𝕜 ↥F D.b)
        = algebraMap 𝕜 (Work.MotV.Om D) D.b := by
      first
        | rfl
        | simp only [IntermediateField.algebraMap_apply, Subalgebra.coe_algebraMap]
    have h3 : algebraMap ↥F (Work.MotV.Om D) (algebraMap (RatFunc 𝕜) ↥F g)
        = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g := by
      first
        | rfl
        | simp only [IntermediateField.algebraMap_apply, IntermediateField.coe_algebraMap_apply]
    rw [h1, h2, h3]
  have hnat : MvPolynomial.aeval
      (fun i => algebraMap ↥F (Work.MotV.Om D) (Work.MotAS.asY0 D g i))
      (Work.MotAS.asCoeff6 (Work.MotV.Om D) (algebraMap 𝕜 (Work.MotV.Om D) D.a)
        (algebraMap 𝕜 (Work.MotV.Om D) D.b)
        (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g) j)
      = algebraMap ↥F (Work.MotV.Om D)
          (MvPolynomial.aeval (Work.MotAS.asY0 D g)
            (Work.MotAS.asCoeff6 ↥F (algebraMap 𝕜 ↥F D.a) (algebraMap 𝕜 ↥F D.b)
              (algebraMap (RatFunc 𝕜) ↥F g) j)) := by
    rw [← hmapF]
    rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval₂Hom_map_hom,
      Algebra.algebraMap_self, RingHom.id_comp]
    rw [MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self,
      MvPolynomial.map_eval₂Hom (RingHom.id ↥F) (Work.MotAS.asY0 D g)
        (algebraMap ↥F (Work.MotV.Om D))
        (Work.MotAS.asCoeff6 ↥F (algebraMap 𝕜 ↥F D.a) (algebraMap 𝕜 ↥F D.b)
          (algebraMap (RatFunc 𝕜) ↥F g) j)]
    rw [RingHom.comp_id]
    try rfl
  have hcoeffF : MvPolynomial.aeval (Work.MotAS.asY0 D g)
      (Work.MotAS.asCoeff6 ↥F (algebraMap 𝕜 ↥F D.a) (algebraMap 𝕜 ↥F D.b)
        (algebraMap (RatFunc 𝕜) ↥F g) j) ≠ 0 := by
    intro h0
    apply hcoeffL
    rw [hnat, h0]
    simp
  -- the value of the ruling point in the twist field is the canonical image of a nonzero polynomial
  refine ⟨0, ?_⟩
  have hA : algebraMap 𝕜 (RatFunc ↥F) D.a
      = algebraMap ↥F (RatFunc ↥F) (algebraMap 𝕜 ↥F D.a) :=
    IsScalarTower.algebraMap_apply 𝕜 ↥F (RatFunc ↥F) D.a
  have hB : algebraMap 𝕜 (RatFunc ↥F) D.b
      = algebraMap ↥F (RatFunc ↥F) (algebraMap 𝕜 ↥F D.b) :=
    IsScalarTower.algebraMap_apply 𝕜 ↥F (RatFunc ↥F) D.b
  have hG : algebraMap (RatFunc 𝕜) (RatFunc ↥F) g
      = algebraMap ↥F (RatFunc ↥F) (algebraMap (RatFunc 𝕜) ↥F g) :=
    IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥F (RatFunc ↥F) g
  rw [hA, hB, hG]
  rw [Work.MotAS.RhoL2.kleinRAS_zero]
  rw [Work.MotAS.RhoL2.kleinRAS0_asRuleQW_eval₂ (φ := algebraMap ↥F (RatFunc ↥F))
    (a := algebraMap 𝕜 ↥F D.a) (b := algebraMap 𝕜 ↥F D.b)
    (g := algebraMap (RatFunc 𝕜) ↥F g) (c := Work.MotAS.asY0 D g)
    (t := (RatFunc.X : RatFunc ↥F))]
  set P : Polynomial ↥F :=
    Work.MotAS.kleinRAS0 (Polynomial.C (algebraMap 𝕜 ↥F D.a)) (Polynomial.C (algebraMap 𝕜 ↥F D.b))
      (Polynomial.C (algebraMap (RatFunc 𝕜) ↥F g))
      (fun k => Polynomial.C (Work.MotAS.asRuleQA (algebraMap 𝕜 ↥F D.a) (algebraMap 𝕜 ↥F D.b)
          (algebraMap (RatFunc 𝕜) ↥F g) (Work.MotAS.asY0 D g) k)
        + Polynomial.X * Polynomial.C (Work.MotAS.asRuleQB (algebraMap 𝕜 ↥F D.a)
          (algebraMap 𝕜 ↥F D.b) (algebraMap (RatFunc 𝕜) ↥F g) (Work.MotAS.asY0 D g) k)) with hP
  have hcoeff_eq : P.coeff j = MvPolynomial.aeval (Work.MotAS.asY0 D g)
      (Work.MotAS.asCoeff6 ↥F (algebraMap 𝕜 ↥F D.a) (algebraMap 𝕜 ↥F D.b)
        (algebraMap (RatFunc 𝕜) ↥F g) j) := by
    rw [hP]
    exact (Work.MotAS.aeval_asCoeff6 (algebraMap 𝕜 ↥F D.a) (algebraMap 𝕜 ↥F D.b)
      (algebraMap (RatFunc 𝕜) ↥F g) (Work.MotAS.asY0 D g) j).symm
  have hPF : P ≠ 0 := by
    intro h0
    exact hcoeffF (by rw [← hcoeff_eq, h0]; simp)
  rw [Work.MotAS.RhoL2.eval₂_eq_algebraMap_poly ↥F P]
  intro hh
  refine hPF ?_
  apply IsFractionRing.injective (Polynomial ↥F) (RatFunc ↥F)
  rw [hh]
  exact (map_zero (algebraMap (Polynomial ↥F) (RatFunc ↥F))).symm

/-! ## The normalised non-vanishing on the ruling point -/

/-- **The normalised form**: `kleinRAS` does not vanish on the ruling point `W / W 0` over the
generic point `asY0` of the asymptotically-twisted Klein curve.  This is the `hrho` input of the
fraction-field assembly. -/
theorem asPhi2_rho_ne_zeroLight (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    Work.MotAS.kleinRAS
      (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.a)
      (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.b)
      (algebraMap (RatFunc 𝕜) (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
        (Work.MotV.fAS 𝕜))
      (fun j =>
        (Work.MotAS.asRuleQW
          (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.a)
          (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.b)
          (algebraMap (RatFunc 𝕜) (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
            (Work.MotV.fAS 𝕜))
          (fun i => algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
            (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
            (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜) i))
          (RatFunc.X : RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))) j
        / (Work.MotAS.asRuleQW
          (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.a)
          (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.b)
          (algebraMap (RatFunc 𝕜) (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
            (Work.MotV.fAS 𝕜))
          (fun i => algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
            (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
            (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜) i))
          (RatFunc.X : RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))) 0) ≠ 0 := by
  classical
  let R := RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
  let A : R := algebraMap 𝕜 R D.a
  let B : R := algebraMap 𝕜 R D.b
  let G : R := algebraMap (RatFunc 𝕜) R (Work.MotV.fAS 𝕜)
  let c : Fin 5 → R := fun i => algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) R
    (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜) i)
  let W : Fin 5 → R := Work.MotAS.asRuleQW A B G c (RatFunc.X : R)
  change Work.MotAS.kleinRAS A B G (fun j => W j / W 0) ≠ 0
  have hW0 : W 0 ≠ 0 := Work.MotAS.asPhi2_denom 𝕜 D hD
  have hV : Work.MotAS.kleinRAS A B G W ≠ 0 := by
    obtain ⟨i, hi⟩ := asRuleQW_kleinRAS_ne_zero 𝕜 D hD
    intro h
    exact hi (by rw [h]; rfl)
  rw [show (fun j => W j / W 0) = fun j => (W 0)⁻¹ * W j from by
    funext j; rw [div_eq_inv_mul]]
  rw [Work.MotAS.kleinRAS_smul]
  intro h
  apply hV
  funext k
  have hk := congrFun h k
  simp only [Pi.zero_apply] at hk
  exact (mul_eq_zero.mp hk).resolve_left (pow_ne_zero 3 (inv_ne_zero hW0))

end Work.MotAS.RhoL2
