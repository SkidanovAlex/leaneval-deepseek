import Mathlib
import Submission.Work.MotC5N3.Ruling
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.asY0_curve
import Submission.Work.MotC5N3.twistFieldAS_eq
import Submission.Work.MotC5N3.KerAevalKleinPASGenAlt
import Submission.Work.MotAS.asCoeff6_isHomogeneous
import Submission.Work.MotAS.asCoeff6_aeval_smul
import Submission.Work.MotAS.aeval_asCoeff6
import Submission.Work.MotAS.aeval_asCoeff6_expansion
import Submission.Work.MotAS.map_asCoeff6
import Submission.Work.MotAS.mem_span_mul_monomial_of_mem_ideal_span
import Submission.Work.MotAS.Ker4.kleinPASm_isHomogeneous
import Submission.Work.MotAS.ASI1Ratio
import Submission.Work.MotAS.map_asRuleQW
import Submission.Work.MotC5N3.Work.KeyCert

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.Work.asRho_ne_zero_general_ne` — the chart-2 rho input for `g ≠ 0`

The assembly that turns the *certificate*

`∃ j, asCoeff6 K (aK K D) (bK K D) g j ∉ asIdeal6 K (aK K D) (bK K D) g`

into the non-vanishing of the inverse AS quadro-cubic map on the ruling line over the generic
curve point, over an arbitrary `𝕜`-algebra field `K` of characteristic `5`.

## The route

1. `Work.MotAS.mem_span_mul_monomial_of_mem_ideal_span` upgrades the certificate to
   non-membership in the full Pfaffian ideal `I = (kleinPASm (aK) (bK) g)` (the form is
   homogeneous of degree `6`, and `asIdeal6` is the degree-`6` part of `I`).
2. `Work.MotC5N3.kerAevalKleinPASGenAlt` (the transported Klein kernel statement, proved) turns
   that into `aeval (asTwY D g) (asCoeff6 K (aK) (bK) g j) ≠ 0` in `OmA K D`.
3. Naturality (`Work.MotAS.map_asCoeff6`) pushes the coefficients from `K` to `OmA K D`, and
   `Work.MotAS.asCoeff6_aeval_smul` (the degree-`6` dilation law) normalises the evaluation point
   to `asTwY D g i / asTwY D g 0`.  Hence the `j`-th coefficient of the cubic
   `kleinRAS0 (C a) (C b) (C g) (asRuleQW a b g c X)` over `OmA K D`, at `c = asTwY/asTwY 0`,
   is nonzero: that polynomial is nonzero.
4. It descends to the twist field `F = twistFieldAS D g`: the map `↥F → OmA K D` is injective and
   `Polynomial.map` of an injective ring hom is injective, so the corresponding polynomial over
   `↥F` is nonzero too.
5. Evaluating at `RatFunc.X` over `R = RatFunc ↥F` (via the naturality
   `kleinRAS0_asRuleQW_eval₂` and `eval₂_eq_algebraMap_poly`) gives the `0`-th component of
   `kleinRAS (as2a D g) (as2b D g) (as2g D g) (asW2 D g)` as the image of a nonzero polynomial,
   whence the vector is nonzero.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 1000000

namespace Work.MotC5N3.Work

open MvPolynomial

/-! ## §1  Elementary bookkeeping lemmas -/

/-- Component `0` of `kleinRAS` is the cubic form `kleinRAS0`. -/
private theorem kleinRAS_zero' {R : Type*} [CommRing R] (a b g : R) (z : Fin 5 → R) :
    Work.MotAS.kleinRAS a b g z 0 = Work.MotAS.kleinRAS0 a b g z := rfl

/-- Evaluation at `RatFunc.X` is the canonical image of the polynomial. -/
private theorem eval₂_eq_algebraMap_poly (L : Type*) [Field L] (P : Polynomial L) :
    P.eval₂ (algebraMap L (RatFunc L)) (RatFunc.X : RatFunc L)
      = algebraMap (Polynomial L) (RatFunc L) P := by
  have h : (Polynomial.eval₂RingHom (algebraMap L (RatFunc L)) (RatFunc.X : RatFunc L))
      = algebraMap (Polynomial L) (RatFunc L) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · show Polynomial.eval₂ (algebraMap L (RatFunc L)) (RatFunc.X : RatFunc L) (Polynomial.C a)
          = algebraMap (Polynomial L) (RatFunc L) (Polynomial.C a)
      rw [Polynomial.eval₂_C, Polynomial.C_eq_algebraMap,
        ← IsScalarTower.algebraMap_apply L (Polynomial L) (RatFunc L) a]
    · show Polynomial.eval₂ (algebraMap L (RatFunc L)) (RatFunc.X : RatFunc L) Polynomial.X
          = algebraMap (Polynomial L) (RatFunc L) Polynomial.X
      rw [Polynomial.eval₂_X, RatFunc.algebraMap_X]
  have h2 := congrFun (congrArg DFunLike.coe h) P
  simpa using h2

/-- Naturality of `kleinRAS0` over a polynomial ring (coefficient form). -/
private theorem map_kleinRAS0_poly {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (z : Fin 5 → Polynomial R) :
    Polynomial.map φ (Work.MotAS.kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g) z)
      = Work.MotAS.kleinRAS0 (Polynomial.C (φ a)) (Polynomial.C (φ b)) (Polynomial.C (φ g))
          (fun k => Polynomial.map φ (z k)) := by
  have h := Work.MotAS.map_kleinRAS0 (R := Polynomial R) (S := Polynomial S)
    (Polynomial.mapRingHom φ) (Polynomial.C a) (Polynomial.C b) (Polynomial.C g) z
  simpa only [Polynomial.coe_mapRingHom, Polynomial.map_C] using h.symm

/-- The value of `kleinRAS0` on a ruling point `A(c) + t·B(c)`, as the evaluation of a
polynomial in `T`. -/
private theorem kleinRAS0_asRuleQW_eval₂ {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T)
    (a b g : R) (c : Fin 5 → R) (t : T) :
    Work.MotAS.kleinRAS0 (φ a) (φ b) (φ g)
        (Work.MotAS.asRuleQW (φ a) (φ b) (φ g) (fun i => φ (c i)) t)
      = (Work.MotAS.kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
          (fun k => Polynomial.C (Work.MotAS.asRuleQA a b g c k)
            + Polynomial.X * Polynomial.C (Work.MotAS.asRuleQB a b g c k))).eval₂ φ t := by
  have key : Work.MotAS.asRuleQW (φ a) (φ b) (φ g) (fun i => φ (c i)) t
      = fun k => φ (Work.MotAS.asRuleQA a b g c k) + t * φ (Work.MotAS.asRuleQB a b g c k) := by
    funext k
    simp only [Work.MotAS.asRuleQW]
    rw [Work.MotAS.map_asRuleQA φ a b g c k, Work.MotAS.map_asRuleQB φ a b g c k]
  rw [key]
  have h := Work.MotAS.map_kleinRAS0 (Polynomial.eval₂RingHom φ t)
    (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
    (fun k => Polynomial.C (Work.MotAS.asRuleQA a b g c k)
      + Polynomial.X * Polynomial.C (Work.MotAS.asRuleQB a b g c k))
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_X] at h
  exact h

/-! ## §2  From an `asRhoPoly`-certificate to the `asCoeff6`-certificate -/

/-- The degree-`6` part of the AS Pfaffian ideal is contained in the ideal. -/
private theorem asIdeal6_le_span_gen (K : Type) [CommRing K] (a b g : K) :
    Work.MotAS.asIdeal6 K a b g ≤
      (Ideal.span (Set.range (Work.MotAS.kleinPASm (K := K) a b g))).restrictScalars K := by
  rw [Work.MotAS.asIdeal6]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨q, hq⟩
  rw [← hq]
  have h1 : Work.MotAS.kleinPASm (K := K) a b g q.1 ∈
      Ideal.span (Set.range (Work.MotAS.kleinPASm (K := K) a b g)) :=
    Ideal.subset_span ⟨q.1, rfl⟩
  exact Ideal.mul_mem_right
    (I := Ideal.span (Set.range (Work.MotAS.kleinPASm (K := K) a b g)))
    (monomial q.2.1 1) h1

/-- `asRhoPoly` is the sum of the four degree-`6` coefficient forms. -/
private theorem asRhoPoly_eq_sum_asCoeff6 (K : Type) [CommRing K] (a b g : K) :
    Work.MotAS.asRhoPoly K a b g = ∑ j ∈ Finset.range 4, Work.MotAS.asCoeff6 K a b g j := by
  have h := Work.MotAS.aeval_asCoeff6_expansion (R := K) (A := MvPolynomial (Fin 5) K) a b g
    (fun i => MvPolynomial.X i) (1 : MvPolynomial (Fin 5) K)
  simp only [MvPolynomial.algebraMap_eq] at h
  simp only [MvPolynomial.aeval_X_left_apply, one_pow, mul_one] at h
  simpa only [Work.MotAS.asRhoPoly] using h

/-- From the non-membership of `asRhoPoly` in the Pfaffian ideal, one of the four coefficient
forms is outside the degree-`6` part. -/
private theorem cert_of_notMem (K : Type) [Field K] (a b g : K)
    (h : Work.MotAS.asRhoPoly K a b g ∉
      Ideal.span (Set.range (Work.MotAS.kleinPASm (K := K) a b g))) :
    ∃ j : ℕ, Work.MotAS.asCoeff6 K a b g j ∉ Work.MotAS.asIdeal6 K a b g := by
  by_contra hcon
  push_neg at hcon
  refine h ?_
  have hsum : (∑ j ∈ Finset.range 4, Work.MotAS.asCoeff6 K a b g j) ∈
      Work.MotAS.asIdeal6 K a b g :=
    Submodule.sum_mem _ fun j _ => hcon j
  rw [asRhoPoly_eq_sum_asCoeff6 K a b g]
  exact asIdeal6_le_span_gen K a b g hsum

/-! ## §3  The assembly -/

/-- The chart-2 rho input, given the degree-`6` certificate over `K`. -/
theorem asRho_of_certificate (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hcert : ∃ j : ℕ, Work.MotAS.asCoeff6 K (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g j ∉
      Work.MotAS.asIdeal6 K (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g) :
    ∃ i : Fin 5, Work.MotAS.kleinRAS (Work.MotC5N3.as2a D g) (Work.MotC5N3.as2b D g)
      (Work.MotC5N3.as2g D g) (Work.MotC5N3.asW2 D g) i ≠ 0 := by
  classical
  haveI : CharP 𝕜 5 := Work.MotC5N3.charP_of_algebra_charP_lemma (𝕜 := 𝕜) (K := K)
  have hDg : D.Good := hD.1
  obtain ⟨j, hj⟩ := hcert
  -- (1) the certificate upgraded to the full Pfaffian ideal
  have hFhom : (Work.MotAS.asCoeff6 K (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g j).IsHomogeneous 6 :=
    Work.MotAS.asCoeff6_isHomogeneous (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g j
  have hj' : Work.MotAS.asCoeff6 K (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g j ∉
      Ideal.span (Set.range (Work.MotAS.kleinPASm (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g)) := by
    intro hmem
    refine hj ?_
    rw [Work.MotAS.asIdeal6]
    exact Work.MotAS.mem_span_mul_monomial_of_mem_ideal_span
      (p := Work.MotAS.kleinPASm (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g) (n := 6)
      (fun k => Work.MotAS.Ker4.kleinPASm_isHomogeneous K (Work.MotC5N3.aK K D)
        (Work.MotC5N3.bK K D) g k)
      hFhom hmem
  -- (2) the transported Klein kernel statement over `K`
  have hcrux : MvPolynomial.aeval (Work.MotC5N3.asTwY D g)
      (Work.MotAS.asCoeff6 K (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g j) ≠ 0 :=
    fun h0 => hj' (Work.MotC5N3.kerAevalKleinPASGenAlt K D hD g 6
      (Work.MotAS.asCoeff6 K (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g j)
      ((MvPolynomial.mem_homogeneousSubmodule 6 _).mpr hFhom) h0)
  -- (3) push the coefficients to `OmA K D`
  have hpush : MvPolynomial.aeval (Work.MotC5N3.asTwY D g)
      (Work.MotAS.asCoeff6 (Work.MotC5N3.OmA K D)
        (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.a)
        (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.b)
        (algebraMap K (Work.MotC5N3.OmA K D) g) j) ≠ 0 := by
    have hmapL : MvPolynomial.map (algebraMap K (Work.MotC5N3.OmA K D))
        (Work.MotAS.asCoeff6 K (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g j)
        = Work.MotAS.asCoeff6 (Work.MotC5N3.OmA K D)
            (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.a)
            (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.b)
            (algebraMap K (Work.MotC5N3.OmA K D) g) j := by
      rw [Work.MotAS.map_asCoeff6]
      have h1 : algebraMap K (Work.MotC5N3.OmA K D) (Work.MotC5N3.aK K D)
          = algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.a := by
        rw [Work.MotC5N3.aK]
        exact IsScalarTower.algebraMap_apply 𝕜 K (Work.MotC5N3.OmA K D) D.a
      have h2 : algebraMap K (Work.MotC5N3.OmA K D) (Work.MotC5N3.bK K D)
          = algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.b := by
        rw [Work.MotC5N3.bK]
        exact IsScalarTower.algebraMap_apply 𝕜 K (Work.MotC5N3.OmA K D) D.b
      rw [h1, h2]
    rw [← hmapL]
    simp only [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval₂Hom_map_hom,
      Algebra.algebraMap_self, RingHom.id_comp]
    simpa only [MvPolynomial.aeval_eq_eval₂Hom] using hcrux
  -- (4) normalise the evaluation point to `asTwY / asTwY 0`
  have hs : (Work.MotC5N3.asTwY D g 0) ≠ 0 := Work.MotC5N3.asTwY_zero_ne_zero D g hDg
  have hcs : MvPolynomial.aeval (fun i => (Work.MotC5N3.asTwY D g 0)⁻¹ * Work.MotC5N3.asTwY D g i)
      (Work.MotAS.asCoeff6 (Work.MotC5N3.OmA K D)
        (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.a)
        (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.b)
        (algebraMap K (Work.MotC5N3.OmA K D) g) j) ≠ 0 := by
    have h := Work.MotAS.asCoeff6_aeval_smul
      (a := algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.a)
      (b := algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.b)
      (g := algebraMap K (Work.MotC5N3.OmA K D) g)
      (s := (Work.MotC5N3.asTwY D g 0)⁻¹) (x := Work.MotC5N3.asTwY D g) (j := j)
    rw [h]
    exact mul_ne_zero (pow_ne_zero 6 (inv_ne_zero hs)) hpush
  -- (5) the twist field and the two polynomials
  set F : IntermediateField K (Work.MotC5N3.OmA K D) := Work.MotC5N3.twistFieldAS D g with hF
  have hcoe : ∀ x : ↥F, algebraMap ↥F (Work.MotC5N3.OmA K D) x = x.1 := fun x => rfl
  have hval : ∀ i : Fin 5, ((Work.MotC5N3.asY0 D g i : ↥F) : Work.MotC5N3.OmA K D)
      = Work.MotC5N3.asTwY D g i / Work.MotC5N3.asTwY D g 0 := fun i => rfl
  have hpt : (fun i => algebraMap ↥F (Work.MotC5N3.OmA K D) (Work.MotC5N3.asY0 D g i))
      = fun i => (Work.MotC5N3.asTwY D g 0)⁻¹ * Work.MotC5N3.asTwY D g i := by
    funext i
    rw [hcoe (Work.MotC5N3.asY0 D g i), hval i, div_eq_mul_inv, mul_comm]
  set aF : ↥F := algebraMap 𝕜 ↥F D.a with haF
  set bF : ↥F := algebraMap 𝕜 ↥F D.b with hbF
  set gF : ↥F := algebraMap K ↥F g with hgF
  have h1a : algebraMap ↥F (Work.MotC5N3.OmA K D) aF
      = algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.a := by
    rw [haF]
    calc algebraMap ↥F (Work.MotC5N3.OmA K D) (algebraMap 𝕜 ↥F D.a)
        = algebraMap ↥F (Work.MotC5N3.OmA K D)
            (algebraMap K ↥F (algebraMap 𝕜 K D.a)) := by
          rw [IsScalarTower.algebraMap_apply 𝕜 K ↥F D.a]
      _ = algebraMap K (Work.MotC5N3.OmA K D) (algebraMap 𝕜 K D.a) :=
          IsScalarTower.algebraMap_apply K ↥F (Work.MotC5N3.OmA K D) (algebraMap 𝕜 K D.a)
      _ = algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.a :=
          IsScalarTower.algebraMap_apply 𝕜 K (Work.MotC5N3.OmA K D) D.a
  have h1b : algebraMap ↥F (Work.MotC5N3.OmA K D) bF
      = algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.b := by
    rw [hbF]
    calc algebraMap ↥F (Work.MotC5N3.OmA K D) (algebraMap 𝕜 ↥F D.b)
        = algebraMap ↥F (Work.MotC5N3.OmA K D)
            (algebraMap K ↥F (algebraMap 𝕜 K D.b)) := by
          rw [IsScalarTower.algebraMap_apply 𝕜 K ↥F D.b]
      _ = algebraMap K (Work.MotC5N3.OmA K D) (algebraMap 𝕜 K D.b) :=
          IsScalarTower.algebraMap_apply K ↥F (Work.MotC5N3.OmA K D) (algebraMap 𝕜 K D.b)
      _ = algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.b :=
          IsScalarTower.algebraMap_apply 𝕜 K (Work.MotC5N3.OmA K D) D.b
  have h1g : algebraMap ↥F (Work.MotC5N3.OmA K D) gF
      = algebraMap K (Work.MotC5N3.OmA K D) g := by
    rw [hgF]
    exact IsScalarTower.algebraMap_apply K ↥F (Work.MotC5N3.OmA K D) g
  set cs : Fin 5 → Work.MotC5N3.OmA K D :=
    fun i => (Work.MotC5N3.asTwY D g 0)⁻¹ * Work.MotC5N3.asTwY D g i with hcsdef
  set P : Polynomial ↥F := Work.MotAS.kleinRAS0 (Polynomial.C aF) (Polynomial.C bF)
      (Polynomial.C gF)
      (fun k => Polynomial.C (Work.MotAS.asRuleQA aF bF gF (Work.MotC5N3.asY0 D g) k)
        + Polynomial.X * Polynomial.C (Work.MotAS.asRuleQB aF bF gF (Work.MotC5N3.asY0 D g) k))
    with hPdef
  set POm : Polynomial (Work.MotC5N3.OmA K D) :=
    Work.MotAS.kleinRAS0 (Polynomial.C (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.a))
      (Polynomial.C (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.b))
      (Polynomial.C (algebraMap K (Work.MotC5N3.OmA K D) g))
      (fun k => Polynomial.C (Work.MotAS.asRuleQA
          (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.a)
          (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.b)
          (algebraMap K (Work.MotC5N3.OmA K D) g) cs k)
        + Polynomial.X * Polynomial.C (Work.MotAS.asRuleQB
          (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.a)
          (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.b)
          (algebraMap K (Work.MotC5N3.OmA K D) g) cs k)) with hPOmdef
  -- (6) naturality of `P` under `↥F → OmA K D`
  have hPOm : Polynomial.map (algebraMap ↥F (Work.MotC5N3.OmA K D)) P = POm := by
    rw [hPdef, hPOmdef]
    rw [map_kleinRAS0_poly (algebraMap ↥F (Work.MotC5N3.OmA K D)) aF bF gF
      (fun k => Polynomial.C (Work.MotAS.asRuleQA aF bF gF (Work.MotC5N3.asY0 D g) k)
        + Polynomial.X * Polynomial.C (Work.MotAS.asRuleQB aF bF gF (Work.MotC5N3.asY0 D g) k))]
    have hfun : (fun k => Polynomial.map (algebraMap ↥F (Work.MotC5N3.OmA K D))
          (Polynomial.C (Work.MotAS.asRuleQA aF bF gF (Work.MotC5N3.asY0 D g) k)
            + Polynomial.X * Polynomial.C
                (Work.MotAS.asRuleQB aF bF gF (Work.MotC5N3.asY0 D g) k)))
        = fun k => Polynomial.C (Work.MotAS.asRuleQA
              (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.a)
              (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.b)
              (algebraMap K (Work.MotC5N3.OmA K D) g) cs k)
          + Polynomial.X * Polynomial.C (Work.MotAS.asRuleQB
              (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.a)
              (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.b)
              (algebraMap K (Work.MotC5N3.OmA K D) g) cs k) := by
      funext k
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
      rw [Work.MotAS.map_asRuleQA (algebraMap ↥F (Work.MotC5N3.OmA K D)) aF bF gF
            (Work.MotC5N3.asY0 D g) k,
          Work.MotAS.map_asRuleQB (algebraMap ↥F (Work.MotC5N3.OmA K D)) aF bF gF
            (Work.MotC5N3.asY0 D g) k,
          h1a, h1b, h1g, hpt]
    rw [hfun, h1a, h1b, h1g]
  -- (7) `POm` is nonzero, from the certificate
  have hne : POm ≠ 0 := by
    intro h0
    refine hcs ?_
    rw [Work.MotAS.aeval_asCoeff6 (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.a)
      (algebraMap 𝕜 (Work.MotC5N3.OmA K D) D.b) (algebraMap K (Work.MotC5N3.OmA K D) g) cs j]
    exact (show POm.coeff j = 0 from by rw [h0]; simp)
  have hPne : P ≠ 0 := by
    intro h0
    exact hne (by rw [← hPOm, h0, Polynomial.map_zero])
  -- (8) the final evaluation over `RatFunc ↥F`
  have htower_a : algebraMap 𝕜 (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) D.a
      = algebraMap ↥(Work.MotC5N3.twistFieldAS D g)
          (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) aF := by
    rw [haF]
    exact IsScalarTower.algebraMap_apply 𝕜 ↥(Work.MotC5N3.twistFieldAS D g)
      (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) D.a
  have htower_b : algebraMap 𝕜 (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) D.b
      = algebraMap ↥(Work.MotC5N3.twistFieldAS D g)
          (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) bF := by
    rw [hbF]
    exact IsScalarTower.algebraMap_apply 𝕜 ↥(Work.MotC5N3.twistFieldAS D g)
      (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) D.b
  have htower_g : algebraMap K (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) g
      = algebraMap ↥(Work.MotC5N3.twistFieldAS D g)
          (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) gF := by
    rw [hgF]
    exact IsScalarTower.algebraMap_apply K ↥(Work.MotC5N3.twistFieldAS D g)
      (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) g
  have hfinal : Work.MotAS.kleinRAS0 (algebraMap ↥F (RatFunc ↥F) aF)
      (algebraMap ↥F (RatFunc ↥F) bF) (algebraMap ↥F (RatFunc ↥F) gF)
      (Work.MotAS.asRuleQW (algebraMap ↥F (RatFunc ↥F) aF) (algebraMap ↥F (RatFunc ↥F) bF)
        (algebraMap ↥F (RatFunc ↥F) gF)
        (fun i => algebraMap ↥F (RatFunc ↥F) (Work.MotC5N3.asY0 D g i))
        (RatFunc.X : RatFunc ↥F)) ≠ 0 := by
    rw [kleinRAS0_asRuleQW_eval₂ (φ := algebraMap ↥F (RatFunc ↥F)) (a := aF) (b := bF) (g := gF)
      (c := Work.MotC5N3.asY0 D g) (t := (RatFunc.X : RatFunc ↥F))]
    rw [← hPdef]
    rw [eval₂_eq_algebraMap_poly ↥F P]
    intro hh
    exact hPne (IsFractionRing.injective (Polynomial ↥F) (RatFunc ↥F) (by rw [hh, map_zero]))
  refine ⟨0, ?_⟩
  rw [kleinRAS_zero']
  unfold Work.MotC5N3.as2a Work.MotC5N3.as2b Work.MotC5N3.as2g Work.MotC5N3.asW2
    Work.MotC5N3.as2A Work.MotC5N3.as2c
  rw [htower_a, htower_b, htower_g]
  exact hfinal


/-- **The chart-2 rho input for `g ≠ 0`.** -/
theorem asRho_ne_zero_general_ne (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : g ≠ 0) :
    ∃ i : Fin 5, Work.MotAS.kleinRAS (Work.MotC5N3.as2a D g) (Work.MotC5N3.as2b D g)
      (Work.MotC5N3.as2g D g) (Work.MotC5N3.asW2 D g) i ≠ 0 := by
  exact asRho_of_certificate K D hD g
    (cert_of_notMem K (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g
      (Work.MotC5N3.Work.asRhoPoly_notMem_span_gen K (Work.MotC5N3.aK K D)
        (Work.MotC5N3.bK K D) g (Work.MotC5N3.aK_ne_zero (K := K) D hD)
        (Work.MotC5N3.bK_ne_zero (K := K) D hD) (Work.MotC5N3.aK_sq_sub_ne (K := K) D hD)))

end Work.MotC5N3.Work
