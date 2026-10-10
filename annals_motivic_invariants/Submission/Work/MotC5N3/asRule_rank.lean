import Mathlib
import Submission.Work.MotC5N3.Ruling
import Submission.Work.MotC5N3.ASZChartSetupGen
import Submission.Work.MotC5N3.AsTwCoordAt
import Submission.Work.MotC5N3.KerAevalKleinPASGenAlt
import Submission.Work.MotC5N3.twistFieldAS_eq
import Submission.Work.MotV5.ASLocal.asRuleMinP_notMem2
import Submission.Work.MotAS.aeval_smul_of_homogeneous
import Submission.Work.MotAS.asRuleMinP_isHomogeneous

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

open MvPolynomial

set_option maxHeartbeats 1000000

variable {𝕜 : Type} [Field 𝕜]
variable {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-- The evaluation of `Work.MotAS.asRuleMinP` is the `(1,0)`-minor of the two AS ruling vectors.
(`RatFunc 𝕜 ↦ K` fork of the naturality statement used by `Work.MotV5.ASLocal.asRule_rank`.) -/
lemma aeval_asRuleMinP {Kc R : Type} [Field Kc] [CharP Kc 5] [CommRing R] [Algebra Kc R]
    (a b g : Kc) (c : Fin 5 → R) :
    (MvPolynomial.aeval c) (Work.MotAS.asRuleMinP a b g)
      = Work.MotAS.asRuleQA (algebraMap Kc R a) (algebraMap Kc R b) (algebraMap Kc R g) c 1
        * Work.MotAS.asRuleQB (algebraMap Kc R a) (algebraMap Kc R b) (algebraMap Kc R g) c 0
        - Work.MotAS.asRuleQA (algebraMap Kc R a) (algebraMap Kc R b) (algebraMap Kc R g) c 0
          * Work.MotAS.asRuleQB (algebraMap Kc R a) (algebraMap Kc R b) (algebraMap Kc R g) c 1 := by
  have h1 : (MvPolynomial.aeval c)
      (Work.MotAS.asRuleQA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (fun i => MvPolynomial.X i) 1)
      = Work.MotAS.asRuleQA (algebraMap Kc R a) (algebraMap Kc R b) (algebraMap Kc R g) c 1 := by
    show ((MvPolynomial.aeval c : MvPolynomial (Fin 5) Kc →ₐ[Kc] R) :
      MvPolynomial (Fin 5) Kc →+* R) _ = _
    rw [Work.MotAS.map_asRuleQA]
    simp
  have h2 : (MvPolynomial.aeval c)
      (Work.MotAS.asRuleQB (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (fun i => MvPolynomial.X i) 0)
      = Work.MotAS.asRuleQB (algebraMap Kc R a) (algebraMap Kc R b) (algebraMap Kc R g) c 0 := by
    show ((MvPolynomial.aeval c : MvPolynomial (Fin 5) Kc →ₐ[Kc] R) :
      MvPolynomial (Fin 5) Kc →+* R) _ = _
    rw [Work.MotAS.map_asRuleQB]
    simp
  have h3 : (MvPolynomial.aeval c)
      (Work.MotAS.asRuleQA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (fun i => MvPolynomial.X i) 0)
      = Work.MotAS.asRuleQA (algebraMap Kc R a) (algebraMap Kc R b) (algebraMap Kc R g) c 0 := by
    show ((MvPolynomial.aeval c : MvPolynomial (Fin 5) Kc →ₐ[Kc] R) :
      MvPolynomial (Fin 5) Kc →+* R) _ = _
    rw [Work.MotAS.map_asRuleQA]
    simp
  have h4 : (MvPolynomial.aeval c)
      (Work.MotAS.asRuleQB (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (fun i => MvPolynomial.X i) 1)
      = Work.MotAS.asRuleQB (algebraMap Kc R a) (algebraMap Kc R b) (algebraMap Kc R g) c 1 := by
    show ((MvPolynomial.aeval c : MvPolynomial (Fin 5) Kc →ₐ[Kc] R) :
      MvPolynomial (Fin 5) Kc →+* R) _ = _
    rw [Work.MotAS.map_asRuleQB]
    simp
  simp only [Work.MotAS.asRuleMinP, map_sub, map_mul, h1, h2, h3, h4]

/-- **The transported AS ruling minor does not vanish at the Galois coordinates.**  The quartic
`asRuleMinP` is homogeneous of degree `4` (`Work.MotAS.asRuleMinP_isHomogeneous`); if its evaluation
at the Lagrange coordinates `asTwY D g` of the Klein point vanished, it would lie in the ideal of
the five transported Pfaffians (`Work.MotC5N3.kerAevalKleinPASGenAlt`), contradicting
`Work.MotV5.ASLocal.asRuleMinP_notMem2`. -/
lemma asRuleMinP_asTwY_ne_zero (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (g : K) :
    (MvPolynomial.aeval (asTwY D g)) (Work.MotAS.asRuleMinP (aK K D) (bK K D) g) ≠ 0 := by
  intro h0
  haveI hchar : CharP 𝕜 5 := charP_of_algebra_charP (𝕜 := 𝕜) (K := K)
  have hF : (Work.MotAS.asRuleMinP (aK K D) (bK K D) g) ∈
      MvPolynomial.homogeneousSubmodule (Fin 5) K 4 :=
    (MvPolynomial.mem_homogeneousSubmodule (R := K) 4 _).mpr
      (Work.MotAS.asRuleMinP_isHomogeneous K (aK K D) (bK K D) g)
  have hmem := kerAevalKleinPASGenAlt K D hD g 4 _ hF h0
  exact Work.MotV5.ASLocal.asRuleMinP_notMem2 K (aK K D) (bK K D) g
    (aK_ne_zero (K := K) D hD) (bK_ne_zero (K := K) D hD) (aK_sq_sub_ne (K := K) D hD) hmem

theorem asRule_rank (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Work.MotAS.asRuleQA (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.a)
        (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.b)
        (algebraMap K ↥(Work.MotC5N3.twistFieldAS D g) g) (Work.MotC5N3.asY0 D g) 1
      * Work.MotAS.asRuleQB (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.a)
        (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.b)
        (algebraMap K ↥(Work.MotC5N3.twistFieldAS D g) g) (Work.MotC5N3.asY0 D g) 0
      - Work.MotAS.asRuleQA (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.a)
        (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.b)
        (algebraMap K ↥(Work.MotC5N3.twistFieldAS D g) g) (Work.MotC5N3.asY0 D g) 0
      * Work.MotAS.asRuleQB (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.a)
        (algebraMap 𝕜 ↥(Work.MotC5N3.twistFieldAS D g) D.b)
        (algebraMap K ↥(Work.MotC5N3.twistFieldAS D g) g) (Work.MotC5N3.asY0 D g) 1 ≠ 0 := by
  classical
  haveI hchar : CharP 𝕜 5 := charP_of_algebra_charP (𝕜 := 𝕜) (K := K)
  set Lf := ↥(twistFieldAS D g) with hLf
  set Om := OmA K D with hOm
  set aL : Lf := algebraMap 𝕜 Lf D.a with haL
  set bL : Lf := algebraMap 𝕜 Lf D.b with hbL
  set gL : Lf := algebraMap K Lf g with hgL
  set cc : Fin 5 → Lf := fun i => asY0 D g i with hcc
  intro hzero
  have hT : Work.MotAS.asRuleQA aL bL gL cc 1 * Work.MotAS.asRuleQB aL bL gL cc 0
      - Work.MotAS.asRuleQA aL bL gL cc 0 * Work.MotAS.asRuleQB aL bL gL cc 1 = 0 := by
    simpa only [haL, hbL, hgL, hcc] using hzero
  have hφa : (algebraMap Lf Om) aL = algebraMap K Om (aK K D) := by
    rw [haL, IsScalarTower.algebraMap_apply 𝕜 K Lf D.a,
      ← IsScalarTower.algebraMap_apply K Lf Om (algebraMap 𝕜 K D.a)]
    simp only [aK]
  have hφb : (algebraMap Lf Om) bL = algebraMap K Om (bK K D) := by
    rw [hbL, IsScalarTower.algebraMap_apply 𝕜 K Lf D.b,
      ← IsScalarTower.algebraMap_apply K Lf Om (algebraMap 𝕜 K D.b)]
    simp only [bK]
  have hφg : (algebraMap Lf Om) gL = algebraMap K Om g := by
    rw [hgL, ← IsScalarTower.algebraMap_apply K Lf Om g]
  have hφcc : ∀ i, (algebraMap Lf Om) (cc i)
      = (asTwY D g 0)⁻¹ * asTwY D g i := by
    intro i
    rw [hcc]
    show (asTwY D g i / asTwY D g 0 : Om)
      = (asTwY D g 0)⁻¹ * asTwY D g i
    rw [div_eq_mul_inv, mul_comm]
  have hstep1 : (algebraMap Lf Om)
        (Work.MotAS.asRuleQA aL bL gL cc 1 * Work.MotAS.asRuleQB aL bL gL cc 0
          - Work.MotAS.asRuleQA aL bL gL cc 0 * Work.MotAS.asRuleQB aL bL gL cc 1)
      = (MvPolynomial.aeval (fun i => (algebraMap Lf Om) (cc i)))
          (Work.MotAS.asRuleMinP (aK K D) (bK K D) g) := by
    rw [map_sub, map_mul, map_mul,
      Work.MotAS.map_asRuleQA (algebraMap Lf Om : Lf →+* Om) aL bL gL cc 1,
      Work.MotAS.map_asRuleQB (algebraMap Lf Om : Lf →+* Om) aL bL gL cc 0,
      Work.MotAS.map_asRuleQA (algebraMap Lf Om : Lf →+* Om) aL bL gL cc 0,
      Work.MotAS.map_asRuleQB (algebraMap Lf Om : Lf →+* Om) aL bL gL cc 1,
      hφa, hφb, hφg, ← aeval_asRuleMinP (aK K D) (bK K D) g
        (fun i => (algebraMap Lf Om) (cc i))]
  have hstep2 : (MvPolynomial.aeval (fun i => (algebraMap Lf Om) (cc i)))
        (Work.MotAS.asRuleMinP (aK K D) (bK K D) g)
      = ((asTwY D g 0)⁻¹) ^ 4
        * (MvPolynomial.aeval (asTwY D g)) (Work.MotAS.asRuleMinP (aK K D) (bK K D) g) := by
    have hfun : (fun i => (algebraMap Lf Om) (cc i))
        = fun i => (asTwY D g 0)⁻¹ * asTwY D g i := by
      funext i; rw [hφcc]
    rw [hfun]
    exact Work.MotAS.aeval_smul_of_homogeneous
      (Work.MotAS.asRuleMinP_isHomogeneous K (aK K D) (bK K D) g) _ _
  rw [hT, map_zero] at hstep1
  rw [hstep2] at hstep1
  have hy0 : asTwY D g 0 ≠ 0 := asTwY_zero_ne_zero D g hD.1
  have hmain : (MvPolynomial.aeval (asTwY D g))
      (Work.MotAS.asRuleMinP (aK K D) (bK K D) g) = 0 := by
    have h2 : ((asTwY D g 0)⁻¹) ^ 4
        * (MvPolynomial.aeval (asTwY D g)) (Work.MotAS.asRuleMinP (aK K D) (bK K D) g) = 0 :=
      hstep1.symm
    exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 4 (inv_ne_zero hy0))
  exact asRuleMinP_asTwY_ne_zero D hD g hmain

end Work.MotC5N3
