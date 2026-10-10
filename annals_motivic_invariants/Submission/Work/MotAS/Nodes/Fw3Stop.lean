import Mathlib
import Submission.Work.MotAS.Nodes.Fw3Aux
import Submission.Work.MotAS.ASRulV2M.HcAuxRelaxed
import Submission.Work.MotAS.ASChart2Defs
import Submission.Work.MotAS.asRuleMinP_isHomogeneous
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.Nodes.Fw3Stop`

The degree-`10` (top) part of the source ruling quintic `sAS2 a b g` of the corrected AS chart
is `C (A ^ 5) * (asQ) ^ 5`, `A = a ^ 2 - a * b - b ^ 2`, `asQ` the source conic; and
`sAS2 a b g` has total degree `10`.

The proof is the same computation as in `Submission/Work/MotC5N3/fwVecAS2_three_notMem_x.lean`,
but self-contained here (that module currently carries a `sorry`, so it is not imported).

Route:

* `sAS2 a b g = kleinSecAS a b g (yQ + yL)` where `yQ` is homogeneous of degree `2` and `yL` of
  total degree `≤ 1` (`ASRulV2M.stereo_eq`); `secPoly` is the quintic form of `kleinSecAS`;
* `HcR.homogeneousComponent_aeval_add` therefore identifies the degree-`10` part with
  `kleinSecAS a b g yQ`, and `yQ` has only its `0`-th entry nonzero (`= -asQ`), so the whole
  expression collapses to the coefficient of `Y₀ ^ 5` times `(-asQ) ^ 5 = -asQ ^ 5`;
* the coefficient of `Y₀ ^ 5` in `kleinSecAS` is `-a ^ 10 + a ^ 5 b ^ 5 + b ^ 10 = -A ^ 5`
  (Freshman's dream in characteristic `5`);
* `totalDegree = 10` follows since the degree-`10` component is nonzero and nothing of higher
  degree survives (`HcR.bound_aeval`).
-/

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace Work.MotAS.Nodes

open MvPolynomial

/-! ## The `secPoly` dictionary -/

/-- Evaluation of `secPoly` as a `kleinSecAS` value, over an arbitrary `K`-algebra. -/
theorem aeval_secPoly_fw {K : Type} [CommRing K] {S : Type} [CommRing S] [Algebra K S]
    (a b g : K) (y : Fin 5 → S) :
    MvPolynomial.aeval y (Work.MotAS.Nodes.Fw3.secPoly K a b g)
      = Work.MotAS.kleinSecAS (algebraMap K S a) (algebraMap K S b) (algebraMap K S g) y := by
  rw [MvPolynomial.aeval_eq_eval₂Hom, Work.MotAS.Nodes.Fw3.secPoly]
  simp only [Work.MotAS.kleinSecAS, map_add, map_sub, map_mul, map_pow, map_neg,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', MvPolynomial.algebraMap_eq,
    map_natCast, map_ofNat]

/-- Evaluation of `secPoly` at a vector of polynomials in `K[X₀,X₁,X₂]`. -/
theorem aeval_secPoly_fw_C {K : Type} [CommRing K] (a b g : K)
    (y : Fin 5 → MvPolynomial (Fin 3) K) :
    MvPolynomial.aeval y (Work.MotAS.Nodes.Fw3.secPoly K a b g)
      = Work.MotAS.kleinSecAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) y := by
  rw [aeval_secPoly_fw]
  simp [MvPolynomial.algebraMap_eq]

/-- The dilation law of `secPoly`: it is a quintic form. -/
theorem secPoly_aeval_smul_fw {K : Type} [CommRing K] {S : Type} [CommRing S] [Algebra K S]
    (a b g : K) (s : S) (y : Fin 5 → S) :
    MvPolynomial.aeval (fun i => s * y i) (Work.MotAS.Nodes.Fw3.secPoly K a b g)
      = s ^ 5 * MvPolynomial.aeval y (Work.MotAS.Nodes.Fw3.secPoly K a b g) := by
  rw [aeval_secPoly_fw, aeval_secPoly_fw]
  exact Work.MotAS.kleinSecAS_smul _ _ _ s y

/-- `secPoly` is a quintic form. -/
theorem secPoly_isHomogeneous_fw (K : Type) [CommRing K] (a b g : K) :
    (Work.MotAS.Nodes.Fw3.secPoly K a b g).IsHomogeneous 5 := by
  refine Work.MotAS.isHomogeneous_of_aeval_fresh
    (Work.MotAS.Nodes.Fw3.secPoly K a b g) 5 ?_
  have hscal := secPoly_aeval_smul_fw (K := K) (S := Polynomial (MvPolynomial (Fin 5) K)) a b g
    (s := (Polynomial.X : Polynomial (MvPolynomial (Fin 5) K)))
    (y := (fun i : Fin 5 => Polynomial.C (MvPolynomial.X i) :
      Fin 5 → Polynomial (MvPolynomial (Fin 5) K)))
  have hsub : (fun i : Fin 5 => Polynomial.C (MvPolynomial.X i) * Polynomial.X :
        Fin 5 → Polynomial (MvPolynomial (Fin 5) K))
      = fun i => Polynomial.X * Polynomial.C (MvPolynomial.X i) := by
    funext i; rw [mul_comm]
  have hC : MvPolynomial.aeval (fun i : Fin 5 => Polynomial.C (MvPolynomial.X i))
      (Work.MotAS.Nodes.Fw3.secPoly K a b g)
      = Polynomial.C (Work.MotAS.Nodes.Fw3.secPoly K a b g) := by
    have h : MvPolynomial.aeval (fun i : Fin 5 => Polynomial.C (MvPolynomial.X i))
        = IsScalarTower.toAlgHom K (MvPolynomial (Fin 5) K)
            (Polynomial (MvPolynomial (Fin 5) K)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp
    rw [h]
    change (algebraMap (MvPolynomial (Fin 5) K) (Polynomial (MvPolynomial (Fin 5) K)))
        (Work.MotAS.Nodes.Fw3.secPoly K a b g)
      = Polynomial.C (Work.MotAS.Nodes.Fw3.secPoly K a b g)
    rw [Polynomial.algebraMap_eq]
  rw [hsub, hscal, hC]

/-! ## The degree-`10` computation -/

section Aux

variable {K : Type} [Field K] [CharP K 5]

/-- In characteristic `5`, `A ^ 5 = a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10`. -/
theorem Fw3_asA_pow_five (a b : K) :
    (Work.MotAS.Nodes.Fw3.asA a b) ^ 5 = a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10 := by
  have hF : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI := hF
  rw [Work.MotAS.Nodes.Fw3.asA]
  have h1 := sub_pow_char_pow (a ^ 2 - a * b) (b ^ 2) 1
  have h2 := sub_pow_char_pow (a ^ 2) (a * b) 1
  simp only [pow_one] at h1 h2
  rw [h1, h2]
  refl_ring1

/-- The `Fw3.asQ` of the source chart is minus the quadratic form `q2` of the stereographic
vector. -/
theorem Fw3_asQ_eq_neg_q2 (a b : K) :
    Work.MotAS.Nodes.Fw3.asQ a b = -Work.MotAS.ASRulV2M.q2 a b := by
  simp only [Work.MotAS.Nodes.Fw3.asQ, Work.MotAS.ASRulV2M.q2, Work.MotAS.Nodes.Fw3.asA,
    Work.MotAS.Nodes.Fw3.asB, Work.MotAS.azA, Work.MotAS.azB]
  simp only [map_add, map_mul, map_pow, map_neg]
  refl_ring1

/-- The source ruling quintic is the `aeval` of `secPoly` at the stereographic vector. -/
theorem sAS2_eq_aeval_fw (a b g : K) :
    Work.MotAS.sAS2 a b g
      = MvPolynomial.aeval
          (fun i => Work.MotAS.ASRulV2M.yQ a b i + Work.MotAS.ASRulV2M.yL a b i)
          (Work.MotAS.Nodes.Fw3.secPoly K a b g) := by
  change Work.MotAS.kleinSecAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (Work.MotAS.kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (Work.MotAS.pAS0 K)
        (Work.MotK.chart3 K))
      = MvPolynomial.aeval
          (fun i => Work.MotAS.ASRulV2M.yQ a b i + Work.MotAS.ASRulV2M.yL a b i)
          (Work.MotAS.Nodes.Fw3.secPoly K a b g)
  rw [Work.MotAS.ASRulV2M.stereo_eq]
  exact (aeval_secPoly_fw_C a b g _).symm

/-- The degree-`10` homogeneous component of the source ruling quintic. -/
theorem homogeneousComponent_ten_sAS2_fw (a b g : K) :
    MvPolynomial.homogeneousComponent 10 (Work.MotAS.sAS2 a b g)
      = MvPolynomial.aeval (Work.MotAS.ASRulV2M.yQ a b) (Work.MotAS.Nodes.Fw3.secPoly K a b g) := by
  have hhom : (Work.MotAS.Nodes.Fw3.secPoly K a b g).IsHomogeneous 5 :=
    secPoly_isHomogeneous_fw K a b g
  have hq : ∀ i, (Work.MotAS.ASRulV2M.yQ a b i).IsHomogeneous 2 :=
    fun i => Work.MotAS.ASRulV2M.isHomogeneous_yQ a b i
  have hl : ∀ i, (Work.MotAS.ASRulV2M.yL a b i).totalDegree ≤ 1 :=
    fun i => Work.MotAS.ASRulV2M.totalDegree_yL a b i
  have hsT : Work.MotAS.sAS2 a b g
      = MvPolynomial.aeval
          (fun i => Work.MotAS.ASRulV2M.yQ a b i + Work.MotAS.ASRulV2M.yL a b i)
          (Work.MotAS.Nodes.Fw3.secPoly K a b g) := sAS2_eq_aeval_fw a b g
  rw [hsT]
  exact Work.MotAS.ASRulV2M.HcR.homogeneousComponent_aeval_add (τ := Fin 3) (d := 5)
    (Work.MotAS.ASRulV2M.yQ a b) (Work.MotAS.ASRulV2M.yL a b)
    (Work.MotAS.Nodes.Fw3.secPoly K a b g) hhom hq hl

/-- `secPoly` evaluated at `yQ` is a power of the conic `asQ`. -/
theorem kleinSecAS_yQ_fw (a b g : K) :
    MvPolynomial.aeval (Work.MotAS.ASRulV2M.yQ a b) (Work.MotAS.Nodes.Fw3.secPoly K a b g)
      = MvPolynomial.C ((Work.MotAS.Nodes.Fw3.asA a b) ^ 5)
        * (Work.MotAS.Nodes.Fw3.asQ a b) ^ 5 := by
  have hmain : Work.MotAS.kleinSecAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (fun i : Fin 5 =>
        (![Work.MotAS.ASRulV2M.q2 a b, 0, 0, 0, 0] : Fin 5 → MvPolynomial (Fin 3) K) i)
      = MvPolynomial.C (-a ^ 10 + a ^ 5 * b ^ 5 + b ^ 10)
          * (Work.MotAS.ASRulV2M.q2 a b) ^ 5 := by
    rw [Work.MotAS.kleinSecAS]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    simp only [map_add, map_mul, map_pow, map_neg]
    refl_ring1
  rw [aeval_secPoly_fw_C]
  change Work.MotAS.kleinSecAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (fun i : Fin 5 =>
        (![Work.MotAS.ASRulV2M.q2 a b, 0, 0, 0, 0] : Fin 5 → MvPolynomial (Fin 3) K) i)
      = MvPolynomial.C ((Work.MotAS.Nodes.Fw3.asA a b) ^ 5)
        * (Work.MotAS.Nodes.Fw3.asQ a b) ^ 5
  rw [hmain, Fw3_asQ_eq_neg_q2,
    show (-a ^ 10 + a ^ 5 * b ^ 5 + b ^ 10 : K) = -((Work.MotAS.Nodes.Fw3.asA a b) ^ 5) by
      rw [Fw3_asA_pow_five]; ring,
    map_neg]
  refl_ring1

/-- The source ruling quintic has top form `C (A ^ 5) * (asQ) ^ 5` and total degree `10`. -/
theorem Fw3_topForm_sAS2 (a b g : K) (hA : Work.MotAS.Nodes.Fw3.asA a b ≠ 0) :
    MvPolynomial.homogeneousComponent 10 (Work.MotAS.sAS2 a b g)
        = MvPolynomial.C ((Work.MotAS.Nodes.Fw3.asA a b) ^ 5)
          * (Work.MotAS.Nodes.Fw3.asQ a b) ^ 5
      ∧ (Work.MotAS.sAS2 a b g).totalDegree = 10 := by
  have hcomp : MvPolynomial.homogeneousComponent 10 (Work.MotAS.sAS2 a b g)
      = MvPolynomial.C ((Work.MotAS.Nodes.Fw3.asA a b) ^ 5)
        * (Work.MotAS.Nodes.Fw3.asQ a b) ^ 5 := by
    rw [homogeneousComponent_ten_sAS2_fw, kleinSecAS_yQ_fw]
  have hne : MvPolynomial.homogeneousComponent 10 (Work.MotAS.sAS2 a b g) ≠ 0 := by
    rw [hcomp]
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr (pow_ne_zero 5 hA))
      (pow_ne_zero 5 (Work.MotAS.Nodes.Fw3.asQ_ne_zero a b hA))
  refine ⟨hcomp, ?_⟩
  have hbound : Work.MotAS.ASRulV2M.HcR.Bound
      (MvPolynomial.aeval
        (fun i => Work.MotAS.ASRulV2M.yQ a b i + Work.MotAS.ASRulV2M.yL a b i)
        (Work.MotAS.Nodes.Fw3.secPoly K a b g)) (2 * 5) :=
    Work.MotAS.ASRulV2M.HcR.bound_aeval (τ := Fin 3) (d := 5)
      (Work.MotAS.ASRulV2M.yQ a b) (Work.MotAS.ASRulV2M.yL a b)
      (Work.MotAS.Nodes.Fw3.secPoly K a b g)
      (secPoly_isHomogeneous_fw K a b g)
      (fun i => Work.MotAS.ASRulV2M.isHomogeneous_yQ a b i)
      (fun i => Work.MotAS.ASRulV2M.totalDegree_yL a b i)
  refine le_antisymm ?_ ?_
  · rw [sAS2_eq_aeval_fw]
    exact hbound.totalDegree_le
  · exact Work.MotAS.ASRulV2M.HcR.le_totalDegree_of_homogeneousComponent_ne_zero hne

end Aux

theorem Fw3Stop (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hA : Work.MotAS.Nodes.Fw3.asA a b ≠ 0) :
    MvPolynomial.homogeneousComponent 10 (Work.MotAS.sAS2 a b g)
        = MvPolynomial.C ((Work.MotAS.Nodes.Fw3.asA a b) ^ 5)
          * (Work.MotAS.Nodes.Fw3.asQ a b) ^ 5
      ∧ (Work.MotAS.sAS2 a b g).totalDegree = 10 := by
  exact Fw3_topForm_sAS2 a b g hA

end Work.MotAS.Nodes
