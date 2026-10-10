import Mathlib
import Submission.Work.MotK.LinkCertDefs
import Submission.Work.MotK.TGen.AevalFhomPoly
import Submission.Work.MotK.TGen.AevalGhomPoly
import Submission.Work.MotK.TGen.AevalFwPoly
import Submission.Work.MotK.TGen.AevalBwPoly
import Submission.Work.MotK.KleinTwLinkComp1
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 3000000
set_option autoImplicit false

namespace Work.MotK

namespace UnitChartCAux
open Work.MotK

/-! ### component lemmas -/

@[simp] theorem chartC0 (K : Type*) [CommRing K] : chartC K 0 = 0 := rfl
@[simp] theorem chartC1 (K : Type*) [CommRing K] : chartC K 1 = MvPolynomial.X 0 := rfl
@[simp] theorem chartC2 (K : Type*) [CommRing K] : chartC K 2 = MvPolynomial.X 1 := rfl
@[simp] theorem chartC3 (K : Type*) [CommRing K] : chartC K 3 = MvPolynomial.X 2 := rfl
@[simp] theorem chartC4 (K : Type*) [CommRing K] : chartC K 4 = 1 := rfl

@[simp] theorem pointC0 (K : Type*) [Field K] (a b h : K) : pointC K a b h 0 = 1 := rfl
@[simp] theorem pointC1 (K : Type*) [Field K] (a b h : K) : pointC K a b h 1 = 0 := rfl
@[simp] theorem pointC2 (K : Type*) [Field K] (a b h : K) : pointC K a b h 2 = 1 := rfl
@[simp] theorem pointC3 (K : Type*) [Field K] (a b h : K) : pointC K a b h 3 = b / (a * h) := rfl
@[simp] theorem pointC4 (K : Type*) [Field K] (a b h : K) : pointC K a b h 4 = 0 := rfl

@[simp] theorem kleinPointT0 (K : Type*) [Field K] (a b h : K) : kleinPointT a b h 0 = 1 := rfl
@[simp] theorem kleinPointT1 (K : Type*) [Field K] (a b h : K) : kleinPointT a b h 1 = 0 := rfl
@[simp] theorem kleinPointT2 (K : Type*) [Field K] (a b h : K) : kleinPointT a b h 2 = 1 := rfl
@[simp] theorem kleinPointT3 (K : Type*) [Field K] (a b h : K) : kleinPointT a b h 3 = b / (a * h) := rfl
@[simp] theorem kleinPointT4 (K : Type*) [Field K] (a b h : K) : kleinPointT a b h 4 = 0 := rfl

@[simp] theorem fin5_mk_add_one_0 : (⟨(0:Fin 3).val + 1, by omega⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_add_one_1 : (⟨(1:Fin 3).val + 1, by omega⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_add_one_2 : (⟨(2:Fin 3).val + 1, by omega⟩ : Fin 5) = 3 := rfl

/-! ### `aeval` functoriality -/

noncomputable def afAlg (K : Type*) [Field K] : MvPolynomial (Fin 3) K →ₐ[K] FracC K where
  toFun := algebraMap _ _
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun k => (IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K) (FracC K) k).symm

@[simp] theorem afAlg_apply (K : Type*) [Field K] (x : MvPolynomial (Fin 3) K) :
    afAlg K x = algebraMap (MvPolynomial (Fin 3) K) (FracC K) x := rfl

theorem algHom_aeval {K0 : Type*} [CommSemiring K0] {n : ℕ} {R A : Type*}
    [CommSemiring R] [Algebra K0 R] [CommSemiring A] [Algebra K0 A]
    (Ψ : R →ₐ[K0] A) (y : Fin n → R) (P : MvPolynomial (Fin n) K0) :
    Ψ (MvPolynomial.aeval y P) = MvPolynomial.aeval (fun i => Ψ (y i)) P := by
  have h : Ψ.comp (MvPolynomial.aeval y) = MvPolynomial.aeval (fun i => Ψ (y i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  simpa using congrArg (fun (f : MvPolynomial (Fin n) K0 →ₐ[K0] A) => f P) h

theorem aeval_algebraMap {K : Type*} [Field K] {n : ℕ}
    (y : Fin n → MvPolynomial (Fin 3) K) (P : MvPolynomial (Fin n) K) :
    MvPolynomial.aeval (fun i => algebraMap (MvPolynomial (Fin 3) K) (FracC K) (y i)) P
      = algebraMap (MvPolynomial (Fin 3) K) (FracC K) (MvPolynomial.aeval y P) := by
  have h := algHom_aeval (afAlg K) y P
  simpa only [afAlg_apply] using h.symm

/-! ### scaling of the five-variable polynomials -/

theorem aeval_smul_GhomPoly {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (a b h : K) (c : A) (y : Fin 5 → A) :
    MvPolynomial.aeval (fun i => c * y i) (GhomPoly K a b h)
      = c^8 * MvPolynomial.aeval y (GhomPoly K a b h) := by
  rw [TGen.AevalGhomPoly, TGen.AevalGhomPoly, kleinTwGhomV_smul]

theorem aeval_smul_FhomPoly {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (a b h : K) (c : A) (y : Fin 5 → A) :
    MvPolynomial.aeval (fun i => c * y i) (FhomPoly K a b h)
      = c^11 * MvPolynomial.aeval y (FhomPoly K a b h) := by
  rw [TGen.AevalFhomPoly, TGen.AevalFhomPoly, kleinTwFhom_smul]

theorem aeval_smul_fwPoly {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (a b h : K) (c : A) (y : Fin 5 → A) (j : Fin 5) :
    MvPolynomial.aeval (fun i => c * y i) (fwPoly K a b h j)
      = c^4 * MvPolynomial.aeval y (fwPoly K a b h j) := by
  rw [TGen.AevalFwPoly, TGen.AevalFwPoly, kleinTwStereo_smul, kleinTwP_homog]
  first | refl_ring1 | ring

theorem kleinTwPi_smul {R : Type*} [CommRing R] (p x : Fin 5 → R) (c : R) :
    kleinTwPi p (fun i => c * x i) = fun i => c * kleinTwPi p x i := by
  funext i
  simp only [kleinTwPi]
  first | refl_ring1 | ring

theorem aeval_smul_bwPoly {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (a b h : K) (c : A) (y : Fin 5 → A) (j : Fin 5) :
    MvPolynomial.aeval (fun i => c * y i) (bwPoly K a b h j)
      = c^3 * MvPolynomial.aeval y (bwPoly K a b h j) := by
  rw [TGen.AevalBwPoly, TGen.AevalBwPoly, kleinTwR_homog, kleinTwPi_smul]

/-! ### chart ring identities -/

theorem kleinTwGhom'_eq_kleinTwGhomV {R : Type*} [CommRing R] (a b h : R) (p w : Fin 5 → R) :
    kleinTwGhom' a b h p w = kleinTwGhomV a b h p w := by
  rw [kleinTwGhom', kleinTwGhomV, kleinTwSDualInv_eq_kleinTwSDualV]

theorem fhatC_zero (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    fhatC K a b h 0 = 0 := by
  rw [fhatC, kleinTwP_zero, ← kleinTwQ, KleinTwQ_stereo, kleinTwQ_pRaC K a b h ha hh,
    mul_zero]

theorem ghatC_zero (K : Type*) [Field K] (a b h : K) : ghatC K a b h 0 = 0 := by
  simp only [ghatC, kleinTwPi, pRaC, pointC0, MvPolynomial.C_1, mul_one, sub_self]

theorem ghatC_four_eq_R (K : Type*) [Field K] (a b h : K) :
    ghatC K a b h 4 = kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (chartC K) 4 := by
  simp only [ghatC, kleinTwPi, pRaC, pointC4, MvPolynomial.C_0, mul_zero, sub_zero]

theorem fhatC_eq (K : Type*) [Field K] (a b h : K) :
    fhatC K a b h = kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (pRaC K a b h) (chartC K)) := rfl

theorem ghatC_eq (K : Type*) [Field K] (a b h : K) :
    ghatC K a b h = kleinTwPi (pRaC K a b h)
      (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chartC K)) := rfl

theorem stereo_four (K : Type*) [Field K] (a b h : K) :
    kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (pRaC K a b h) (chartC K) 4
      = -kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (pRaC K a b h) (chartC K) := by
  simp only [kleinTwStereo, pRaC, pointC4, MvPolynomial.C_0, chartC4, mul_zero, zero_sub,
    mul_one]

theorem aeval_chartC_GhomPoly (K : Type*) [Field K] (a b h : K) :
    MvPolynomial.aeval (chartC K) (GhomPoly K a b h) = FambC K a b h := by
  rw [TGen.AevalGhomPoly, FambC, kleinTwGhom'_eq_kleinTwGhomV,
    show (pRaC K a b h) = (fun i => MvPolynomial.C (pointC K a b h i)) from rfl,
    MvPolynomial.C_eq_algebraMap]
  rfl

theorem aeval_chartC_FhomPoly (K : Type*) [Field K] (a b h : K) :
    MvPolynomial.aeval (chartC K) (FhomPoly K a b h) = GambC K a b h := by
  rw [TGen.AevalFhomPoly, GambC,
    show (pRaC K a b h) = (fun i => MvPolynomial.C (pointC K a b h i)) from rfl,
    MvPolynomial.C_eq_algebraMap]
  rfl

theorem aeval_chartC_bwPoly (K : Type*) [Field K] (a b h : K) (j : Fin 5) :
    MvPolynomial.aeval (chartC K) (bwPoly K a b h j) = ghatC K a b h j := by
  rw [TGen.AevalBwPoly, ghatC,
    show (pRaC K a b h) = (fun i => MvPolynomial.C (pointC K a b h i)) from rfl,
    MvPolynomial.C_eq_algebraMap]
  rfl

theorem aeval_chartC_fwPoly (K : Type*) [Field K] (a b h : K) (j : Fin 5) :
    MvPolynomial.aeval (chartC K) (fwPoly K a b h j) = fhatC K a b h j := by
  rw [TGen.AevalFwPoly, fhatC,
    show (pRaC K a b h) = (fun i => MvPolynomial.C (pointC K a b h i)) from rfl,
    MvPolynomial.C_eq_algebraMap]
  rfl

/-! ### the substitution vectors -/

theorem psiCh_chartC (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0)
    (hf4' : algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4) ≠ 0) :
    (fun i : Fin 5 => PsiCh K a b h (chartC K i))
      = fun i => (algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4))⁻¹
          * algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h i) := by
  funext i
  fin_cases i
  · simp only [fin5_zero, chartC0, map_zero, fhatC_zero K a b h ha hh, mul_zero]
  · simp only [fin5_one, chartC1, PsiCh, MvPolynomial.aeval_X, phiCh, fin5_mk_add_one_0]
    first | refl_ring1 | ring
  · simp only [fin5_two, chartC2, PsiCh, MvPolynomial.aeval_X, phiCh, fin5_mk_add_one_1]
    first | refl_ring1 | ring
  · simp only [fin5_three, chartC3, PsiCh, MvPolynomial.aeval_X, phiCh, fin5_mk_add_one_2]
    first | refl_ring1 | ring
  · simp only [fin5_four, chartC4, map_one]
    exact (inv_mul_cancel₀ hf4').symm

theorem etaCh_chartC (K : Type*) [Field K] (a b h : K)
    (hg4' : algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4) ≠ 0) :
    (fun i : Fin 5 => PhiCh K a b h (chartC K i))
      = fun i => (algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4))⁻¹
          * algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h i) := by
  funext i
  fin_cases i
  · simp only [fin5_zero, chartC0, map_zero, ghatC_zero K a b h, mul_zero]
  · simp only [fin5_one, chartC1, PhiCh, MvPolynomial.aeval_X, etaCh, fin5_mk_add_one_0]
    first | refl_ring1 | ring
  · simp only [fin5_two, chartC2, PhiCh, MvPolynomial.aeval_X, etaCh, fin5_mk_add_one_1]
    first | refl_ring1 | ring
  · simp only [fin5_three, chartC3, PhiCh, MvPolynomial.aeval_X, etaCh, fin5_mk_add_one_2]
    first | refl_ring1 | ring
  · simp only [fin5_four, chartC4, map_one]
    exact (inv_mul_cancel₀ hg4').symm


theorem mul_aux {A : Type*} [CommRing A] {a x b : A} (h : a * b = 1) : a * x * b = x := by
  rw [mul_assoc, mul_comm x b, ← mul_assoc, h, one_mul]

/-! ### non-vanishing of the two denominators -/

theorem aeval_chartC_vec (K : Type*) [Field K] :
    (fun i : Fin 5 => MvPolynomial.aeval (fun i : Fin 3 => ![0, (0:K), 1] i) (chartC K i))
      = ![0, (0:K), (0:K), (1:K), (1:K)] := by
  funext i
  fin_cases i <;>
    simp only [chartC0, chartC1, chartC2, chartC3, chartC4, fin5_zero, fin5_one, fin5_two,
      fin5_three, fin5_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.head_cons, MvPolynomial.aeval_X, MvPolynomial.aeval_C, map_zero, map_one]


theorem ghatC_four_eq (K : Type*) [Field K] (a b h : K) :
    ghatC K a b h 4 = MvPolynomial.C (a^3*b*h) * (MvPolynomial.X 0)^2
      + MvPolynomial.C (a^2*b^2*h) * (MvPolynomial.X 1)^3
      - MvPolynomial.C (a*b^3) * MvPolynomial.X 2
      - MvPolynomial.C (a^4*h) * (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) := by
  simp only [ghatC, kleinTwPi, kleinTwR_zero, kleinTwR_four, kleinTwR0, kleinTwR4,
    pRaC, pointC0, pointC4, chartC0, chartC1, chartC2, chartC3, chartC4, MvPolynomial.C_0,
    MvPolynomial.C_mul, MvPolynomial.C_pow, mul_zero, zero_mul, sub_zero, zero_sub, mul_one,
    zero_add, add_zero]
  first | refl_ring1 | ring

theorem ghatC_four_ne_zero (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hh : h ≠ 0) : ghatC K a b h 4 ≠ 0 := by
  have hval : MvPolynomial.aeval (fun i : Fin 3 => ![0, (1:K), 0] i) (ghatC K a b h 4)
      = a^2*b^2*h := by
    rw [ghatC_four_eq]
    simp
  intro h0
  rw [h0, map_zero] at hval
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)) hh) hval.symm

theorem fhatC_four_val (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    MvPolynomial.aeval (fun i : Fin 3 => ![0, (0:K), 1] i) (fhatC K a b h 4)
      = -(a^5*b*h^3) := by
  rw [← aeval_chartC_fwPoly K a b h 4]
  rw [algHom_aeval (MvPolynomial.aeval (fun i : Fin 3 => ![0, (0:K), 1] i)) (chartC K)
    (fwPoly K a b h 4), aeval_chartC_vec K]
  rw [TGen.AevalFwPoly]
  simp only [kleinTwP_four, kleinTwP4, kleinTwStereo, kleinTwBilin, kleinTwQ, kleinTwP0,
    kleinPointT0, kleinPointT1, kleinPointT2, kleinPointT3, kleinPointT4, Pi.add_apply,
    Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
    Matrix.head_cons, map_zero, map_one, Algebra.algebraMap_self, RingHom.id_apply]
  field_simp
  first | refl_ring1 | ring

theorem fhatC_four_ne_zero (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hh : h ≠ 0) : fhatC K a b h 4 ≠ 0 := by
  have hval := fhatC_four_val K a b h ha hh
  intro h0
  rw [h0, map_zero] at hval
  exact (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero 5 ha) hb) (pow_ne_zero 3 hh)))
    hval.symm

/-! ### the four clauses -/

theorem clause1 (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hf4 : fhatC K a b h 4 ≠ 0) :
    PsiCh K a b h (FambC K a b h)
        * (algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4)) ^ 8
      = algebraMap (MvPolynomial (Fin 3) K) (FracC K)
          (-(kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b)
                  (MvPolynomial.C h) (pRaC K a b h) (chartC K))) ^ 2
              * kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                  (pRaC K a b h) (chartC K)
              * GambC K a b h) := by
  have hf4' : algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4) ≠ 0 := fun h0 =>
    hf4 (IsFractionRing.injective (MvPolynomial (Fin 3) K) (FracC K) (by rw [h0, map_zero]))
  have hvec := psiCh_chartC K a b h ha hh hf4'
  have hGhom : MvPolynomial.aeval (fhatC K a b h) (GhomPoly K a b h)
      = -(kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
              (pRaC K a b h) (chartC K))) ^ 2
          * kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
              (pRaC K a b h) (chartC K)
          * GambC K a b h := by
    rw [TGen.AevalGhomPoly, ← MvPolynomial.C_eq_algebraMap,
      show (fun i => MvPolynomial.C (kleinPointT a b h i)) = (pRaC K a b h) from rfl,
      fhatC_eq K a b h, GambC]
    exact kleinTwLinkUnitV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (pRaC K a b h) (chartC K) (kleinTwQ_pRaC K a b h ha hh)
  have hmain : PsiCh K a b h (FambC K a b h)
      = ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4))⁻¹) ^ 8
        * algebraMap (MvPolynomial (Fin 3) K) (FracC K)
            (MvPolynomial.aeval (fhatC K a b h) (GhomPoly K a b h)) := by
    rw [← aeval_chartC_GhomPoly,
      algHom_aeval (PsiCh K a b h) (chartC K) (GhomPoly K a b h), hvec,
      aeval_smul_GhomPoly (c := (algebraMap (MvPolynomial (Fin 3) K) (FracC K)
          (fhatC K a b h 4))⁻¹)
        (y := fun i => algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h i)),
      aeval_algebraMap (y := fhatC K a b h) (P := GhomPoly K a b h)]
  have hkey : ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4))⁻¹) ^ 8
      * (algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4)) ^ 8 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hf4', one_pow]
  rw [hmain, hGhom]
  exact mul_aux hkey

theorem clause2 (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hf4 : fhatC K a b h 4 ≠ 0) (hg4 : ghatC K a b h 4 ≠ 0) :
    PsiCh K a b h (ghatC K a b h 4)
        * (algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4)) ^ 3
      = algebraMap (MvPolynomial (Fin 3) K) (FracC K) (-(GambC K a b h)) := by
  have hf4' : algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4) ≠ 0 := fun h0 =>
    hf4 (IsFractionRing.injective (MvPolynomial (Fin 3) K) (FracC K) (by rw [h0, map_zero]))
  have hvec := psiCh_chartC K a b h ha hh hf4'
  have hbw : MvPolynomial.aeval (fhatC K a b h) (bwPoly K a b h 4) = -(GambC K a b h) := by
    rw [TGen.AevalBwPoly, ← MvPolynomial.C_eq_algebraMap, fhatC_eq K a b h, GambC, kleinTwFhom]
    simp only [kleinTwPi, kleinPointT4, MvPolynomial.C_0, mul_zero, sub_zero]
    rw [KleinTwI1 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (pRaC K a b h) (chartC K)) 4]
    rw [stereo_four]
    first | refl_ring1 | ring
  have hmain : PsiCh K a b h (ghatC K a b h 4)
      = ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4))⁻¹) ^ 3
        * algebraMap (MvPolynomial (Fin 3) K) (FracC K)
            (MvPolynomial.aeval (fhatC K a b h) (bwPoly K a b h 4)) := by
    rw [← aeval_chartC_bwPoly K a b h 4,
      algHom_aeval (PsiCh K a b h) (chartC K) (bwPoly K a b h 4), hvec,
      aeval_smul_bwPoly (c := (algebraMap (MvPolynomial (Fin 3) K) (FracC K)
          (fhatC K a b h 4))⁻¹)
        (y := fun i => algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h i))
        (j := 4),
      aeval_algebraMap (y := fhatC K a b h) (P := bwPoly K a b h 4)]
  have hkey : ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4))⁻¹) ^ 3
      * (algebraMap (MvPolynomial (Fin 3) K) (FracC K) (fhatC K a b h 4)) ^ 3 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hf4', one_pow]
  rw [hmain, hbw]
  exact mul_aux hkey

theorem clause3 (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hg4 : ghatC K a b h 4 ≠ 0) :
    PhiCh K a b h (GambC K a b h)
        * (algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4)) ^ 11
      = algebraMap (MvPolynomial (Fin 3) K) (FracC K)
          (-(kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                (pRaC K a b h)
                (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                  (chartC K))) ^ 3
              * (FambC K a b h) ^ 3) := by
  have hg4' : algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4) ≠ 0 := fun h0 =>
    hg4 (IsFractionRing.injective (MvPolynomial (Fin 3) K) (FracC K) (by rw [h0, map_zero]))
  have hvec := etaCh_chartC K a b h hg4'
  have hFh : MvPolynomial.aeval (ghatC K a b h) (FhomPoly K a b h)
      = -(kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (pRaC K a b h)
            (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
              (chartC K))) ^ 3
          * (FambC K a b h) ^ 3 := by
    rw [TGen.AevalFhomPoly, ← MvPolynomial.C_eq_algebraMap,
      show (fun i => MvPolynomial.C (kleinPointT a b h i)) = (pRaC K a b h) from rfl,
      ghatC_eq K a b h, FambC]
    exact KleinTwLinkUnitInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (pRaC K a b h) (chartC K) (kleinTwQ_pRaC K a b h ha hh) (chartC0 K)
      ⟨4, by rw [← ghatC_four_eq_R]; exact hg4⟩
  have hmain : PhiCh K a b h (GambC K a b h)
      = ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4))⁻¹) ^ 11
        * algebraMap (MvPolynomial (Fin 3) K) (FracC K)
            (MvPolynomial.aeval (ghatC K a b h) (FhomPoly K a b h)) := by
    rw [← aeval_chartC_FhomPoly,
      algHom_aeval (PhiCh K a b h) (chartC K) (FhomPoly K a b h), hvec,
      aeval_smul_FhomPoly (c := (algebraMap (MvPolynomial (Fin 3) K) (FracC K)
          (ghatC K a b h 4))⁻¹)
        (y := fun i => algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h i)),
      aeval_algebraMap (y := ghatC K a b h) (P := FhomPoly K a b h)]
  have hkey : ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4))⁻¹) ^ 11
      * (algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4)) ^ 11 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hg4', one_pow]
  rw [hmain, hFh]
  exact mul_aux hkey

theorem clause4 (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hg4 : ghatC K a b h 4 ≠ 0) :
    PhiCh K a b h (fhatC K a b h 4)
        * (algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4)) ^ 4
      = algebraMap (MvPolynomial (Fin 3) K) (FracC K)
          ((kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                (pRaC K a b h)
                (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                  (chartC K))) ^ 2
              * kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                  (chartC K)) := by
  have hg4' : algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4) ≠ 0 := fun h0 =>
    hg4 (IsFractionRing.injective (MvPolynomial (Fin 3) K) (FracC K) (by rw [h0, map_zero]))
  have hvec := etaCh_chartC K a b h hg4'
  have hfw : MvPolynomial.aeval (ghatC K a b h) (fwPoly K a b h 4)
      = (kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (pRaC K a b h)
            (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
              (chartC K))) ^ 2
          * kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
              (chartC K) := by
    rw [TGen.AevalFwPoly, ← MvPolynomial.C_eq_algebraMap, ghatC_eq K a b h,
      show (pRaC K a b h) = (fun i => MvPolynomial.C (kleinPointT a b h i)) from rfl]
    rw [KleinTwLinkComp1 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (fun i => MvPolynomial.C (kleinPointT a b h i)) (chartC K)
      (kleinTwQ_pRaC K a b h ha hh) (chartC0 K)]
    simp only [chartC4, mul_one]
  have hmain : PhiCh K a b h (fhatC K a b h 4)
      = ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4))⁻¹) ^ 4
        * algebraMap (MvPolynomial (Fin 3) K) (FracC K)
            (MvPolynomial.aeval (ghatC K a b h) (fwPoly K a b h 4)) := by
    rw [← aeval_chartC_fwPoly K a b h 4,
      algHom_aeval (PhiCh K a b h) (chartC K) (fwPoly K a b h 4), hvec,
      aeval_smul_fwPoly (c := (algebraMap (MvPolynomial (Fin 3) K) (FracC K)
          (ghatC K a b h 4))⁻¹)
        (y := fun i => algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h i))
        (j := 4),
      aeval_algebraMap (y := ghatC K a b h) (P := fwPoly K a b h 4)]
  have hkey : ((algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4))⁻¹) ^ 4
      * (algebraMap (MvPolynomial (Fin 3) K) (FracC K) (ghatC K a b h 4)) ^ 4 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hg4', one_pow]
  rw [hmain, hfw]
  exact mul_aux hkey

end UnitChartCAux

open UnitChartCAux

/-- **The unit chart identities of the T-twisted Crauder--Katz link.** -/
theorem UnitChartC (K : Type*) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Work.MotK.PsiCh K a b h (Work.MotK.FambC K a b h)
        * (algebraMap (MvPolynomial (Fin 3) K) (Work.MotK.FracC K) (Work.MotK.fhatC K a b h 4)) ^ 8
      = algebraMap (MvPolynomial (Fin 3) K) (Work.MotK.FracC K)
          (-(Work.MotK.kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                (Work.MotK.kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b)
                  (MvPolynomial.C h) (Work.MotK.pRaC K a b h) (Work.MotK.chartC K))) ^ 2
              * Work.MotK.kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                  (Work.MotK.pRaC K a b h) (Work.MotK.chartC K)
              * Work.MotK.GambC K a b h) ∧
    Work.MotK.PsiCh K a b h (Work.MotK.ghatC K a b h 4)
        * (algebraMap (MvPolynomial (Fin 3) K) (Work.MotK.FracC K) (Work.MotK.fhatC K a b h 4)) ^ 3
      = algebraMap (MvPolynomial (Fin 3) K) (Work.MotK.FracC K) (-(Work.MotK.GambC K a b h)) ∧
    Work.MotK.PhiCh K a b h (Work.MotK.GambC K a b h)
        * (algebraMap (MvPolynomial (Fin 3) K) (Work.MotK.FracC K) (Work.MotK.ghatC K a b h 4)) ^ 11
      = algebraMap (MvPolynomial (Fin 3) K) (Work.MotK.FracC K)
          (-(Work.MotK.kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                (Work.MotK.pRaC K a b h)
                (Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                  (Work.MotK.chartC K))) ^ 3
              * (Work.MotK.FambC K a b h) ^ 3) ∧
    Work.MotK.PhiCh K a b h (Work.MotK.fhatC K a b h 4)
        * (algebraMap (MvPolynomial (Fin 3) K) (Work.MotK.FracC K) (Work.MotK.ghatC K a b h 4)) ^ 4
      = algebraMap (MvPolynomial (Fin 3) K) (Work.MotK.FracC K)
          ((Work.MotK.kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                (Work.MotK.pRaC K a b h)
                (Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                  (Work.MotK.chartC K))) ^ 2
              * Work.MotK.kleinTwSDualInv (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                  (Work.MotK.chartC K)) := by
  refine ⟨clause1 K a b h ha hb hh (fhatC_four_ne_zero K a b h ha hb hh), ?_, ?_, ?_⟩
  · exact clause2 K a b h ha hb hh (fhatC_four_ne_zero K a b h ha hb hh)
      (ghatC_four_ne_zero K a b h ha hb hh)
  · exact clause3 K a b h ha hb hh (ghatC_four_ne_zero K a b h ha hb hh)
  · exact clause4 K a b h ha hb hh (ghatC_four_ne_zero K a b h ha hb hh)

end Work.MotK
