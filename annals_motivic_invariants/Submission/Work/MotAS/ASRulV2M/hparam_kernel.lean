import Mathlib
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASRulV2.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000

namespace Work.MotAS.ASRulV2M

open MvPolynomial

/-- The "corrected" AS ruling matrix `AmatAS2` agrees with `ASRul.AmatAS` (the matrix whose kernel
is computed by `ASRul.kernel_basis`) on every base-point vector. -/
theorem AmatAS2_eq_AmatAS {R : Type*} [CommRing R] (a b g : R) (c : Fin 5 → R) :
    Work.MotAS.AmatAS2 a b g c = Work.MotAS.ASRul.AmatAS a b g c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Work.MotAS.AmatAS2, Work.MotAS.ASRul.AmatAS] <;> ring)

/-- The elementary field identity behind the ratio formula: if `y₃ = c·δv` and `y₄ = d·δw` then
`(c·R + d·W)/y₄ = (y₃/y₄)·(R/δv) + W/δw`. -/
private lemma ratio_identity {K : Type*} [Field K] (y₃ y₄ R W δv δw : K)
    (hy₄ : y₄ ≠ 0) (hδv : δv ≠ 0) (hδw : δw ≠ 0) :
    ((y₃ / δv) * R + (y₄ / δw) * W) / y₄ = (y₃ / y₄) * R / δv + W / δw := by
  field_simp

theorem hparam_kernel {K : Type} [Field K] [CharP K 5] (a b g u v w : K) (y : Fin 5 → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : b ≠ 2 * a) (hg : g ≠ 0) (hw : w ≠ 0) (hy4 : y 4 ≠ 0)
    (hbase : ∀ j : Fin 5, MvPolynomial.eval ![u, v, w] (Work.MotAS.zcubAS a b g j) = 0)
    (hker : Matrix.mulVec (Work.MotAS.AmatAS2 a b g ![1, u, v, w, 0]) y = 0) :
    ∀ j : Fin 3,
      y (Work.MotAS.asCh3 j) / y 4
        = (y 3 / y 4) * (MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j)))
            / (MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRv a b g 3))
          + (MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j)))
            / (MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRw a b g 4)) := by
  -- the two constants `2a − b`, `a + 2b` are nonzero
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hA : 2 * a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hB : a + 2 * b ≠ 0 := by
    intro h0
    have hkey : 2 * a - b = 2 * (a + 2 * b) - 5 * b := by ring
    rw [h0, h5] at hkey
    exact hA (by simpa using hkey)
  have hδv : (2 * a - b) * (a + 2 * b) * w ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hA hB) (pow_ne_zero 2 hw)
  have hδw : (2 * a - b) * (a + 2 * b) ^ 2 * w ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hA (pow_ne_zero 2 hB)) (pow_ne_zero 2 hw)
  -- rewrite the hypothesis as a kernel condition for `ASRul.AmatAS`
  have hkerA : Matrix.mulVec (Work.MotAS.ASRul.AmatAS a b g ![1, u, v, w, 0]) y = 0 := by
    rw [← AmatAS2_eq_AmatAS a b g ![1, u, v, w, 0]]
    exact hker
  -- evaluations of the two ruling vectors
  have hrvE := Work.MotAS.ASRul.eval_kbRv a b g u v w
  have hrwE := Work.MotAS.ASRul.eval_kbRw a b g u v w
  have hrv3 : Work.MotAS.ASRul.rvEv a b g u v w 3 = (2 * a - b) * (a + 2 * b) * w ^ 2 := by
    simp [Work.MotAS.ASRul.rvEv]
  have hrv4 : Work.MotAS.ASRul.rvEv a b g u v w 4 = 0 := by
    simp [Work.MotAS.ASRul.rvEv]
  have hrw3 : Work.MotAS.ASRul.rwEv a b g u v w 3 = 0 := by
    simp [Work.MotAS.ASRul.rwEv]
  have hrw4 : Work.MotAS.ASRul.rwEv a b g u v w 4 = (2 * a - b) * (a + 2 * b) ^ 2 * w ^ 2 := by
    simp [Work.MotAS.ASRul.rwEv]
  -- the ruling point `zv` of the line through `y`, determined by its coordinates `3` and `4`
  set zv : Fin 5 → K :=
    (y 3 / ((2 * a - b) * (a + 2 * b) * w ^ 2)) • Work.MotAS.ASRul.rvEv a b g u v w
      + (y 4 / ((2 * a - b) * (a + 2 * b) ^ 2 * w ^ 2)) • Work.MotAS.ASRul.rwEv a b g u v w
    with hzv
  have hz3 : (y - zv) 3 = 0 := by
    have hc3 : y 3 / ((2 * a - b) * (a + 2 * b) * w ^ 2) * ((2 * a - b) * (a + 2 * b) * w ^ 2)
        = y 3 := div_mul_cancel₀ _ hδv
    rw [hzv]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hrv3, hrw3, mul_zero,
      add_zero, hc3, sub_self]
  have hz4 : (y - zv) 4 = 0 := by
    have hc4 : y 4 / ((2 * a - b) * (a + 2 * b) ^ 2 * w ^ 2)
        * ((2 * a - b) * (a + 2 * b) ^ 2 * w ^ 2) = y 4 := div_mul_cancel₀ _ hδw
    rw [hzv]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hrv4, hrw4, mul_zero,
      zero_add, hc4, sub_self]
  have hzvker : Matrix.mulVec (Work.MotAS.ASRul.AmatAS a b g ![1, u, v, w, 0]) zv = 0 := by
    rw [hzv, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Work.MotAS.ASRul.AmatAS_mulVec_kbRv_zero a b g u v w hA (hbase 4),
      Work.MotAS.ASRul.AmatAS_mulVec_kbRw_zero a b g u v w (hbase 3)]
    simp
  have hzm : Matrix.mulVec (Work.MotAS.ASRul.AmatAS a b g ![1, u, v, w, 0]) (y - zv) = 0 := by
    rw [Matrix.mulVec_sub, hkerA, hzvker, sub_zero]
  have hdecomp : y = zv :=
    sub_eq_zero.mp
      (Work.MotAS.ASRul.AmatAS_kernel_eq_zero a b g u v w hA hB hw (y - zv) hz3 hz4 hzm)
  intro j
  have hRj : MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j))
      = Work.MotAS.ASRul.rvEv a b g u v w (Work.MotAS.asCh3 j) := congrFun hrvE _
  have hWj : MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j))
      = Work.MotAS.ASRul.rwEv a b g u v w (Work.MotAS.asCh3 j) := congrFun hrwE _
  have hR3 : MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRv a b g 3)
      = (2 * a - b) * (a + 2 * b) * w ^ 2 := by
    rw [congrFun hrvE 3, hrv3]
  have hW4 : MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRw a b g 4)
      = (2 * a - b) * (a + 2 * b) ^ 2 * w ^ 2 := by
    rw [congrFun hrwE 4, hrw4]
  rw [congrFun hdecomp (Work.MotAS.asCh3 j), hzv, hRj, hWj, hR3, hW4]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact ratio_identity (y 3) (y 4) _ _ _ _ hy4 hδv hδw

end Work.MotAS.ASRulV2M
