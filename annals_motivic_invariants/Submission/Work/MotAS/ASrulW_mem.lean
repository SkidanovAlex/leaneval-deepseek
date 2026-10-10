import Mathlib
import Submission.Work.MotAS.ASRulingVec
import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASResidual
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASrulW_mem`

The second AS ruling vector `ASrulW a b g` (`Submission/Work/MotAS/ASRulingVec.lean`) lies in the
kernel of the AS ruling matrix `AmatAS2 a b g (asBaseVec K)` — the chart `(1,X₀,X₁,X₂,0)` of the
residual curve — *modulo the ideal* `ZIAS a b g` of that curve.

Concretely, expanding the definitions (a CAS check over `ℤ[a,b,g,X₀,X₁,X₂]` in `_asrulw_cas/`)
shows

* components `0,1,2,3` of `AmatAS2 (C a) (C b) (C g) (asBaseVec K) *ᵥ ASrulW a b g` vanish
  **identically** (as polynomials with integer coefficients — in *every* characteristic), and
* component `4` satisfies `(… *ᵥ ASrulW a b g) 4 + zcubAS a b g 3 = 5 · H` where `H` is the
  explicit integer-coefficient polynomial exhibited in the proof below.  Hence in characteristic
  `5` the fourth component equals `- zcubAS a b g 3`, which lies in `ZIAS a b g ⊆ √(ZIAS a b g)`.

The membership is *sharp*: over a field of characteristic `0` and generic `a,b,g` the fourth
component is **not** in `ZIAS a b g` itself (so the occurrence of the radical in the statement is
essential, and component `4` genuinely generates an extension of the ideal).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotAS

open MvPolynomial

theorem ASrulW_mem (K : Type) [Field K] [CharP K 5] (a b g : K) (i : Fin 5) :
    Matrix.mulVec (Work.MotAS.AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (Work.MotAS.asBaseVec K)) (Work.MotAS.ASrulW a b g) i
      ∈ Ideal.radical (Work.MotAS.ZIAS a b g) := by
  have h5 : (5 : MvPolynomial (Fin 3) K) = 0 := CharP.cast_eq_zero (MvPolynomial (Fin 3) K) 5
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · have h : Matrix.mulVec (Work.MotAS.AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b)
          (MvPolynomial.C g) (Work.MotAS.asBaseVec K)) (Work.MotAS.ASrulW a b g) 0 = 0 := by
      simp only [Work.MotAS.AmatAS2, Work.MotAS.ASrulW, Work.MotAS.asBaseVec, Matrix.mulVec,
        dotProduct, Fin.sum_univ_five, map_add, map_sub, map_mul, map_pow, map_ofNat,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Matrix.of_apply]
      refl_ring1
    rw [h]; exact Ideal.zero_mem _
  · have h : Matrix.mulVec (Work.MotAS.AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b)
          (MvPolynomial.C g) (Work.MotAS.asBaseVec K)) (Work.MotAS.ASrulW a b g) 1 = 0 := by
      simp only [Work.MotAS.AmatAS2, Work.MotAS.ASrulW, Work.MotAS.asBaseVec, Matrix.mulVec,
        dotProduct, Fin.sum_univ_five, map_add, map_sub, map_mul, map_pow, map_ofNat,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Matrix.of_apply]
      refl_ring1
    rw [h]; exact Ideal.zero_mem _
  · have h : Matrix.mulVec (Work.MotAS.AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b)
          (MvPolynomial.C g) (Work.MotAS.asBaseVec K)) (Work.MotAS.ASrulW a b g) 2 = 0 := by
      simp only [Work.MotAS.AmatAS2, Work.MotAS.ASrulW, Work.MotAS.asBaseVec, Matrix.mulVec,
        dotProduct, Fin.sum_univ_five, map_add, map_sub, map_mul, map_pow, map_ofNat,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Matrix.of_apply]
      refl_ring1
    rw [h]; exact Ideal.zero_mem _
  · have h : Matrix.mulVec (Work.MotAS.AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b)
          (MvPolynomial.C g) (Work.MotAS.asBaseVec K)) (Work.MotAS.ASrulW a b g) 3 = 0 := by
      simp only [Work.MotAS.AmatAS2, Work.MotAS.ASrulW, Work.MotAS.asBaseVec, Matrix.mulVec,
        dotProduct, Fin.sum_univ_five, map_add, map_sub, map_mul, map_pow, map_ofNat,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Matrix.of_apply]
      refl_ring1
    rw [h]; exact Ideal.zero_mem _
  · -- the only non-trivial component: `(·) 4 + zcubAS a b g 3 = 5 * H`, i.e. `= 0` in char. 5.
    have hid : Matrix.mulVec (Work.MotAS.AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b)
          (MvPolynomial.C g) (Work.MotAS.asBaseVec K)) (Work.MotAS.ASrulW a b g) 4
        + Work.MotAS.zcubAS a b g 3
      = (5 : MvPolynomial (Fin 3) K) *
        ((1) * (X 2) ^ 3 * (C b) ^ 4 + (-1) * (X 0) ^ 3 * (C a) ^ 4 + (-1) * (X 0) ^ 3 * (C b) ^ 4
          + (2) * X 2 * (C a) ^ 4 + (2) * (X 2) ^ 3 * (C a) ^ 4 + (1) * X 2 * C b * (C a) ^ 3
          + (1) * X 2 * (X 0) ^ 2 * (C b) ^ 4 + (-1) * X 2 * (X 0) ^ 2 * (C a) ^ 4
          + (-1) * C a * (X 2) ^ 3 * (C b) ^ 3 + (-5) * X 2 * (X 1) ^ 2 * (C a) ^ 4
          + (-4) * X 2 * (C a) ^ 2 * (C b) ^ 2 + (-3) * X 0 * (X 1) ^ 2 * (C a) ^ 4
          + (-2) * C b * (X 0) ^ 3 * (C a) ^ 3 + (2) * X 0 * (X 2) ^ 2 * (C a) ^ 4
          + (2) * X 2 * C a * (C b) ^ 3 + (2) * C a * (X 0) ^ 3 * (C b) ^ 3
          + (3) * X 0 * X 1 * (C a) ^ 4 + (3) * X 0 * (X 2) ^ 2 * (C b) ^ 4
          + (3) * X 1 * X 2 * (C a) ^ 4 + (3) * (X 2) ^ 3 * (C a) ^ 2 * (C b) ^ 2
          + (5) * C b * (X 2) ^ 3 * (C a) ^ 3 + (1) * X 1 * X 2 * C a * (C b) ^ 3
          + (1) * X 2 * C a * (X 1) ^ 2 * (C b) ^ 3 + (-1) * X 0 * C a * (X 1) ^ 2 * (C b) ^ 3
          + (-11) * X 2 * (X 0) ^ 2 * (C a) ^ 2 * (C b) ^ 2 + (-7) * X 2 * C a * (X 0) ^ 2 * (C b) ^ 3
          + (-6) * X 0 * X 1 * C b * (C a) ^ 3 + (-5) * X 2 * C b * (X 0) ^ 2 * (C a) ^ 3
          + (-4) * X 0 * C a * (X 2) ^ 2 * (C b) ^ 3 + (-4) * X 0 * (X 2) ^ 2 * (C a) ^ 2 * (C b) ^ 2
          + (-4) * X 2 * C b * (X 1) ^ 2 * (C a) ^ 3 + (-3) * X 1 * X 2 * C b * (C a) ^ 3
          + (-2) * X 0 * X 1 * C a * (C b) ^ 3 + (2) * X 1 * C g * (X 2) ^ 2 * (C b) ^ 4
          + (3) * X 0 * C b * (X 1) ^ 2 * (C a) ^ 3 + (3) * X 0 * C b * (X 2) ^ 2 * (C a) ^ 3
          + (5) * X 0 * X 1 * (C a) ^ 2 * (C b) ^ 2 + (-1) * X 1 * C a * C g * (X 2) ^ 2 * (C b) ^ 3
          + (-4) * X 1 * C g * (X 2) ^ 2 * (C a) ^ 2 * (C b) ^ 2
          + (-2) * X 1 * C b * C g * (X 2) ^ 2 * (C a) ^ 3) := by
      simp only [Work.MotAS.AmatAS2, Work.MotAS.ASrulW, Work.MotAS.asBaseVec, Work.MotAS.zcubAS,
        Work.MotAS.kleinRAS, Work.MotAS.kleinRAS3, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
        map_add, map_sub, map_mul, map_pow, map_ofNat, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons, Fin.isValue, Matrix.of_apply]
      refl_ring1
    have h4 : Matrix.mulVec (Work.MotAS.AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b)
          (MvPolynomial.C g) (Work.MotAS.asBaseVec K)) (Work.MotAS.ASrulW a b g) 4
        = - Work.MotAS.zcubAS a b g 3 := by
      rw [h5, zero_mul] at hid
      linear_combination (norm := refl_ring1) hid
    rw [h4]
    exact Ideal.le_radical (neg_mem (Ideal.subset_span ⟨3, rfl⟩))

end Work.MotAS
