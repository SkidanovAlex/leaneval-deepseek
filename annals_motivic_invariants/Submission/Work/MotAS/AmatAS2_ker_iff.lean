import Mathlib
import Submission.Work.MotAS.ASRulingVec3
import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASrulV3_mem
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The kernel of the AS ruling matrix at a point of the residual curve

For `K` a field of characteristic `5` and `a b g : K` with `a * b ≠ 0` and
`a ^ 2 - a * b - b ^ 2 ≠ 0`, the kernel of the AS ruling matrix `AmatAS2 a b g c` at a point
`c = (x0, x1, x2, 1, 0)` of the AS residual curve `ZIAS3 a b g` is spanned by the two ruling
vectors `ASrulV3 a b g` and `ASrulW3 a b g` (evaluated at `(x0, x1, x2)`).

The proof splits into the two directions.

* `←`: the ruling vectors lie in the kernel.  In characteristic `5` the components `0..3` of
  `AmatAS2 … (asBaseVec3 K) *ᵥ ASrulV3 a b g` (resp. `… *ᵥ ASrulW3 a b g`) vanish identically;
  for the last component one has
  `… ∈ radical (ZIAS3 a b g)` for `ASrulV3` (`Work.MotAS.ASrulV3_mem`) and
  `… ∈ ZIAS3 a b g` for `ASrulW3` (proved below via the explicit certificate `asRulW3_H`).
  Evaluating at `(x0, x1, x2)` — where all five generators of `ZIAS3` vanish by `hbase` —
  therefore gives `0`.

* `→`: at the chart `{c₃ = 1, c₄ = 0}` the rows `0, 1, 2` of the matrix have pivots the
  *constants* `-(a + 2b)`, `a + 2b`, `-(2a - b)`, all non-zero since
  `2 * (a ^ 2 - a * b - b ^ 2) = (a + 2b) * (2a - b)` and, in characteristic `5`,
  `a ^ 2 - a * b - b ^ 2 = (a - 3b) * (a + 2b) + 5 * b ^ 2`.  Hence a vector of the kernel is
  determined by its last two coordinates, which are exactly the parameters of the two ruling
  vectors (their `3`rd resp. `4`th components are `(2a-b)(a+2b)` and `(a+2b)^2 (2a-b)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS

open MvPolynomial Matrix

/-- Explicit certificate: in every commutative ring,
`(AmatAS2 (C a) (C b) (C g) (asBaseVec3 K) *ᵥ ASrulW3 a b g) 4 + kleinRAS … 3 = 5 * asRulW3_H K a b g`. -/
private noncomputable def asRulW3_H (K : Type*) [CommRing K] (a b g : K) :
    MvPolynomial (Fin 3) K :=
  2 * ((C a) ^ 4 * (X 0) ^ 2) + 3 * ((C a) ^ 4 * X 0 * X 1 * X 2) + 3 * ((C a) ^ 4 * X 0 * X 2)
   + (-1) * ((C a) ^ 4 * (X 1) ^ 3) + (-1) * ((C a) ^ 4 * (X 1) ^ 2)
   + (-3) * ((C a) ^ 4 * X 1 * (X 2) ^ 2) + 2 * ((C a) ^ 4 * X 1)
   + (-5) * ((C a) ^ 4 * (X 2) ^ 2) + 2 * (C a) ^ 4 + (-2) * ((C a) ^ 3 * C b * C g * X 2)
   + ((C a) ^ 3 * C b * (X 0) ^ 2) + (-6) * ((C a) ^ 3 * C b * X 0 * X 1 * X 2)
   + (-3) * ((C a) ^ 3 * C b * X 0 * X 2) + (-2) * ((C a) ^ 3 * C b * (X 1) ^ 3)
   + (-5) * ((C a) ^ 3 * C b * (X 1) ^ 2) + 3 * ((C a) ^ 3 * C b * X 1 * (X 2) ^ 2)
   + 3 * ((C a) ^ 3 * C b * X 1) + (-4) * ((C a) ^ 3 * C b * (X 2) ^ 2) + 5 * ((C a) ^ 3 * C b)
   + (-4) * ((C a) ^ 2 * (C b) ^ 2 * C g * X 2) + (-4) * ((C a) ^ 2 * (C b) ^ 2 * (X 0) ^ 2)
   + 5 * ((C a) ^ 2 * (C b) ^ 2 * X 0 * X 1 * X 2)
   + (-11) * ((C a) ^ 2 * (C b) ^ 2 * (X 1) ^ 2) + (-4) * ((C a) ^ 2 * (C b) ^ 2 * X 1)
   + 3 * ((C a) ^ 2 * (C b) ^ 2) + (-1) * (C a * (C b) ^ 3 * C g * X 2)
   + 2 * (C a * (C b) ^ 3 * (X 0) ^ 2) + (-2) * (C a * (C b) ^ 3 * X 0 * X 1 * X 2)
   + (C a * (C b) ^ 3 * X 0 * X 2) + 2 * (C a * (C b) ^ 3 * (X 1) ^ 3)
   + (-7) * (C a * (C b) ^ 3 * (X 1) ^ 2) + (-1) * (C a * (C b) ^ 3 * X 1 * (X 2) ^ 2)
   + (-4) * (C a * (C b) ^ 3 * X 1) + (C a * (C b) ^ 3 * (X 2) ^ 2) + (-1) * (C a * (C b) ^ 3)
   + 2 * ((C b) ^ 4 * C g * X 2) + (-1) * ((C b) ^ 4 * (X 1) ^ 3) + ((C b) ^ 4 * (X 1) ^ 2)
   + 3 * ((C b) ^ 4 * X 1) + (C b) ^ 4

/-- **The chart-`{c₃ = 1, c₄ = 0}` W-ruling vector lies in the AS residual ideal.**  Components
`0…3` of `AmatAS2 ⋯ (asBaseVec3 K) *ᵥ ASrulW3 a b g` vanish identically and component `4` differs
from `-kleinRAS ⋯ 3` by a multiple of `5`, hence lies in `ZIAS3 a b g`. -/
theorem ASrulW3_mem_ideal (K : Type) [Field K] [CharP K 5] (a b g : K) (i : Fin 5) :
    Matrix.mulVec (AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (asBaseVec3 K)) (ASrulW3 a b g) i
      ∈ ZIAS3 a b g := by
  have h0 : Matrix.mulVec (AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (asBaseVec3 K)) (ASrulW3 a b g) 0 = 0 := by
    simp only [AmatAS2, ASrulW3, asBaseVec3, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
      map_add, map_sub, map_mul, map_pow, map_ofNat, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Fin.isValue, Matrix.of_apply]
    refl_ring1
  have h1 : Matrix.mulVec (AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (asBaseVec3 K)) (ASrulW3 a b g) 1 = 0 := by
    simp only [AmatAS2, ASrulW3, asBaseVec3, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
      map_add, map_sub, map_mul, map_pow, map_ofNat, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Fin.isValue, Matrix.of_apply]
    refl_ring1
  have h2 : Matrix.mulVec (AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (asBaseVec3 K)) (ASrulW3 a b g) 2 = 0 := by
    simp only [AmatAS2, ASrulW3, asBaseVec3, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
      map_add, map_sub, map_mul, map_pow, map_ofNat, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Fin.isValue, Matrix.of_apply]
    refl_ring1
  have h3 : Matrix.mulVec (AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (asBaseVec3 K)) (ASrulW3 a b g) 3 = 0 := by
    simp only [AmatAS2, ASrulW3, asBaseVec3, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
      map_add, map_sub, map_mul, map_pow, map_ofNat, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Fin.isValue, Matrix.of_apply]
    refl_ring1
  have h4 : Matrix.mulVec (AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (asBaseVec3 K)) (ASrulW3 a b g) 4
      = (-1 : MvPolynomial (Fin 3) K) * kleinRAS (MvPolynomial.C a) (MvPolynomial.C b)
          (MvPolynomial.C g) (asBaseVec3 K) 3 := by
    rw [← neg_eq_neg_one_mul, eq_neg_iff_add_eq_zero]
    have hid : Matrix.mulVec (AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (asBaseVec3 K)) (ASrulW3 a b g) 4
        + kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (asBaseVec3 K) 3
        = 5 * asRulW3_H K a b g := by
      simp only [AmatAS2, ASrulW3, asBaseVec3, asRulW3_H, kleinRAS, kleinRAS0, kleinRAS1,
        kleinRAS2, kleinRAS3, kleinRAS4, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Fin.isValue,
        map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_zero]
      refl_ring1
    have h5 : (5 : MvPolynomial (Fin 3) K) = 0 := CharP.cast_eq_zero _ 5
    rw [h5, zero_mul] at hid
    exact hid
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    fin_cases i <;> simp
  rcases hi with h | h | h | h | h
  · rw [h, h0]; exact Ideal.zero_mem _
  · rw [h, h1]; exact Ideal.zero_mem _
  · rw [h, h2]; exact Ideal.zero_mem _
  · rw [h, h3]; exact Ideal.zero_mem _
  · rw [h, h4]
    exact Ideal.mul_mem_left _ (-1) (Ideal.subset_span (Set.mem_range_self 3))

/-- Row `0` of the AS ruling matrix in the chart `{c₃ = 1, c₄ = 0}`. -/
private theorem row0 (K : Type) [Field K] (a b g x0 x1 x2 : K) (z : Fin 5 → K)
    (h3 : z 3 = 0) (h4 : z 4 = 0) :
    Matrix.mulVec (AmatAS2 a b g ![x0, x1, x2, 1, 0]) z 0 = -(a + 2 * b) * z 2 := by
  simp only [AmatAS2, Matrix.mulVec, dotProduct, Fin.sum_univ_five, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Fin.isValue, h3, h4, mul_zero,
    add_zero, zero_add]
  refl_ring1

/-- Row `1` of the AS ruling matrix in the chart `{c₃ = 1, c₄ = 0}`. -/
private theorem row1 (K : Type) [Field K] (a b g x0 x1 x2 : K) (z : Fin 5 → K)
    (h2 : z 2 = 0) (h3 : z 3 = 0) (h4 : z 4 = 0) :
    Matrix.mulVec (AmatAS2 a b g ![x0, x1, x2, 1, 0]) z 1 = (a + 2 * b) * z 1 := by
  simp only [AmatAS2, Matrix.mulVec, dotProduct, Fin.sum_univ_five, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Fin.isValue, h2, h3, h4, mul_zero,
    add_zero, zero_add]
  refl_ring1

/-- Row `2` of the AS ruling matrix in the chart `{c₃ = 1, c₄ = 0}`. -/
private theorem row2 (K : Type) [Field K] (a b g x0 x1 x2 : K) (z : Fin 5 → K)
    (h1 : z 1 = 0) (h2 : z 2 = 0) (h3 : z 3 = 0) (h4 : z 4 = 0) :
    Matrix.mulVec (AmatAS2 a b g ![x0, x1, x2, 1, 0]) z 2 = -(2 * a - b) * z 0 := by
  simp only [AmatAS2, Matrix.mulVec, dotProduct, Fin.sum_univ_five, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Fin.isValue, h1, h2, h3, h4, mul_zero,
    add_zero, zero_add]
  refl_ring1



theorem AmatAS2_ker_iff (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hab : a * b ≠ 0) (hd : a ^ 2 - a * b - b ^ 2 ≠ 0) (x0 x1 x2 : K)
    (hbase : ∀ k : Fin 5, MvPolynomial.eval ![x0, x1, x2]
        (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (Work.MotAS.asBaseVec3 K) k) = 0)
    (y : Fin 5 → K) :
    Matrix.mulVec (Work.MotAS.AmatAS2 a b g ![x0, x1, x2, 1, 0]) y = 0 ↔
      ∃ α β : K, y = α • (fun i => MvPolynomial.eval ![x0, x1, x2] (Work.MotAS.ASrulV3 a b g i))
        + β • (fun i => MvPolynomial.eval ![x0, x1, x2] (Work.MotAS.ASrulW3 a b g i)) := by
  set v : Fin 5 → K := fun i => MvPolynomial.eval ![x0, x1, x2] (ASrulV3 a b g i) with hvdef
  set w : Fin 5 → K := fun i => MvPolynomial.eval ![x0, x1, x2] (ASrulW3 a b g i) with hwdef
  -- ## Step 0: the entries of the ruling vectors
  have hv3 : v 3 = (2 * a - b) * (a + 2 * b) := by
    rw [hvdef]
    simp only [ASrulV3, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_four,
      Matrix.of_apply, Fin.isValue, map_mul, MvPolynomial.eval_C]
  have hv4 : v 4 = 0 := by
    rw [hvdef]
    simp [ASrulV3]
  have hw3 : w 3 = 0 := by
    rw [hwdef]
    simp [ASrulW3]
  have hw4 : w 4 = (a + 2 * b) ^ 2 * (2 * a - b) := by
    rw [hwdef]
    simp only [ASrulW3, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.of_apply, Fin.isValue, map_mul, map_pow, MvPolynomial.eval_C]
  -- ## Step 1: the two matrices are related by evaluation
  have hM : (AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (asBaseVec3 K)).map (MvPolynomial.eval ![x0, x1, x2])
      = AmatAS2 a b g ![x0, x1, x2, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.map_apply, AmatAS2, asBaseVec3, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_succ, Matrix.head_cons,
        Matrix.tail_cons, Fin.isValue, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg,
        map_zero, map_one, MvPolynomial.eval_X, MvPolynomial.eval_C] <;>
      refl_ring1
  -- ## Step 2: non-degeneracy of the two pivots
  have hs : a + 2 * b ≠ 0 := by
    intro h
    apply hd
    have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
    have e1 : a ^ 2 - a * b - b ^ 2 = (a - 3 * b) * (a + 2 * b) + 5 * b ^ 2 := by ring
    rw [e1, h, h5]
    refl_ring1
  have ht : 2 * a - b ≠ 0 := by
    intro h
    apply hd
    have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
    have e1 : a ^ 2 - a * b - b ^ 2 = (3 * a + b) * (2 * a - b) - 5 * a ^ 2 := by ring
    rw [e1, h, h5]
    refl_ring1
  have hst : (2 * a - b) * (a + 2 * b) ≠ 0 := mul_ne_zero ht hs
  have hμ : (a + 2 * b) ^ 2 * (2 * a - b) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hs) ht
  -- ## Step 2: evaluation at the base point kills the residual ideal
  have hkillI : ∀ x ∈ ZIAS3 a b g, MvPolynomial.eval ![x0, x1, x2] x = 0 := by
    have hle : ZIAS3 a b g ≤ RingHom.ker (MvPolynomial.eval ![x0, x1, x2] :
        MvPolynomial (Fin 3) K →+* K) := by
      rw [ZIAS3, Ideal.span_le]
      rintro x ⟨k, rfl⟩
      exact hbase k
    intro x hx
    exact hle hx
  have hkillR : ∀ x ∈ Ideal.radical (ZIAS3 a b g),
      MvPolynomial.eval ![x0, x1, x2] x = 0 := by
    intro x hx
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
    have h : MvPolynomial.eval ![x0, x1, x2] x ^ n = 0 := by
      rw [← map_pow]
      exact hkillI _ hn
    by_contra hx0
    exact absurd h (pow_ne_zero n hx0)
  -- ## Step 3: the two ruling vectors lie in the kernel at the base point
  have hcv : (MvPolynomial.eval ![x0, x1, x2]) ∘ (ASrulV3 a b g) = v := by
    rw [hvdef]
    rfl
  have hcw : (MvPolynomial.eval ![x0, x1, x2]) ∘ (ASrulW3 a b g) = w := by
    rw [hwdef]
    rfl
  have hMv : Matrix.mulVec (AmatAS2 a b g ![x0, x1, x2, 1, 0]) v = 0 := by
    rw [← hM]
    have h1 : Matrix.mulVec ((AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (asBaseVec3 K)).map (MvPolynomial.eval ![x0, x1, x2])) v
        = fun i => MvPolynomial.eval ![x0, x1, x2]
            (Matrix.mulVec (AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
              (asBaseVec3 K)) (ASrulV3 a b g) i) := by
      funext i
      rw [← hcv, RingHom.map_mulVec]
    rw [h1]
    funext i
    simp only [Pi.zero_apply]
    exact hkillR _ (ASrulV3_mem K a b g i)
  have hMw : Matrix.mulVec (AmatAS2 a b g ![x0, x1, x2, 1, 0]) w = 0 := by
    rw [← hM]
    have h1 : Matrix.mulVec ((AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (asBaseVec3 K)).map (MvPolynomial.eval ![x0, x1, x2])) w
        = fun i => MvPolynomial.eval ![x0, x1, x2]
            (Matrix.mulVec (AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
              (asBaseVec3 K)) (ASrulW3 a b g) i) := by
      funext i
      rw [← hcw, RingHom.map_mulVec]
    rw [h1]
    funext i
    simp only [Pi.zero_apply]
    exact hkillI _ (ASrulW3_mem_ideal K a b g i)
  constructor
  · -- ## Step 4: `→`, the kernel is spanned by the two ruling vectors
    intro hy
    refine ⟨y 3 / ((2 * a - b) * (a + 2 * b)), y 4 / ((a + 2 * b) ^ 2 * (2 * a - b)), ?_⟩
    set z : Fin 5 → K := y - (y 3 / ((2 * a - b) * (a + 2 * b))) • v
      - (y 4 / ((a + 2 * b) ^ 2 * (2 * a - b))) • w with hzdef
    have hz3 : z 3 = 0 := by
      rw [hzdef]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hv3, hv4, hw3, hw4, mul_zero,
        sub_zero]
      rw [div_mul_cancel₀ (y 3) hst]
      refl_ring1
    have hz4 : z 4 = 0 := by
      rw [hzdef]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hv3, hv4, hw3, hw4, mul_zero,
        sub_zero]
      rw [div_mul_cancel₀ (y 4) hμ]
      refl_ring1
    have hMz : Matrix.mulVec (AmatAS2 a b g ![x0, x1, x2, 1, 0]) z = 0 := by
      rw [hzdef]
      rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hy, hMv, hMw]
      simp
    have hz2 : z 2 = 0 := by
      have h := congrFun hMz 0
      simp only [Pi.zero_apply] at h
      rw [row0 K a b g x0 x1 x2 z hz3 hz4] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd (neg_eq_zero.mp h') hs
      · exact h'
    have hz1 : z 1 = 0 := by
      have h := congrFun hMz 1
      simp only [Pi.zero_apply] at h
      rw [row1 K a b g x0 x1 x2 z hz2 hz3 hz4] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hs
      · exact h'
    have hz0 : z 0 = 0 := by
      have h := congrFun hMz 2
      simp only [Pi.zero_apply] at h
      rw [row2 K a b g x0 x1 x2 z hz1 hz2 hz3 hz4] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd (neg_eq_zero.mp h') ht
      · exact h'
    have hz : z = 0 := by
      funext i
      fin_cases i
      · exact hz0
      · exact hz1
      · exact hz2
      · exact hz3
      · exact hz4
    have hz' : y - ((y 3 / ((2 * a - b) * (a + 2 * b))) • v
        + (y 4 / ((a + 2 * b) ^ 2 * (2 * a - b))) • w) = 0 := by
      rw [← sub_sub]
      rw [← hzdef]
      exact hz
    exact sub_eq_zero.mp hz'
  · -- ## Step 5: `←`, any combination of the ruling vectors is in the kernel
    rintro ⟨α, β, rfl⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hMv, hMw]
    simp

end Work.MotAS
