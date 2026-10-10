import Mathlib
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASRulV2.Defs
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASRulingMain
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedSimpArgs false

namespace Work.MotC5N3

/-- **The ruling parametrisation of a point of the source ruling line over a base point
`(1,u,v,w,0)` of the AS residual curve.**

`K` is a field of characteristic `5`, `a b g : K` with `a b ≠ 0`, `b ≠ 2a`, `g ≠ 0`,
`(u,v,w) ∈ V(ZIAS)` with `w ≠ 0`, and `y` is a point of the ruling line over the base point, i.e.
`AmatAS2 a b g ![1,u,v,w,0] *ᵥ y = 0`, with `y 4 ≠ 0`.  Then the chart coordinates of `y` are the
ruling parametrisation: for `j : Fin 3`,

`y (asCh3 j)/y 4 = (y 3/y 4) * ev (kbRv (asCh3 j)) / ev (kbRv 3) + ev (kbRw (asCh3 j)) / ev (kbRw 4)`

where `ev q = MvPolynomial.eval ![u,v,w] q`.

PROOF ROUTE.  This is a pure consequence of the (already proved, sorry-free)
`Work.MotAS.ASRul.kernel_basis a b g ha hb hab hg`, whose proof uses the explicit witnesses
`rv = kbRv a b g`, `rw = kbRw a b g`.  Copy that proof script (it is in this workspace, readable)
with the witnesses inlined, so as to obtain the spanning statement for `kbRv`, `kbRw`; the only
extra ingredient is `Work.MotAS.ASRul.AmatAS_eq_AmatAS2` (proved in
`Submission/Work/MotAS/ASRulingMain.lean`).  Then `y = c • ev kbRv + d • ev kbRw`.  The four pivot
values are proved in `ASRulingMain.lean`: `ev (kbRv 3) = (2a−b)(a+2b)w²`, `ev (kbRv 4) = 0`,
`ev (kbRw 3) = 0`, `ev (kbRw 4) = (a+2b)²(2a−b)w² = (a+2b) · ev (kbRv 3)`
(`Work.MotAS.eval_kbRv_three`, `Work.MotAS.eval_kbRv_four`, `Work.MotAS.eval_kbRw_three`,
`Work.MotAS.eval_kbRw_four`).  Hence `y 3 = c · ev (kbRv 3)`, `y 4 = d · ev (kbRw 4)`, and the
claim follows by dividing — the identity holds for every point of the ruling line, not just one. -/
theorem hparam_kernel {K : Type} [Field K] [CharP K 5] (a b g u v w : K) (y : Fin 5 → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : b ≠ 2 * a) (hg : g ≠ 0) (hw : w ≠ 0) (hy4 : y 4 ≠ 0)
    (hbase : ∀ j : Fin 5, MvPolynomial.eval ![u, v, w] (Work.MotAS.zcubAS a b g j) = 0)
    (hker : Matrix.mulVec (Work.MotAS.AmatAS2 a b g ![1, u, v, w, 0]) y = 0) :
    ∀ j : Fin 3,
      y (Work.MotAS.asCh3 j) / y 4
        = (y 3 / y 4) * (MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRv a b g
              (Work.MotAS.asCh3 j)))
            / (MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRv a b g 3))
          + (MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRw a b g
              (Work.MotAS.asCh3 j)))
            / (MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRw a b g 4)) := by
  -- characteristic `5` and the non-vanishing of the two pivot values
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hA : 2 * a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hB : a + 2 * b ≠ 0 := by
    intro h
    apply hA
    linear_combination (norm := first | refl_ring1 | ring1) (-3) * h + (a + b) * h5
  -- the kernel of `AmatAS2` is that of `AmatAS`
  have hker' : Matrix.mulVec (Work.MotAS.ASRul.AmatAS a b g ![1, u, v, w, 0]) y = 0 := by
    rw [Work.MotAS.ASRul.AmatAS_eq_AmatAS2]
    exact hker
  have hrv := Work.MotAS.ASRul.AmatAS_mulVec_kbRv_zero a b g u v w hA (hbase 4)
  have hrw := Work.MotAS.ASRul.AmatAS_mulVec_kbRw_zero a b g u v w (hbase 3)
  have hdv : (2 * a - b) * (a + 2 * b) * w ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hA hB) (pow_ne_zero 2 hw)
  have hdw : (2 * a - b) * (a + 2 * b) ^ 2 * w ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hA (pow_ne_zero 2 hB)) (pow_ne_zero 2 hw)
  -- subtract the explicit combination from `y`; the difference lies in the kernel and has
  -- vanishing last two coordinates, hence is zero
  have hz := Work.MotAS.ASRul.AmatAS_kernel_eq_zero a b g u v w hA hB hw
      (y - ((y 3 / ((2 * a - b) * (a + 2 * b) * w ^ 2)) • Work.MotAS.ASRul.rvEv a b g u v w
        + (y 4 / ((2 * a - b) * (a + 2 * b) ^ 2 * w ^ 2)) • Work.MotAS.ASRul.rwEv a b g u v w))
      (by
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Work.MotAS.ASRul.rvEv, Work.MotAS.ASRul.rwEv, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
          Matrix.head_cons, Matrix.tail_cons, Matrix.empty_eq, Fin.isValue,
          div_mul_cancel₀ _ hdv, mul_zero, add_zero, sub_self])
      (by
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Work.MotAS.ASRul.rvEv, Work.MotAS.ASRul.rwEv, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
          Matrix.head_cons, Matrix.tail_cons, Matrix.empty_eq, Fin.isValue,
          div_mul_cancel₀ _ hdw, mul_zero, zero_add, add_zero, sub_self])
      (by
        rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hker',
          hrv, hrw]
        simp)
  -- hence `y` is the explicit combination of the two evaluated ruling vectors
  have hy : y = (y 3 / ((2 * a - b) * (a + 2 * b) * w ^ 2)) • Work.MotAS.ASRul.rvEv a b g u v w
        + (y 4 / ((2 * a - b) * (a + 2 * b) ^ 2 * w ^ 2)) • Work.MotAS.ASRul.rwEv a b g u v w :=
    sub_eq_zero.mp hz
  -- rewrite everything in terms of the evaluations of `kbRv`, `kbRw`
  have hyEv : ∀ i : Fin 5, y i
      = (y 3 / ((2 * a - b) * (a + 2 * b) * w ^ 2))
          * (MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRv a b g i))
        + (y 4 / ((2 * a - b) * (a + 2 * b) ^ 2 * w ^ 2))
          * (MvPolynomial.eval ![u, v, w] (Work.MotAS.ASRul.kbRw a b g i)) := by
    intro i
    have hi := congrFun hy i
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at hi
    rw [hi, congrFun (Work.MotAS.ASRul.eval_kbRv a b g u v w) i,
      congrFun (Work.MotAS.ASRul.eval_kbRw a b g u v w) i]
  -- the two pivot evaluations
  intro j
  rw [hyEv (Work.MotAS.asCh3 j), Work.MotAS.eval_kbRv_three, Work.MotAS.eval_kbRw_four]
  field_simp [hdv, hdw, hy4]

end Work.MotC5N3
