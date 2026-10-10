import Mathlib
import Submission.Work.MotAS.ASRul.SrcRul
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASChart2Defs
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.MotAS.KleinTwScalarASv
import Submission.Work.MotAS.ASRul.det_submatrix_kleinMAS
import Submission.Work.MotAS.ASRul.kleinMAS_fibre
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRul.sAS2_ruling_mem`

The source ruling divisor `sAS2` vanishes on the ruling lines of the AS (`CharP · 5`)
Crauder–Katz link: for every base point `(u,v,w)` of the residual curve `V(ZIAS)` with `w ≠ 0` and
every ruling parameter `t`, the chart point `srcRulPt` of the ruling line over `(1 : u : v : w : 0)`
lies on `V(sAS2)`.

The proof (`K =` the field, `c = (1,u,v,w,0)`, `z = t • rvEv + rwEv` the ruling point):

* `z` is in the kernel of the AS ruling matrix over `c` (`AmatAS2 a b g c · z = 0`), i.e.
  `kleinMAS a b g z *ᵥ c = 0` (`AmatAS2_mulVec` + the chart identification `AmatAS2 = AmatAS`),
  because the two ruling vectors `rvEv, rwEv` are in that kernel
  (`AmatAS_mulVec_kbRv_zero`, `AmatAS_mulVec_kbRw_zero`);
* hence, by the AS fibre lemma `kleinMAS_fibre`, either `kleinPAS z = 0`, or
  `kleinPAS z = μ • c` with `μ ≠ 0`; in both cases `kleinRAS (kleinPAS z) = 0`, since `c` lies on
  the residual curve `V(kleinRAS)` (the hypothesis on the five cubics `zcubAS`);
* I1 (`KleinTwScalarASv`) then gives `kleinSecAS z * z 4 = 0`, and `z 4 = (2a-b)(a+2b)²w² ≠ 0`;
* finally `eval (srcRulPt) sAS2 = kleinSecAS (kleinStereoAS e₀ chart)`, and
  `kleinStereoAS e₀ (0, z₁/z₄, …, 1)` is proportional to `z` (by `kleinStereoAS_pi` and
  `kleinQAS z = 0`, the char-`5` identity proved by the explicit certificate below), so
  `kleinSecAS` of it vanishes by homogeneity.

The two explicit `5·Z` certificates (`kleinQAS_srcRul`, `det_submatrix_kleinMAS`) are the
`CharP · 5` reductions; `linear_combination … * h5` consumes them.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option maxRecDepth 100000

namespace Work.MotAS.ASRul

open MvPolynomial

/-! ## §1  Evaluation of the AS link data at a `K`-point -/

section Eval

variable {K : Type} [CommRing K]

/-- `MvPolynomial.eval` commutes with the AS quadric. -/
theorem eval_kleinQAS (a b : K) (V : Fin 5 → MvPolynomial (Fin 3) K) (x : Fin 3 → K) :
    MvPolynomial.eval x (Work.MotAS.kleinQAS (MvPolynomial.C a) (MvPolynomial.C b) V)
      = Work.MotAS.kleinQAS a b (fun i => MvPolynomial.eval x (V i)) := by
  rw [Work.MotAS.kleinQAS, Work.MotAS.kleinQAS]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, MvPolynomial.eval_C]

/-- `MvPolynomial.eval` commutes with the polar form of the AS quadric. -/
theorem eval_kleinBilinAS (a b : K) (U V : Fin 5 → MvPolynomial (Fin 3) K) (x : Fin 3 → K) :
    MvPolynomial.eval x (Work.MotAS.kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) U V)
      = Work.MotAS.kleinBilinAS a b (fun i => MvPolynomial.eval x (U i))
          (fun i => MvPolynomial.eval x (V i)) := by
  rw [Work.MotAS.kleinBilinAS, Work.MotAS.kleinBilinAS]
  simp only [map_sub]
  have hUV : (fun i => MvPolynomial.eval x ((U + V) i))
      = (fun i => MvPolynomial.eval x (U i)) + (fun i => MvPolynomial.eval x (V i)) := by
    funext i
    simp only [Pi.add_apply, map_add]
  rw [eval_kleinQAS, eval_kleinQAS, eval_kleinQAS, hUV]

/-- `MvPolynomial.eval` commutes with the AS stereographic map. -/
theorem eval_kleinStereoAS (a b : K) (P V : Fin 5 → MvPolynomial (Fin 3) K) (x : Fin 3 → K)
    (i : Fin 5) :
    MvPolynomial.eval x (Work.MotAS.kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) P V i)
      = Work.MotAS.kleinStereoAS a b (fun i => MvPolynomial.eval x (P i))
          (fun i => MvPolynomial.eval x (V i)) i := by
  rw [Work.MotAS.kleinStereoAS, Work.MotAS.kleinStereoAS]
  simp only [map_sub, map_mul]
  rw [eval_kleinQAS, eval_kleinBilinAS]

/-- `MvPolynomial.eval` commutes with the AS source ruling quintic. -/
theorem eval_kleinSecAS (a b g : K) (Y : Fin 5 → MvPolynomial (Fin 3) K) (x : Fin 3 → K) :
    MvPolynomial.eval x (Work.MotAS.kleinSecAS (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C g) Y)
      = Work.MotAS.kleinSecAS a b g (fun i => MvPolynomial.eval x (Y i)) := by
  rw [Work.MotAS.kleinSecAS, Work.MotAS.kleinSecAS]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, MvPolynomial.eval_C]

/-- `MvPolynomial.eval` commutes with the AS inverse quadro-cubic map. -/
theorem eval_kleinRAS (a b g : K) (Y : Fin 5 → MvPolynomial (Fin 3) K) (x : Fin 3 → K)
    (j : Fin 5) :
    MvPolynomial.eval x ((Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C g) Y) j)
      = (Work.MotAS.kleinRAS a b g (fun i => MvPolynomial.eval x (Y i))) j := by
  fin_cases j <;>
  · simp only [Work.MotAS.kleinRAS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Fin.reduceFinMk, Fin.isValue]
    first
     | rw [Work.MotAS.kleinRAS0, Work.MotAS.kleinRAS0]
     | rw [Work.MotAS.kleinRAS1, Work.MotAS.kleinRAS1]
     | rw [Work.MotAS.kleinRAS2, Work.MotAS.kleinRAS2]
     | rw [Work.MotAS.kleinRAS3, Work.MotAS.kleinRAS3]
     | rw [Work.MotAS.kleinRAS4, Work.MotAS.kleinRAS4]
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, MvPolynomial.eval_C]

/-- `MvPolynomial.eval` commutes with the AS Pfaffian vector. -/
theorem eval_kleinPAS (a b g : K) (Y : Fin 5 → MvPolynomial (Fin 3) K) (x : Fin 3 → K)
    (j : Fin 5) :
    MvPolynomial.eval x ((Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C g) Y) j)
      = (Work.MotAS.kleinPAS a b g (fun i => MvPolynomial.eval x (Y i))) j := by
  fin_cases j <;>
  · simp only [Work.MotAS.kleinPAS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Fin.reduceFinMk, Fin.isValue]
    first
     | rw [Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS0]
     | rw [Work.MotAS.kleinPAS1, Work.MotAS.kleinPAS1]
     | rw [Work.MotAS.kleinPAS2, Work.MotAS.kleinPAS2]
     | rw [Work.MotAS.kleinPAS3, Work.MotAS.kleinPAS3]
     | rw [Work.MotAS.kleinPAS4, Work.MotAS.kleinPAS4]
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, MvPolynomial.eval_C]

end Eval

/-! ## §2  The source ruling quintic at the chart point -/

/-- **`sAS2` evaluated at a `K`-point**: the AS source ruling quintic at the stereographic image
of `(0, x₀, x₁, x₂, 1)`. -/
theorem eval_sAS2 {K : Type} [Field K] (a b g : K) (x : Fin 3 → K) :
    MvPolynomial.eval x (Work.MotAS.sAS2 a b g)
      = Work.MotAS.kleinSecAS a b g
          (Work.MotAS.kleinStereoAS a b ![1, 0, 0, 0, 0] ![0, x 0, x 1, x 2, 1]) := by
  rw [Work.MotAS.sAS2, eval_kleinSecAS]
  congr 1
  funext i
  rw [eval_kleinStereoAS]
  have hP : (fun i : Fin 5 => MvPolynomial.eval x (Work.MotAS.pAS0 K i)) = ![1, 0, 0, 0, 0] := by
    funext i
    fin_cases i <;> simp [Work.MotAS.pAS0]
  have hV : (fun i : Fin 5 => MvPolynomial.eval x (Work.MotK.chart3 K i))
      = ![0, x 0, x 1, x 2, 1] := by
    funext i
    fin_cases i <;> simp [Work.MotK.chart3]
  rw [hP, hV]

/-- The stereographic point `e₀ = (1,0,0,0,0)` lies on the AS quadric. -/
theorem kleinQAS_e0 {K : Type} [CommRing K] (a b : K) :
    Work.MotAS.kleinQAS a b ![1, 0, 0, 0, 0] = 0 := by
  rw [Work.MotAS.kleinQAS]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val', Matrix.of_apply]
  refl_ring1

/-! ## §3  The char-`5` identities -/

/-- **The ruling line lies on the AS quadric**: `kleinQAS z = 0` for `z = t • rv + rw`, in
characteristic `5` (the explicit cofactor of `5` is exhibited in the proof).  This is the AS
analogue of the T-route's `Work.MotK.TwCensus.quad_lin_comb`. -/
theorem kleinQAS_srcRul {K : Type} [Field K] [CharP K 5] (a b g u v w t : K) :
    Work.MotAS.kleinQAS a b (fun i => t * rvEv a b g u v w i + rwEv a b g u v w i) = 0 := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  rw [Work.MotAS.kleinQAS]
  simp only [Work.MotAS.ASRul.rvEv, Work.MotAS.ASRul.rwEv, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val', Matrix.of_apply]
  linear_combination (norm := refl_ring1)
    (  - 4 * a^(8:ℕ) * w^(4:ℕ) + 8 * a^(7:ℕ) * b * u^(2:ℕ) * w^(2:ℕ) + 24 * a^(7:ℕ) * b * u * w^(3:ℕ) - 14 * a^(7:ℕ) * b * w^(4:ℕ) + 8 * a^(7:ℕ) * u * v * w^(2:ℕ) * t + 12 * a^(7:ℕ) * v * w^(3:ℕ) * t + 4 * a^(7:ℕ) * w^(3:ℕ) * t + 12 * a^(6:ℕ) * b^(2:ℕ) * u^(2:ℕ) * w^(2:ℕ) + 84 * a^(6:ℕ) * b^(2:ℕ) * u * w^(3:ℕ) + 6 * a^(6:ℕ) * b^(2:ℕ) * w^(4:ℕ) - 8 * a^(6:ℕ) * b * u * v * w^(2:ℕ) * t + 10 * a^(6:ℕ) * b * v * w^(3:ℕ) * t + 10 * a^(6:ℕ) * b * w^(3:ℕ) * t - 4 * a^(6:ℕ) * v^(2:ℕ) * w^(2:ℕ) * t^(2:ℕ) - 38 * a^(5:ℕ) * b^(3:ℕ) * u^(2:ℕ) * w^(2:ℕ) + 16 * a^(5:ℕ) * b^(3:ℕ) * u * w^(3:ℕ) + 79 * a^(5:ℕ) * b^(3:ℕ) * w^(4:ℕ) - 38 * a^(5:ℕ) * b^(2:ℕ) * u * v * w^(2:ℕ) * t - 60 * a^(5:ℕ) * b^(2:ℕ) * v * w^(3:ℕ) * t - 6 * a^(5:ℕ) * b^(2:ℕ) * w^(3:ℕ) * t + 8 * a^(5:ℕ) * b * w^(4:ℕ) * t^(2:ℕ) - 35 * a^(4:ℕ) * b^(4:ℕ) * u^(2:ℕ) * w^(2:ℕ) - 180 * a^(4:ℕ) * b^(4:ℕ) * u * w^(3:ℕ) + 111 * a^(4:ℕ) * b^(4:ℕ) * w^(4:ℕ) + 40 * a^(4:ℕ) * b^(3:ℕ) * u * v * w^(2:ℕ) * t - 62 * a^(4:ℕ) * b^(3:ℕ) * v * w^(3:ℕ) * t - 20 * a^(4:ℕ) * b^(3:ℕ) * w^(3:ℕ) * t + 15 * a^(4:ℕ) * b^(2:ℕ) * v^(2:ℕ) * w^(2:ℕ) * t^(2:ℕ) + 8 * a^(4:ℕ) * b^(2:ℕ) * w^(4:ℕ) * t^(2:ℕ) + 55 * a^(3:ℕ) * b^(5:ℕ) * u^(2:ℕ) * w^(2:ℕ) - 130 * a^(3:ℕ) * b^(5:ℕ) * u * w^(3:ℕ) + 35 * a^(3:ℕ) * b^(5:ℕ) * w^(4:ℕ) + 30 * a^(3:ℕ) * b^(4:ℕ) * u * v * w^(2:ℕ) * t + 24 * a^(3:ℕ) * b^(4:ℕ) * v * w^(3:ℕ) * t - 10 * a^(3:ℕ) * b^(4:ℕ) * w^(3:ℕ) * t - 5 * a^(3:ℕ) * b^(3:ℕ) * v^(2:ℕ) * w^(2:ℕ) * t^(2:ℕ) - 14 * a^(3:ℕ) * b^(3:ℕ) * w^(4:ℕ) * t^(2:ℕ) + a^(2:ℕ) * b^(6:ℕ) * u^(2:ℕ) * w^(2:ℕ) + 38 * a^(2:ℕ) * b^(6:ℕ) * u * w^(3:ℕ) - 39 * a^(2:ℕ) * b^(6:ℕ) * w^(4:ℕ) - 24 * a^(2:ℕ) * b^(5:ℕ) * u * v * w^(2:ℕ) * t + 46 * a^(2:ℕ) * b^(5:ℕ) * v * w^(3:ℕ) * t - 22 * a^(2:ℕ) * b^(5:ℕ) * w^(3:ℕ) * t - 5 * a^(2:ℕ) * b^(4:ℕ) * v^(2:ℕ) * w^(2:ℕ) * t^(2:ℕ) + 4 * a^(2:ℕ) * b^(4:ℕ) * w^(4:ℕ) * t^(2:ℕ) - 16 * a * b^(7:ℕ) * u^(2:ℕ) * w^(2:ℕ) + 48 * a * b^(7:ℕ) * u * w^(3:ℕ) - 16 * a * b^(7:ℕ) * w^(4:ℕ) - 6 * a * b^(6:ℕ) * u * v * w^(2:ℕ) * t + 6 * a * b^(6:ℕ) * v * w^(3:ℕ) * t + 2 * a * b^(5:ℕ) * v^(2:ℕ) * w^(2:ℕ) * t^(2:ℕ) + 4 * b^(8:ℕ) * u^(2:ℕ) * w^(2:ℕ) - 8 * b^(8:ℕ) * u * w^(3:ℕ) + 4 * b^(8:ℕ) * w^(4:ℕ) + 4 * b^(7:ℕ) * u * v * w^(2:ℕ) * t - 12 * b^(7:ℕ) * v * w^(3:ℕ) * t + 8 * b^(7:ℕ) * w^(3:ℕ) * t  ) * h5

/-- **The AS ruling matrix at the chart point is the corrected one.**  On the chart
`(1,u,v,w,0)` the matrices `AmatAS2` (`ASRulingMainAux`) and `AmatAS` (`ASRul.Matrices`) agree, so
the kernel computation of `kernel_basis` applies to `AmatAS2`. -/
theorem AmatAS2_chart_eq {K : Type} [Field K] (a b g u v w : K) :
    Work.MotAS.AmatAS2 a b g ![1, u, v, w, 0] = Work.MotAS.ASRul.AmatAS a b g ![1, u, v, w, 0] := by
  ext i l
  fin_cases i <;> fin_cases l <;>
  · simp only [Work.MotAS.AmatAS2, Work.MotAS.ASRul.AmatAS, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val', Matrix.of_apply]
    first | refl_ring1 | ring

/-! ## §4  The main theorem -/

/-- **The source ruling divisor `sAS2` vanishes on the ruling lines.**
For every base point `(u,v,w)` of the residual curve `V(ZIAS)` (the common zeros of the five cubics
`zcubAS a b g`) with `w ≠ 0`, and every ruling parameter `t`, the point of the source chart cut out
by the ruling line over `(1 : u : v : w : 0)` lies on `V(sAS2)`.  This is the Artin–Schreier
analogue of the T-route's `Work.MotK.TwCensus.s_ruling_mem`
(`s (T·rv + w) ∈ Ideal.span {Pt1, Pt2}`) and is the certificate behind `sAS2 ∈ ker θ` for the
ruling presentation `θ`. -/
theorem sAS2_ruling_mem {K : Type} [Field K] [CharP K 5] (a b g : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : b ≠ 2 * a) (hg : g ≠ 0) :
    ∀ u v w t : K, w ≠ 0 →
      (∀ j : Fin 5, MvPolynomial.eval ![u, v, w] (Work.MotAS.zcubAS a b g j) = 0) →
      MvPolynomial.eval (Work.MotAS.ASRul.srcRulPt a b g u v w t) (Work.MotAS.sAS2 a b g) = 0 := by
  intro u v w t hw hbase
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  -- the base point of the residual curve and the ruling point
  set c : Fin 5 → K := ![1, u, v, w, 0] with hc
  set z : Fin 5 → K := t • rvEv a b g u v w + rwEv a b g u v w with hz
  have hcne : c ≠ 0 := by
    intro hzero
    have h0 := congrFun hzero 0
    simp [hc] at h0
  -- (0) the two constants `2a - b` and `a + 2b` are nonzero
  have hA : 2 * a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hB : a + 2 * b ≠ 0 := by
    intro h0
    have hkey : 2 * a - b = 2 * (a + 2 * b) - 5 * b := by ring
    rw [h0, h5] at hkey
    have hkey2 : 2 * a - b = 0 := by simpa using hkey
    exact hab (by linear_combination -hkey2)
  -- (1) the fourth coordinate of the ruling point is nonzero
  have hz4val : z 4 = (2 * a - b) * (a + 2 * b) ^(2:ℕ) * w ^(2:ℕ) := by
    rw [hz]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rvEv, rwEv, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val', Matrix.of_apply]
    refl_ring1
  have hz4 : z 4 ≠ 0 := by
    rw [hz4val]
    exact mul_ne_zero (mul_ne_zero hA (pow_ne_zero 2 hB)) (pow_ne_zero 2 hw)
  -- (2) the base point lies on the residual curve `V(kleinRAS)`
  have hRc : Work.MotAS.kleinRAS a b g c = 0 := by
    funext j
    have h1 : MvPolynomial.eval ![u, v, w]
        ((Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          ![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0]) j) = 0 := by
      rw [← show Work.MotAS.zcubAS a b g j = (Work.MotAS.kleinRAS (MvPolynomial.C a)
          (MvPolynomial.C b) (MvPolynomial.C g)
          ![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0]) j from rfl]
      exact hbase j
    rw [eval_kleinRAS] at h1
    have h2 : (fun i => MvPolynomial.eval ![u, v, w]
        (![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] i)) = c := by
      funext i
      fin_cases i <;> simp [hc]
    rw [h2] at h1
    exact h1
  -- (3) the ruling point is in the kernel of the AS ruling matrix over the base point
  have hker : Matrix.mulVec (kleinMAS a b g z) c = 0 := by
    have h1 : Matrix.mulVec (Work.MotAS.AmatAS2 a b g c) z
        = Matrix.mulVec (kleinMAS a b g z) c := Work.MotAS.AmatAS2_mulVec a b g z c
    rw [← h1, hc, AmatAS2_chart_eq, hz]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul,
      AmatAS_mulVec_kbRv_zero a b g u v w hA (hbase 4),
      AmatAS_mulVec_kbRw_zero a b g u v w (hbase 3)]
    simp
  -- (4) `kleinPAS z` is on the residual curve, hence killed by `kleinRAS`
  have hRP : Work.MotAS.kleinRAS a b g (Work.MotAS.kleinPAS a b g z) = 0 := by
    by_cases hP : Work.MotAS.kleinPAS a b g z = 0
    · have h0 : Work.MotAS.kleinRAS a b g (fun _ : Fin 5 => (0 : K)) = 0 := by
        have h := Work.MotAS.kleinRAS_smul a b g (0 : K) (fun _ : Fin 5 => (0 : K))
        simp only [mul_zero, zero_mul, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at h
        rw [h]
        funext i
        rfl
      have hz0 : Work.MotAS.kleinPAS a b g z = fun _ : Fin 5 => (0 : K) := by
        rw [hP]
        rfl
      rw [hz0]
      exact h0
    · obtain ⟨mu, hmu, hmu'⟩ :=
        (kleinMAS_fibre K a b g z c hP hcne).mp hker
      have hzP : Work.MotAS.kleinPAS a b g z = fun i => mu * c i := funext hmu'
      rw [hzP, Work.MotAS.kleinRAS_smul, hRc]
      funext i
      simp
  -- (5) the source ruling quintic vanishes at the ruling point
  have hsec : Work.MotAS.kleinSecAS a b g z = 0 := by
    have h1 := congrFun (Work.MotAS.KleinTwScalarASv a b g z h5) 4
    rw [hRP, Pi.zero_apply] at h1
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hz4
  -- (6) `sAS2` at the chart point of the ruling line
  rw [eval_sAS2]
  have hxr : srcRulPt a b g u v w t = ![z 1 / z 4, z 2 / z 4, z 3 / z 4] := by
    funext i
    fin_cases i <;>
      simp [Work.MotAS.ASRul.srcRulPt, Work.MotAS.ASRul.srcRvEv, Work.MotAS.ASRul.srcRwEv,
        Work.MotAS.ASRul.rvEv, Work.MotAS.ASRul.rwEv, hz, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val', Matrix.of_apply]
  rw [hxr]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val', Matrix.of_apply,
    Fin.reduceFinMk]
  set V : Fin 5 → K := Work.MotK.kleinTwPi ![1, 0, 0, 0, 0] z with hV
  have hVval : V = ![0, z 1, z 2, z 3, z 4] := by
    funext i
    fin_cases i <;>
      simp [hV, Work.MotK.kleinTwPi, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val', Matrix.of_apply]
  have hchart : (![0, z 1 / z 4, z 2 / z 4, z 3 / z 4, 1] : Fin 5 → K) = fun i => (z 4)⁻¹ * V i := by
    funext i
    fin_cases i <;>
      simp [hVval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val', Matrix.of_apply, div_eq_inv_mul, inv_mul_cancel₀ hz4]
  rw [hchart, Work.MotAS.kleinStereoAS_smul]
  have hstereo : Work.MotAS.kleinStereoAS a b ![1, 0, 0, 0, 0] V
      = fun i => -(Work.MotAS.kleinBilinAS a b ![1, 0, 0, 0, 0] z) * z i := by
    rw [hV, Work.MotAS.kleinStereoAS_pi a b ![1, 0, 0, 0, 0] z (kleinQAS_e0 a b)]
    have hqz : Work.MotAS.kleinQAS a b z = 0 := by
      rw [hz]
      exact kleinQAS_srcRul a b g u v w t
    rw [hqz]
    funext i
    refl_ring1
  rw [hstereo]
  rw [show (fun i => (z 4)⁻¹ ^(2:ℕ) * (-(Work.MotAS.kleinBilinAS a b ![1, 0, 0, 0, 0] z) * z i))
      = fun i => ((z 4)⁻¹ ^(2:ℕ) * (-(Work.MotAS.kleinBilinAS a b ![1, 0, 0, 0, 0] z))) * z i
      from by funext i; ring]
  rw [Work.MotAS.kleinSecAS_smul, hsec, mul_zero]

end Work.MotAS.ASRul
