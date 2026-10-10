import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.AzDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRulV2M.Defs` — the quadratic form of the AS forward chart

The forward chart map of the corrected AS link is
`fwVecAS2 a b g j = kleinPAS a b g (kleinStereoAS a b (pAS0 K) (chart3 K)) j`, and the
stereographic vector is

`y = (azq a b, 2A·X₀, 2A·X₁, 2A·X₂, 2A)`   with   `A = a² − ab − b²` (`azA a b`).

This file fixes:

* the *degree-`2` part* `q2 a b = -A·X₁² - 2A·X₀X₂ + 2B·X₂²` of the Galois coordinate `azq`,
  together with its degree-`≤1` complement `q2L a b = -2B·X₁ + azc a b` (`azq = q2 + q2L`);
* the vectors `yQ a b = ![q2,0,0,0,0]` (each entry homogeneous of degree `2`) and
  `yL a b = ![q2L, 2A·X₀, 2A·X₁, 2A·X₂, 2A]` (each entry of total degree `≤ 1`), with
  `kleinStereoAS a b (pAS0 K) (chart3 K) = yQ + yL`.

These are the data with which the degree-`10` part of `sAS2` is computed: since `kleinSecAS` is
homogeneous of degree `5` in its five arguments, splitting the stereographic vector into its
degree-`2` and degree-`≤1` parts shows that
`homogeneousComponent 10 (sAS2 a b g) = kleinSecAS a b g (yQ a b)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Work.MotAS.ASRulV2M

open MvPolynomial

variable {K : Type*} [Field K]

/-- The quadratic form `q₂ = -A·X₁² - 2A·X₀X₂ + 2B·X₂²`, `A = a² − ab − b²`, `B = a² + b²`:
the degree-`2` part of the Galois coordinate `azq a b`. -/
noncomputable def q2 (a b : K) : MvPolynomial (Fin 3) K :=
  C (-(2 * Work.MotAS.azA a b)) * X 0 * X 2 + C (-(Work.MotAS.azA a b)) * X 1 ^ 2
    + C (2 * Work.MotAS.azB a b) * X 2 ^ 2

/-- The degree-`≤1` complement of `q₂` inside the Galois coordinate: `azq = q2 + q2L`. -/
noncomputable def q2L (a b : K) : MvPolynomial (Fin 3) K :=
  C (-(2 * Work.MotAS.azB a b)) * X 1 + C (Work.MotAS.azc a b)

/-- `azq` splits as its degree-`2` part plus its degree-`≤1` part. -/
theorem azq_eq_q2_add (a b : K) : Work.MotAS.azq a b = q2 a b + q2L a b := by
  simp only [q2, q2L, Work.MotAS.azq, Work.MotAS.azA, Work.MotAS.azB, Work.MotAS.azc]
  first | refl_ring1 | ring

/-- The degree-`2` part of the stereographic vector. -/
noncomputable def yQ (a b : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  ![q2 a b, 0, 0, 0, 0]

/-- The degree-`≤1` part of the stereographic vector. -/
noncomputable def yL (a b : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  ![q2L a b, C (2 * Work.MotAS.azA a b) * X 0, C (2 * Work.MotAS.azA a b) * X 1,
    C (2 * Work.MotAS.azA a b) * X 2, C (2 * Work.MotAS.azA a b)]

/-- The Galois coordinate of the source chart vector: `kleinQAS a b (chart3 K) = azq a b`. -/
theorem kleinQAS_chart3_eq_azq (a b : K) :
    Work.MotAS.kleinQAS (C a) (C b) (Work.MotK.chart3 K) = Work.MotAS.azq a b := by
  simp only [Work.MotAS.kleinQAS, Work.MotAS.azq, Work.MotAS.azA, Work.MotAS.azB,
    Work.MotAS.azc, Work.MotK.chart3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
    map_zero]
  first | refl_ring1 | ring

/-- **The stereographic vector is `yQ + yL`** (pointwise form, with the case analysis on the
index). -/
theorem stereo_apply (a b : K) (i : Fin 5) :
    Work.MotAS.kleinStereoAS (C a) (C b) (Work.MotAS.pAS0 K) (Work.MotK.chart3 K) i
      = yQ a b i + yL a b i := by
  rw [Work.MotAS.kleinStereoAS_pAS0_chart3, kleinQAS_chart3_eq_azq, azq_eq_q2_add]
  fin_cases i <;>
    · simp only [yQ, yL, Work.MotAS.pAS0, Work.MotK.chart3, Matrix.cons_val_zero,
        Matrix.cons_val_zero', Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.head_cons,
        Matrix.tail_cons, Pi.add_apply, map_one, map_zero, mul_one, mul_zero, one_mul,
        zero_mul, add_zero, zero_add]

/-- **The stereographic vector is `yQ + yL`.** -/
theorem stereo_eq (a b : K) :
    Work.MotAS.kleinStereoAS (C a) (C b) (Work.MotAS.pAS0 K) (Work.MotK.chart3 K)
      = fun i => yQ a b i + yL a b i :=
  funext fun i => stereo_apply a b i

/-- Every entry of `yQ` is homogeneous of degree `2`. -/
theorem isHomogeneous_yQ (a b : K) (i : Fin 5) : (yQ a b i).IsHomogeneous 2 := by
  have hC : ∀ r : K, (MvPolynomial.C r : MvPolynomial (Fin 3) K).IsHomogeneous 0 :=
    fun r => isHomogeneous_C (Fin 3) r
  have hX : ∀ j : Fin 3, ((MvPolynomial.X j : MvPolynomial (Fin 3) K)).IsHomogeneous 1 :=
    fun j => isHomogeneous_X (σ := Fin 3) K j
  have h0 : (q2 a b).IsHomogeneous 2 := by
    rw [q2]
    refine IsHomogeneous.add (IsHomogeneous.add ?_ ?_) ?_
    · exact ((hC _).mul (hX 0)).mul (hX 2)
    · exact (hC _).mul ((hX 1).pow 2)
    · exact (hC _).mul ((hX 2).pow 2)
  fin_cases i <;>
    · simp only [yQ, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons]
      first
      | exact h0
      | exact isHomogeneous_zero (σ := Fin 3) (R := K) 2

/-- Every entry of `yL` has total degree `≤ 1`. -/
theorem totalDegree_yL (a b : K) (i : Fin 5) : (yL a b i).totalDegree ≤ 1 := by
  fin_cases i
  · show (q2L a b).totalDegree ≤ 1
    rw [q2L]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    · rw [MvPolynomial.totalDegree_C]; omega
  · show (C (2 * Work.MotAS.azA a b) * (X 0 : MvPolynomial (Fin 3) K)).totalDegree ≤ 1
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · show (C (2 * Work.MotAS.azA a b) * (X 1 : MvPolynomial (Fin 3) K)).totalDegree ≤ 1
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · show (C (2 * Work.MotAS.azA a b) * (X 2 : MvPolynomial (Fin 3) K)).totalDegree ≤ 1
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · show (C (2 * Work.MotAS.azA a b) : MvPolynomial (Fin 3) K).totalDegree ≤ 1
    rw [MvPolynomial.totalDegree_C]; omega

/-- `kleinSecAS` read as a polynomial in its five arguments, with coefficients in
`MvPolynomial (Fin 3) K`.  Evaluating this polynomial at a vector `y` recovers
`kleinSecAS (C a) (C b) (C g) y` (to be proved as `kleinSecAS_aeval_eq`); it is the polynomial whose
degree-`5` homogeneity governs the degree-`10` part of `sAS2`. -/
noncomputable def kleinSecASPolyK (K : Type) [Field K] (a b g : K) :
    MvPolynomial (Fin 5) (MvPolynomial (Fin 3) K) :=
  Work.MotAS.kleinSecAS (MvPolynomial.C (MvPolynomial.C a : MvPolynomial (Fin 3) K))
    (MvPolynomial.C (MvPolynomial.C b)) (MvPolynomial.C (MvPolynomial.C g))
    (fun i : Fin 5 => MvPolynomial.X i)

end Work.MotAS.ASRulV2M
