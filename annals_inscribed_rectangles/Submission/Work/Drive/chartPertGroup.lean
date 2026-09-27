import Mathlib
import Submission.Work.Drive.classRowRebasing

/-!
# The **group structure of the chart perturbations** `chartPert`

`Work.Drive.chartPert τ` is the perturbation of the capping space used throughout the ends-clause
design: it multiplies the level by `exp (τ 0)` and acts on the class `ℝP³ = ℙ ℍ` by the
projectivisation of the quaternionic *left multiplication* by `1 + (τ 1 i + τ 2 j + τ 3 k)`
(`Work.Drive.classEquiv τ = 1 + classGen τ`).

The aim of this file is the **exact composition law**

> `chartPert (qMul a b) = chartPert a ∘ chartPert b`

for an explicit binary operation `qMul` on the perturbation parameters `𝔼⁴` (the level coordinate
adds, the class coordinates multiply as quaternions).  The mathematical point is that although
`classEquiv a * classEquiv b` is *not* a `classEquiv`, it is a **nonzero scalar multiple** of one:

> `(1 + L_a)(1 + L_b) = (1 - ⟪a,b⟫) · (1 + L_c)`,  `c = (1 - ⟪a,b⟫)⁻¹ (a + b + a × b)`,

because `L_a ∘ L_b = -⟪a,b⟫ · 1 + L_{a×b}` (quaternionic multiplication; `L` is left multiplication by
the imaginary part).  Since `classMap` only remembers the *projectivisation*, the two maps induce the
same class action.

## Why this matters (the re-basing of the class-level rows)

`Submission/Work/Drive/CLASSROWS_DENSITY_MECHANISM.md` §2 re-bases the design parameter at an arbitrary
`χ` and lets the perturbation `σ` tend to `0`; the transfer step there is recorded as needing
*openness* of each row in the family.  With the composition law above the transfer is **exact**: the
re-based presentation `chartPert σ k ∘ chartPert χ k ∘ P k` *is* the design's presentation
`chartPert (qMul σ χ) k ∘ P k` at the parameter `qMul σ χ`, so every row, every `Meet3Hyp`-type datum
and `classTripleSet` itself transfer with no approximation and no openness hypothesis.  See
`Submission/Work/Drive/chartPertRebase.lean` for the consumer-facing forms.
-/

namespace Work.Drive

open scoped Manifold ContDiff LinearAlgebra.Projectivization

noncomputable section

/-! ## 1. The quaternionic product of the pure parts -/

/-- The inner product of the **pure parts** `(a 1, a 2, a 3)`, `(b 1, b 2, b 3)`. -/
def pureInner (a b : Eucl 3) : ℝ := a 1 * b 1 + a 2 * b 2 + a 3 * b 3

/-- The **cross product** of the pure parts, placed in the coordinates `1,2,3`. -/
def pureCross (a b : Eucl 3) : Eucl 3 :=
  WithLp.toLp 2 ![(0 : ℝ), a 2 * b 3 - a 3 * b 2, a 3 * b 1 - a 1 * b 3, a 1 * b 2 - a 2 * b 1]

@[simp] lemma pureCross_ofLp_zero (a b : Eucl 3) : (pureCross a b).ofLp (0 : Fin 4) = 0 := by
  simp [pureCross, WithLp.ofLp_toLp]

@[simp] lemma pureCross_ofLp_one (a b : Eucl 3) :
    (pureCross a b).ofLp (1 : Fin 4) = a 2 * b 3 - a 3 * b 2 := by
  simp [pureCross, WithLp.ofLp_toLp]

@[simp] lemma pureCross_ofLp_two (a b : Eucl 3) :
    (pureCross a b).ofLp (2 : Fin 4) = a 3 * b 1 - a 1 * b 3 := by
  simp [pureCross, WithLp.ofLp_toLp]

@[simp] lemma pureCross_ofLp_three (a b : Eucl 3) :
    (pureCross a b).ofLp (3 : Fin 4) = a 1 * b 2 - a 2 * b 1 := by
  simp [pureCross, WithLp.ofLp_toLp]

@[simp] lemma pureInner_zero_left (b : Eucl 3) : pureInner (0 : Eucl 3) b = 0 := by
  simp [pureInner]

@[simp] lemma pureInner_zero_right (a : Eucl 3) : pureInner a (0 : Eucl 3) = 0 := by
  simp [pureInner]

/-- **The cross product with the zero parameter on the left.** -/
@[simp] lemma pureCross_zero_left (b : Eucl 3) : pureCross (0 : Eucl 3) b = 0 := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i
  case «0» =>
    show (pureCross (0 : Eucl 3) b).ofLp (0 : Fin 4) = (0 : Eucl 3).ofLp (0 : Fin 4)
    simp
  case «1» =>
    show (pureCross (0 : Eucl 3) b).ofLp (1 : Fin 4) = (0 : Eucl 3).ofLp (1 : Fin 4)
    simp
  case «2» =>
    show (pureCross (0 : Eucl 3) b).ofLp (2 : Fin 4) = (0 : Eucl 3).ofLp (2 : Fin 4)
    simp
  case «3» =>
    show (pureCross (0 : Eucl 3) b).ofLp (3 : Fin 4) = (0 : Eucl 3).ofLp (3 : Fin 4)
    simp

/-- **The cross product with the zero parameter on the right.** -/
@[simp] lemma pureCross_zero_right (a : Eucl 3) : pureCross a (0 : Eucl 3) = 0 := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i
  case «0» =>
    show (pureCross a (0 : Eucl 3)).ofLp (0 : Fin 4) = (0 : Eucl 3).ofLp (0 : Fin 4)
    simp
  case «1» =>
    show (pureCross a (0 : Eucl 3)).ofLp (1 : Fin 4) = (0 : Eucl 3).ofLp (1 : Fin 4)
    simp
  case «2» =>
    show (pureCross a (0 : Eucl 3)).ofLp (2 : Fin 4) = (0 : Eucl 3).ofLp (2 : Fin 4)
    simp
  case «3» =>
    show (pureCross a (0 : Eucl 3)).ofLp (3 : Fin 4) = (0 : Eucl 3).ofLp (3 : Fin 4)
    simp

/-- **The class generator is linear in its parameter.** -/
lemma classGen_smul (c : ℝ) (a : Eucl 3) : classGen (c • a) = c • classGen a := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [classGen_apply, smul_apply, classGen_apply]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]

/-- **The quaternionic product rule for the class generator**:
`L_a ∘ L_b = -⟪a,b⟫ · 1 + L_{a×b}`. -/
theorem classGen_mul_apply (a b v : Eucl 3) :
    classGen a (classGen b v) = -(pureInner a b) • v + classGen (pureCross a b) v := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i
  case «0» =>
    show ((classGen a) ((classGen b) v)).ofLp (0 : Fin 4)
      = (-(pureInner a b) • v + (classGen (pureCross a b)) v).ofLp (0 : Fin 4)
    simp only [classGen_ofLp_0, classGen_ofLp_1, classGen_ofLp_2, classGen_ofLp_3,
      pureCross_ofLp_zero, pureCross_ofLp_one, pureCross_ofLp_two, pureCross_ofLp_three,
      pureInner, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  case «1» =>
    show ((classGen a) ((classGen b) v)).ofLp (1 : Fin 4)
      = (-(pureInner a b) • v + (classGen (pureCross a b)) v).ofLp (1 : Fin 4)
    simp only [classGen_ofLp_0, classGen_ofLp_1, classGen_ofLp_2, classGen_ofLp_3,
      pureCross_ofLp_zero, pureCross_ofLp_one, pureCross_ofLp_two, pureCross_ofLp_three,
      pureInner, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  case «2» =>
    show ((classGen a) ((classGen b) v)).ofLp (2 : Fin 4)
      = (-(pureInner a b) • v + (classGen (pureCross a b)) v).ofLp (2 : Fin 4)
    simp only [classGen_ofLp_0, classGen_ofLp_1, classGen_ofLp_2, classGen_ofLp_3,
      pureCross_ofLp_zero, pureCross_ofLp_one, pureCross_ofLp_two, pureCross_ofLp_three,
      pureInner, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  case «3» =>
    show ((classGen a) ((classGen b) v)).ofLp (3 : Fin 4)
      = (-(pureInner a b) • v + (classGen (pureCross a b)) v).ofLp (3 : Fin 4)
    simp only [classGen_ofLp_0, classGen_ofLp_1, classGen_ofLp_2, classGen_ofLp_3,
      pureCross_ofLp_zero, pureCross_ofLp_one, pureCross_ofLp_two, pureCross_ofLp_three,
      pureInner, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring

/-! ## 2. The product of two perturbation parameters -/

/-- The **class part of the product** of the two quaternions `1 + a` and `1 + b`. -/
def qPure (a b : Eucl 3) : Eucl 3 :=
  (1 - pureInner a b)⁻¹ •
    (a + b + pureCross a b + (-(a 0 + b 0)) • (e0 : Eucl 3))

/-- **The product of two perturbation parameters**: the level coordinates add, the class coordinates
multiply as quaternions. -/
def qMul (a b : Eucl 3) : Eucl 3 := (a 0 + b 0) • (e0 : Eucl 3) + qPure a b

@[simp] lemma qMul_apply_zero (a b : Eucl 3) : (qMul a b) 0 = a 0 + b 0 := by
  simp only [qMul, qPure, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, e0_ofLp_zero,
    pureCross_ofLp_zero]
  ring

/-- The class part of the product, in terms of `classGen`. -/
lemma classGen_qMul (a b : Eucl 3) :
    classGen (qMul a b) = (1 - pureInner a b)⁻¹ • classGen (a + b + pureCross a b) := by
  rw [qMul, classGen_add, classGen_smul_e0, zero_add, qPure, classGen_smul, classGen_add,
    classGen_smul_e0, add_zero]

/-- **`qMul` with the zero parameter on the left.** -/
@[simp] lemma qMul_zero_left (b : Eucl 3) : qMul (0 : Eucl 3) b = b := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i
  case «0» =>
    show (qMul (0 : Eucl 3) b).ofLp (0 : Fin 4) = b.ofLp (0 : Fin 4)
    simp only [qMul, qPure, pureCross_zero_left, pureInner_zero_left, PiLp.add_apply,
      PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, e0_ofLp_zero, zero_add, zero_mul,
      mul_zero, add_zero, sub_zero, inv_one, one_mul]
    ring
  case «1» =>
    show (qMul (0 : Eucl 3) b).ofLp (1 : Fin 4) = b.ofLp (1 : Fin 4)
    simp only [qMul, qPure, pureCross_zero_left, pureInner_zero_left, PiLp.add_apply,
      PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, e0_ofLp_one, zero_add, zero_mul,
      mul_zero, add_zero, sub_zero, inv_one, one_mul]
  case «2» =>
    show (qMul (0 : Eucl 3) b).ofLp (2 : Fin 4) = b.ofLp (2 : Fin 4)
    simp only [qMul, qPure, pureCross_zero_left, pureInner_zero_left, PiLp.add_apply,
      PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, e0_ofLp_two, zero_add, zero_mul,
      mul_zero, add_zero, sub_zero, inv_one, one_mul]
  case «3» =>
    show (qMul (0 : Eucl 3) b).ofLp (3 : Fin 4) = b.ofLp (3 : Fin 4)
    simp only [qMul, qPure, pureCross_zero_left, pureInner_zero_left, PiLp.add_apply,
      PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, e0_ofLp_three, zero_add, zero_mul,
      mul_zero, add_zero, sub_zero, inv_one, one_mul]

/-- **`qMul` with the zero parameter on the right.** -/
@[simp] lemma qMul_zero_right (a : Eucl 3) : qMul a (0 : Eucl 3) = a := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i
  case «0» =>
    show (qMul a (0 : Eucl 3)).ofLp (0 : Fin 4) = a.ofLp (0 : Fin 4)
    simp only [qMul, qPure, pureCross_zero_right, pureInner_zero_right, PiLp.add_apply,
      PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, e0_ofLp_zero, add_zero, mul_zero,
      zero_mul, one_mul, sub_zero, inv_one]
    ring
  case «1» =>
    show (qMul a (0 : Eucl 3)).ofLp (1 : Fin 4) = a.ofLp (1 : Fin 4)
    simp only [qMul, qPure, pureCross_zero_right, pureInner_zero_right, PiLp.add_apply,
      PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, e0_ofLp_one, add_zero, mul_zero,
      zero_mul, one_mul, sub_zero, inv_one]
    ring
  case «2» =>
    show (qMul a (0 : Eucl 3)).ofLp (2 : Fin 4) = a.ofLp (2 : Fin 4)
    simp only [qMul, qPure, pureCross_zero_right, pureInner_zero_right, PiLp.add_apply,
      PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, e0_ofLp_two, add_zero, mul_zero,
      zero_mul, one_mul, sub_zero, inv_one]
    ring
  case «3» =>
    show (qMul a (0 : Eucl 3)).ofLp (3 : Fin 4) = a.ofLp (3 : Fin 4)
    simp only [qMul, qPure, pureCross_zero_right, pureInner_zero_right, PiLp.add_apply,
      PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, e0_ofLp_three, add_zero, mul_zero,
      zero_mul, one_mul, sub_zero, inv_one]
    ring

/-! ## 3. The composition of the class actions -/

/-- **The composition of two class actions is the class action of the product**, pointwise:
`(1 + L_a)(1 + L_b) = (1 - ⟪a,b⟫) (1 + L_c)` with `c` the class parameter of `qMul a b`. -/
theorem classEquiv_mul (a b v : Eucl 3) (h : pureInner a b ≠ 1) :
    classEquiv a (classEquiv b v) = (1 - pureInner a b) • classEquiv (qMul a b) v := by
  have hμ : (1 : ℝ) - pureInner a b ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hμv : (1 - pureInner a b) • v = v + (-(pureInner a b)) • v := by
    rw [sub_eq_add_neg, add_smul, one_smul]
  simp only [classEquiv_apply]
  rw [map_add]
  rw [classGen_mul_apply a b v]
  rw [classGen_qMul a b, smul_apply, classGen_add, classGen_add]
  rw [add_apply, add_apply]
  rw [smul_add, smul_smul, mul_inv_cancel₀ hμ, one_smul, hμv]
  abel

/-- **The design's perturbation as the composite of the two re-based ones**, as an identity of
continuous linear maps: `classEquiv (qMul a b) = (1 - ⟪a,b⟫)⁻¹ • (classEquiv a * classEquiv b)`.
This is the form of the composition law that re-bases a *linear family*: for a linear automorphism
`Φ`, `Φ.trans (classEquiv (qMul a b))` is a positive scalar multiple of
`(Φ.trans (classEquiv a)).trans (classEquiv b)`. -/
theorem classEquiv_qMul (a b : Eucl 3) (h : pureInner a b ≠ 1) :
    (classEquiv (qMul a b) : Eucl 3 →L[ℝ] Eucl 3)
      = (1 - pureInner a b)⁻¹ •
        ((classEquiv a : Eucl 3 →L[ℝ] Eucl 3) * (classEquiv b : Eucl 3 →L[ℝ] Eucl 3)) := by
  have hμ : (1 : ℝ) - pureInner a b ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [smul_apply, mul_apply_eq_comp]
  show classEquiv (qMul a b) v = ((1 - pureInner a b)⁻¹ : ℝ) • classEquiv a (classEquiv b v)
  rw [classEquiv_mul a b v h, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- **The composition of two class maps is the class map of the product.** -/
theorem classMap_mul (a b : Eucl 3) (h : pureInner a b ≠ 1) :
    classMap (qMul a b) = classMap a ∘ classMap b := by
  have hμ : (1 : ℝ) - pureInner a b ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  funext p
  induction p using Projectivization.ind with
  | h v hv =>
    show classMap (qMul a b) (Projectivization.mk ℝ v hv)
      = classMap a (classMap b (Projectivization.mk ℝ v hv))
    rw [classMap_mk, classMap_mk, classMap_mk]
    refine (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      ⟨(1 - pureInner a b)⁻¹, ?_⟩
    rw [classEquiv_mul a b v h, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- **The level scalings compose**: the level coordinates add. -/
theorem levelScale_mul (a b : Eucl 3) (r : Set.Ioi (0 : ℝ)) :
    levelScale (qMul a b) r = levelScale a (levelScale b r) := by
  refine expHomeo.symm.injective ?_
  rw [expHomeo_symm_levelScale, expHomeo_symm_levelScale, expHomeo_symm_levelScale,
    qMul_apply_zero]
  rw [add_smul]
  abel

/-- **The two factors of `coordFam` compose.** -/
theorem coordFam_mul (a b : Eucl 3) (h : pureInner a b ≠ 1)
    (x : Set.Ioi (0 : ℝ) × Projectivization ℝ (Eucl 3)) :
    coordFam (qMul a b) x = coordFam a (coordFam b x) := by
  refine Prod.ext ?_ ?_
  · show levelScale (qMul a b) x.1 = levelScale a (levelScale b x.1)
    exact levelScale_mul a b x.1
  · show classMap (qMul a b) x.2 = classMap a (classMap b x.2)
    exact congrFun (classMap_mul a b h) x.2

/-- **THE COMPOSITION LAW of the chart perturbations**: the perturbation of the parameter `qMul a b` is
the composite of the perturbations `a` and `b`. -/
theorem chartPert_mul (a b : Eucl 3) (h : pureInner a b ≠ 1) :
    chartPert (qMul a b) = chartPert a ∘ chartPert b := by
  funext p
  rw [Function.comp_apply, chartPert, chartPert, chartPert,
    cappingSpaceHomeoProj.apply_symm_apply, coordFam_mul a b h]

end

end Work.Drive
