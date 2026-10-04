import Submission.ModelBound
import Submission.Commons.Analysis.InnerProductSpace.great_circle_norm
import Submission.Commons.Analysis.InnerProductSpace.great_circle_orth_norm
import Submission.Commons.Analysis.InnerProductSpace.norm_sq_polar_decomp

set_option backward.isDefEq.respectTransparency.types false

/-!
# The great-circle model path and the local hinge comparison

This file continues route (M) of `Submission/Roadmap.lean` §28.4.  Given the model differential
bound of `Submission/ModelBound.lean`, it constructs the **great circle** joining the polar
coordinate points `(sin r₁·U, cos r₁)` and `(sin r₂·V, cos r₂)` in `T_{x₀}M × ℝ`, maps it back to
`T_{x₀}M` by the polar-coordinate map `(sin r·e, cos r) ↦ r·e`, and integrates the differential
bound along the resulting path.  The result is the **local hinge comparison** (Toponogov's hinge
theorem for small hinges):

`d(exp_{x₀}(r₁·U), exp_{x₀}(r₂·V)) ≤ arccos (cos r₁ cos r₂ + sin r₁ sin r₂ ⟨U,V⟩)`.

Sections:

* `1.` the great circle in components and its derivative, together with the two basic identities
  (unit norm, constant speed `Φ`);
* `2.` the polar coordinates `(r, e)`, `(r', e')` of a curve on the unit sphere and the *polar
  decomposition identity* `‖P'‖² = r'² + sin²r ‖e'‖²`;
* `3.` the assembly: the pointwise bound, the length integral and the hinge comparison.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartBounds
open Submission.Gauss
open Submission.Minimal
open Submission.SphereCoord

namespace Submission.ModelPath

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-! ## 1. The great circle in components -/

/-- The `F`-component of the great circle through `(A₁,c₁)` and `(A₂,c₂)`. -/
def gcA {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (A₁ A₂ : F) (Φ : ℝ) : ℝ → F :=
  fun s => (Real.sin ((1 - s) * Φ) / Real.sin Φ) • A₁
    + (Real.sin (s * Φ) / Real.sin Φ) • A₂

/-- The `ℝ`-component of the great circle. -/
def gcC (c₁ c₂ : ℝ) (Φ : ℝ) : ℝ → ℝ :=
  fun s => (Real.sin ((1 - s) * Φ) / Real.sin Φ) * c₁
    + (Real.sin (s * Φ) / Real.sin Φ) * c₂

/-- The derivative of the `F`-component of the great circle. -/
def gcA' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (A₁ A₂ : F) (Φ : ℝ) : ℝ → F :=
  fun s => ((-Φ * Real.cos ((1 - s) * Φ)) / Real.sin Φ) • A₁
    + ((Φ * Real.cos (s * Φ)) / Real.sin Φ) • A₂

/-- The derivative of the `ℝ`-component of the great circle. -/
def gcC' (c₁ c₂ : ℝ) (Φ : ℝ) : ℝ → ℝ :=
  fun s => ((-Φ * Real.cos ((1 - s) * Φ)) / Real.sin Φ) * c₁
    + ((Φ * Real.cos (s * Φ)) / Real.sin Φ) * c₂

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Expansion of the squared norm of `a • x + b • y`. -/
lemma norm_sq_smul_add_smul (a b : ℝ) (x y : F) :
    ‖a • x + b • y‖ ^ 2
      = a ^ 2 * ‖x‖ ^ 2 + b ^ 2 * ‖y‖ ^ 2 + 2 * a * b * inner ℝ x y := by
  rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
    sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The derivative of `u ↦ sin ((1-u)Φ)/sin Φ`. -/
lemma hasDerivAt_coef1 (Φ s : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sin ((1 - u) * Φ) / Real.sin Φ)
      ((Real.cos ((1 - s) * Φ) * (-Φ)) / Real.sin Φ) s := by
  have h : HasDerivAt (fun u : ℝ => (1 - u) * Φ) (-Φ) s := by
    have := ((hasDerivAt_const (c := (1 : ℝ)) s).sub (hasDerivAt_id s)).mul_const Φ
    simpa using this
  exact h.sin.div_const _

/-- The derivative of `u ↦ sin (uΦ)/sin Φ`. -/
lemma hasDerivAt_coef2 (Φ s : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sin (u * Φ) / Real.sin Φ)
      ((Real.cos (s * Φ) * Φ) / Real.sin Φ) s := by
  have h : HasDerivAt (fun u : ℝ => u * Φ) Φ s := by
    simpa using (hasDerivAt_id s).mul_const Φ
  exact h.sin.div_const _

lemma hasDerivAt_gcA (A₁ A₂ : F) (Φ s : ℝ) :
    HasDerivAt (gcA A₁ A₂ Φ) (gcA' A₁ A₂ Φ s) s := by
  have h1 := (hasDerivAt_coef1 Φ s).smul_const A₁
  have h2 := (hasDerivAt_coef2 Φ s).smul_const A₂
  have h := h1.add h2
  have hv : ((Real.cos ((1 - s) * Φ) * (-Φ)) / Real.sin Φ) • A₁
        + ((Real.cos (s * Φ) * Φ) / Real.sin Φ) • A₂ = gcA' A₁ A₂ Φ s := by
    have hc1 : (Real.cos ((1 - s) * Φ) * (-Φ)) / Real.sin Φ
        = (-Φ * Real.cos ((1 - s) * Φ)) / Real.sin Φ := by ring
    have hc2 : (Real.cos (s * Φ) * Φ) / Real.sin Φ
        = (Φ * Real.cos (s * Φ)) / Real.sin Φ := by ring
    rw [hc1, hc2, gcA']
  rwa [hv] at h

/-- The derivative of the `F`-component of the great circle, in an arbitrary normed space (the
version `hasDerivAt_gcA` above lives in a section carrying an inner product structure). -/
lemma hasDerivAt_gcA_normed {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A₁ A₂ : G) (Φ s : ℝ) :
    HasDerivAt (gcA A₁ A₂ Φ) (gcA' A₁ A₂ Φ s) s := by
  have h1 := (hasDerivAt_coef1 Φ s).smul_const A₁
  have h2 := (hasDerivAt_coef2 Φ s).smul_const A₂
  have h := h1.add h2
  have hv : ((Real.cos ((1 - s) * Φ) * (-Φ)) / Real.sin Φ) • A₁
        + ((Real.cos (s * Φ) * Φ) / Real.sin Φ) • A₂ = gcA' A₁ A₂ Φ s := by
    have hc1 : (Real.cos ((1 - s) * Φ) * (-Φ)) / Real.sin Φ
        = (-Φ * Real.cos ((1 - s) * Φ)) / Real.sin Φ := by ring
    have hc2 : (Real.cos (s * Φ) * Φ) / Real.sin Φ
        = (Φ * Real.cos (s * Φ)) / Real.sin Φ := by ring
    rw [hc1, hc2, gcA']
  rwa [hv] at h

lemma hasDerivAt_gcC (c₁ c₂ : ℝ) (Φ s : ℝ) :
    HasDerivAt (gcC c₁ c₂ Φ) (gcC' c₁ c₂ Φ s) s := by
  have h := (hasDerivAt_coef1 Φ s).mul_const c₁ |> fun h => h.add ((hasDerivAt_coef2 Φ s).mul_const c₂)
  have hv : ((Real.cos ((1 - s) * Φ) * (-Φ)) / Real.sin Φ) * c₁
        + ((Real.cos (s * Φ) * Φ) / Real.sin Φ) * c₂ = gcC' c₁ c₂ Φ s := by
    have hc1 : (Real.cos ((1 - s) * Φ) * (-Φ)) / Real.sin Φ
        = (-Φ * Real.cos ((1 - s) * Φ)) / Real.sin Φ := by ring
    have hc2 : (Real.cos (s * Φ) * Φ) / Real.sin Φ
        = (Φ * Real.cos (s * Φ)) / Real.sin Φ := by ring
    rw [hc1, hc2, gcC']
  rwa [hv] at h

/-- The coefficient identity behind the unit-norm property of the great circle. -/
lemma great_circle_unit_coeff (Φ s : ℝ) (hΦ0 : 0 < Φ) (hΦπ : Φ < Real.pi) :
    (Real.sin ((1 - s) * Φ) / Real.sin Φ) ^ 2 + (Real.sin (s * Φ) / Real.sin Φ) ^ 2
      + 2 * (Real.sin ((1 - s) * Φ) / Real.sin Φ) * (Real.sin (s * Φ) / Real.sin Φ)
          * Real.cos Φ = 1 := by
  have hsin : Real.sin Φ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ)
  have hAB : (1 - s) * Φ + s * Φ = Φ := by ring
  have hca : Real.cos Φ = Real.cos ((1 - s) * Φ) * Real.cos (s * Φ)
      - Real.sin ((1 - s) * Φ) * Real.sin (s * Φ) := by
    conv_lhs => rw [← hAB]
    rw [Real.cos_add]
  have hsa : Real.sin Φ = Real.sin ((1 - s) * Φ) * Real.cos (s * Φ)
      + Real.cos ((1 - s) * Φ) * Real.sin (s * Φ) := by
    conv_lhs => rw [← hAB]
    rw [Real.sin_add]
  have htrig : Real.sin ((1 - s) * Φ) ^ 2 + Real.sin (s * Φ) ^ 2
      + 2 * Real.sin ((1 - s) * Φ) * Real.sin (s * Φ) * Real.cos Φ = Real.sin Φ ^ 2 := by
    rw [hca, hsa]
    nlinarith [Real.sin_sq_add_cos_sq ((1 - s) * Φ), Real.sin_sq_add_cos_sq (s * Φ)]
  field_simp
  linarith [htrig]

/-- The coefficient identity behind the constant-speed property of the great circle. -/
lemma great_circle_speed_coeff (Φ s : ℝ) (hΦ0 : 0 < Φ) (hΦπ : Φ < Real.pi) :
    ((-Φ * Real.cos ((1 - s) * Φ)) / Real.sin Φ) ^ 2
      + ((Φ * Real.cos (s * Φ)) / Real.sin Φ) ^ 2
      + 2 * ((-Φ * Real.cos ((1 - s) * Φ)) / Real.sin Φ)
          * ((Φ * Real.cos (s * Φ)) / Real.sin Φ) * Real.cos Φ = Φ ^ 2 := by
  have hsin : Real.sin Φ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ)
  have hAB : Φ * (1 - s) + Φ * s = Φ := by ring
  have hca : Real.cos Φ = Real.cos (Φ * (1 - s)) * Real.cos (Φ * s)
      - Real.sin (Φ * (1 - s)) * Real.sin (Φ * s) := by
    conv_lhs => rw [← hAB]
    rw [Real.cos_add]
  have hsa : Real.sin Φ = Real.sin (Φ * (1 - s)) * Real.cos (Φ * s)
      + Real.cos (Φ * (1 - s)) * Real.sin (Φ * s) := by
    conv_lhs => rw [← hAB]
    rw [Real.sin_add]
  have htrig : Real.cos (Φ * (1 - s)) ^ 2 + Real.cos (Φ * s) ^ 2
      - 2 * Real.cos (Φ * (1 - s)) * Real.cos (Φ * s) * Real.cos Φ = Real.sin Φ ^ 2 := by
    rw [hca, hsa]
    nlinarith [Real.sin_sq_add_cos_sq (Φ * (1 - s)), Real.sin_sq_add_cos_sq (Φ * s)]
  field_simp
  nlinarith [htrig]

/-- **The great-circle point is on the unit sphere.** -/
lemma gc_unit (A₁ A₂ : F) (c₁ c₂ Φ s : ℝ) (h1 : ‖A₁‖ ^ 2 + c₁ ^ 2 = 1)
    (h2 : ‖A₂‖ ^ 2 + c₂ ^ 2 = 1) (hcos : inner ℝ A₁ A₂ + c₁ * c₂ = Real.cos Φ)
    (hΦ0 : 0 < Φ) (hΦπ : Φ < Real.pi) :
    ‖gcA A₁ A₂ Φ s‖ ^ 2 + (gcC c₁ c₂ Φ s) ^ 2 = 1 := by
  have hExp : ‖gcA A₁ A₂ Φ s‖ ^ 2 + (gcC c₁ c₂ Φ s) ^ 2
      = (Real.sin ((1 - s) * Φ) / Real.sin Φ) ^ 2 * (‖A₁‖ ^ 2 + c₁ ^ 2)
        + (Real.sin (s * Φ) / Real.sin Φ) ^ 2 * (‖A₂‖ ^ 2 + c₂ ^ 2)
        + 2 * (Real.sin ((1 - s) * Φ) / Real.sin Φ) * (Real.sin (s * Φ) / Real.sin Φ)
            * (inner ℝ A₁ A₂ + c₁ * c₂) := by
    rw [gcA, gcC, norm_sq_smul_add_smul]
    ring
  rw [hExp, h1, h2, hcos]
  simp only [mul_one]
  exact great_circle_unit_coeff Φ s hΦ0 hΦπ

/-- **The great circle has constant speed `Φ`.** -/
lemma gc_speed (A₁ A₂ : F) (c₁ c₂ Φ s : ℝ) (h1 : ‖A₁‖ ^ 2 + c₁ ^ 2 = 1)
    (h2 : ‖A₂‖ ^ 2 + c₂ ^ 2 = 1) (hcos : inner ℝ A₁ A₂ + c₁ * c₂ = Real.cos Φ)
    (hΦ0 : 0 < Φ) (hΦπ : Φ < Real.pi) :
    ‖gcA' A₁ A₂ Φ s‖ ^ 2 + (gcC' c₁ c₂ Φ s) ^ 2 = Φ ^ 2 := by
  have hExp : ‖gcA' A₁ A₂ Φ s‖ ^ 2 + (gcC' c₁ c₂ Φ s) ^ 2
      = ((-Φ * Real.cos ((1 - s) * Φ)) / Real.sin Φ) ^ 2 * (‖A₁‖ ^ 2 + c₁ ^ 2)
        + ((Φ * Real.cos (s * Φ)) / Real.sin Φ) ^ 2 * (‖A₂‖ ^ 2 + c₂ ^ 2)
        + 2 * ((-Φ * Real.cos ((1 - s) * Φ)) / Real.sin Φ)
            * ((Φ * Real.cos (s * Φ)) / Real.sin Φ) * (inner ℝ A₁ A₂ + c₁ * c₂) := by
    rw [gcA', gcC', norm_sq_smul_add_smul]
    ring
  rw [hExp, h1, h2, hcos]
  simp only [mul_one]
  exact great_circle_speed_coeff Φ s hΦ0 hΦπ

/-! ## 2. Polar coordinates on the unit sphere -/

/-- The polar radius `r = arccos c` of a point of the unit sphere of `F × ℝ` with `ℝ`-coordinate `c`
and `F`-coordinate `A` (normalised so that `‖A‖ = sin r`). -/
def pRadius (C : ℝ → ℝ) : ℝ → ℝ := fun s => Real.arccos (C s)

/-- `sin r` expressed through the `ℝ`-coordinate: `sin r = √(1-c²)`. -/
def pSin (C : ℝ → ℝ) : ℝ → ℝ := fun s => Real.sqrt (1 - (C s) ^ 2)

/-- The azimuth `e = A/‖A‖`. -/
def pE (A : ℝ → F) (C : ℝ → ℝ) : ℝ → F := fun s => (pSin C s)⁻¹ • A s

/-- The derivative of the polar radius: `r' = -c'/sin r`. -/
def pR (C C' : ℝ → ℝ) : ℝ → ℝ := fun s => - C' s / pSin C s

def pE' (A A' : ℝ → F) (C C' : ℝ → ℝ) : ℝ → F :=
  fun s => (pSin C s)⁻¹ • A' s + (((C s) * (C' s)) / (pSin C s) ^ 3) • A s

/-- The curve in `F` obtained from a curve on the unit sphere of `F × ℝ` by the polar-coordinate
map `(sin r · e, cos r) ↦ r · e`. -/
def pσ (A : ℝ → F) (C : ℝ → ℝ) : ℝ → F := fun s => (pRadius C s) • (pE A C s)

/-- The derivative of `pσ`. -/
def pσ' (A A' : ℝ → F) (C C' : ℝ → ℝ) : ℝ → F :=
  fun s => (pR C C' s) • (pE A C s) + (pRadius C s) • (pE' A A' C C' s)

/-- `sin` of the polar radius. -/
lemma sin_pRadius (C : ℝ → ℝ) (s : ℝ) : Real.sin (pRadius C s) = pSin C s :=
  Real.sin_arccos (C s)

/-- The polar radius vanishes exactly where the `F`-coordinate does. -/
lemma pSin_eq_norm (A : ℝ → F) (C : ℝ → ℝ) (s : ℝ) (hunit : ‖A s‖ ^ 2 + (C s) ^ 2 = 1) :
    pSin C s = ‖A s‖ := by
  rw [pSin]
  have h : 1 - (C s) ^ 2 = ‖A s‖ ^ 2 := by linarith
  rw [h, Real.sqrt_sq (norm_nonneg _)]

lemma pSin_pos (A : ℝ → F) (C : ℝ → ℝ) (s : ℝ) (hunit : ‖A s‖ ^ 2 + (C s) ^ 2 = 1)
    (hne : A s ≠ 0) : 0 < pSin C s := by
  rw [pSin_eq_norm A C s hunit]
  exact norm_pos_iff.mpr hne

/-- The derivative of `sin r`. -/
lemma hasDerivAt_pSin (C : ℝ → ℝ) (C' : ℝ → ℝ) (s : ℝ) (hC : HasDerivAt C (C' s) s)
    (hS : 0 < pSin C s) :
    HasDerivAt (pSin C) (-((C s) * (C' s)) / pSin C s) s := by
  have hg : HasDerivAt (fun u : ℝ => 1 - (C u) ^ 2) (-(2 * (C s) * (C' s))) s := by
    have h2 : HasDerivAt (fun u : ℝ => (C u) ^ 2) (2 * (C s) ^ (2 - 1) * C' s) s := hC.pow 2
    have h4 : HasDerivAt (fun u : ℝ => 1 - (C u) ^ 2) (0 - 2 * (C s) ^ (2 - 1) * C' s) s :=
      (hasDerivAt_const (c := (1 : ℝ)) s).sub h2
    have : 0 - 2 * (C s) ^ (2 - 1) * C' s = -(2 * (C s) * (C' s)) := by ring
    rwa [this] at h4
  have hne : (1 : ℝ) - (C s) ^ 2 ≠ 0 := by
    have := Real.sqrt_pos.mp hS
    linarith
  have hsqrt := (Real.hasDerivAt_sqrt hne).comp s hg
  rw [pSin]
  have hv : 1 / (2 * Real.sqrt (1 - (C s) ^ 2)) * (-(2 * (C s) * (C' s)))
      = -((C s) * (C' s)) / Real.sqrt (1 - (C s) ^ 2) := by
    field_simp
  rwa [hv] at hsqrt

/-- The derivative of the polar radius. -/
lemma hasDerivAt_pRadius (C : ℝ → ℝ) (C' : ℝ → ℝ) (s : ℝ) (hC : HasDerivAt C (C' s) s)
    (hS : 0 < pSin C s) : HasDerivAt (pRadius C) (pR C C' s) s := by
  have hne1 : C s ≠ 1 := by
    intro h
    have h2 := hS
    rw [pSin, h] at h2
    simp at h2
  have hne2 : C s ≠ -1 := by
    intro h
    have h2 := hS
    rw [pSin, h] at h2
    simp at h2
  have h := (Real.hasDerivAt_arccos hne2 hne1).comp s hC
  have hv : -(1 / Real.sqrt (1 - (C s) ^ 2)) * (C' s) = pR C C' s := by
    rw [pR, pSin]
    ring
  rwa [hv] at h

/-- The derivative of the azimuth. -/
lemma hasDerivAt_pE (A A' : ℝ → F) (C C' : ℝ → ℝ) (s : ℝ) (hA : HasDerivAt A (A' s) s)
    (hC : HasDerivAt C (C' s) s) (hS : 0 < pSin C s) :
    HasDerivAt (pE A C) (pE' A A' C C' s) s := by
  have hSin := hasDerivAt_pSin C C' s hC hS
  have hinv : HasDerivAt (fun u : ℝ => (pSin C u)⁻¹)
      (-(-((C s) * (C' s)) / pSin C s) / (pSin C s) ^ 2) s := hSin.inv (ne_of_gt hS)
  have h := hinv.smul hA
  have hv : (pSin C s)⁻¹ • A' s
        + (-(-((C s) * (C' s)) / pSin C s) / (pSin C s) ^ 2) • A s
      = pE' A A' C C' s := by
    simp only [pE']
    congr 1
    field_simp
  rw [hv] at h
  exact h

/-- `pσ` is differentiable with derivative `pσ'`. -/
lemma hasDerivAt_pσ (A A' : ℝ → F) (C C' : ℝ → ℝ) (s : ℝ) (hA : HasDerivAt A (A' s) s)
    (hC : HasDerivAt C (C' s) s) (hS : 0 < pSin C s) :
    HasDerivAt (pσ A C) (pσ' A A' C C' s) s := by
  have hr := hasDerivAt_pRadius C C' s hC hS
  have he := hasDerivAt_pE A A' C C' s hA hC hS
  have h := hr.smul he
  have hv : pRadius C s • pE' A A' C C' s + pR C C' s • pE A C s = pσ' A A' C C' s := by
    simp only [pσ']
    rw [add_comm]
  rw [hv] at h
  exact h

/-- The azimuth is a unit vector. -/
lemma pE_norm (A : ℝ → F) (C : ℝ → ℝ) (s : ℝ) (hunit : ‖A s‖ ^ 2 + (C s) ^ 2 = 1) (hne : A s ≠ 0) :
    ‖pE A C s‖ = 1 := by
  have hpos := pSin_pos A C s hunit hne
  rw [pE, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), pSin_eq_norm A C s hunit,
    inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr hne))]

/-- The azimuth is orthogonal to its derivative. -/
lemma inner_pE_pE' (A A' : ℝ → F) (C C' : ℝ → ℝ) (s : ℝ)
    (hunit : ‖A s‖ ^ 2 + (C s) ^ 2 = 1) (hne : A s ≠ 0)
    (htan : inner ℝ (A' s) (A s) + (C' s) * (C s) = 0) :
    inner ℝ (pE A C s) (pE' A A' C C' s) = 0 := by
  have hS := pSin_eq_norm A C s hunit
  have hpos := pSin_pos A C s hunit hne
  have hAA : inner ℝ (A s) (A s) = (‖A s‖) ^ 2 := real_inner_self_eq_norm_sq _
  have hswap : inner ℝ (A s) (A' s) = inner ℝ (A' s) (A s) := real_inner_comm _ _
  simp only [pE, pE']
  rw [real_inner_smul_left, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    hAA, hswap, hS]
  have ht : inner ℝ (A' s) (A s) = -(C' s * C s) := by linarith [htan]
  rw [ht]
  field_simp
  ring

/-- **The polar decomposition identity.**  For a point `(A, c)` of the unit sphere of `F × ℝ` with
`A ≠ 0`, with tangent vector `(A', c')`, the squared Euclidean norm of `(A', c')` is
`r'² + sin²r ‖e'‖²` where `r = arccos c`, `e = A/‖A‖` and `r'`, `e'` are the corresponding
derivatives. -/
lemma polar_identity (A A' : ℝ → F) (C C' : ℝ → ℝ) (s Φ : ℝ)
    (hunit : ‖A s‖ ^ 2 + (C s) ^ 2 = 1) (hne : A s ≠ 0)
    (htan : inner ℝ (A' s) (A s) + (C' s) * (C s) = 0)
    (hspeed : ‖A' s‖ ^ 2 + (C' s) ^ 2 = Φ ^ 2) :
    (pR C C' s) ^ 2 + (Real.sin (pRadius C s)) ^ 2 * ‖pE' A A' C C' s‖ ^ 2 = Φ ^ 2 := by
  have hS := pSin_eq_norm A C s hunit
  have h := Commons.Analysis.InnerProductSpace.norm_sq_polar_decomp
    (A s) (A' s) (C s) (C' s) hunit hne htan
  rw [hspeed] at h
  have hpR : pR C C' s = -(C' s) / ‖A s‖ := by rw [pR, hS]
  have hpE : pE' A A' C C' s
      = (‖A s‖)⁻¹ • A' s + (((C s) * (C' s)) / (‖A s‖) ^ 3) • A s := by
    rw [pE', hS]
  rw [sin_pRadius, hS, hpR, hpE]
  have hsq : (-(C' s) / ‖A s‖) ^ 2 = (C' s / ‖A s‖) ^ 2 := by ring
  rw [hsq]
  linarith [h]

/-! ## 3. The local hinge comparison -/

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- Two-dimensional Cauchy–Schwarz. -/
lemma abs_inner_add_mul_le {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (A₁ A₂ : G) (c₁ c₂ : ℝ) :
    |inner ℝ A₁ A₂ + c₁ * c₂|
      ≤ Real.sqrt (‖A₁‖ ^ 2 + c₁ ^ 2) * Real.sqrt (‖A₂‖ ^ 2 + c₂ ^ 2) := by
  have h1 : |inner ℝ A₁ A₂ + c₁ * c₂| ≤ ‖A₁‖ * ‖A₂‖ + |c₁| * |c₂| := by
    calc |inner ℝ A₁ A₂ + c₁ * c₂| ≤ |inner ℝ A₁ A₂| + |c₁ * c₂| := abs_add_le _ _
      _ = |inner ℝ A₁ A₂| + |c₁| * |c₂| := by rw [abs_mul]
      _ ≤ ‖A₁‖ * ‖A₂‖ + |c₁| * |c₂| := add_le_add (abs_real_inner_le_norm A₁ A₂) le_rfl
  have hle : (‖A₁‖ * ‖A₂‖ + |c₁| * |c₂|) ^ 2
      ≤ (‖A₁‖ ^ 2 + c₁ ^ 2) * (‖A₂‖ ^ 2 + c₂ ^ 2) := by
    have h := sq_nonneg (‖A₁‖ * |c₂| - |c₁| * ‖A₂‖)
    nlinarith [h, sq_abs c₁, sq_abs c₂]
  calc |inner ℝ A₁ A₂ + c₁ * c₂|
      ≤ ‖A₁‖ * ‖A₂‖ + |c₁| * |c₂| := h1
    _ = Real.sqrt ((‖A₁‖ * ‖A₂‖ + |c₁| * |c₂|) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt ((‖A₁‖ ^ 2 + c₁ ^ 2) * (‖A₂‖ ^ 2 + c₂ ^ 2)) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (‖A₁‖ ^ 2 + c₁ ^ 2) * Real.sqrt (‖A₂‖ ^ 2 + c₂ ^ 2) :=
        Real.sqrt_mul (by positivity) _

/-- The model distance `Φ = arccos (cos r₁ cos r₂ + sin r₁ sin r₂ ⟨U,V⟩)`, together with its
cosine and its range. -/
lemma model_cos_range (x₀ : M) (r₁ r₂ : ℝ) (U V : TangentSpace I x₀) (hU : ‖U‖ = 1)
    (hV : ‖V‖ = 1) :
    Real.cos (Real.arccos (Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V))
      = Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V
    ∧ -1 ≤ Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V
    ∧ Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V ≤ 1 := by
  set A₁ : TangentSpace I x₀ := Real.sin r₁ • U with hA₁
  set A₂ : TangentSpace I x₀ := Real.sin r₂ • V with hA₂
  have h1 : ‖A₁‖ ^ 2 + (Real.cos r₁) ^ 2 = 1 := by
    rw [hA₁, norm_smul, Real.norm_eq_abs, hU, mul_one, sq_abs]
    exact Real.sin_sq_add_cos_sq r₁
  have h2 : ‖A₂‖ ^ 2 + (Real.cos r₂) ^ 2 = 1 := by
    rw [hA₂, norm_smul, Real.norm_eq_abs, hV, mul_one, sq_abs]
    exact Real.sin_sq_add_cos_sq r₂
  have hin : inner ℝ A₁ A₂ = Real.sin r₁ * Real.sin r₂ * inner ℝ U V := by
    rw [hA₁, hA₂, real_inner_smul_left, real_inner_smul_right]
    ring
  have hbound := abs_inner_add_mul_le A₁ A₂ (Real.cos r₁) (Real.cos r₂)
  rw [h1, h2, Real.sqrt_one, one_mul] at hbound
  have hle : |Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V| ≤ 1 := by
    rw [add_comm, ← hin]
    exact hbound
  rw [abs_le] at hle
  refine ⟨?_, hle.1, hle.2⟩
  exact Real.cos_arccos hle.1 hle.2

/-- The `ℝ`-coordinate `C s` of the great circle is at least `cos (max r₁ r₂)` (for
`max r₁ r₂ ≤ π/2`). -/
lemma gcC_ge (r₁ r₂ Φ : ℝ) (hr1 : 0 ≤ r₁) (hr2 : 0 ≤ r₂) (hmax : max r₁ r₂ ≤ Real.pi / 2)
    (hΦ0 : 0 < Φ) (hΦπ : Φ < Real.pi) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Real.cos (max r₁ r₂) ≤ gcC (Real.cos r₁) (Real.cos r₂) Φ s := by
  have hsin : 0 < Real.sin Φ := Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ
  have hA : (1 - s) * Φ ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨mul_nonneg (sub_nonneg.mpr hs.2) hΦ0.le,
      by nlinarith [mul_le_mul_of_nonneg_right (by linarith [hs.1] : (1 - s) ≤ 1) hΦ0.le, hΦπ]⟩
  have hB : s * Φ ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨mul_nonneg hs.1 hΦ0.le,
      by nlinarith [mul_le_mul_of_nonneg_right hs.2 hΦ0.le, hΦπ]⟩
  have hα : 0 ≤ Real.sin ((1 - s) * Φ) / Real.sin Φ :=
    div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hA.1 hA.2) hsin.le
  have hβ : 0 ≤ Real.sin (s * Φ) / Real.sin Φ :=
    div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hB.1 hB.2) hsin.le
  have hsum : 1 ≤ Real.sin ((1 - s) * Φ) / Real.sin Φ + Real.sin (s * Φ) / Real.sin Φ := by
    have hAB : (1 - s) * Φ + s * Φ = Φ := by ring
    have hkey : Real.sin ((1 - s) * Φ) + Real.sin (s * Φ) - Real.sin Φ
        = Real.sin ((1 - s) * Φ) * (1 - Real.cos (s * Φ))
          + Real.sin (s * Φ) * (1 - Real.cos ((1 - s) * Φ)) := by
      have hsa : Real.sin Φ = Real.sin ((1 - s) * Φ) * Real.cos (s * Φ)
          + Real.cos ((1 - s) * Φ) * Real.sin (s * Φ) := by
        conv_lhs => rw [← hAB]
        rw [Real.sin_add]
      rw [hsa]; ring
    have hnn : 0 ≤ Real.sin ((1 - s) * Φ) + Real.sin (s * Φ) - Real.sin Φ := by
      rw [hkey]
      have h1 := Real.sin_nonneg_of_nonneg_of_le_pi hA.1 hA.2
      have h2 := Real.sin_nonneg_of_nonneg_of_le_pi hB.1 hB.2
      have h3 := Real.cos_le_one (s * Φ)
      have h4 := Real.cos_le_one ((1 - s) * Φ)
      nlinarith
    rw [← add_div, one_le_div hsin]
    linarith [hnn]
  have hx : 0 ≤ max r₁ r₂ := le_trans hr1 (le_max_left _ _)
  have hc1 : Real.cos (max r₁ r₂) ≤ Real.cos r₁ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hr1 (by linarith [hmax, Real.pi_pos]) (le_max_left _ _)
  have hc2 : Real.cos (max r₁ r₂) ≤ Real.cos r₂ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hr2 (by linarith [hmax, Real.pi_pos]) (le_max_right _ _)
  have hc0 : 0 ≤ Real.cos (max r₁ r₂) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx, Real.pi_pos], hmax⟩
  show Real.cos (max r₁ r₂)
    ≤ (Real.sin ((1 - s) * Φ) / Real.sin Φ) * Real.cos r₁
      + (Real.sin (s * Φ) / Real.sin Φ) * Real.cos r₂
  have h1 : (Real.sin ((1 - s) * Φ) / Real.sin Φ) * Real.cos (max r₁ r₂)
      + (Real.sin (s * Φ) / Real.sin Φ) * Real.cos (max r₁ r₂)
      ≤ (Real.sin ((1 - s) * Φ) / Real.sin Φ) * Real.cos r₁
        + (Real.sin (s * Φ) / Real.sin Φ) * Real.cos r₂ := by
    have hh1 := mul_le_mul_of_nonneg_left hc1 hα
    have hh2 := mul_le_mul_of_nonneg_left hc2 hβ
    linarith
  have h2 : Real.cos (max r₁ r₂)
      ≤ (Real.sin ((1 - s) * Φ) / Real.sin Φ) * Real.cos (max r₁ r₂)
        + (Real.sin (s * Φ) / Real.sin Φ) * Real.cos (max r₁ r₂) := by
    nlinarith [hsum, hc0]
  linarith [h1, h2]

/-- The azimuth of the great circle is non-zero when `U` and `V` are linearly independent. -/
lemma gcA_ne_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (r₁ r₂ Φ : ℝ) {U V : F}
    (hr1 : 0 < r₁) (hr2 : 0 < r₂)
    (hr1π : r₁ < Real.pi) (hr2π : r₂ < Real.pi) (hΦ0 : 0 < Φ) (hΦπ : Φ < Real.pi)
    (hind : ∀ a b : ℝ, a • U + b • V = 0 → a = 0 ∧ b = 0) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    gcA (Real.sin r₁ • U) (Real.sin r₂ • V) Φ s ≠ 0 := by
  intro hzero
  have hsin : 0 < Real.sin Φ := Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ
  have hsin1 : 0 < Real.sin r₁ := Real.sin_pos_of_pos_of_lt_pi hr1 hr1π
  have hsin2 : 0 < Real.sin r₂ := Real.sin_pos_of_pos_of_lt_pi hr2 hr2π
  have hzero' : (Real.sin ((1 - s) * Φ) / Real.sin Φ) • (Real.sin r₁ • U)
      + (Real.sin (s * Φ) / Real.sin Φ) • (Real.sin r₂ • V) = 0 := hzero
  rw [smul_smul, smul_smul] at hzero'
  obtain ⟨hα0, hβ0⟩ := hind _ _ hzero'
  have hα : Real.sin ((1 - s) * Φ) = 0 := by
    rcases mul_eq_zero.mp hα0 with h | h
    · exact (div_eq_zero_iff).mp h |>.resolve_right (ne_of_gt hsin)
    · exact absurd h (ne_of_gt hsin1)
  have hβ : Real.sin (s * Φ) = 0 := by
    rcases mul_eq_zero.mp hβ0 with h | h
    · exact (div_eq_zero_iff).mp h |>.resolve_right (ne_of_gt hsin)
    · exact absurd h (ne_of_gt hsin2)
  have hA1 : 0 ≤ (1 - s) * Φ := mul_nonneg (sub_nonneg.mpr hs.2) hΦ0.le
  have hA2 : (1 - s) * Φ < Real.pi := by
    have := mul_le_mul_of_nonneg_right (by linarith [hs.1] : (1 - s) ≤ 1) hΦ0.le
    linarith
  have hB1 : 0 ≤ s * Φ := mul_nonneg hs.1 hΦ0.le
  have hB2 : s * Φ < Real.pi := by
    have := mul_le_mul_of_nonneg_right hs.2 hΦ0.le
    linarith
  have hs1 : (1 - s) * Φ = 0 := by
    rcases eq_or_lt_of_le hA1 with h | h
    · exact h.symm
    · exact absurd hα (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h hA2))
  have hs2 : s * Φ = 0 := by
    rcases eq_or_lt_of_le hB1 with h | h
    · exact h.symm
    · exact absurd hβ (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h hB2))
  have h1 : s = 1 := by
    rcases mul_eq_zero.mp hs1 with h | h
    · linarith
    · exact absurd h (ne_of_gt hΦ0)
  have h2 : s = 0 := by
    rcases mul_eq_zero.mp hs2 with h | h
    · linarith
    · exact absurd h (ne_of_gt hΦ0)
  linarith

/-- The model distance is `< 1` in cosine. -/
lemma modelDist_lt_one (x₀ : M) {r₁ r₂ : ℝ} {U V : TangentSpace I x₀} (hr1 : 0 < r₁)
    (hr2 : 0 < r₂) (hr1π : r₁ < Real.pi / 3) (hr2π : r₂ < Real.pi / 3) (hU : ‖U‖ = 1)
    (hV : ‖V‖ = 1) (hind : ∀ a b : ℝ, a • U + b • V = 0 → a = 0 ∧ b = 0) :
    Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V < 1 := by
  have hsin1 : 0 < Real.sin r₁ :=
    Real.sin_pos_of_pos_of_lt_pi hr1 (by linarith [hr1π, Real.pi_pos])
  have hsin2 : 0 < Real.sin r₂ :=
    Real.sin_pos_of_pos_of_lt_pi hr2 (by linarith [hr2π, Real.pi_pos])
  have hc1 : inner ℝ U V ≤ 1 := by
    have := real_inner_le_norm U V
    rw [hU, hV, mul_one] at this
    exact this
  have hkey : Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V
      = Real.cos (r₁ - r₂) + Real.sin r₁ * Real.sin r₂ * (inner ℝ U V - 1) := by
    rw [Real.cos_sub]; ring
  rcases lt_trichotomy r₁ r₂ with h | h | h
  · have hcos : Real.cos (r₁ - r₂) < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := r₂ - r₁) (le_refl 0)
        (by linarith [hr2π, Real.pi_pos]) (by linarith)
      rw [Real.cos_zero] at this
      rwa [show r₁ - r₂ = -(r₂ - r₁) by ring, Real.cos_neg]
    have : Real.sin r₁ * Real.sin r₂ * (inner ℝ U V - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hsin1.le hsin2.le) (by linarith)
    linarith [hkey]
  · subst h
    have hcne : inner ℝ U V ≠ 1 := by
      intro hc
      have hzero : ‖U - V‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real, hU, hV, hc]
        norm_num
      have hzero' : ‖U - V‖ = 0 := by nlinarith [hzero, norm_nonneg (U - V)]
      have hUV : U = V := sub_eq_zero.mp (norm_eq_zero.mp hzero')
      have h0 : (1 : ℝ) • U + (-1 : ℝ) • V = 0 := by
        rw [one_smul, neg_one_smul, hUV, add_neg_cancel]
      obtain ⟨ha, _⟩ := hind 1 (-1) h0
      norm_num at ha
    have hneg : Real.sin r₁ * Real.sin r₁ * (inner ℝ U V - 1) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hsin1 hsin1) (by
        have := lt_of_le_of_ne hc1 hcne; linarith)
    have hk := hkey
    simp only [sub_self, Real.cos_zero] at hk
    linarith [hk]
  · have hcos : Real.cos (r₁ - r₂) < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := r₁ - r₂) (le_refl 0)
        (by linarith [hr1π, Real.pi_pos]) (by linarith)
      rwa [Real.cos_zero] at this
    have : Real.sin r₁ * Real.sin r₂ * (inner ℝ U V - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hsin1.le hsin2.le) (by linarith)
    linarith [hkey]

/-- The model distance is `> -1` in cosine. -/
lemma modelDist_gt_neg_one (x₀ : M) {r₁ r₂ : ℝ} {U V : TangentSpace I x₀} (hr1 : 0 < r₁)
    (hr2 : 0 < r₂) (hr1π : r₁ < Real.pi / 3) (hr2π : r₂ < Real.pi / 3) (hU : ‖U‖ = 1)
    (hV : ‖V‖ = 1) :
    -1 < Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V := by
  have hsin1 : 0 ≤ Real.sin r₁ :=
    (Real.sin_pos_of_pos_of_lt_pi hr1 (by linarith [hr1π, Real.pi_pos])).le
  have hsin2 : 0 ≤ Real.sin r₂ :=
    (Real.sin_pos_of_pos_of_lt_pi hr2 (by linarith [hr2π, Real.pi_pos])).le
  have hc1 : -1 ≤ inner ℝ U V := by
    have h := abs_real_inner_le_norm U V
    rw [hU, hV, mul_one] at h
    exact neg_le_of_abs_le h
  have hsum : r₁ + r₂ < Real.pi := by linarith [hr1π, hr2π, Real.pi_pos]
  have hcos : -1 < Real.cos (r₁ + r₂) := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := r₁ + r₂) (y := Real.pi)
      (by linarith [hr1, hr2]) le_rfl hsum
    rwa [Real.cos_pi] at this
  have hkey : Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V
      = Real.cos (r₁ + r₂) + Real.sin r₁ * Real.sin r₂ * (inner ℝ U V + 1) := by
    rw [Real.cos_add]; ring
  have : 0 ≤ Real.sin r₁ * Real.sin r₂ * (inner ℝ U V + 1) :=
    mul_nonneg (mul_nonneg hsin1 hsin2) (by linarith)
  linarith [hkey, hcos]

/-- The velocity identity for the exponential map at `x₀`, with the tangent space as the model
(the fibre version of `Submission.Minimal.curveVelocity_eq_exp_deriv`). -/
lemma curveVelocity_eq_exp_deriv_fiber (x₀ : M) {σ σ' : ℝ → TangentSpace I x₀} {γ : ℝ → M}
    {t : ℝ}
    (hσ : HasDerivAt σ (σ' t) t)
    (hsm : MDifferentiableAt 𝓘(ℝ, TangentSpace I x₀) I
      (fun z : TangentSpace I x₀ => expMap cov x₀ z) (σ t))
    (hev : γ =ᶠ[𝓝 t] (fun r => expMap cov x₀ (σ r))) :
    curveVelocity (I := I) γ t
      = (mfderiv 𝓘(ℝ, TangentSpace I x₀) I
          (fun z : TangentSpace I x₀ => expMap cov x₀ z) (σ t)) (σ' t) := by
  have h1 : mfderiv 𝓘(ℝ) I γ t
      = (mfderiv 𝓘(ℝ, TangentSpace I x₀) I
          (fun z : TangentSpace I x₀ => expMap cov x₀ z) (σ t)).comp
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, TangentSpace I x₀) σ t) := by
    rw [hev.mfderiv_eq]
    exact mfderiv_comp t hsm (mdifferentiableAt_iff_differentiableAt.mpr hσ.differentiableAt)
  change (mfderiv 𝓘(ℝ) I γ t) (1 : ℝ) = _
  rw [h1]
  change (mfderiv 𝓘(ℝ, TangentSpace I x₀) I
      (fun z : TangentSpace I x₀ => expMap cov x₀ z) (σ t))
      ((mfderiv 𝓘(ℝ) 𝓘(ℝ, TangentSpace I x₀) σ t) (1 : ℝ)) = _
  rw [show (mfderiv 𝓘(ℝ) 𝓘(ℝ, TangentSpace I x₀) σ t) (1 : ℝ) = deriv σ t from by
    rw [mfderiv_eq_fderiv]; rfl, hσ.deriv]

/-- **The pointwise bound along the model path** (model-space form of the differential: the
derivative is taken for `exp` regarded as a map on the model space `E`, while the path lives in the
fibre `F`; the two are bridged by definitional equality).  `hbound` is the model differential bound
for `expMap` at `x₀`, phrased with the chart metric at `x₀`. -/
theorem pointwise_bound [Nontrivial E]
    {x₀ : M} {ρ Φ r₁ r₂ : ℝ} {U V : TangentSpace I x₀}
    (hbound : ∀ (r r' : ℝ) (e e' : TangentSpace I x₀), 0 < r → r < ρ →
      chartGram (I := I) x₀ x₀ e e = 1 → chartGram (I := I) x₀ x₀ e e' = 0 →
      ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) (r • e)) (r' • e + r • e')‖ ^ 2
        ≤ r' ^ 2 + (Real.sin r) ^ 2 * ‖e'‖ ^ 2)
    (hr1 : 0 < r₁) (hr1ρ : r₁ < ρ) (hr2 : 0 < r₂) (hr2ρ : r₂ < ρ)
    (hr1π : r₁ < Real.pi / 3) (hr2π : r₂ < Real.pi / 3)
    (hU : ‖U‖ = 1) (hV : ‖V‖ = 1) (hΦ0 : 0 < Φ) (hΦπ : Φ < Real.pi)
    (hcos : Real.cos Φ = Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V)
    (hind : ∀ a b : ℝ, a • U + b • V = 0 → a = 0 ∧ b = 0) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z)
          (show TangentSpace I x₀ from
            pσ (gcA (Real.sin r₁ • U) (Real.sin r₂ • V) Φ)
              (gcC (Real.cos r₁) (Real.cos r₂) Φ) s))
        (show TangentSpace I x₀ from
          pσ' (gcA (Real.sin r₁ • U) (Real.sin r₂ • V) Φ)
            (gcA' (Real.sin r₁ • U) (Real.sin r₂ • V) Φ)
            (gcC (Real.cos r₁) (Real.cos r₂) Φ) (gcC' (Real.cos r₁) (Real.cos r₂) Φ) s)‖ ≤ Φ := by
  intro s hs
  set A : ℝ → TangentSpace I x₀ := gcA (Real.sin r₁ • U) (Real.sin r₂ • V) Φ with hA
  set C : ℝ → ℝ := gcC (Real.cos r₁) (Real.cos r₂) Φ with hC
  set A' : ℝ → TangentSpace I x₀ := gcA' (Real.sin r₁ • U) (Real.sin r₂ • V) Φ with hA'
  set C' : ℝ → ℝ := gcC' (Real.cos r₁) (Real.cos r₂) Φ with hC'
  have hAA₁ : ‖Real.sin r₁ • U‖ ^ 2 + (Real.cos r₁) ^ 2 = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hU, mul_one, sq_abs]
    exact Real.sin_sq_add_cos_sq r₁
  have hAA₂ : ‖Real.sin r₂ • V‖ ^ 2 + (Real.cos r₂) ^ 2 = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hV, mul_one, sq_abs]
    exact Real.sin_sq_add_cos_sq r₂
  have hcosAA : inner ℝ (Real.sin r₁ • U) (Real.sin r₂ • V)
      + Real.cos r₁ * Real.cos r₂ = Real.cos Φ := by
    rw [real_inner_smul_left, real_inner_smul_right, hcos]
    ring
  have hunit : ‖A s‖ ^ 2 + (C s) ^ 2 = 1 := by
    rw [hA, hC]
    exact gc_unit _ _ _ _ _ _ hAA₁ hAA₂ hcosAA hΦ0 hΦπ
  have hspeed : ‖A' s‖ ^ 2 + (C' s) ^ 2 = Φ ^ 2 := by
    rw [hA', hC']
    exact gc_speed _ _ _ _ _ _ hAA₁ hAA₂ hcosAA hΦ0 hΦπ
  have hne : A s ≠ 0 := by
    rw [hA]
    exact gcA_ne_zero r₁ r₂ Φ hr1 hr2 (by linarith [hr1π, Real.pi_pos])
      (by linarith [hr2π, Real.pi_pos]) hΦ0 hΦπ hind hs
  have hderA : HasDerivAt A (gcA' (Real.sin r₁ • U) (Real.sin r₂ • V) Φ s) s := by
    rw [hA]; exact hasDerivAt_gcA _ _ _ s
  have hderC : HasDerivAt C (gcC' (Real.cos r₁) (Real.cos r₂) Φ s) s := by
    rw [hC]; exact hasDerivAt_gcC _ _ _ s
  have htan : inner ℝ (A' s) (A s) + (C' s) * (C s) = 0 := by
    have hder : HasDerivAt (fun u : ℝ => ‖A u‖ ^ 2 + (C u) ^ 2) 0 s := by
      have hconst : (fun u : ℝ => ‖A u‖ ^ 2 + (C u) ^ 2) = fun _ => (1 : ℝ) := by
        funext u
        rw [hA, hC]
        exact gc_unit _ _ _ _ _ _ hAA₁ hAA₂ hcosAA hΦ0 hΦπ
      rw [hconst]
      exact hasDerivAt_const _ _
    have hder2 : HasDerivAt (fun u : ℝ => ‖A u‖ ^ 2 + (C u) ^ 2)
        (2 * inner ℝ (A s) (A' s) + 2 * (C s * C' s)) s := by
      have hA'eq : gcA' (Real.sin r₁ • U) (Real.sin r₂ • V) Φ = A' := hA'.symm
      have hC'eq : gcC' (Real.cos r₁) (Real.cos r₂) Φ = C' := hC'.symm
      have h1 : HasDerivAt (fun u : ℝ => ‖A u‖ ^ 2) (2 * inner ℝ (A s) (A' s)) s := by
        have := hderA.norm_sq
        rw [hA'eq] at this
        exact this
      have h2 : HasDerivAt (fun u : ℝ => (C u) ^ 2) (2 * (C s * C' s)) s := by
        have hm := hderC.mul hderC
        rw [hC'eq] at hm
        have hfun : (C * C) = fun u : ℝ => (C u) ^ 2 := by
          funext u; rw [Pi.mul_apply, sq]
        rw [hfun] at hm
        have hval : C' s * C s + C s * C' s = 2 * (C s * C' s) := by ring
        rw [hval] at hm
        exact hm
      exact h1.add h2
    have huniq := hder.unique hder2
    have hsym : inner ℝ (A' s) (A s) = inner ℝ (A s) (A' s) := real_inner_comm _ _
    linarith
  have hrp : 0 < pRadius C s := by
    have hcle : C s ≤ 1 := by
      have h2 : C s ^ 2 ≤ 1 := by nlinarith [hunit, sq_nonneg (‖A s‖)]
      nlinarith [h2, sq_nonneg (C s - 1)]
    have hclt : C s < 1 := by
      rcases lt_or_eq_of_le hcle with h' | h'
      · exact h'
      · exfalso
        have h0 : ‖A s‖ = 0 := by nlinarith [hunit, h', norm_nonneg (A s)]
        exact hne (norm_eq_zero.mp h0)
    rw [pRadius]
    exact Real.arccos_pos.mpr hclt
  have hrmaxlt : max r₁ r₂ < Real.pi / 3 := max_lt hr1π hr2π
  have hrmax : max r₁ r₂ ≤ Real.pi / 2 := by linarith [hrmaxlt, Real.pi_pos]
  have hrle : pRadius C s ≤ max r₁ r₂ := by
    have hge : Real.cos (max r₁ r₂) ≤ C s := by
      rw [hC]
      exact gcC_ge r₁ r₂ Φ hr1.le hr2.le hrmax hΦ0 hΦπ hs
    rw [pRadius]
    calc Real.arccos (C s) ≤ Real.arccos (Real.cos (max r₁ r₂)) := Real.arccos_le_arccos hge
      _ = max r₁ r₂ := Real.arccos_cos (le_trans hr1.le (le_max_left _ _))
          (le_trans hrmax (by linarith [Real.pi_pos]))
  have hrlt : pRadius C s < ρ := lt_of_le_of_lt hrle (max_lt hr1ρ hr2ρ)
  set e : TangentSpace I x₀ := pE A C s with he
  set e' : TangentSpace I x₀ := pE' A A' C C' s with he'
  have he1 : ‖e‖ = 1 := by rw [he]; exact pE_norm A C s hunit hne
  have hee' : inner ℝ e e' = 0 := by
    rw [he, he']; exact inner_pE_pE' A A' C C' s hunit hne htan
  have hcg1 : chartGram (I := I) x₀ x₀ e e = 1 := by
    rw [Submission.ModelBound.chartGram_self_eq_norm_sq_fiber, he1]
    norm_num
  have hcg2 : chartGram (I := I) x₀ x₀ e e' = 0 := by
    rw [Submission.ModelBound.chartGram_self_eq_inner_fiber]
    exact hee'
  have hb := hbound (pRadius C s) (pR C C' s) e e' hrp hrlt hcg1 hcg2
  have hpolar := polar_identity A A' C C' s Φ hunit hne htan hspeed
  rw [← he'] at hpolar
  have hσs : (show TangentSpace I x₀ from pσ A C s) = (pRadius C s) • e := by
    simp only [pσ, he]
  have hσs' : (show TangentSpace I x₀ from pσ' A A' C C' s)
      = (pR C C' s) • e + (pRadius C s) • e' := by
    simp only [pσ', he, he']
  have hfinal : ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z)
        (show TangentSpace I x₀ from pσ A C s))
      (show TangentSpace I x₀ from pσ' A A' C C' s)‖ ^ 2 ≤ Φ ^ 2 := by
    rw [hσs, hσs']
    exact hb.trans_eq hpolar
  exact (sq_le_sq₀ (norm_nonneg _) hΦ0.le).mp hfinal
/-! ## 4. Generic (model-space) forms of the polar parametrisation

The following two lemmas are the model-space counterparts of `hasDerivAt_pσ` and of the smoothness
of `pσ`: they live in an arbitrary normed space (no inner product needed), so that they can be
applied to the model space `E` as well as to the fibre. -/

/-- The derivative of the polar parametrisation `u ↦ r(u) • (sin r(u))⁻¹ • A(u)`. -/
lemma hasDerivAt_modelPath {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A A' : ℝ → G) (C C' : ℝ → ℝ) (s : ℝ)
    (hA : HasDerivAt A (A' s) s) (hC : HasDerivAt C (C' s) s) (hS : 0 < pSin C s) :
    HasDerivAt (fun u : ℝ => (pRadius C u) • ((pSin C u)⁻¹ • A u))
      ((pR C C' s) • ((pSin C s)⁻¹ • A s)
        + (pRadius C s) • ((pSin C s)⁻¹ • A' s
            + (((C s) * (C' s)) / (pSin C s) ^ 3) • A s)) s := by
  have hSin := hasDerivAt_pSin C C' s hC hS
  have hinv : HasDerivAt (fun u : ℝ => (pSin C u)⁻¹)
      (-(-((C s) * (C' s)) / pSin C s) / (pSin C s) ^ 2) s := hSin.inv (ne_of_gt hS)
  have he : HasDerivAt (fun u : ℝ => (pSin C u)⁻¹ • A u)
      ((pSin C s)⁻¹ • A' s
        + (-(-((C s) * (C' s)) / pSin C s) / (pSin C s) ^ 2) • A s) s := hinv.smul hA
  have he' : HasDerivAt (fun u : ℝ => (pSin C u)⁻¹ • A u)
      ((pSin C s)⁻¹ • A' s + (((C s) * (C' s)) / (pSin C s) ^ 3) • A s) s := by
    convert he using 1
    congr 1
    field_simp
  have hr := hasDerivAt_pRadius C C' s hC hS
  have h := hr.smul he'
  rw [add_comm] at h
  exact h

/-- Smoothness of the polar parametrisation `u ↦ r(u) • (sin r(u))⁻¹ • A(u)`. -/
lemma contDiffAt_modelPath {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : ℝ → G) (C : ℝ → ℝ) (s : ℝ) (hA : ContDiffAt ℝ ∞ A s) (hC : ContDiffAt ℝ ∞ C s)
    (hm1 : -1 < C s) (h1 : C s < 1) :
    ContDiffAt ℝ ∞ (fun u : ℝ => (pRadius C u) • ((pSin C u)⁻¹ • A u)) s := by
  have hsq : (C s) ^ 2 < 1 := by nlinarith
  have hpos : 0 < 1 - (C s) ^ 2 := by linarith
  have hass : ContDiffAt ℝ ∞ (pSin C) s := by
    show ContDiffAt ℝ ∞ (fun u : ℝ => Real.sqrt (1 - (C u) ^ 2)) s
    refine (Real.contDiffAt_sqrt (x := 1 - (C s) ^ 2) (ne_of_gt hpos)).comp s ?_
    exact (contDiffAt_const (c := (1 : ℝ))).sub (hC.pow 2)
  have hinv : ContDiffAt ℝ ∞ (fun u : ℝ => (pSin C u)⁻¹) s :=
    hass.inv (ne_of_gt (Real.sqrt_pos.mpr hpos))
  have hr : ContDiffAt ℝ ∞ (pRadius C) s := by
    show ContDiffAt ℝ ∞ (fun u : ℝ => Real.arccos (C u)) s
    exact (Real.contDiffAt_arccos (by linarith) (by linarith)).comp s hC
  exact hr.smul (hinv.smul hA)


/-! ## 5. The local hinge comparison: assembly -/

/-- The identity of the fibre `TangentSpace I x₀` with the model space `E`, as a continuous linear
map.  The two types are definitionally the same but carry different norm structures, so this map is
the bridge used to transfer differentiability statements. -/
def coeLM (x₀ : M) : TangentSpace I x₀ →L[ℝ] E where
  toLinearMap :=
    { toFun := fun z => (z : E)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  cont := continuous_id

/-- **The local hinge comparison.**  There is `ρ > 0` such that for all linearly independent unit
vectors `U`, `V` in `T_{x₀}M` and all `r₁, r₂ ∈ (0, ρ)`,
`d(exp_{x₀}(r₁ U), exp_{x₀}(r₂ V)) ≤ arccos (cos r₁ cos r₂ + sin r₁ sin r₂ ⟪U,V⟫)`, the model
distance on the unit sphere of curvature `1`. -/
theorem edist_expMap_le_model_ind [Nontrivial E]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (r₁ r₂ : ℝ) (U V : TangentSpace I x₀),
      0 < r₁ → r₁ < ρ → 0 < r₂ → r₂ < ρ → ‖U‖ = 1 → ‖V‖ = 1 →
      (∀ a b : ℝ, a • U + b • V = 0 → a = 0 ∧ b = 0) →
      Manifold.riemannianEDist I (expMap cov x₀ (r₁ • U)) (expMap cov x₀ (r₂ • V))
        ≤ ENNReal.ofReal (Real.arccos (Real.cos r₁ * Real.cos r₂
            + Real.sin r₁ * Real.sin r₂ * inner ℝ U V)) := by
  obtain ⟨ρb, hρb, hbound₀⟩ := Submission.ModelBound.mfderiv_expMap_model_bound_polar
    (cov := cov) hmet htor hpinch x₀
  obtain ⟨ρsm, hρsm, hsm⟩ := Submission.Geodesic.exists_radius_contMDiffAt_expMap (cov := cov) x₀
  obtain ⟨lam, hlam, Lam, hLam, hgram⟩ := Submission.ChartBounds.exists_chartGram_bounds (I := I)
    (x₀ := x₀) (K := {x₀}) isCompact_singleton (singleton_nonempty x₀) (by
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact mem_chart_source H x₀)
  have hslpos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  haveI hcontR : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I) (M := M)
  refine ⟨min (min ρb (Real.pi / 3)) (Real.sqrt lam * ρsm),
    lt_min (lt_min hρb (by linarith [Real.pi_pos])) (mul_pos hslpos hρsm), ?_⟩
  intro r₁ r₂ U V hr1 hr1ρ hr2 hr2ρ hU hV hind
  have hr1b : r₁ < ρb := lt_of_lt_of_le hr1ρ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hr2b : r₂ < ρb := lt_of_lt_of_le hr2ρ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hr1pi : r₁ < Real.pi / 3 :=
    lt_of_lt_of_le hr1ρ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hr2pi : r₂ < Real.pi / 3 :=
    lt_of_lt_of_le hr2ρ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hr1sm : r₁ < Real.sqrt lam * ρsm := lt_of_lt_of_le hr1ρ (min_le_right _ _)
  have hr2sm : r₂ < Real.sqrt lam * ρsm := lt_of_lt_of_le hr2ρ (min_le_right _ _)
  set Φ : ℝ := Real.arccos (Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V)
    with hΦdef
  have hΦcos : Real.cos Φ = Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V := by
    rw [hΦdef]
    exact (model_cos_range x₀ r₁ r₂ U V hU hV).1
  have hΦlt : Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V < 1 :=
    modelDist_lt_one x₀ hr1 hr2 hr1pi hr2pi hU hV hind
  have hΦgt : -1 < Real.cos r₁ * Real.cos r₂ + Real.sin r₁ * Real.sin r₂ * inner ℝ U V :=
    modelDist_gt_neg_one x₀ hr1 hr2 hr1pi hr2pi hU hV
  have hΦ0 : 0 < Φ := by rw [hΦdef]; exact Real.arccos_pos.mpr hΦlt
  have hΦπ : Φ < Real.pi := by rw [hΦdef]; exact Real.arccos_lt_pi.mpr hΦgt
  -- the fibre copy, needed for the metric facts
  set AF : ℝ → TangentSpace I x₀ := gcA (Real.sin r₁ • U) (Real.sin r₂ • V) Φ with hAF
  set CF : ℝ → ℝ := gcC (Real.cos r₁) (Real.cos r₂) Φ with hCF
  set AF' : ℝ → TangentSpace I x₀ := gcA' (Real.sin r₁ • U) (Real.sin r₂ • V) Φ with hAF'
  set CF' : ℝ → ℝ := gcC' (Real.cos r₁) (Real.cos r₂) Φ with hCF'
  have hAA₁ : ‖Real.sin r₁ • U‖ ^ 2 + (Real.cos r₁) ^ 2 = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hU, mul_one, sq_abs]
    exact Real.sin_sq_add_cos_sq r₁
  have hAA₂ : ‖Real.sin r₂ • V‖ ^ 2 + (Real.cos r₂) ^ 2 = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hV, mul_one, sq_abs]
    exact Real.sin_sq_add_cos_sq r₂
  have hcosAA : inner ℝ (Real.sin r₁ • U) (Real.sin r₂ • V)
      + Real.cos r₁ * Real.cos r₂ = Real.cos Φ := by
    rw [real_inner_smul_left, real_inner_smul_right, hΦcos]
    ring
  have hunitF : ∀ s, ‖AF s‖ ^ 2 + (CF s) ^ 2 = 1 := by
    intro s
    rw [hAF, hCF]
    exact gc_unit _ _ _ _ _ _ hAA₁ hAA₂ hcosAA hΦ0 hΦπ
  have hneF : ∀ s ∈ Set.Icc (0 : ℝ) 1, AF s ≠ 0 := by
    intro s hs
    rw [hAF]
    exact gcA_ne_zero r₁ r₂ Φ hr1 hr2 (by linarith [hr1pi, Real.pi_pos])
      (by linarith [hr2pi, Real.pi_pos]) hΦ0 hΦπ hind hs
  have hrmaxlt : max r₁ r₂ < Real.pi / 3 := max_lt hr1pi hr2pi
  have hrmax : max r₁ r₂ ≤ Real.pi / 2 := by linarith [hrmaxlt, Real.pi_pos]
  have hrle : ∀ s ∈ Set.Icc (0 : ℝ) 1, pRadius CF s ≤ max r₁ r₂ := by
    intro s hs
    have hge : Real.cos (max r₁ r₂) ≤ CF s := by
      rw [hCF]
      exact gcC_ge r₁ r₂ Φ hr1.le hr2.le hrmax hΦ0 hΦπ hs
    rw [pRadius]
    calc Real.arccos (CF s) ≤ Real.arccos (Real.cos (max r₁ r₂)) := Real.arccos_le_arccos hge
      _ = max r₁ r₂ := Real.arccos_cos (le_trans hr1.le (le_max_left _ _))
          (le_trans hrmax (by linarith [Real.pi_pos]))
  -- the pointwise bound for the differential (in the model space)
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(mfderiv 𝓘(ℝ, E) I
      (fun z : E => expMap cov x₀ z) (show TangentSpace I x₀ from pσ AF CF t))
      (show TangentSpace I x₀ from pσ' AF AF' CF CF' t)‖ ≤ Φ := by
    intro t ht
    exact pointwise_bound (x₀ := x₀) (ρ := ρb) (Φ := Φ) (r₁ := r₁) (r₂ := r₂)
      (U := U) (V := V) hbound₀ hr1 hr1b hr2 hr2b hr1pi hr2pi hU hV hΦ0 hΦπ hΦcos hind t ht
  -- the model-space copy of the model path
  set A : ℝ → E := gcA (Real.sin r₁ • (show E from U)) (Real.sin r₂ • (show E from V)) Φ with hA
  set A' : ℝ → E :=
    gcA' (Real.sin r₁ • (show E from U)) (Real.sin r₂ • (show E from V)) Φ with hA'
  set σ : ℝ → E := fun u => (pRadius CF u) • ((pSin CF u)⁻¹ • A u) with hσ
  set σ' : ℝ → E := fun u => (pR CF CF' u) • ((pSin CF u)⁻¹ • A u)
      + (pRadius CF u) • ((pSin CF u)⁻¹ • A' u
          + (((CF u) * (CF' u)) / (pSin CF u) ^ 3) • A u) with hσ'
  set Γ : ℝ → M := fun u => expMap cov x₀ (σ u) with hΓ
  have hAsm : ContDiff ℝ ∞ A := by
    rw [hA]
    show ContDiff ℝ ∞ (fun s : ℝ => (Real.sin ((1 - s) * Φ) / Real.sin Φ) •
      (Real.sin r₁ • (show E from U))
      + (Real.sin (s * Φ) / Real.sin Φ) • (Real.sin r₂ • (show E from V)))
    exact (((Real.contDiff_sin.comp ((contDiff_const.sub contDiff_id).mul contDiff_const)).div_const
      _).smul_const _).add
      (((Real.contDiff_sin.comp (contDiff_id.mul contDiff_const)).div_const _).smul_const _)
  have hCFsm : ContDiff ℝ ∞ CF := by
    rw [hCF]
    show ContDiff ℝ ∞ (fun s : ℝ => (Real.sin ((1 - s) * Φ) / Real.sin Φ) * Real.cos r₁
      + (Real.sin (s * Φ) / Real.sin Φ) * Real.cos r₂)
    exact (((Real.contDiff_sin.comp ((contDiff_const.sub contDiff_id).mul contDiff_const)).div_const
      _).mul contDiff_const).add
      ((((Real.contDiff_sin.comp (contDiff_id.mul contDiff_const)).div_const _).mul contDiff_const))
  -- the endpoints
  have hσ0 : σ 0 = r₁ • (show E from U) := by
    show (Real.arccos (CF 0)) • ((Real.sqrt (1 - (CF 0) ^ 2))⁻¹ • (A 0))
      = r₁ • (show E from U)
    have hA0 : A 0 = Real.sin r₁ • (show E from U) := by
      rw [hA]
      show (Real.sin ((1 - 0) * Φ) / Real.sin Φ) • (Real.sin r₁ • (show E from U))
        + (Real.sin (0 * Φ) / Real.sin Φ) • (Real.sin r₂ • (show E from V))
        = Real.sin r₁ • (show E from U)
      rw [sub_zero, one_mul, zero_mul, Real.sin_zero, zero_div, zero_smul, add_zero,
        div_self (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ)), one_smul]
    have hC0 : CF 0 = Real.cos r₁ := by
      rw [hCF]
      show (Real.sin ((1 - 0) * Φ) / Real.sin Φ) * Real.cos r₁
        + (Real.sin (0 * Φ) / Real.sin Φ) * Real.cos r₂ = Real.cos r₁
      rw [sub_zero, one_mul, zero_mul, Real.sin_zero, zero_div, zero_mul, add_zero,
        div_self (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ)), one_mul]
    rw [hA0, hC0]
    have hsin1 : 0 < Real.sin r₁ :=
      Real.sin_pos_of_pos_of_lt_pi hr1 (by linarith [hr1pi, Real.pi_pos])
    have hs : Real.sqrt (1 - Real.cos r₁ ^ 2) = Real.sin r₁ := by
      rw [← Real.sin_sq, Real.sqrt_sq hsin1.le]
    rw [hs, Real.arccos_cos hr1.le (le_of_lt (by linarith [hr1pi, Real.pi_pos])),
      inv_smul_smul₀ (ne_of_gt hsin1)]
  have hσ1 : σ 1 = r₂ • (show E from V) := by
    show (Real.arccos (CF 1)) • ((Real.sqrt (1 - (CF 1) ^ 2))⁻¹ • (A 1))
      = r₂ • (show E from V)
    have hA1 : A 1 = Real.sin r₂ • (show E from V) := by
      rw [hA]
      show (Real.sin ((1 - 1) * Φ) / Real.sin Φ) • (Real.sin r₁ • (show E from U))
        + (Real.sin (1 * Φ) / Real.sin Φ) • (Real.sin r₂ • (show E from V))
        = Real.sin r₂ • (show E from V)
      rw [sub_self, zero_mul, Real.sin_zero, zero_div, zero_smul, zero_add, one_mul,
        div_self (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ)), one_smul]
    have hC1 : CF 1 = Real.cos r₂ := by
      rw [hCF]
      show (Real.sin ((1 - 1) * Φ) / Real.sin Φ) * Real.cos r₁
        + (Real.sin (1 * Φ) / Real.sin Φ) * Real.cos r₂ = Real.cos r₂
      rw [sub_self, zero_mul, Real.sin_zero, zero_div, zero_mul, zero_add, one_mul,
        div_self (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hΦ0 hΦπ)), one_mul]
    rw [hA1, hC1]
    have hsin2 : 0 < Real.sin r₂ :=
      Real.sin_pos_of_pos_of_lt_pi hr2 (by linarith [hr2pi, Real.pi_pos])
    have hs : Real.sqrt (1 - Real.cos r₂ ^ 2) = Real.sin r₂ := by
      rw [← Real.sin_sq, Real.sqrt_sq hsin2.le]
    rw [hs, Real.arccos_cos hr2.le (le_of_lt (by linarith [hr2pi, Real.pi_pos])),
      inv_smul_smul₀ (ne_of_gt hsin2)]
  -- the fibre norm of the path
  have hfnorm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(show TangentSpace I x₀ from σ t)‖ = pRadius CF t := by
    intro t ht
    have hS : 0 < pSin CF t := pSin_pos AF CF t (hunitF t) (hneF t ht)
    show ‖(pRadius CF t) • ((pSin CF t)⁻¹ • (show TangentSpace I x₀ from A t))‖ = pRadius CF t
    have hAN : ‖(show TangentSpace I x₀ from A t)‖ = pSin CF t := by
      have h1 : (show TangentSpace I x₀ from A t) = AF t := rfl
      rw [h1]
      exact (pSin_eq_norm AF CF t (hunitF t)).symm
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ pRadius CF t from Real.arccos_nonneg (CF t)),
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hS), hAN,
      inv_mul_cancel₀ (ne_of_gt hS), mul_one]
  -- smallness in the model norm
  have hsmall : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖σ t‖ < ρsm := by
    intro t ht
    have hlem := (hgram x₀ (by simp) (σ t)).1
    have hchart : chartGram (I := I) x₀ x₀ (σ t) (σ t)
        = ‖(show TangentSpace I x₀ from σ t)‖ ^ 2 :=
      Submission.ModelBound.chartGram_self_eq_norm_sq_fiber x₀ (show TangentSpace I x₀ from σ t)
    rw [hchart, hfnorm t ht] at hlem
    have hr : pRadius CF t < Real.sqrt lam * ρsm :=
      lt_of_le_of_lt (hrle t ht) (max_lt hr1sm hr2sm)
    have h2 : (pRadius CF t) ^ 2 < lam * ρsm ^ 2 := by
      have h3 := mul_self_lt_mul_self (show 0 ≤ pRadius CF t from Real.arccos_nonneg (CF t)) hr
      calc (pRadius CF t) ^ 2 = pRadius CF t * pRadius CF t := by rw [pow_two]
        _ < (Real.sqrt lam * ρsm) * (Real.sqrt lam * ρsm) := h3
        _ = lam * ρsm ^ 2 := by
            rw [mul_mul_mul_comm, Real.mul_self_sqrt hlam.le]
            ring
    have h4 : lam * ‖σ t‖ ^ 2 < lam * ρsm ^ 2 := lt_of_le_of_lt hlem h2
    have h5 := lt_of_mul_lt_mul_left h4 hlam.le
    nlinarith [h5, hρsm, norm_nonneg (σ t)]
  -- the derivative of the path
  have hσd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt σ (σ' t) t := by
    intro t ht
    have hS : 0 < pSin CF t := pSin_pos AF CF t (hunitF t) (hneF t ht)
    have hAd : HasDerivAt A (A' t) t := by
      rw [hA, hA']
      exact hasDerivAt_gcA_normed _ _ _ t
    have hCd : HasDerivAt CF (CF' t) t := by
      rw [hCF, hCF']
      exact hasDerivAt_gcC _ _ _ t
    show HasDerivAt (fun u : ℝ => (pRadius CF u) • ((pSin CF u)⁻¹ • A u))
      ((pR CF CF' t) • ((pSin CF t)⁻¹ • A t)
        + (pRadius CF t) • ((pSin CF t)⁻¹ • A' t
            + (((CF t) * (CF' t)) / (pSin CF t) ^ 3) • A t)) t
    exact hasDerivAt_modelPath A A' CF CF' t hAd hCd hS
  -- smoothness of the path
  have hσsm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ σ t := by
    intro t ht
    have hCs : CF t ∈ Set.Ioo (-1 : ℝ) 1 := by
      have h := hunitF t
      constructor
      · by_contra hcon
        rw [not_lt] at hcon
        have h0 : ‖AF t‖ = 0 := by nlinarith [h, hcon, norm_nonneg (AF t)]
        exact hneF t ht (norm_eq_zero.mp h0)
      · by_contra hcon
        rw [not_lt] at hcon
        have h0 : ‖AF t‖ = 0 := by nlinarith [h, hcon, norm_nonneg (AF t)]
        exact hneF t ht (norm_eq_zero.mp h0)
    show ContDiffAt ℝ ∞ (fun u : ℝ => (pRadius CF u) • ((pSin CF u)⁻¹ • A u)) t
    exact contDiffAt_modelPath A CF t hAsm.contDiffAt hCFsm.contDiffAt hCs.1 hCs.2
  -- smoothness of the curve in `M`
  have hΓsm : CMDiff[Set.Icc (0 : ℝ) 1] 1 Γ := by
    have h1 : ContMDiffOn 𝓘(ℝ) I ∞ Γ (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      have hσc : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ σ t :=
        contMDiffAt_iff_contDiffAt.mpr (hσsm t ht)
      have hexp : ContMDiffAt 𝓘(ℝ, E) I ∞ (fun z : E => expMap cov x₀ z) (σ t) :=
        hsm (σ t) (hsmall t ht)
      exact (hexp.comp t hσc).contMDiffWithinAt.mono (Set.subset_univ _)
    exact h1.of_le (WithTop.coe_le_coe.mpr le_top)
  -- the velocity identity
  have hvel : ∀ t ∈ Set.Icc (0 : ℝ) 1, curveVelocity (I := I) Γ t
      = (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ t)) (σ' t) := by
    intro t ht
    have hsmE : MDifferentiableAt 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ t) :=
      (hsm (σ t) (hsmall t ht)).mdifferentiableAt (by norm_num)
    have hev : Γ =ᶠ[𝓝 t] (fun r => expMap cov x₀ (σ r)) := Filter.EventuallyEq.of_eq rfl
    exact Submission.Minimal.curveVelocity_eq_exp_deriv (cov := cov) x₀ (hσd t ht) hsmE hev
  -- the length integral
  have hdist : Manifold.riemannianEDist I (Γ 0) (Γ 1) ≤ Manifold.pathELength I Γ 0 1 :=
    Submission.EDist.riemannianEDist_le_pathELength (I := I) hΓsm rfl rfl zero_le_one
  have hlen : Manifold.pathELength I Γ 0 1
      = ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Γ t) (1 : ℝ)‖ₑ :=
    Manifold.pathELength_eq_lintegral_mfderiv_Icc
  have hae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
      ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Γ t) (1 : ℝ)‖ₑ ≤ ENNReal.ofReal Φ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    have h1 : ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Γ t) (1 : ℝ)‖ₑ
        = ENNReal.ofReal ‖curveVelocity (I := I) Γ t‖ := by
      change ‖curveVelocity (I := I) Γ t‖ₑ = _
      rw [Submission.Minimal.enorm_eq_ofReal_norm]
    rw [h1, hvel t ht]
    exact ENNReal.ofReal_le_ofReal (hpoint t ht)
  calc Manifold.riemannianEDist I (expMap cov x₀ (r₁ • U)) (expMap cov x₀ (r₂ • V))
      = Manifold.riemannianEDist I (Γ 0) (Γ 1) := by
        congr 1
        · show expMap cov x₀ (r₁ • U) = expMap cov x₀ (σ 0)
          rw [hσ0]
        · show expMap cov x₀ (r₂ • V) = expMap cov x₀ (σ 1)
          rw [hσ1]
    _ ≤ Manifold.pathELength I Γ 0 1 := hdist
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I Γ t) (1 : ℝ)‖ₑ := hlen
    _ ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal Φ := MeasureTheory.lintegral_mono_ae hae
    _ = ENNReal.ofReal Φ := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
        norm_num


end

end Submission.ModelPath
