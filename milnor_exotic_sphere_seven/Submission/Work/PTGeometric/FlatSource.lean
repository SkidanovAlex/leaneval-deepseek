import Submission.Work.PTGeometric.RegionManifoldNC
import Submission.Work.PTGeometric.SourceHomotopy
import Submission.Work.PTGeometric.nonempty_halfBallSource
import Submission.Work.PTGeometric.TubeAmbient

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the flat source of the last mile (the design of `SOURCE_PLAN.md` / README §29)

The source of the last mile is the **half-space** `EuclideanHalfSpace ((8+k)+1)`: its boundary
`{x 0 = 0}` is where the pieces sit (so that `∂M` meets the zero set `W` in the pieces), and its
remaining coordinates are an honest flat chart of the *cube* of the null-homotopy, so that TUBULAR's
collapse data — which are data on the cube — become smooth functions of coordinates of the source.
This file contains the definitions of that design and their first properties:

* `Work.PTGeometric.cubeCoord` — the explicit diffeomorphism `ℝ^n ≅ int I^n`,
  `y ↦ ((1 + y_i/√(1+y_i²))/2)_i`;
* `Work.PTGeometric.clamp` — the smooth `ℝ → [0,1]` which is `0` on `(-∞,0]` and `1` on `[1/2,∞)`;
* `Work.PTGeometric.head`, `Work.PTGeometric.tail` — the time coordinate and the cube coordinates;
* `Work.PTGeometric.flatSourceHomotopy` — the null-homotopy on the flat source,
  `x ↦ H (φ (cubeCoord (tail x)), 1 + clamp (head x))`, with its continuity and its **collar
  identity** (where the homotopy is stationary, i.e. where the pieces live), which is what makes
  the ambient field smooth at the pieces.

## Main definitions

* `Work.PTGeometric.cubeCoord`, `Work.PTGeometric.clamp`, `Work.PTGeometric.flatSourceHomotopy`

## Main results

* `Work.PTGeometric.continuous_flatSourceHomotopy`
* `Work.PTGeometric.flatSourceHomotopy_eq_collapse`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

variable {k : ℕ}

/-- **The cube chart of the flat source**: the explicit diffeomorphism `ℝ^n ≅ int I^n` given by the
coordinatewise inverse of `x ↦ x/√(1-x²)`, i.e. `y ↦ ((1 + y/√(1+y²))/2)`.  Its `i`-th component is
`0` at `y_i = -∞` and `1` at `y_i = +∞`, and it is *smooth* — which is why the cube coordinates of
TUBULAR's collapse are smooth functions of the source coordinates. -/
def cubeCoord (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) : Fin n → Set.Icc (0 : ℝ) 1 :=
  fun i => ⟨(1 + y i / Real.sqrt (1 + (y i) ^ 2)) / 2, by
    have hs : 0 < Real.sqrt (1 + (y i) ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have h2 : |y i| < Real.sqrt (1 + (y i) ^ 2) := by
      rw [Real.lt_sqrt (abs_nonneg _)]
      nlinarith [sq_abs (y i), sq_nonneg (y i)]
    have h1 : -1 < y i / Real.sqrt (1 + (y i) ^ 2) := by
      rw [lt_div_iff₀ hs, neg_mul, one_mul]
      have := neg_lt_of_abs_lt h2
      linarith
    have h3 : y i / Real.sqrt (1 + (y i) ^ 2) < 1 := by
      rw [div_lt_one hs]
      exact (abs_lt.mp h2).2
    constructor <;> linarith⟩

@[simp] theorem cubeCoord_apply_coe (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ((cubeCoord n y i : Set.Icc (0 : ℝ) 1) : ℝ)
      = (1 + y i / Real.sqrt (1 + (y i) ^ 2)) / 2 := rfl

theorem cubeCoord_pos (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    0 < ((cubeCoord n y i : Set.Icc (0 : ℝ) 1) : ℝ) := by
  rw [cubeCoord_apply_coe]
  have hs : 0 < Real.sqrt (1 + (y i) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h2 : |y i| < Real.sqrt (1 + (y i) ^ 2) := by
    rw [Real.lt_sqrt (abs_nonneg _)]
    nlinarith [sq_abs (y i), sq_nonneg (y i)]
  have h1 : -1 < y i / Real.sqrt (1 + (y i) ^ 2) := by
    rw [lt_div_iff₀ hs, neg_mul, one_mul]
    have := neg_lt_of_abs_lt h2
    linarith
  linarith

theorem cubeCoord_lt_one (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ((cubeCoord n y i : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
  rw [cubeCoord_apply_coe]
  have hs : 0 < Real.sqrt (1 + (y i) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h3 : y i / Real.sqrt (1 + (y i) ^ 2) < 1 := by
    rw [div_lt_one hs]
    have h2 : |y i| < Real.sqrt (1 + (y i) ^ 2) := by
      rw [Real.lt_sqrt (abs_nonneg _)]
      nlinarith [sq_abs (y i), sq_nonneg (y i)]
    exact (abs_lt.mp h2).2
  linarith

theorem continuous_cubeCoord_apply (n : ℕ) (i : Fin n) :
    Continuous (fun y : EuclideanSpace ℝ (Fin n) => ((cubeCoord n y i : Set.Icc (0 : ℝ) 1) : ℝ)) := by
  have hnum : Continuous (fun y : EuclideanSpace ℝ (Fin n) => y i) := (continuous_apply i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).continuous
  have hs : Continuous (fun y : EuclideanSpace ℝ (Fin n) => Real.sqrt (1 + (y i) ^ 2)) :=
    Continuous.sqrt (continuous_const.add (hnum.pow 2))
  have hne : ∀ y : EuclideanSpace ℝ (Fin n), Real.sqrt (1 + (y i) ^ 2) ≠ 0 := fun y =>
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have h : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
      (1 + y i / Real.sqrt (1 + (y i) ^ 2)) / 2) :=
    (continuous_const.add (hnum.div hs hne)).div_const 2
  simpa only [cubeCoord_apply_coe] using h

theorem continuous_cubeCoord (n : ℕ) :
    Continuous (cubeCoord n) := by
  refine continuous_pi (fun i => Continuous.subtype_mk ?_ _)
  simpa only [cubeCoord_apply_coe] using continuous_cubeCoord_apply n i

/-- **The time clamp** of the flat source: the smooth function which is `0` for `t ≤ 0` and `1` for
`1/2 ≤ t`.  It reparametrises the time coordinate of the annulus null-homotopy
`Hbar : S^n × [1,2] → D.T` into the first coordinate `x 0 ≥ 0` of the flat source, so that the
homotopy is *stationary* on `x 0 ≤ 0`. -/
def clamp (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1)

theorem clamp_nonneg (t : ℝ) : 0 ≤ clamp t := Real.smoothTransition.nonneg _

theorem clamp_le_one (t : ℝ) : clamp t ≤ 1 := Real.smoothTransition.le_one _

theorem clamp_eq_zero_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : clamp t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem clamp_eq_one_of_one_le {t : ℝ} (ht : 1 ≤ t) : clamp t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem clamp_mono : Monotone clamp := fun a b hab =>
  Real.smoothTransition.monotone (by linarith)

theorem continuous_clamp : Continuous clamp :=
  Real.smoothTransition.continuous.comp
    ((continuous_const.mul continuous_id).sub continuous_const)

/-- The **time coordinate** of the flat source `EuclideanSpace ℝ (Fin (N+1))`. -/
def head (N : ℕ) (x : EuclideanSpace ℝ (Fin (N + 1))) : ℝ := x 0

/-- The **cube coordinates** of the flat source `EuclideanSpace ℝ (Fin (N+1))`: the last `N`
coordinates (`Fin.tail`, as the continuous linear map `tailCLM`). -/
def tail (N : ℕ) (x : EuclideanSpace ℝ (Fin (N + 1))) : EuclideanSpace ℝ (Fin N) := tailCLM N x

theorem tail_apply (N : ℕ) (x : EuclideanSpace ℝ (Fin (N + 1))) (i : Fin N) :
    tail N x i = x (Fin.succ i) := tailCLM_apply N x i

theorem continuous_head (N : ℕ) : Continuous (head N) := by
  have h : Continuous (fun x : EuclideanSpace ℝ (Fin (N + 1)) => x 0) :=
    (continuous_apply 0).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (N+1) => ℝ)).continuous
  exact h

theorem continuous_tail (N : ℕ) : Continuous (tail N) := (tailCLM N).continuous

/-- The time coordinate of the annulus null-homotopy: `τ := 1 + clamp (head x) ∈ [1,2]`. -/
def srcTime (N : ℕ) (x : EuclideanSpace ℝ (Fin (N + 1))) : Set.Icc (1 : ℝ) 2 :=
  ⟨1 + clamp (head N x), by
    have h1 := clamp_nonneg (head N x)
    have h2 := clamp_le_one (head N x)
    constructor <;> linarith⟩

@[simp] theorem srcTime_coe (N : ℕ) (x : EuclideanSpace ℝ (Fin (N + 1))) :
    ((srcTime N x : Set.Icc (1 : ℝ) 2) : ℝ) = 1 + clamp (head N x) := rfl

/-- **The null-homotopy on the flat source.**  From the annulus null-homotopy
`Hbar : S^n × [1,2] → D.T` (whose `0`-collar is the explicit cube loop `α`) and the collapsing cube
map `φ`, the flat source `EuclideanSpace ℝ (Fin (n+1))` carries the homotopy
`x ↦ Hbar (φ (cubeCoord (tail x)), 1 + clamp (head x))`: the cube coordinates of the source are read
by `cubeCoord`, and the time coordinate of the annulus by `clamp` of the first coordinate. -/
def flatSourceHomotopy (n : ℕ) {D : ThomTarget k}
    (H : C(SourceModel n, D.T))
    (φ : C(Fin n → Set.Icc (0 : ℝ) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (x : EuclideanSpace ℝ (Fin (n + 1))) : D.T :=
  H (φ (cubeCoord n (tail n x)), srcTime n x)

theorem continuous_srcTime (n : ℕ) : Continuous (srcTime n) :=
  Continuous.subtype_mk (continuous_const.add (continuous_clamp.comp (continuous_head n))) _

theorem continuous_flatSourceHomotopy (n : ℕ) {D : ThomTarget k}
    (H : C(SourceModel n, D.T))
    (φ : C(Fin n → Set.Icc (0 : ℝ) 1, Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    Continuous (flatSourceHomotopy (k := k) n H φ) :=
  H.continuous.comp (((φ.continuous.comp (continuous_cubeCoord n)).comp (continuous_tail n)).prodMk
    (continuous_srcTime n))

/-- **The collar identity.**  Where the annulus homotopy is stationary (its `0`-collar), the flat
source homotopy is the explicit cube loop `α` read at the cube coordinates of the source, and is
independent of the time coordinate.  This is the statement the source construction consumes at the
pieces: it exhibits the ambient field near the pieces as TUBULAR's collapse data in a *smooth*
coordinate of the source. -/
theorem flatSourceHomotopy_eq_collapse (n : ℕ) {D : ThomTarget k}
    (H : C(SourceModel n, D.T))
    (φ : C(Fin n → Set.Icc (0 : ℝ) 1, Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (α : GenLoop (Fin n) D.T D.t₀)
    (hH : ∀ (y : Fin n → Set.Icc (0 : ℝ) 1) (τ : Set.Icc (1 : ℝ) 2),
      (τ : ℝ) ≤ 3 / 2 → H (φ y, τ) = α y)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : head n x ≤ 1 / 2) :
    flatSourceHomotopy (k := k) n H φ x = α (cubeCoord n (tail n x)) := by
  have hcl : clamp (head n x) = 0 := clamp_eq_zero_of_le_half hx
  have hτ : ((srcTime n x : Set.Icc (1 : ℝ) 2) : ℝ) ≤ 3 / 2 := by
    rw [srcTime_coe, hcl]; norm_num
  exact hH (cubeCoord n (tail n x)) (srcTime n x) hτ

end

end Work.PTGeometric
