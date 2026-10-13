import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Green.integral_gauss_smul_laplaceTraceVec
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the coordinatewise pairing with the trace of the Hessian

`Work.FTS.PressureOn.Auxiliary.integrable_inner_laplaceTraceVec_coord`.

For a smooth vector field `V` on `ℝ³` and a smooth *compactly supported* vector field `W`, and for
every coordinate index `j`, the two coordinatewise pairings

  `x ↦ (V x) j * Δ((W ·) j)(x)`  and  `x ↦ Δ((V ·) j)(x) * (W x) j`

are integrable on `ℝ³`.

Both are immediate: the trace of the Hessian of a compactly supported smooth function is
continuous (`Green.continuous_laplaceTrace`) and supported in `tsupport` of that function
(`Green.laplaceTrace_eq_zero_of_notMem_tsupport`), hence bounded with compact support; multiplying
it by the continuous coordinate function `x ↦ (V x) j` (resp. `x ↦ (W x) j`) keeps it continuous
with compact support, and a continuous compactly supported function is integrable.

The only structural inputs are the two elementary facts that the coordinate functions of a smooth
vector field are smooth and compactly supported whenever the field is.
-/

namespace Work.FTS.PressureOn.Auxiliary

open MeasureTheory

/-- The coordinate functions `x ↦ (V x) j` of a smooth vector field are smooth: they are the
composites of `V` with the continuous linear projection `PiLp.proj`. -/
lemma contDiff_coord (V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hV : ∀ n : ℕ, ContDiff ℝ n V) (j : Fin 3) :
    ∀ n : ℕ, ContDiff ℝ n (fun x : EuclideanSpace ℝ (Fin 3) => (V x) j) := by
  intro n
  fun_prop

/-- The coordinate functions `x ↦ (V x) j` of a compactly supported vector field are compactly
supported (their support is contained in the support of the field). -/
lemma hasCompactSupport_coord (V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hVc : HasCompactSupport V) (j : Fin 3) :
    HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 3) => (V x) j) := by
  refine hVc.mono' fun z hz => ?_
  by_contra h
  exact hz (by simp [image_eq_zero_of_notMem_tsupport h])

/-- The trace of the Hessian of a coordinate function of a compactly supported smooth vector field
is compactly supported. -/
lemma hasCompactSupport_laplaceTrace_coord
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hWc : HasCompactSupport W) (j : Fin 3) :
    HasCompactSupport
      (Work.FTS.PressureOn.laplaceTrace (fun y : EuclideanSpace ℝ (Fin 3) => (W y) j)) :=
  (hasCompactSupport_coord W hWc j).mono' fun _ hz => by
    by_contra h
    exact hz (Work.FTS.PressureOn.Green.laplaceTrace_eq_zero_of_notMem_tsupport h)

/-- The trace of the Hessian of a coordinate function of a smooth vector field is continuous. -/
lemma continuous_laplaceTrace_coord
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hW : ∀ n : ℕ, ContDiff ℝ n W) (j : Fin 3) :
    Continuous
      (Work.FTS.PressureOn.laplaceTrace (fun y : EuclideanSpace ℝ (Fin 3) => (W y) j)) :=
  Work.FTS.PressureOn.Green.continuous_laplaceTrace _ ((contDiff_coord W hW j) 2)

theorem integrable_inner_laplaceTraceVec_coord
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hV : ∀ n : ℕ, ContDiff ℝ n V) (hW : ∀ n : ℕ, ContDiff ℝ n W)
    (hWc : HasCompactSupport W) (j : Fin 3) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        (V x) j * Work.FTS.PressureOn.laplaceTrace (fun y => (W y) j) x) ∧
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        Work.FTS.PressureOn.laplaceTrace (fun y => (V y) j) x * (W x) j) := by
  have hVj : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => (V x) j) :=
    ((contDiff_coord V hV j) 0).continuous
  have hWjc : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 3) => (W x) j) :=
    hasCompactSupport_coord W hWc j
  have hWj : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => (W x) j) :=
    ((contDiff_coord W hW j) 0).continuous
  have hΔWj : Continuous
      (Work.FTS.PressureOn.laplaceTrace (fun y : EuclideanSpace ℝ (Fin 3) => (W y) j)) :=
    continuous_laplaceTrace_coord W hW j
  have hΔWjc : HasCompactSupport
      (Work.FTS.PressureOn.laplaceTrace (fun y : EuclideanSpace ℝ (Fin 3) => (W y) j)) :=
    hasCompactSupport_laplaceTrace_coord W hWc j
  have hΔVj : Continuous
      (Work.FTS.PressureOn.laplaceTrace (fun y : EuclideanSpace ℝ (Fin 3) => (V y) j)) :=
    continuous_laplaceTrace_coord V hV j
  constructor
  · refine (hVj.mul hΔWj).integrable_of_hasCompactSupport ?_
    exact hΔWjc.mul_left (f := fun x : EuclideanSpace ℝ (Fin 3) => (V x) j)
  · refine (hΔVj.mul hWj).integrable_of_hasCompactSupport ?_
    exact hWjc.mul_left (f := fun x : EuclideanSpace ℝ (Fin 3) =>
      Work.FTS.PressureOn.laplaceTrace (fun y => (V y) j) x)

end Work.FTS.PressureOn.Auxiliary
