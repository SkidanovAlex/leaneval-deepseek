/-
# Symmetry of the `laplaceTraceVec` pairing (Green's second identity, vector form)

`Work.FTS.PressureOn.Auxiliary.integral_inner_laplaceTraceVec_comm`:

  `∫ x, ⟪V x, laplaceTraceVec W x⟫ = ∫ x, ⟪laplaceTraceVec V x, W x⟫`

for `V, W : ℝ³ → ℝ³` of class `C^∞` with `W` compactly supported, where
`laplaceTraceVec W = ∑ᵢ ∂ᵢ∂ᵢW` is the componentwise Laplacian
(`Work.FTS.PressureOn.Defs`).  This is the integration-by-parts (Green) symmetry of the vector
Laplacian; it lets a vector field be paired against a compactly supported one on either side.
The scalar analogue is `Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm`.

## The route

Everything is reduced to the *scalar* identity, coordinate by coordinate.

* `PiLp.inner_apply` expands `⟪V x, laplaceTraceVec W x⟫` as `∑ j, (V x) j * (laplaceTraceVec W x) j`,
  and `Work.FTS.PressureOn.Green.IgslvAux.laplaceTraceVec_coord` identifies the `j`-th coordinate of
  the vector Laplacian with the scalar Laplacian of the `j`-th coordinate:
  `(laplaceTraceVec W x) j = laplaceTrace (fun y => (W y) j) x`.
* `MeasureTheory.integral_finsetSum` pulls the integral out of the finite sum, which needs the
  `Integrable`-ness of each coordinate summand; the summand `(V x) j * laplaceTrace (W · j) x` is
  the product of a continuous function with a continuous compactly supported one (the support lies
  in `tsupport W`, by `IgslvAux.support_laplaceTrace_subset`), and its mirror image
  `laplaceTrace (V · j) x * (W x) j` is supported in `tsupport (W · j)`.  Those two integrability
  statements are the delegated lemma `integrable_inner_laplaceTraceVec_coord`.
* Each coordinate integral is then handled by the proved scalar Green identity
  `Green.integral_mul_laplaceTrace_comm`, applied to `f = fun y => (V y) j` and
  `u = fun y => (W y) j` (the compact support hypothesis is
  `IgslvAux.hasCompactSupport_coord`), and the sum is folded back into an integral and finally
  into `⟪laplaceTraceVec V x, W x⟫`.

No growth hypothesis on `V` is needed: both integrands are supported in the compact set
`tsupport W`, where the corresponding factor is continuous.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.PressureOn.Green.integral_gauss_smul_laplaceTraceVec
import Submission.Work.FTS.PressureOn.Auxiliary.integrable_inner_laplaceTraceVec_coord

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity MeasureTheory

namespace Work.FTS.PressureOn.Auxiliary

open Work.FTS.PressureOn.Green

/-- For real numbers the inner product is the product. -/
private lemma inner_real_coord (a b : ℝ) : inner ℝ a b = a * b := by
  rw [RCLike.inner_apply]; simp; ring

theorem integral_inner_laplaceTraceVec_comm (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hV : ∀ n : ℕ, ContDiff ℝ n V) (hW : ∀ n : ℕ, ContDiff ℝ n W)
    (hWc : HasCompactSupport W) :
    ∫ x, inner ℝ (V x) (Work.FTS.PressureOn.laplaceTraceVec W x)
      = ∫ x, inner ℝ (Work.FTS.PressureOn.laplaceTraceVec V x) (W x) := by
  -- the two pointwise coordinate expansions of the inner products
  have hptL : ∀ x, inner ℝ (V x) (Work.FTS.PressureOn.laplaceTraceVec W x)
      = ∑ j : Fin 3, (V x) j * Work.FTS.PressureOn.laplaceTrace (fun y => (W y) j) x := by
    intro x
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IgslvAux.laplaceTraceVec_coord W (hW 2) x j, inner_real_coord]
  have hptR : ∀ x, inner ℝ (Work.FTS.PressureOn.laplaceTraceVec V x) (W x)
      = ∑ j : Fin 3, Work.FTS.PressureOn.laplaceTrace (fun y => (V y) j) x * (W x) j := by
    intro x
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IgslvAux.laplaceTraceVec_coord V (hV 2) x j, inner_real_coord]
  -- integrability of the coordinate summands
  have hintL : ∀ j : Fin 3, Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (V x) j * Work.FTS.PressureOn.laplaceTrace (fun y => (W y) j) x) :=
    fun j => (integrable_inner_laplaceTraceVec_coord V W hV hW hWc j).1
  have hintR : ∀ j : Fin 3, Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      Work.FTS.PressureOn.laplaceTrace (fun y => (V y) j) x * (W x) j) :=
    fun j => (integrable_inner_laplaceTraceVec_coord V W hV hW hWc j).2
  calc ∫ x, inner ℝ (V x) (Work.FTS.PressureOn.laplaceTraceVec W x)
      = ∫ x, ∑ j : Fin 3,
          (V x) j * Work.FTS.PressureOn.laplaceTrace (fun y => (W y) j) x := by
        rw [funext hptL]
    _ = ∑ j : Fin 3, ∫ x,
          (V x) j * Work.FTS.PressureOn.laplaceTrace (fun y => (W y) j) x := by
        simpa using integral_finsetSum Finset.univ (fun j _ => hintL j)
    _ = ∑ j : Fin 3, ∫ x,
          Work.FTS.PressureOn.laplaceTrace (fun y => (V y) j) x * (W x) j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm (fun y => (V y) j)
          (fun y => (W y) j) (IgslvAux.contDiff_coord V (hV 2) j)
          (IgslvAux.contDiff_coord W (hW 2) j) (IgslvAux.hasCompactSupport_coord W hWc j)
    _ = ∫ x, ∑ j : Fin 3,
          Work.FTS.PressureOn.laplaceTrace (fun y => (V y) j) x * (W x) j := by
        simpa using (integral_finsetSum Finset.univ (fun j _ => hintR j)).symm
    _ = ∫ x, inner ℝ (Work.FTS.PressureOn.laplaceTraceVec V x) (W x) := by
        rw [funext (fun x => (hptR x).symm)]

end Work.FTS.PressureOn.Auxiliary
