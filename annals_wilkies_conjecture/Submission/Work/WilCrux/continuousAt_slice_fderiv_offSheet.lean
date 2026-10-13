import Mathlib
import Submission.Work.WilCrux.SliceCauchyDefs
import Submission.Work.WilCrux.fibreFderivFamFun

open scoped Topology

noncomputable section

namespace Work.WilCrux

/-- **The off-sheet slice partial is continuous in the parameter.**  If `famFun G` is `C¹` at
the off-sheet point `(w₀, z₀)`, then the `j`-th partial `w ↦ fderiv ℝ (G w) z₀ (Pi.single j 1)`
of the slice is continuous at `w₀`.

Proof: `w ↦ Fin.append w z₀` is continuous, `ContDiffAt` is an open condition, so
`w ↦ fderiv ℝ (famFun G) (Fin.append w z₀)` is continuous at `w₀`
(`ContDiffAt.continuousAt_fderiv` composed with a continuous map), and evaluating a continuous
linear map at a fixed vector is continuous.  `Work.WilCrux.fibreFderivFamFun` (already proved in
`Submission/Work/WilCrux/fibreFderivFamFun.lean`) identifies
`fderiv ℝ (famFun G) (Fin.append w z₀) (Fin.append 0 v)` with `fderiv ℝ (G w) z₀ v` whenever
`famFun G` is differentiable at `Fin.append w z₀`, and
`Fin.append 0 (Pi.single j 1) = Pi.single (Fin.natAdd a j) 1` (prove by `funext` +
`Fin.addCases`). -/
theorem continuousAt_slice_fderiv_offSheet {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w₀ : Fin a → ℝ) (z₀ : Fin b → ℝ) (j : Fin b)
    (h : ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w₀ z₀)) :
    ContinuousAt (fun w : Fin a → ℝ => fderiv ℝ (G w) z₀ (Pi.single j 1)) w₀ := by
  -- `w ↦ Fin.append w z₀` is continuous at `w₀`.
  have happ : ContinuousAt (fun w : Fin a → ℝ => Fin.append w z₀) w₀ :=
    ((Fin.continuous_append (X := ℝ) a b).continuousAt).comp
      (ContinuousAt.prodMk continuousAt_id continuousAt_const)
  -- `famFun G` is `C¹` at `(w₀, z₀)`, hence `fderiv ℝ (famFun G)` is continuous there.
  have hfd : ContinuousAt (fderiv ℝ (Work.WilG4c.famFun G)) (Fin.append w₀ z₀) :=
    h.continuousAt_fderiv (by norm_num)
  -- hence the slice `w ↦ fderiv ℝ (famFun G) (Fin.append w z₀)` is continuous at `w₀`.
  have hcomp : ContinuousAt
      (fun w : Fin a → ℝ => fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z₀)) w₀ :=
    ContinuousAt.comp (g := fderiv ℝ (Work.WilG4c.famFun G))
      (f := fun w : Fin a → ℝ => Fin.append w z₀) hfd happ
  -- evaluating a continuous linear map at the fixed vector `Fin.append 0 (Pi.single j 1)`.
  have hmain : ContinuousAt
      (fun w : Fin a → ℝ =>
        fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z₀)
          (Fin.append (0 : Fin a → ℝ) (Pi.single j 1))) w₀ :=
    hcomp.clm_apply continuousAt_const
  -- On a neighbourhood of `w₀`, the two functions agree by `fibreFderivFamFun`.
  refine hmain.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ w : Fin a → ℝ in 𝓝 w₀,
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z₀) :=
    Filter.Tendsto.eventually happ (h.eventually (by norm_num))
  filter_upwards [hev] with w hw
  exact (fibreFderivFamFun G w z₀ (Pi.single j 1) (hw.differentiableAt (by norm_num))).symm

end Work.WilCrux
