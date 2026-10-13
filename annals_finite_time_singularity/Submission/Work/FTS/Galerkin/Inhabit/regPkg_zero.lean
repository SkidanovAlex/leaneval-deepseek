import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin.Inhabit

set_option autoImplicit false

/-! ## The zero function under the operators of `ℋ^k`

All the weighted derivatives occurring in `Work.Spaces.HkIntegrand` are built from `∂_z`, `∂_θ`
and the multiplications by `z` resp. `sin (2θ)`; each of them maps the zero function to itself, so
the integrand of the zero function vanishes identically and the zero function lies in `ℋ^k`. -/

/-- `∂_z 0 = 0`. -/
private theorem pz_zeroF : Work.Spaces.pz (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  funext z θ; simp [Work.Spaces.pz]

/-- `∂_θ 0 = 0`. -/
private theorem pth_zeroF : Work.Spaces.pth (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  funext z θ; simp [Work.Spaces.pth]

/-- Every iterated `D_z`-derivative of the zero function vanishes. -/
private theorem DzIter_zeroF (i : ℕ) :
    Work.Spaces.DzIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dz, pz_zeroF]

/-- Every iterated `D_θ`-derivative of the zero function vanishes. -/
private theorem DthIter_zeroF (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dth, pth_zeroF]

/-- Every mixed `D`-derivative of the zero function vanishes. -/
private theorem mixed_zeroF (j i : ℕ) :
    Work.Spaces.mixed j i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  simp only [Work.Spaces.mixed, DthIter_zeroF, DzIter_zeroF]

/-- The `ℋ^k`-integrand of the zero function vanishes identically. -/
theorem HkIntegrand_zeroF (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [DzIter_zeroF, mixed_zeroF]

/-- The zero function lies in `ℋ^k` for every `k`: its integrand is the zero function, which is
integrable on every set. -/
theorem HkMem_zeroF (α : ℝ) (k : ℕ) : Work.Spaces.HkMem α k (fun _ _ : ℝ => (0 : ℝ)) := by
  constructor
  · intro z hz
    refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
    exact (HkIntegrand_zeroF α k z θ).symm
  · refine IntegrableOn.congr_fun integrableOn_zero (fun z _ => ?_) measurableSet_Ici
    rw [funext (fun θ => HkIntegrand_zeroF α k z θ), MeasureTheory.integral_zero]

/-- The fake-time derivative of the zero family vanishes. -/
theorem gdot_zeroF (τ : ℝ) :
    Work.FTS.Galerkin.gdot (fun _ _ _ : ℝ => (0 : ℝ)) τ = fun _ _ => 0 := by
  funext z θ
  simp [Work.FTS.Galerkin.gdot]

/-- **Inhabitation of `RegPkg`:** the identically zero family satisfies the regularity package for
every `α`. The fake-time derivative of the zero family is zero, so all membership clauses reduce to
membership of the zero function (`Work.Spaces.HkMem α k 0`, whose integrand is the zero function). -/
theorem regPkg_zero (α : ℝ) : Work.FTS.Galerkin.RegPkg α (fun _ _ _ => 0) := by
  refine ⟨contDiffOn_const, ?_, ?_, ?_, ?_, ?_⟩
  · intro z θ hzθ
    exact continuousOn_const
  · intro τ hτ
    exact HkMem_zeroF α 4
  · intro τ hτ
    exact HkMem_zeroF α 5
  · intro τ hτ
    rw [gdot_zeroF]
    exact HkMem_zeroF α 3
  · intro τ hτ
    exact ⟨fun z => rfl, fun z => rfl⟩

end Work.FTS.Galerkin.Inhabit
