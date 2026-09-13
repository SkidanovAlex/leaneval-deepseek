import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus.FDeriv

open scoped Topology ContDiff

/-- The iterated derivative of the composition with a continuous linear map on the right,
computed with only a local `C^n` hypothesis. -/
theorem iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (h : F → ℝ) (y : E) (n : ℕ)
    (hh : ContDiffAt ℝ n h (L y)) :
    iteratedFDeriv ℝ n (fun y : E => h (L y)) y =
      (iteratedFDeriv ℝ n h (L y)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨u, hu_nhds, hu⟩ := hh.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVsub, hVopen, hLVy⟩ := mem_nhds_iff.mp hu_nhds
  have hV : ContDiffOn ℝ (n : ℕ∞ω) h V := hu.mono hVsub
  have hpre_open : IsOpen (L ⁻¹' V) := hVopen.preimage L.continuous
  have hcomp : ContDiffOn ℝ (n : ℕ∞ω) (fun y : E => h (L y)) (L ⁻¹' V) :=
    hV.comp_continuousLinearMap L
  have key := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ) L hV
    hVopen.uniqueDiffOn hpre_open.uniqueDiffOn (x := y) hLVy (i := n) (le_refl (n : ℕ∞ω))
  have hL : iteratedFDerivWithin ℝ n (fun y : E => h (L y)) (L ⁻¹' V) y
      = iteratedFDeriv ℝ n (fun y : E => h (L y)) y :=
    iteratedFDerivWithin_eq_iteratedFDeriv (f := fun y : E => h (L y))
      hpre_open.uniqueDiffOn (hcomp.contDiffAt (hpre_open.mem_nhds hLVy)) hLVy
  have hR : iteratedFDerivWithin ℝ n h V (L y) = iteratedFDeriv ℝ n h (L y) :=
    iteratedFDerivWithin_eq_iteratedFDeriv (f := h) hVopen.uniqueDiffOn hh hLVy
  have key' : iteratedFDerivWithin ℝ n (fun y : E => h (L y)) (L ⁻¹' V) y
      = (iteratedFDerivWithin ℝ n h V (L y)).compContinuousLinearMap (fun _ => L) := key
  rw [hL, hR] at key'
  exact key'

theorem fderiv_fderiv_comp_add_linear_of_contDiffAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (x₀ : F)
    (f : F → ℝ) (y u v : E) (hf : ContDiffAt ℝ 2 f (x₀ + L y)) :
    fderiv ℝ (fderiv ℝ (fun y : E => f (x₀ + L y))) y u v =
      (fderiv ℝ (fderiv ℝ f) (x₀ + L y)) (L u) (L v) := by
  have hA : ContDiffAt ℝ 2 (fun z : F => f (x₀ + z)) (L y) := by
    have hshift : ContDiffAt ℝ 2 (fun z : F => x₀ + z) (L y) := by fun_prop
    exact ContDiffAt.comp (L y) hf hshift
  have haux : iteratedFDeriv ℝ 2 (fun y : E => f (x₀ + L y)) y
      = (iteratedFDeriv ℝ 2 (fun z : F => f (x₀ + z)) (L y)).compContinuousLinearMap
          (fun _ => L) :=
    iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt L (fun z : F => f (x₀ + z)) y 2 hA
  have hL2 : fderiv ℝ (fderiv ℝ (fun y : E => f (x₀ + L y))) y u v
      = iteratedFDeriv ℝ 2 (fun y : E => f (x₀ + L y)) y ![u, v] := by
    simp [iteratedFDeriv_two_apply]
  have hR2 : (fderiv ℝ (fderiv ℝ f) (x₀ + L y)) (L u) (L v)
      = iteratedFDeriv ℝ 2 f (x₀ + L y) ![L u, L v] := by
    simp [iteratedFDeriv_two_apply]
  rw [hL2, hR2, haux]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_left]
  congr 1
  ext i
  fin_cases i <;> simp

end Commons.Analysis.Calculus.FDeriv