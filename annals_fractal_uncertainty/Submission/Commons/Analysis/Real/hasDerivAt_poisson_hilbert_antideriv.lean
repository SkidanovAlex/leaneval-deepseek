import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Real

theorem hasDerivAt_poisson_hilbert_antideriv {s y : ℝ} (hs : 0 < s) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        -(s / (2 * (y ^ 2 + s ^ 2))) *
            (Real.log ((u - y) ^ 2 + s ^ 2) - Real.log ((u + y) ^ 2 + s ^ 2))
          + (y / (y ^ 2 + s ^ 2)) *
            (Real.arctan ((u - y) / s) + Real.arctan ((u + y) / s)))
      (4 * s * y / (((t - y) ^ 2 + s ^ 2) * ((t + y) ^ 2 + s ^ 2))) t := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hy2 : y ^ 2 + s ^ 2 ≠ 0 := by positivity
  have hAt : (t - y) ^ 2 + s ^ 2 ≠ 0 := by positivity
  have hBt : (t + y) ^ 2 + s ^ 2 ≠ 0 := by positivity
  have hA : HasDerivAt (fun u : ℝ => (u - y) ^ 2 + s ^ 2) (2 * (t - y)) t := by
    have h2 := ((hasDerivAt_id t).sub_const y).pow 2
    simp only [id_eq, mul_one] at h2
    norm_num at h2
    simpa using h2.add_const (s ^ 2)
  have hB : HasDerivAt (fun u : ℝ => (u + y) ^ 2 + s ^ 2) (2 * (t + y)) t := by
    have h2 := ((hasDerivAt_id t).add_const y).pow 2
    simp only [id_eq, mul_one] at h2
    norm_num at h2
    simpa using h2.add_const (s ^ 2)
  have hlogA : HasDerivAt (fun u : ℝ => Real.log ((u - y) ^ 2 + s ^ 2))
      (2 * (t - y) / ((t - y) ^ 2 + s ^ 2)) t := hA.log hAt
  have hlogB : HasDerivAt (fun u : ℝ => Real.log ((u + y) ^ 2 + s ^ 2))
      (2 * (t + y) / ((t + y) ^ 2 + s ^ 2)) t := hB.log hBt
  have harctanA : HasDerivAt (fun u : ℝ => Real.arctan ((u - y) / s))
      (s / ((t - y) ^ 2 + s ^ 2)) t := by
    have hg : HasDerivAt (fun u : ℝ => (u - y) / s) (1 / s) t :=
      ((hasDerivAt_id t).sub_const y).div_const s
    have h := (Real.hasDerivAt_arctan ((t - y) / s)).comp t hg
    have hval : 1 / (1 + ((t - y) / s) ^ 2) * (1 / s) = s / ((t - y) ^ 2 + s ^ 2) := by
      field_simp
      ring
    rw [hval] at h
    exact h
  have harctanB : HasDerivAt (fun u : ℝ => Real.arctan ((u + y) / s))
      (s / ((t + y) ^ 2 + s ^ 2)) t := by
    have hg : HasDerivAt (fun u : ℝ => (u + y) / s) (1 / s) t :=
      ((hasDerivAt_id t).add_const y).div_const s
    have h := (Real.hasDerivAt_arctan ((t + y) / s)).comp t hg
    have hval : 1 / (1 + ((t + y) / s) ^ 2) * (1 / s) = s / ((t + y) ^ 2 + s ^ 2) := by
      field_simp
      ring
    rw [hval] at h
    exact h
  have hsub := hlogA.sub hlogB
  have hterm1 := hsub.const_mul (-(s / (2 * (y ^ 2 + s ^ 2))))
  have hadd := harctanA.add harctanB
  have hterm2 := hadd.const_mul (y / (y ^ 2 + s ^ 2))
  have hF := hterm1.add hterm2
  have hval : -(s / (2 * (y ^ 2 + s ^ 2))) *
        (2 * (t - y) / ((t - y) ^ 2 + s ^ 2) - 2 * (t + y) / ((t + y) ^ 2 + s ^ 2))
      + y / (y ^ 2 + s ^ 2) *
        (s / ((t - y) ^ 2 + s ^ 2) + s / ((t + y) ^ 2 + s ^ 2))
      = 4 * s * y / (((t - y) ^ 2 + s ^ 2) * ((t + y) ^ 2 + s ^ 2)) := by
    field_simp
    ring
  rw [hval] at hF
  exact hF

end Commons.Analysis.Real