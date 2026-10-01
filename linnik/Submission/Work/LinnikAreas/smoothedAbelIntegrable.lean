import Mathlib

open MeasureTheory

namespace Work.LinnikAreas

theorem smoothedAbelIntegrable (β : ℝ) (x : ℕ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun u : ℝ => (((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ)
      + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1)))) volume (1:ℝ) (x:ℝ) := by
  apply ContinuousOn.intervalIntegrable
  have h1x : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hxne : (x:ℂ) ≠ 0 := by
    have : x ≠ 0 := by omega
    exact_mod_cast this
  have hmem : ∀ u ∈ Set.uIcc (1:ℝ) (x:ℝ), (u:ℂ) ∈ Complex.slitPlane := by
    intro u hu
    rw [Set.uIcc_of_le h1x] at hu
    rw [Complex.ofReal_mem_slitPlane]
    linarith [hu.1]
  have hcpow1 : ContinuousOn (fun u : ℝ => (u:ℂ) ^ (-(β:ℂ))) (Set.uIcc (1:ℝ) (x:ℝ)) :=
    Complex.continuous_ofReal.continuousOn.cpow continuousOn_const hmem
  have hcpow2 : ContinuousOn (fun u : ℝ => (u:ℂ) ^ (-((β:ℂ) + 1))) (Set.uIcc (1:ℝ) (x:ℝ)) :=
    Complex.continuous_ofReal.continuousOn.cpow continuousOn_const hmem
  have hmain : ContinuousOn
      (fun u : ℝ => (1 - β : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ)) (Set.uIcc (1:ℝ) (x:ℝ)) :=
    (hcpow1.const_mul ((1 - β : ℂ))).div continuousOn_const (fun u _ => hxne)
  have hmain2 : ContinuousOn
      (fun u : ℝ => (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1))) (Set.uIcc (1:ℝ) (x:ℝ)) :=
    hcpow2.const_mul ((β:ℂ))
  exact hmain.add hmain2

end Work.LinnikAreas
