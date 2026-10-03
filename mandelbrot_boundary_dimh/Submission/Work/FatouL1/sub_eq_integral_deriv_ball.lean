import Mathlib

namespace Work.FatouL1

/-- Fundamental theorem of calculus along the segment from `a` to `b` for a complex
differentiable function on a convex open set. -/
theorem sub_eq_integral_deriv_ball {f : ℂ → ℂ} {U : Set ℂ} {a b : ℂ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (ha : a ∈ U) (hb : b ∈ U)
    (hfd : DifferentiableOn ℂ f U) :
    f b - f a = (b - a) * ∫ t in (0 : ℝ)..1, deriv f (a + t • (b - a)) := by
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, a + t • (b - a) ∈ U := by
    intro t ht
    have h1 : 0 ≤ 1 - t := by linarith [ht.2]
    have h2 : 0 ≤ t := ht.1
    have h3 : (1 - t) + t = 1 := by ring
    have hmem := (convex_iff_add_mem.mp hconv) ha hb h1 h2 h3
    have heq : a + t • (b - a) = (1 - t) • a + t • b := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rwa [heq]
  have hgamma : ContinuousOn (fun t : ℝ => a + t • (b - a)) (Set.Icc (0:ℝ) 1) := by fun_prop
  have hmapγ : Set.MapsTo (fun t : ℝ => a + t • (b - a)) (Set.Icc (0:ℝ) 1) U := hseg
  have hd1 : ∀ t ∈ Set.Icc (0:ℝ) 1, DifferentiableAt ℂ f (a + t • (b - a)) := fun t ht =>
    (hfd _ (hseg t ht)).differentiableAt (hU.mem_nhds (hseg t ht))
  have hdd : DifferentiableOn ℂ (deriv f) U := hfd.deriv hU
  have hcont1 : ContinuousOn (fun t : ℝ => deriv f (a + t • (b - a))) (Set.Icc (0:ℝ) 1) :=
    hdd.continuousOn.comp hgamma hmapγ
  have hE1 : (b - a) • (∫ t in (0:ℝ)..1, deriv f (a + t • (b - a)))
      = f (a + (b - a)) - f a :=
    intervalIntegral.integral_unitInterval_deriv_eq_sub hcont1
      (fun t ht => (hd1 t ht).hasDerivAt)
  have hba : a + (b - a) = b := by abel
  rw [hba, smul_eq_mul] at hE1
  exact hE1.symm

end Work.FatouL1
