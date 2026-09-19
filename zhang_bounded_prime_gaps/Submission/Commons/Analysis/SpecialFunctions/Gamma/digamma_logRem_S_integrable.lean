import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set Filter
open scoped Topology

namespace Commons.Analysis.SpecialFunctions.Gamma

theorem digamma_logRem_S_integrable (z : ℂ) (hz : 0 < z.re) (m : ℕ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      Complex.exp (-(z * (t : ℂ))) * ∑ k ∈ Finset.range (m + 1),
        Complex.exp (-((k : ℂ) * (t : ℂ)))) (Set.Ioi (0 : ℝ)) := by
  have hterm : ∀ k : ℕ, k ∈ Finset.range (m + 1) →
      IntegrableOn (fun t : ℝ => Complex.exp (-((z + (k : ℂ)) * (t : ℂ)))) (Set.Ioi (0 : ℝ)) := by
    intro k hk
    have hk0 : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    have ha : (-(z + (k : ℂ))).re < 0 := by
      simpa using (show -(z.re + (k : ℝ)) < 0 by linarith)
    have h := integrableOn_exp_mul_complex_Ioi (a := -(z + (k : ℂ))) ha (0 : ℝ)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro t ht
    refine congrArg Complex.exp ?_
    ring
  let S : ℝ → ℂ := fun t => ∑ k ∈ Finset.range (m + 1), Complex.exp (-((z + (k : ℂ)) * (t : ℂ)))
  have hS_int : IntegrableOn S (Set.Ioi (0 : ℝ)) := by
    exact integrable_finsetSum (s := Finset.range (m + 1))
      (f := fun (k : ℕ) (t : ℝ) => Complex.exp (-((z + (k : ℂ)) * (t : ℂ))))
      (μ := volume.restrict (Set.Ioi (0 : ℝ))) (by intro k hk; exact hterm k hk)
  have hEq : Set.EqOn S
      (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * ∑ k ∈ Finset.range (m + 1),
        Complex.exp (-((k : ℂ) * (t : ℂ)))) (Set.Ioi (0 : ℝ)) := by
    intro t ht
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Complex.exp_add]
    refine congrArg Complex.exp ?_
    ring
  exact hS_int.congr_fun hEq measurableSet_Ioi

end Commons.Analysis.SpecialFunctions.Gamma