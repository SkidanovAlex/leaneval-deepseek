import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

open Set

namespace Commons.Analysis.SpecialFunctions

theorem log_one_add_le_quintic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.log (1 + x) ≤ x - x^2/2 + x^3/3 - x^4/4 + x^5/5 := by
  let F : ℝ → ℝ := fun u => (u - u^2/2 + u^3/3 - u^4/4 + u^5/5) - Real.log (1 + u)
  have hF : ∀ t : ℝ, (1 + t) ≠ 0 → HasDerivAt F (t^5 / (1 + t)) t := by
    intro t ht
    change HasDerivAt (fun u : ℝ =>
      (u - u^2/2 + u^3/3 - u^4/4 + u^5/5) - Real.log (1 + u)) (t^5/(1+t)) t
    have h1 : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id' t
    have h2 : HasDerivAt (fun u : ℝ => u^2/2) t t := by
      convert! (hasDerivAt_pow 2 t).div_const (2:ℝ) using 1
      norm_num [pow_one]
    have h3 : HasDerivAt (fun u : ℝ => u^3/3) (t^2) t := by
      convert! (hasDerivAt_pow 3 t).div_const (3:ℝ) using 1
      norm_num
    have h4 : HasDerivAt (fun u : ℝ => u^4/4) (t^3) t := by
      convert! (hasDerivAt_pow 4 t).div_const (4:ℝ) using 1
      norm_num
    have h5 : HasDerivAt (fun u : ℝ => u^5/5) (t^4) t := by
      convert! (hasDerivAt_pow 5 t).div_const (5:ℝ) using 1
      norm_num
    have hpoly : HasDerivAt (fun u : ℝ => u - u^2/2 + u^3/3 - u^4/4 + u^5/5)
        (1 - t + t^2 - t^3 + t^4) t :=
      ((((h1.sub h2).add h3).sub h4).add h5)
    have hlog : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1/(1+t)) t := by
      have hlin : HasDerivAt (fun u : ℝ => 1 + u) 1 t := by
        simpa using (hasDerivAt_id t).const_add 1
      have h := (Real.hasDerivAt_log ht).comp t hlin
      simpa [Function.comp_def] using h
    have h := hpoly.sub hlog
    convert h using 1
    all_goals first | rfl | (field_simp; ring)
  have hcont : ContinuousOn F (Set.Ici 0) := by
    change ContinuousOn (fun u : ℝ =>
      (u - u^2/2 + u^3/3 - u^4/4 + u^5/5) - Real.log (1 + u)) (Set.Ici 0)
    apply ContinuousOn.sub
    · fun_prop
    · apply ContinuousOn.log
      · fun_prop
      · intro u hu
        have : (0:ℝ) ≤ u := hu
        positivity
  have hderiv : ∀ t ∈ interior (Set.Ici (0:ℝ)),
      HasDerivWithinAt F (t^5/(1+t)) (interior (Set.Ici (0:ℝ))) t := by
    intro t ht
    simp only [interior_Ici, Set.mem_Ioi] at ht
    exact (hF t (by linarith)).hasDerivWithinAt
  have hnonneg : ∀ t ∈ interior (Set.Ici (0:ℝ)), 0 ≤ t^5/(1+t) := by
    intro t ht
    simp only [interior_Ici, Set.mem_Ioi] at ht
    positivity
  have hmono : MonotoneOn F (Set.Ici (0:ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ)) hcont hderiv hnonneg
  have h0 : F 0 = 0 := by
    change (0 - 0^2/2 + 0^3/3 - 0^4/4 + 0^5/5) - Real.log (1 + 0) = 0
    norm_num
  have hx : F 0 ≤ F x := hmono (by simp) (by simpa using hx0) hx0
  rw [h0] at hx
  change 0 ≤ (x - x^2/2 + x^3/3 - x^4/4 + x^5/5) - Real.log (1 + x) at hx
  linarith

end Commons.Analysis.SpecialFunctions