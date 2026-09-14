import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus

open Set Filter in
lemma rpow_neg_third_deriv_le_implies_lower_bound {g : ℝ → ℝ} {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 ≤ c)
    (hcont : ContinuousOn g (Icc a b))
    (hdiff : DifferentiableOn ℝ g (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, deriv g x ≤ c * x ^ (-(1:ℝ)/3)) :
    g b - (3 * c / 2) * b ^ ((2:ℝ)/3) ≤ g a := by
  -- Consider `F x = g x - (3c/2) x^(2/3)`, whose derivative `g' - c x^(-1/3)` is `≤ 0`.
  set F : ℝ → ℝ := fun x => g x - (3 * c / 2) * x ^ ((2:ℝ)/3) with hF
  have hcontF : ContinuousOn F (Icc a b) := by
    rw [hF]
    exact hcont.sub ((continuousOn_id.rpow_const (fun x _ => Or.inr (by norm_num))).const_mul _)
  have hdiffF : DifferentiableOn ℝ F (Ioo a b) := by
    rw [hF]
    refine hdiff.sub ?_
    have hsub : Ioo a b ⊆ ({0}ᶜ : Set ℝ) := fun x hx =>
      ne_of_gt (lt_of_lt_of_le ha (le_of_lt hx.1))
    exact ((Real.differentiableOn_rpow_const ((2:ℝ)/3)).mono hsub).const_mul _
  have hderivF : ∀ x ∈ interior (Icc a b), deriv F x ≤ 0 := by
    intro x hx
    rw [interior_Icc] at hx
    have hxne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha (le_of_lt hx.1))
    have hdg : DifferentiableAt ℝ g x := (hdiff x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
    have h1 : HasDerivAt (fun y : ℝ => y ^ ((2:ℝ)/3)) (((2:ℝ)/3) * x ^ ((2:ℝ)/3 - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hxne)
    have h3 := hdg.hasDerivAt.sub (h1.const_mul ((3 * c) / 2))
    have key : deriv (g - fun y : ℝ => (3 * c / 2) * y ^ ((2:ℝ)/3)) x =
        deriv g x - (3 * c / 2) * (((2:ℝ)/3) * x ^ ((2:ℝ)/3 - 1)) := h3.deriv
    have hfun : (fun z : ℝ => g z - (3 * c / 2) * z ^ ((2:ℝ)/3)) =
        (g - fun y : ℝ => (3 * c / 2) * y ^ ((2:ℝ)/3)) := by
      funext z; rfl
    have hdF : deriv F x = deriv g x - c * x ^ (-(1:ℝ)/3) := by
      rw [hF, hfun, key, show (2:ℝ)/3 - 1 = -(1:ℝ)/3 by norm_num]
      ring
    rw [hdF]
    have h := hderiv x hx
    linarith
  have hanti :=
    antitoneOn_of_deriv_nonpos (convex_Icc a b) hcontF (by rw [interior_Icc]; exact hdiffF) hderivF
  have hba : F b ≤ F a := hanti (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  rw [hF] at hba
  have hnonneg : 0 ≤ (3 * c / 2) * a ^ ((2:ℝ)/3) := by
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt ha) _)
  linarith

end Commons.Analysis.Calculus