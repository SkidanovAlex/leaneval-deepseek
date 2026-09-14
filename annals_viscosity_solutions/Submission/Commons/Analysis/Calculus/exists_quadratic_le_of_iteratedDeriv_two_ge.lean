import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology

open Filter Set
open scoped Topology

namespace Commons.Analysis.Calculus

/-- If `0 < h` then the quadratic `h * x^2 + a * x + b` is nonnegative for all sufficiently
large `x`. -/
private lemma exists_quadratic_nonneg {h a b : ℝ} (hh : 0 < h) :
    ∃ N : ℝ, ∀ x : ℝ, N ≤ x → 0 ≤ h * x ^ 2 + a * x + b := by
  refine ⟨max 1 ((|a| + |b|) / h), fun x hx => ?_⟩
  have hx1 : (1:ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (|a| + |b|) / h ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hxh : |a| + |b| ≤ h * x := by
    rw [div_le_iff₀ hh] at hx2; linarith
  have hkey : (|a| + |b|) * x ≤ h * x ^ 2 := by
    calc (|a| + |b|) * x ≤ (h * x) * x :=
            mul_le_mul_of_nonneg_right hxh hxpos.le
      _ = h * x ^ 2 := by ring
  have hax : -( |a| * x ) ≤ a * x := by
    have h := mul_le_mul_of_nonneg_right (neg_abs_le a) hxpos.le
    nlinarith [h]
  have hb : -|b| ≤ b := neg_abs_le b
  nlinarith [hkey, hax, hb, abs_nonneg b, hx1]

/-- The derivative of `y ↦ c * y^2`. -/
private lemma hasDerivAt_const_mul_sq {c x : ℝ} :
    HasDerivAt (fun y : ℝ => c * y^2) (2*c*x) x := by
  have h : HasDerivAt (fun y : ℝ => c * y^2) (c * (2 * x)) x := by
    have h0 := (hasDerivAt_pow 2 x).const_mul c
    simp only [Nat.reduceSub, pow_one] at h0
    exact h0
  convert h using 1
  ring

/-- If `f` is `C²` on `(0,∞)` with `f'' ≥ 4h` there and `h > 0`, then `f` dominates the
quadratic `h * t^2` for all sufficiently large `t`. -/
theorem exists_quadratic_le_of_iteratedDeriv_two_ge {f : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hf : ContDiffOn ℝ 2 f (Set.Ioi (0 : ℝ)))
    (h2 : ∀ t ∈ Set.Ioi (0 : ℝ), 4 * h ≤ iteratedDeriv 2 f t) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → h * t ^ 2 ≤ f t := by
  have h2fun : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h2' : ∀ t ∈ Set.Ioi (0:ℝ), 4 * h ≤ deriv (deriv f) t := by
    intro t ht; simpa [h2fun] using h2 t ht
  -- `deriv f` is `C¹` (hence continuous and differentiable) on `(0,∞)`
  have hdf : ContDiffOn ℝ 1 (deriv f) (Set.Ioi (0:ℝ)) :=
    hf.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdf_diff : DifferentiableOn ℝ (deriv f) (Set.Ioi (0:ℝ)) := hdf.differentiableOn_one
  have hdf_cont : ContinuousOn (deriv f) (Set.Ioi (0:ℝ)) := hdf.continuousOn
  -- Step 1: `u x = (deriv f) x - 4 h x` is monotone on `[1,∞)`
  have hu_cont : ContinuousOn (fun y : ℝ => deriv f y - 4 * h * y) (Set.Ici 1) := by
    apply ContinuousOn.sub
    · exact hdf_cont.mono (fun x hx => show (0:ℝ) < x from lt_of_lt_of_le zero_lt_one hx)
    · exact (continuous_const.mul continuous_id).continuousOn
  have hu_mono : MonotoneOn (fun y : ℝ => deriv f y - 4*h*y) (Set.Ici (1:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1) hu_cont
    · rw [interior_Ici]
      apply DifferentiableOn.sub
      · exact hdf_diff.mono (fun x hx => show (0:ℝ) < x from lt_trans zero_lt_one hx)
      · exact (differentiable_id.const_mul (4*h)).differentiableOn
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
      have hdf_at : DifferentiableAt ℝ (deriv f) x :=
        hdf_diff.differentiableAt (isOpen_Ioi.mem_nhds hx0)
      have h1 : HasDerivAt (deriv f) (deriv (deriv f) x) x := hdf_at.hasDerivAt
      have h2lin : HasDerivAt (fun y : ℝ => 4 * h * y) (4 * h) x := by
        have hh2 := (hasDerivAt_id x).const_mul (4*h)
        simpa using hh2
      have hsub : HasDerivAt (fun y : ℝ => deriv f y - 4*h*y) (deriv (deriv f) x - 4*h) x :=
        h1.sub h2lin
      rw [hsub.deriv]
      linarith [h2' x hx0]
  have hu1_le : ∀ x, 1 ≤ x → deriv f 1 - 4*h ≤ deriv f x - 4*h*x := by
    intro x hx
    have hm := hu_mono (le_refl (1:ℝ)) hx hx
    simpa using hm
  -- Step 2: apply the MVT comparison to `ψ x = f x - 2 h x^2`
  have hψ_cont : ContinuousOn (fun y : ℝ => f y - 2*h*y^2) (Set.Ici 1) := by
    apply ContinuousOn.sub
    · exact hf.continuousOn.mono (fun x hx => show (0:ℝ) < x from lt_of_lt_of_le zero_lt_one hx)
    · exact (continuous_const.mul (continuous_id.pow 2)).continuousOn
  have hψ_diff : DifferentiableOn ℝ (fun y : ℝ => f y - 2*h*y^2) (Set.Ioi 1) := by
    apply DifferentiableOn.sub
    · exact (hf.differentiableOn (by norm_num)).mono (fun x hx => show (0:ℝ) < x from lt_trans zero_lt_one hx)
    · exact (differentiable_id.pow 2).const_mul (2*h) |>.differentiableOn
  have hψ_deriv : ∀ y ∈ Set.Ioi (1:ℝ),
      deriv (fun z : ℝ => f z - 2*h*z^2) y = deriv f y - 4*h*y := by
    intro y hy
    have hy0 : (0:ℝ) < y := lt_trans zero_lt_one hy
    have hf_at : DifferentiableAt ℝ f y :=
      (hf.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hy0)
    have h1 : HasDerivAt f (deriv f y) y := hf_at.hasDerivAt
    have h2sq : HasDerivAt (fun z : ℝ => 2*h*z^2) (2*(2*h)*y) y :=
      hasDerivAt_const_mul_sq (c := 2*h) (x := y)
    have hsub : HasDerivAt (fun z : ℝ => f z - 2*h*z^2) (deriv f y - 2*(2*h)*y) y :=
      h1.sub h2sq
    rw [hsub.deriv]; ring
  have hψ_bound : ∀ x, 1 ≤ x →
      (deriv f 1 - 4*h) * (x - 1) ≤ (f x - 2*h*x^2) - (f 1 - 2*h) := by
    intro x hx
    have hC : ∀ y ∈ interior (Set.Ici (1:ℝ)),
        deriv f 1 - 4*h ≤ deriv (fun z : ℝ => f z - 2*h*z^2) y := by
      intro y hy
      rw [interior_Ici] at hy
      rw [hψ_deriv y hy]
      exact hu1_le y (le_of_lt hy)
    have hdiff' : DifferentiableOn ℝ (fun z : ℝ => f z - 2*h*z^2) (interior (Set.Ici (1:ℝ))) := by
      rw [interior_Ici]; exact hψ_diff
    have h := (convex_Ici (1:ℝ)).mul_sub_le_image_sub_of_le_deriv hψ_cont hdiff' hC (1:ℝ)
      (by simp : (1:ℝ) ∈ Set.Ici 1) x hx hx
    simpa using h
  -- Step 3: the resulting quadratic lower bound grows without bound
  obtain ⟨N, hN⟩ := exists_quadratic_nonneg (h := h) (a := deriv f 1 - 4*h)
    (b := f 1 - 2*h - (deriv f 1 - 4*h)) hh
  refine ⟨max N 1, fun t ht => ?_⟩
  have ht1 : (1:ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have htN : N ≤ t := le_trans (le_max_left _ _) ht
  have hb := hψ_bound t ht1
  have hq := hN t htN
  linarith

end Commons.Analysis.Calculus