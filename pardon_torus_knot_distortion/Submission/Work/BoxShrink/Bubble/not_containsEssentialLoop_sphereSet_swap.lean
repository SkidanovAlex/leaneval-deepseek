import Mathlib
import Submission.Work.BoxShrink.Bubble.standard_counterexample

/-!
# No essential loop on the box sphere, for every `s ≥ 5/2`

`Submission/Work/BoxShrink/Bubble/standard_counterexample.lean` proves
`¬ standard.ContainsEssentialLoop (sphereSet 0 (swap 1 2) (5/2))`: the box sphere at the critical
size `5/2` carries no essential loop of the standard torus, because a point of the torus on that
sphere has `|x| = 5/2`, which forces both angle parameters of any lift to avoid the zeros of `cos`.

The present file removes the restriction `s = 5/2`.  The point is that the `y`- and `z`-coordinates
of a point of the standard torus are *automatically* inside the box of size `5/2`
(`cex_coord_one_lt`, `cex_coord_two_lt`), so for a point of the torus with box norm `s ≥ 5/2` the
box norm is attained by the `x`-coordinate: `|x| = s`.  In particular `|x| ≥ 5/2` still holds, and
the winding argument goes through verbatim.  This is what makes Pardon's sphere count usable for
every box that contains the critical one.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

/-- **The `x`-coordinate of a point of the standard torus dominates its box norm, as soon as the
latter is at least `5/2`.**  Indeed the `y`- and `z`-contributions to the box norm are always
`< 5/2` on the standard torus, so a box norm `s ≥ 5/2` can only be attained by `|x|` (and then
`|x| = s ≥ 5/2`). -/
lemma cex_fst_ge_of_boxNorm_eq {y : R3} (hy : y ∈ Work.CoreTopology.standard.carrier)
    {s : ℝ} (hs : 5 / 2 ≤ s)
    (h : Submission.boxNorm 0 (Equiv.swap (1 : Fin 3) 2) y = s) : 5 / 2 ≤ |y 0| := by
  obtain ⟨θ, φ, hθφ⟩ :=
    (Work.CoreTopology.ParamTorus.mem_carrier_iff Work.CoreTopology.standard y).mp hy
  rw [← hθφ] at h ⊢
  simp only [Work.CoreTopology.standard_psi] at h ⊢
  rw [cex_boxNorm] at h
  have h2 := cex_coord_two_lt θ φ
  have h1 := cex_coord_one_lt θ φ
  by_contra hc
  push Not at hc
  have hlt : max (max |(Work.Core.torusMap θ φ) 0|
      (|(Work.Core.torusMap θ φ) 2| / (2 : ℝ) ^ (1 / 3 : ℝ)))
      (|(Work.Core.torusMap θ φ) 1| / (2 : ℝ) ^ (2 / 3 : ℝ)) < 5 / 2 :=
    max_lt (max_lt hc h2) h1
  rw [h] at hlt
  linarith

/-- **No essential loop of the standard torus lies on the box sphere** `∂PBox s 0 (swap 1 2)` for
every `s ≥ 5/2`.

Every point of the torus on the sphere has `|x| ≥ 5/2` (`cex_fst_ge_of_boxNorm_eq`), i.e.
`|2 + cos Φ| · |cos Θ| ≥ 5/2`; as `|cos Θ| ≤ 1` this gives `2 + cos Φ ≥ 5/2`, so `cos Φ > 0`, and
`s = 0` in particular forces `cos Θ ≠ 0`.  Hence along a lift of any loop of the sphere both angle
parameters are confined to intervals of length `π` (the components of `{cos ≠ 0}`), so both winding
coordinates vanish and the loop is inessential. -/
theorem not_containsEssentialLoop_sphereSet_swap (s : ℝ) (hs : 5 / 2 ≤ s) :
    ¬ Work.CoreTopology.standard.ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet 0 (Equiv.swap (1 : Fin 3) 2) s) := by
  rintro ⟨γ, hess, hmem⟩
  obtain ⟨L, hL⟩ := hess
  have hcoord0 : ∀ t : ℝ, (γ.γ t) 0 = (2 + Real.cos (L.Φ t)) * Real.cos (L.Θ t) := by
    intro t
    have hl := congrArg (fun u : R3 => u 0) (L.lifts t)
    simpa only [Work.CoreTopology.standard_psi, Work.CoreTopology.torusMap_apply_zero] using hl.symm
  have hfst : ∀ t : ℝ, 5 / 2 ≤ |(γ.γ t) 0| := fun t =>
    cex_fst_ge_of_boxNorm_eq (γ.mem t) hs (Work.BoxShrink.Core.mem_sphereSet.mp (hmem t))
  have hcosΘ : ∀ t : ℝ, Real.cos (L.Θ t) ≠ 0 := by
    intro t hc
    have h0 := hfst t
    rw [hcoord0 t, hc, mul_zero, abs_zero] at h0
    linarith
  have hcosΦ : ∀ t : ℝ, Real.cos (L.Φ t) ≠ 0 := by
    intro t
    have h0 := hfst t
    rw [hcoord0 t, abs_mul] at h0
    have hle : |Real.cos (L.Θ t)| ≤ 1 := Real.abs_cos_le_one _
    have hge : 5 / 2 ≤ |2 + Real.cos (L.Φ t)| :=
      le_trans h0 (mul_le_of_le_one_right (abs_nonneg _) hle)
    have hpos : (0 : ℝ) < 2 + Real.cos (L.Φ t) := by linarith [Real.neg_one_le_cos (L.Φ t)]
    rw [abs_of_pos hpos] at hge
    linarith
  have hΘ := cex_abs_sub_lt_pi_of_cos_ne_zero L.contΘ hcosΘ
  have hΦ := cex_abs_sub_lt_pi_of_cos_ne_zero L.contΦ hcosΦ
  have hw1 : (L.winding).1 = 0 := by
    apply cex_int_eq_zero_of_abs_mul_two_pi_lt (b := Real.pi) (by linarith [Real.pi_pos])
    have hb := hΘ 0 (2 * Real.pi)
    rw [L.winding_spec.1, add_sub_cancel_left] at hb
    exact hb
  have hw2 : (L.winding).2 = 0 := by
    apply cex_int_eq_zero_of_abs_mul_two_pi_lt (b := Real.pi) (by linarith [Real.pi_pos])
    have hb := hΦ 0 (2 * Real.pi)
    rw [L.winding_spec.2, add_sub_cancel_left] at hb
    exact hb
  exact hL (Prod.ext hw1 hw2)

end

end Work.BoxShrink.Bubble
