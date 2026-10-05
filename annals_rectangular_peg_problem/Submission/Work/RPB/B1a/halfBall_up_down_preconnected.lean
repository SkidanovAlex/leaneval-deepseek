import Mathlib
import Submission.Work.RPB.B1a.HalfBallDefs
import Submission.Work.RPB.B1a.HalfBallRegion
import Submission.Work.RPB.B1a.HalfBallIdent
import Submission.Work.RPB.B1a.shearRegion_preconnected_of_mono
import Submission.Work.RPB.B1a.mono_and_nocap_of_bounds
import Submission.Work.RPB.B1a.bounds_of_lipschitz

/-!
# `Work.RPB.B1a`: the two straightening half-balls are preconnected

For a `C^2` local displacement `g : ℝ → ℂ` of a loop with `g 0 = 0` and `deriv g 0 = w ≠ 0`, the
two straightening half-balls `halfBallUp g w ρ` and `halfBallDn g w ρ` (the two local sides of the
straightening chart at `0`, cut to the ball of radius `2ρ/‖w‖`) are preconnected for all
sufficiently small `ρ`.

The proof is the standard "the region is a small sheared half-disk" argument:

* `hArg g w x = I * g x / w` is a `C^2` parametrisation of the curve `g` seen from the
  straightening chart, and `‖g x + y (I w)‖ = ‖w‖ * ‖y - hArg g w x‖`, so the half-balls are the
  sheared half-disks `shearRegion (hRe g w) (hIm g w) r` (and, for the lower one, the reflection of
  the same with `hRe`, `hIm` negated), `r = ρ / ‖w‖`  (`HalfBallIdent`).
* Because `g` is `C^2`, `deriv g` is Lipschitz near `0` with some constant `K`; hence
  `hRe g w x = O(x^2)` and `hIm g w x = x + O(x^2)` on `|x| ≤ 2r` with room to spare, which makes
  each horizontal section of the sheared half-disk an interval containing the "spine" `x = 0`
  (`mono_and_nocap_of_bounds`, `mono_and_nocap_of_bounds` applied to the negated data).
* The region is then preconnected: every point joins horizontally to the spine
  `{(0,y) : 0 < y < r}`, along which the region is an interval
  (`shearRegion_preconnected_of_mono`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1a

open Complex Set Metric

theorem halfBall_up_down_preconnected (g : ℝ → ℂ) (w : ℂ) (hw : w ≠ 0) (hg0 : g 0 = 0)
    (hgd : HasDerivAt g w 0) (hg : ContDiff ℝ 2 g) :
    ∃ ρ₀, 0 < ρ₀ ∧ ∀ ρ, 0 < ρ → ρ ≤ ρ₀ →
      IsPreconnected (Work.RPB.B1a.halfBallUp g w ρ) ∧
        IsPreconnected (Work.RPB.B1a.halfBallDn g w ρ) := by
  -- `deriv g` is Lipschitz near `0`; enlarge the constant by `1` for room.
  obtain ⟨K, hK, δ, hδ, hLip⟩ := exists_deriv_lipschitz_bound g w hgd hg
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ g x :=
    fun x => (hg.differentiable (by norm_num)).differentiableAt
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hK1pos : (0 : ℝ) < K + 1 := by positivity
  refine ⟨min (δ * ‖w‖ / 2) (‖w‖ ^ 2 / (8 * (K + 1))), ?_, ?_⟩
  · positivity
  · intro ρ hρ hρle
    have hr : 0 < ρ / ‖w‖ := by positivity
    have hMnn : 0 ≤ (K + 1) / ‖w‖ := by positivity
    have hLip' : ∀ x, |x| ≤ δ → ‖deriv g x - w‖ ≤ (K + 1) * |x| := by
      intro x hx
      have h := hLip x hx
      nlinarith [h, abs_nonneg x]
    have h2rδ : 2 * (ρ / ‖w‖) ≤ δ := by
      have h1 : ρ ≤ δ * ‖w‖ / 2 := le_trans hρle (min_le_left _ _)
      rw [← mul_div_assoc, div_le_iff₀ hwpos]
      nlinarith [h1, hwpos]
    have hMr : ((K + 1) / ‖w‖) * (ρ / ‖w‖) ≤ 1 / 8 := by
      have h1 : ρ ≤ ‖w‖ ^ 2 / (8 * (K + 1)) := le_trans hρle (min_le_right _ _)
      have h7 : ((K + 1) / ‖w‖) * (ρ / ‖w‖) = (K + 1) * ρ / ‖w‖ ^ 2 := by
        rw [div_mul_div_comm, pow_two]
      rw [h7, div_le_iff₀ (by positivity : (0 : ℝ) < ‖w‖ ^ 2)]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (K + 1))] at h1
      nlinarith [h1]
    -- the derivative data of the straightening coordinates
    obtain ⟨hP0, hQ0, hbnd⟩ :=
      bounds_of_lipschitz g w hw hg0 hdiff (K := K + 1) (δ := δ) (r := ρ / ‖w‖)
        hK1pos.le hδ hr h2rδ hLip'
    -- the upper half-ball
    have hub := mono_and_nocap_of_bounds (hRe g w) (hIm g w) (hDre g w) (hDim g w)
        (σ := 1) (M := (K + 1) / ‖w‖) (r := ρ / ‖w‖) hr hMnn hMr (Or.inl rfl) hP0 hQ0
        (fun x hx => (hbnd x hx).1) (fun x hx => (hbnd x hx).2.1)
        (fun x hx => (hbnd x hx).2.2.1) (fun x hx => (hbnd x hx).2.2.2)
    have hpre : IsPreconnected (shearRegion (hRe g w) (hIm g w) (ρ / ‖w‖)) :=
      shearRegion_preconnected_of_mono (hRe g w) (hIm g w) hr hP0 hQ0 hub.1 hub.2
    have hup : IsPreconnected (halfBallUp g w ρ) := by
      rw [halfBallUp_eq_shearRegion g w hw hρ]
      exact hpre
    -- the lower half-ball: the same with `hRe`, `hIm` negated
    have hub' := mono_and_nocap_of_bounds (fun x => -hRe g w x) (fun x => -hIm g w x)
        (fun x => -hDre g w x) (fun x => -hDim g w x) (σ := -1) (M := (K + 1) / ‖w‖)
        (r := ρ / ‖w‖) hr hMnn hMr (Or.inr rfl) (by simpa using hP0) (by simpa using hQ0)
        (fun x hx => (hbnd x hx).1.neg) (fun x hx => (hbnd x hx).2.1.neg)
        (fun x hx => by simpa using (hbnd x hx).2.2.1)
        (fun x hx => by
          have h := (hbnd x hx).2.2.2
          have hh : (-hDim g w x - -1) = -(hDim g w x - 1) := by ring
          rw [hh, abs_neg]
          exact h)
    have hpre' : IsPreconnected (shearRegion (fun x => -hRe g w x) (fun x => -hIm g w x)
        (ρ / ‖w‖)) :=
      shearRegion_preconnected_of_mono _ _ hr (by simpa using hP0) (by simpa using hQ0)
        hub'.1 hub'.2
    have hdn : IsPreconnected (halfBallDn g w ρ) := by
      rw [halfBallDn_eq_image_shearRegion g w hw hρ]
      exact hpre'.image _ (by fun_prop)
    exact ⟨hup, hdn⟩

end Work.RPB.B1a
