import Mathlib
import Submission.Work.Sweep.Defs

/-!
# Almost every horizontal level is transverse

For a smooth knot `K`, a point `x` and a radius `R`, the curve is transverse to the
horizontal plane `{y | y 2 = s}` at every intersection point inside the ball `B(x,R)`
for almost every level `s`.

This is Sard's theorem in dimension one: the set of critical values of the coordinate
function `t ↦ (K.curve t) 2` on the (compact) fundamental interval is a null set, so for
almost every `s` a point `t` with `(K.curve t) 2 = s` cannot be a critical point, i.e.
`deriv (fun u => (K.curve u) 2) t ≠ 0`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace Work.Sweep.AeTransverseCoord

theorem ae_transverse_coord (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (x : LeanEval.KnotTheory.PardonDistortion.R3) (R : ℝ) :
    ∀ᵐ s ∂MeasureTheory.volume, Work.Sweep.IsTransverseCoord K x R s := by
  -- The third coordinate function of the curve.
  set g : ℝ → ℝ := fun u => (K.curve u) 2 with hgdef
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    have h : ContDiff ℝ (⊤ : ℕ∞)
        (fun u : ℝ => (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2) (K.curve u)) :=
      ContDiff.continuousLinearMap_comp _ K.smooth
    simpa [g] using h
  have hgd : ∀ t, HasDerivAt g (deriv g t) t := fun t =>
    (hg.differentiable (by simp)).differentiableAt.hasDerivAt
  -- Sard: the image of the critical set of `g` is a null set.
  have hnull : volume (g '' {t | deriv g t = 0}) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
      (f' := fun t => ContinuousLinearMap.toSpanSingleton ℝ (deriv g t)) ?_ ?_
    · intro t _
      exact (hgd t).hasFDerivAt.hasFDerivWithinAt
    · intro t ht
      rw [ht, ContinuousLinearMap.det_toSpanSingleton]
  have hae : ∀ᵐ s ∂volume, s ∉ g '' {t | deriv g t = 0} := by
    rw [MeasureTheory.ae_iff]
    convert hnull using 3
    ext a
    simp [Set.mem_image, eq_comm]
  filter_upwards [hae] with s hs t ht hzero
  exact hs ⟨t, hzero, by simpa [g] using ht.1.2⟩

end Work.Sweep.AeTransverseCoord
