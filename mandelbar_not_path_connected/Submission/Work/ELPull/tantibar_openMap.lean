/-
# The antiholomorphic quadratic map `Tantibar c` is an open map

The one piece of plane topology that the "pull-back side" argument
(`Work.ELPull.side_image_eq`, `Work.ELPull.image_arcSide_of_pullback`) needs beyond the
closedness of the pair curve: the *image of an open set is open*.

`Tantibar c(z) = conj z ^ 2 + c` is the composition of the conjugation `conj` (a homeomorphism),
the squaring map `z ↦ z ^ 2` and the translation `z ↦ z + c`, so it suffices to know that the
square map on `ℂ` is open.  Mathlib has this for the linear equivalences (`conj`) and for
translations (`isOpenMap_add_right`), but not for `z ↦ z ^ 2`; the proof below is the explicit
elementary one:

* given `z₀` and `ε > 0`, every `w` with `‖w - z₀ ^ 2‖ < ε ^ 2` has a square root `v` with
  `‖v - z₀‖ < ε`.  Indeed, if `v ^ 2 = w` then
  `‖v - z₀‖ * ‖v + z₀‖ = ‖v ^ 2 - z₀ ^ 2‖ = ‖w - z₀ ^ 2‖ < ε ^ 2`, and replacing `v` by `-v`
  if necessary makes `‖v - z₀‖` the smaller of the two factors, so `‖v - z₀‖ ^ 2 ≤ ‖w - z₀ ^ 2‖`
  and hence `‖v - z₀‖ < ε`.

Consequently the square map sends the ball of radius `ε` about `z₀` onto a set containing the
ball of radius `ε ^ 2` about `z₀ ^ 2`: it is open.  (No use of the critical point: the estimate
is uniform in `z₀`.)
-/
import Mathlib
import Submission.Work.ELPull.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set Function Filter
open scoped Topology

namespace Work.ELPull

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The square map on `ℂ` is open**: the ball of radius `ε` around `z₀` is mapped onto a set
containing the ball of radius `ε ^ 2` around `z₀ ^ 2`. -/
theorem isOpenMap_sq : IsOpenMap (fun z : ℂ => z ^ 2) := by
  intro U hU
  rw [Metric.isOpen_iff] at hU ⊢
  rintro w ⟨z₀, hz₀, rfl⟩
  obtain ⟨ε, hε, hball⟩ := hU z₀ hz₀
  refine ⟨ε ^ 2, pow_pos hε 2, fun w hw => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hw
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_eq_mul_self w
  have hvv : v ^ 2 = w := by rw [pow_two, hv]
  have hfac : ‖v - z₀‖ * ‖v + z₀‖ = ‖w - z₀ ^ 2‖ := by
    rw [← hvv]
    have : v ^ 2 - z₀ ^ 2 = (v - z₀) * (v + z₀) := by ring
    rw [this, norm_mul]
  rcases le_total ‖v - z₀‖ ‖v + z₀‖ with hle | hle
  · refine ⟨v, hball ?_, hvv⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖v - z₀‖ ^ 2 ≤ ‖v - z₀‖ * ‖v + z₀‖ := by
      nlinarith [norm_nonneg (v - z₀)]
    rw [hfac] at h1
    nlinarith [norm_nonneg (v - z₀)]
  · refine ⟨-v, hball ?_, by show (-v) ^ 2 = w; rw [pow_two, neg_mul_neg, ← pow_two, hvv]⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hneg : ‖-v - z₀‖ = ‖v + z₀‖ := by
      rw [show -v - z₀ = -(v + z₀) by ring, norm_neg]
    rw [hneg]
    have h1 : ‖v + z₀‖ ^ 2 ≤ ‖v - z₀‖ * ‖v + z₀‖ := by
      nlinarith [norm_nonneg (v + z₀)]
    rw [hfac] at h1
    nlinarith [norm_nonneg (v + z₀)]

/-- The conjugation `conj` is an open map, being a homeomorphism of `ℂ`. -/
theorem isOpenMap_conj : IsOpenMap (fun z : ℂ => starRingEnd ℂ z) :=
  ContinuousLinearEquiv.isOpenMap Complex.conjCLE

/-- **`Tantibar c` is an open map.**  It is the composition of the conjugation, the square map
and the translation `z ↦ z + c`, all of which are open. -/
theorem isOpenMap_Tantibar (c : ℂ) : IsOpenMap (Tantibar c) := by
  have hfun : Tantibar c
      = (fun z : ℂ => z + c) ∘ (fun z : ℂ => z ^ 2) ∘ (fun z : ℂ => starRingEnd ℂ z) := by
    funext z
    simp only [Tantibar, Function.comp_apply]
  rw [hfun]
  exact (isOpenMap_add_right c).comp (isOpenMap_sq.comp isOpenMap_conj)

end Work.ELPull
