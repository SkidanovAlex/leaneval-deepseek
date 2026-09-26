import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteNC.Config

/-!
# The slice of the `nc` configuration carries no essential loop

The configuration of `RefuteNC/Config.lean` is the standard torus of revolution (`ψ = idDiffeo`,
whose surface is the standard torus definitionally), the box
`PBox ncRad ncCtr ncCyc3` (`ncRad = 1`, `ncCtr = (1, 19/10, 0)`, `ncCyc3 = (0 1 2)`) and the
cutting plane `{x = 1/2}` (`ncU = -1/2`).

In the parameter plane `(θ, φ)` of the standard torus the slice `Σ` is the set of points with

* `(2 + cos φ) cos θ = 1/2` (the plane `{x = 1/2}`), and
* `|(2 + cos φ) sin θ - 19/10| < 1` (the `y₁`-window of the box; the `z`- and `x`-windows of the
  box are automatic at these points).

Geometrically `Σ` is a union of two open arcs — the trace of the plane `{x = 1/2}` on the torus,
cut by the box — and this module proves that it carries no essential loop.

## The two confinements

Write `A = 2 + cos φ`.  The plane equation gives `A cos θ = 1/2`, so `cos θ = 1/(2A)`, and since
`1 ≤ A ≤ 3` this is positive: **`cos θ > 0`**.  The box window gives `A sin θ ∈ (9/10, 29/10)`,
and therefore

  `A² = (A cos θ)² + (A sin θ)² = 1/4 + (A sin θ)² > 1/4 + 81/100 = 1.06 > (1.02)²`,

so `A > 1.02` and **`cos φ = A - 2 > -0.98`**.

## The winding argument

A lift `L` of a loop of `Σ` therefore has `cos (L.Θ ·) > 0` everywhere, so `L.Θ` is confined to
an interval of length `π < 2π` over a period
(`Work.BoxShrink.PinchOff.int_eq_zero_of_cos_gt`), forcing `(L.winding).1 = 0`; and it has
`cos (L.Φ ·) > -0.98`, so `L.Φ` avoids the interval `[2.95, 2π - 2.95]` modulo `2π` — a fact which
is exactly the containment `cos ψ ≤ -0.98` on that interval, proved from the Taylor bound
`1 - x²/2 ≤ cos x` (`Real.one_sub_sq_div_two_le_cos`) together with `π < 3.15`.  The avoidance of
an interval of length `5.9` confines `L.Φ` over a period to an interval of length `2π - 5.9 < 2π`
(`Work.BoxShrink.Bubble.cex_abs_sub_lt_of_forall_notMem_Icc`), forcing `(L.winding).2 = 0`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteNC

noncomputable section

/-! ## The shape of the slice in the parameter plane -/

/-- **The shape lemma for the slice of the `nc` configuration.**  A point `torusMap u v` of the
slice satisfies `0 < cos u` (the plane `{x = 1/2}` cuts the torus at the parameter
`cos u = 1/(2 (2 + cos v)) ≥ 1/6`) and `-0.98 < cos v` (the `y₁`-window of the box forces
`2 + cos v > 1.02`). -/
theorem nc_slice_shape {u v : ℝ}
    (h : Work.Core.torusMap u v ∈ Work.BoxShrink.Core.sliceRegion Work.CoreTopology.standard
      Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
      Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU) :
    0 < Real.cos u ∧ (-0.98 : ℝ) < Real.cos v := by
  obtain ⟨-, hbox, hplane⟩ := (Work.BoxShrink.Core.mem_sliceRegion).mp h
  -- the plane equation `(2 + cos v) cos u = 1/2`
  have hplane' : (2 + Real.cos v) * Real.cos u = 1 / 2 := by
    have h := hplane
    rw [Work.BoxShrink.PinchOff.ncCyc3_two, Work.BoxShrink.PinchOff.ncCtr_zero,
      Work.BoxShrink.PinchOff.ncU_eq] at h
    norm_num at h
    exact h
  -- the `y₁`-window of the box: `|(2 + cos v) sin u - 19/10| < 1`
  have hbox1 : |(2 + Real.cos v) * Real.sin u - 19 / 10| < 1 := by
    have h := (Work.BoxShrink.PinchOff.mem_PBox_nc (Work.Core.torusMap u v)).mp hbox
    exact h.1
  have hApos : 0 < 2 + Real.cos v := by linarith [Real.neg_one_le_cos v]
  have hcosu : 0 < Real.cos u := by
    by_contra hc
    push Not at hc
    nlinarith [hplane', hApos]
  refine ⟨hcosu, ?_⟩
  have hY : 9 / 10 < (2 + Real.cos v) * Real.sin u := by
    rw [abs_lt] at hbox1
    linarith [hbox1.1]
  -- `(2 + cos v)² = 1/4 + ((2 + cos v) sin u)²`
  have hkey : (2 + Real.cos v) ^ 2 = 1 / 4 + ((2 + Real.cos v) * Real.sin u) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq u, hplane', sq_nonneg (2 + Real.cos v)]
  have hbig : 1.06 < (2 + Real.cos v) ^ 2 := by
    nlinarith [hkey, hY]
  have hA : 1.02 < 2 + Real.cos v := by
    by_contra hc
    push Not at hc
    nlinarith [hApos, hbig, hc]
  linarith

/-! ## The numerical confinement of the meridian coordinate -/

/-- **On the arc `[2.95, 2π - 2.95]` the cosine is below `-0.98`.**  The arc is symmetric about
`π` and of half-length `π - 2.95 < 0.2`, so for `ψ` in it the distance `x = |ψ - π|` is `< 0.2`,
whence `cos ψ = -cos x ≤ -(1 - x²/2) < -0.98`. -/
theorem cos_lt_of_mem_Icc_2_95 {ψ : ℝ}
    (h1 : 2.95 ≤ ψ) (h2 : ψ ≤ 2 * Real.pi - 2.95) : Real.cos ψ < -0.98 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  -- `x = |ψ - π| < 0.2`
  have hx : |ψ - Real.pi| < 0.2 := by
    rw [abs_lt]
    constructor
    · linarith
    · linarith
  have hxnn : 0 ≤ |ψ - Real.pi| := abs_nonneg _
  -- `cos ψ = -cos |ψ - π|`
  have hcos : Real.cos ψ = -Real.cos |ψ - Real.pi| := by
    have hsub : Real.cos ψ = -Real.cos (Real.pi - ψ) := by
      conv_lhs => rw [show ψ = Real.pi - (Real.pi - ψ) by ring]
      rw [Real.cos_pi_sub]
    have habs : Real.cos |ψ - Real.pi| = Real.cos (Real.pi - ψ) := by
      rw [Real.cos_abs]
      conv_lhs => rw [show ψ - Real.pi = -(Real.pi - ψ) by ring]
      rw [Real.cos_neg]
    rw [hsub, ← habs]
  have hsq : |ψ - Real.pi| ^ 2 / 2 < 0.02 := by
    nlinarith [hxnn, hx]
  have hcos98 : 0.98 < Real.cos |ψ - Real.pi| := by
    have := Real.one_sub_sq_div_two_le_cos (x := |ψ - Real.pi|)
    linarith
  linarith [hcos, hcos98]

/-! ## The slice is inessential -/

/-- **The slice of the `nc` configuration carries no essential loop.** -/
theorem slice_inessential_nc :
    ¬ (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo).ContainsEssentialLoop
      (Work.BoxShrink.PinchOff.Sigma Work.BoxShrink.PinchOff.idDiffeo
        Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
        Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU) := by
  rw [Work.BoxShrink.PinchOff.surface_idDiffeo_eq_standard]
  rintro ⟨γ, ⟨L, hL⟩, hγ⟩
  -- the two confinements along the lift
  have hshape : ∀ t : ℝ, 0 < Real.cos (L.Θ t) ∧ (-0.98 : ℝ) < Real.cos (L.Φ t) := by
    intro t
    have hmem : Work.Core.torusMap (L.Θ t) (L.Φ t) ∈
        Work.BoxShrink.Core.sliceRegion Work.CoreTopology.standard
          Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
          Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU := by
      have h := hγ t
      rwa [← L.lifts t] at h
    exact nc_slice_shape hmem
  -- the longitude parameter is confined to an interval of length `π`
  have h1 : (L.winding).1 = 0 := by
    apply Work.BoxShrink.PinchOff.int_eq_zero_of_cos_gt (c := 0) (m := (L.winding).1) L.contΘ
      (by norm_num) (by norm_num) (fun t => (hshape t).1)
    linarith [L.winding_spec.1]
  -- the meridian parameter avoids `[2.95, 2π - 2.95]` modulo `2π`
  have h2 : (L.winding).2 = 0 := by
    have hbd : |L.Φ (2 * Real.pi) - L.Φ 0| < 5.9 := by
      have h := Work.BoxShrink.Bubble.cex_abs_sub_lt_of_forall_notMem_Icc (f := L.Φ) L.contΦ
        (L := 2 * Real.pi) (a := 2.95) (b := 2 * Real.pi - 2.95)
        (by positivity) (by linarith [Real.pi_gt_d2]) (by linarith [Real.pi_pos])
        (fun t k hmem => by
          have hle1 : 2.95 ≤ L.Φ t - (k : ℝ) * (2 * Real.pi) := by linarith [hmem.1]
          have hle2 : L.Φ t - (k : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi - 2.95 := by
            linarith [hmem.2]
          have hc := cos_lt_of_mem_Icc_2_95 hle1 hle2
          rw [Real.cos_sub_int_mul_two_pi] at hc
          linarith [(hshape t).2, hc]) 0 (2 * Real.pi)
      linarith [h]
    have hw : |(((L.winding).2 : ℤ) : ℝ) * (2 * Real.pi)| < 5.9 := by
      have hspec : L.Φ (2 * Real.pi) - L.Φ 0 = ((L.winding).2 : ℝ) * (2 * Real.pi) := by
        linarith [L.winding_spec.2]
      rw [← hspec]
      exact hbd
    exact Work.BoxShrink.Bubble.cex_int_eq_zero_of_abs_mul_two_pi_lt
      (b := 5.9) (by linarith [Real.pi_gt_d2]) hw
  exact hL (Prod.ext h1 h2)

end

end Work.BoxShrink.PinchOff.RefuteNC
