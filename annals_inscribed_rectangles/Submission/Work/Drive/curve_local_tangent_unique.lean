import Mathlib
import Submission.Work.Drive.rot90

set_option autoImplicit false
noncomputable section

namespace Work.Drive

open Submission.Geometry
open Filter
open scoped Topology

/-- A real function with nonzero derivative at a point does not take the value `f t` again
arbitrarily close to `t`: it is locally injective at `t`. -/
lemma exists_ne_of_hasDerivAt_ne {f : ℝ → ℝ} {c t : ℝ} (h : HasDerivAt f c t) (hc : c ≠ 0) :
    ∃ δ > 0, ∀ s : ℝ, |s - t| < δ → f s = f t → s = t := by
  have ht := h.tendsto_slope
  have hev : ∀ᶠ s in 𝓝[≠] t, slope f t s ≠ 0 := ht.eventually_ne hc
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  refine ⟨δ, hδpos, fun s hs hfs => ?_⟩
  by_contra hst
  refine hδ (by rw [Real.dist_eq]; exact hs) (by simpa using hst) ?_
  rw [slope_def_field, hfs, sub_self, zero_div]

/-- The normal vector `rot90 V` is orthogonal to `V`. -/
lemma eucDot_rot90_self (V : ℝ × ℝ) : eucDot (rot90 V) V = 0 := by
  simp [eucDot, rot90]; ring

/-- The directional derivative of the map `w ↦ eucDot w V` composed with `G`. -/
lemma hasDerivAt_eucDot_comp (G : ℝ → ℝ × ℝ) {V : ℝ × ℝ} (hder : HasDerivAt G V 0) :
    HasDerivAt (fun t => eucDot (G t) V) (V.1 ^ 2 + V.2 ^ 2) 0 := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ :=
    V.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + V.2 • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hLapply : ∀ w : ℝ × ℝ, L w = eucDot w V := by
    intro w; simp [L, eucDot]; ring
  have hcomp : HasFDerivAt (fun t => eucDot (G t) V)
      (L ∘SL ContinuousLinearMap.toSpanSingleton ℝ V) 0 := by
    have h1 := (ContinuousLinearMap.hasFDerivAt L (x := G 0)).comp 0 hder.hasFDerivAt
    simpa only [Function.comp_def, hLapply] using h1
  have h2 := hcomp.hasDerivAt
  have h3 : (L ∘SL ContinuousLinearMap.toSpanSingleton ℝ V) 1 = eucDot V V := by
    rw [ContinuousLinearMap.comp_apply]
    simp [hLapply]
  rw [h3] at h2
  simpa using h2

/-- Local uniqueness: if `G : ℝ → ℝ × ℝ` has nonzero derivative `V` at `0`, then near `0` the curve
`G` meets the normal line `G 0 + span (rot90 V)` only at `t = 0`. -/
theorem curve_local_tangent_unique (G : ℝ → ℝ × ℝ) {V : ℝ × ℝ} (hV : V ≠ 0)
    (hder : HasDerivAt G V 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ t τ : ℝ, |t| < η → G t = G 0 + τ • rot90 V → t = 0 := by
  -- the derivative of `t ↦ ⟪G t, V⟫` at `0` is `‖V‖² ≠ 0`
  have hderiv : HasDerivAt (fun t => eucDot (G t) V) (V.1 ^ 2 + V.2 ^ 2) 0 :=
    hasDerivAt_eucDot_comp G hder
  have hne : V.1 ^ 2 + V.2 ^ 2 ≠ 0 := by
    intro h
    apply hV
    have h1 : V.1 = 0 := by nlinarith [sq_nonneg V.1, sq_nonneg V.2]
    have h2 : V.2 = 0 := by nlinarith [sq_nonneg V.1, sq_nonneg V.2]
    ext <;> assumption
  obtain ⟨η, hηpos, hη⟩ := exists_ne_of_hasDerivAt_ne hderiv hne
  refine ⟨η, hηpos, fun t τ ht hEq => hη t (by simpa using ht) ?_⟩
  -- a point of the normal line has the same `V`-component as `G 0`
  have hnorm : eucDot (G 0 + τ • rot90 V) V = eucDot (G 0) V := by
    rw [eucDot_add_left, eucDot_smul_left, eucDot_rot90_self, mul_zero, add_zero]
  rw [← hnorm, ← hEq]

end Work.Drive
