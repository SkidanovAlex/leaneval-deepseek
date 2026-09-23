import Mathlib

namespace Work.OddBound.mountainPass

open scoped Topology

/-- **Strict sublevel points accumulate at a critical point whose Hessian is negative definite on
a plane.**  Let `f : E → ℝ` be `C²` on a finite-dimensional real inner product space, let `z` be a
critical point of `f` (`fderiv ℝ f z = 0`) with value `Λ`, and suppose the second derivative of `f`
at `z` is *strictly negative* on the whole plane spanned by two vectors `v`, `w`
(if moreover `v`, `w` were linearly independent this would say that the Hessian has index at
least two).  Then every neighbourhood of `z` contains a point at which `f` is strictly below `Λ`.

The proof restricts `f` to the line `t ↦ z + t • v` in the direction of the negative plane.  The
second-order Taylor expansion of `f` along this line (Mathlib's
`Convex.taylor_approx_two_segment`, applied with `v := 0` and `w := v` on `s = univ`) reads
`f (z + t • v) = f z + (t²/2) • (D²f z) v v + o(t²)`; since `(D²f z) v v < 0` and `o(t²)` is
controlled, `f (z + t • v) < f z = Λ` for all small enough `t > 0`. -/
theorem exists_sublevel_near_of_negDefPlane
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {Λ : ℝ} {z : E} (hz : f z = Λ)
    (hcz : fderiv ℝ f z = 0)
    (hbad : ∃ v w : E, ∀ c d : ℝ, (c, d) ≠ 0 →
      (fderiv ℝ (fderiv ℝ f) z) (c • v + d • w) (c • v + d • w) < 0) :
    ∀ ρ > 0, ∃ x : E, dist x z < ρ ∧ f x < Λ := by
  intro ρ hρ
  obtain ⟨v, w, hvw⟩ := hbad
  -- the second derivative of `f` at `z` is negative in the direction `v`
  have hv : ((fderiv ℝ (fderiv ℝ f) z) v) v < 0 := by
    have h := hvw 1 0 (by norm_num)
    simpa using h
  -- second order Taylor expansion of `f` along the line `t ↦ z + t • v`
  have hmain : (fun h : ℝ =>
        f (z + h • v) - f z - (h^2/2) • (((fderiv ℝ (fderiv ℝ f) z) v) v)) =o[𝓝[>] 0]
      (fun h : ℝ => h^2) := by
    have h := Convex.taylor_approx_two_segment (s := Set.univ) (f := f) (f' := fderiv ℝ f)
      (f'' := fderiv ℝ (fderiv ℝ f) z) (x := z) (v := 0) (w := v) convex_univ
      (fun _ _ => (((hf.differentiable (by norm_num)).differentiableAt)).hasFDerivAt)
      trivial
      (((((hf.fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num)).differentiableAt))).hasFDerivAt.hasFDerivWithinAt
      (by simp) (by simp)
    simpa [hcz] using h
  -- the same expansion with `f z` replaced by `Λ`
  let L : ℝ → ℝ := fun h => f (z + h • v) - Λ - (h^2/2) • (((fderiv ℝ (fderiv ℝ f) z) v) v)
  have hL : L =o[𝓝[>] 0] (fun h : ℝ => h^2) := by
    simpa [L, hz] using hmain
  -- with `κ = - (D²f z) v v > 0` we get `‖L h‖ ≤ (κ/4) h²` for small `h > 0`
  set κ : ℝ := -(((fderiv ℝ (fderiv ℝ f) z) v) v) with hκ
  have hκpos : 0 < κ := by rw [hκ]; exact neg_pos.mpr hv
  have hbound : ∀ᶠ h in 𝓝[>] (0:ℝ), ‖L h‖ ≤ (κ/4) * ‖h^2‖ :=
    hL.def (by linarith)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhdsWithin_iff.mp hbound
  -- a small step `t` which keeps us inside both the `δ` and the `ρ` balls
  set t : ℝ := min (δ/2) (ρ / (2 * (‖v‖ + 1))) with ht
  have htpos : 0 < t := by
    rw [ht]; exact lt_min (by linarith) (by positivity)
  have htδ : t < δ := by
    rw [ht]
    calc min (δ/2) (ρ/(2*(‖v‖ + 1))) ≤ δ/2 := min_le_left _ _
      _ < δ := by linarith
  have htρ : t * (‖v‖ + 1) < ρ := by
    have hle : t * (‖v‖ + 1) ≤ (ρ / (2 * (‖v‖ + 1))) * (‖v‖ + 1) :=
      mul_le_mul_of_nonneg_right (by rw [ht]; exact min_le_right _ _) (by positivity)
    have hval : (ρ / (2 * (‖v‖ + 1))) * (‖v‖ + 1) = ρ / 2 := by
      field_simp
    linarith
  refine ⟨z + t • v, ?_, ?_⟩
  · -- the point `z + t • v` is within `ρ` of `z`
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have : t * ‖v‖ ≤ t * (‖v‖ + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) htpos.le
    linarith
  · -- and `f` is strictly below `Λ` there
    have hmem : t ∈ Metric.ball (0:ℝ) δ ∩ Set.Ioi 0 := by
      refine ⟨?_, htpos⟩
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos htpos]
      exact htδ
    have hb : ‖L t‖ ≤ (κ/4) * ‖t^2‖ := hδ hmem
    have hb' : L t ≤ (κ/4) * t^2 := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] at hb
      exact le_trans (le_abs_self (L t)) hb
    have hLt : L t = f (z + t • v) - Λ + (t^2/2) * κ := by
      simp only [L, hκ, smul_eq_mul]
      ring
    have ht2 : 0 < t^2 := pow_pos htpos 2
    nlinarith [hb', hLt, hκpos, ht2]

end Work.OddBound.mountainPass
