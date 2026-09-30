/-
# The junction of the collar and the polar charts: `cuspInvOuter ∘ polarToUHS = cuspInvInner`

The filling piece `W_v` of the Dehn filling carries two coordinate systems that meet at the
junction layer `‖p‖∞ = 1/2`, i.e. at the metric radius `r = r_J`:

* the **collar** (UHS, outer) coordinates `(x,s)`, whose inverse is `Work.Cusp.cuspInvOuter v`;
* the **polar** (warped, inner) coordinates `(r,θ,w₁,w₂)`, whose inverse is
  `Work.Cusp.cuspInvInner v`; the isometry relating them is
  `Work.Cusp.polarToUHS v : (r,θ,w₁,w₂) ↦ (x,s)`.

This file proves that the two inverses agree on the collar side of the junction: for
`q = (r,θ,w₁,w₂)` with `r_J ≤ q 0` (so that the point lies in the collar, where the UHS coordinate
system is the metric model of the filling),

  `cuspInvOuter v (polarToUHS v q) = cuspInvInner v q`.

This is the identity the junction charts `Work.RTOWed.jCoordM` need in order to be well defined at
the junction layer `r = r_J` (their two branches `cuspCoordMTop ∘ polarToUHS` and
`incW ∘ cuspInvInner` must describe the same point of `M̂`).

## The three ingredients

Written out, the two sides are: with `x = (q₁/(2π))·σ_v + q₂·Ê₂ + q₃·Ê₃ ∈ ℝ³`,
`y = invY v (q₂,q₃)` and `u = (q₁ − 2π⟪cuspY v y, σ_v⟫/‖σ_v‖²)/(2π)`,

  LHS `= (T_o • bndOfU (outerU v x), outerY v x)`,
  RHS `= (T_i • bndOfU u, y)`,

where `T_o = 1 + (log s − log β(x))/(2(log β(x) − log s_J))`,
`T_i = if r ≤ r_J then r/(2r_J) else 1 + (R₀ − r − log β)/(2(log β − log s_J))`, and

1. **the horizontal part** (`cuspX_cuspUInv_cuspYInv`): `x = cuspX v u y`, i.e. `outerU v x = u`
   and `outerY v x = y` (`outerU_cuspX`, `outerY_cuspX`).  The `σ_v`-component `q₁/(2π)` of `x`
   together with the `w`-coordinates `(q₂,q₃) = wOf v y` (the input convention of
   `polarToUHS`, i.e. `wOf_invY`) is precisely the cusp coordinate of the pair `(u,y)`: the
   projection `(⟪cuspY v y, σ_v⟫/‖σ_v‖²)·σ_v` is the `σ̂_v`-term of the frame expansion
   `frame_expansion`, and the remainder is rebuilt from `q₂,q₃`;
2. **the radial part** (`collar_t_eq`): the layer parameter recovered from the height
   `s = e^{R₀−r}` by the collar inverse is the layer parameter recovered from `r` by the polar
   inverse.  Off the junction this is `log (e^{R₀−r}) = R₀ − r`; at the junction `r = r_J` the
   collar formula evaluates to `r_J/(2 r_J) = 1/2 = ‖p‖∞`, which is the inner branch
   (`log s_J = R₀ − r_J = 1/2`);
3. `β(x) = β (cuspX v u y)` by (1), which is what lets (2) be applied to both sides.

The only geometric inputs are `frame_expansion`, `inner_slope_smul`, `wOf_invY` and the bounds
`0 < β ≤ β_max < s_J`; no arithmetic on the cusp data `kappa`/`slopeB` is needed here.
-/
import Mathlib
import Submission.Work.RTOwed.FillBigDefs
import Submission.Work.Cusp.wOf_invY

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Real RealInnerProductSpace InnerProductSpace

namespace Work.RTOWed

open Work.Cusp

/-! ### The polar coordinates of a UHS point, and the inner inverse written with them -/

/-- The horizontal part `x = (q₀,q₁,q₂)` of a UHS coordinate `q = (x,s)`. -/
def uhsOf (q : Cusp.E4) : Cusp.E3 := !₂[q 0, q 1, q 2]

/-- The torus coordinates `y = invY v (q₂,q₃)` recovered from the `w`-coordinates of `q` by
`cuspInvInner v` (`wOf_invY` is the statement that this really inverts `wOf v`). -/
def cuspYInv (v : Fin 5) (q : Cusp.E4) : Cusp.E2 := Cusp.invY v (!₂[q 2, q 3] : Cusp.E2)

/-- The perimeter coordinate `u = (q₁ − 2π⟪cuspY v y, σ_v⟫/‖σ_v‖²)/(2π)` recovered from the angle
`q₁` and the torus coordinates `y = cuspYInv v q` by `cuspInvInner v`. -/
def cuspUInv (v : Fin 5) (q : Cusp.E4) : ℝ :=
  (q 1 - 2 * Real.pi * (⟪Cusp.cuspY v (cuspYInv v q), Cusp.slope v⟫_ℝ / ‖Cusp.slope v‖ ^ 2))
    / (2 * Real.pi)

/-! ### The horizontal part: `x = cuspX v (cuspUInv v q) (cuspYInv v q)` -/

/-- The horizontal coordinates of `polarToUHS v q` are `(‖σ_v‖/2π)·q₁·σ̂_v + q₂Ê₂ + q₃Ê₃`. -/
theorem uhsOf_polarToUHS_apply (v : Fin 5) (q : Cusp.E4) :
    uhsOf (Cusp.polarToUHS v q) =
      (‖Cusp.slope v‖ / (2 * Real.pi) * q 1) • Cusp.frame1 v
        + q 2 • Cusp.frame2 v + q 3 • Cusp.frame3 v := by
  ext i
  fin_cases i <;> simp [uhsOf, Cusp.polarToUHS]

/-- **The polar inverse of a point of the collar, in cusp coordinates.**  Let `y` be a pair of
torus coordinates whose `w`-coordinates are `(q₂,q₃)` (`wOf v y = (q₂,q₃)`) and let `u` satisfy
`u + ⟪cuspY v y, σ_v⟫/‖σ_v‖² = q₁/(2π)`, so that `u` is the perimeter coordinate of `cuspInvInner v`
applied to `q`.  Then the cusp coordinate of `(u,y)` is the horizontal part `x` of
`polarToUHS v q`:
`x = u·σ_v + cuspY v y = (q₁/(2π))·σ_v + q₂Ê₂ + q₃Ê₃`.

Indeed, expanding `cuspY v y` in the orthonormal frame `(σ̂_v, Ê₂, Ê₃)`
(`frame_expansion`) splits it into its `σ_v`-component `(⟪cuspY v y,σ_v⟫/‖σ_v‖²)·σ_v`
(`inner_slope_smul`) plus the two `w`-terms `q₂Ê₂ + q₃Ê₃`, which is exactly what the shifted
perimeter coordinate `u` is designed to absorb. -/
theorem cuspX_of_polar_wOf (v : Fin 5) (q : Cusp.E4) (y : Cusp.E2) (uu : ℝ)
    (hw : Cusp.wOf v y = (!₂[q 2, q 3] : Cusp.E2))
    (hu : uu + ⟪Cusp.cuspY v y, Cusp.slope v⟫_ℝ / ‖Cusp.slope v‖ ^ 2 = q 1 / (2 * Real.pi)) :
    Cusp.cuspX v uu y = uhsOf (Cusp.polarToUHS v q) := by
  have hW2 : Cusp.wOf v y 0 = q 2 := by rw [hw]; simp
  have hW3 : Cusp.wOf v y 1 = q 3 := by rw [hw]; simp
  have hW2' : ⟪Cusp.cuspY v y, Cusp.frame2 v⟫_ℝ = q 2 := hW2
  have hW3' : ⟪Cusp.cuspY v y, Cusp.frame3 v⟫_ℝ = q 3 := hW3
  -- `cuspY v y`, split into its `σ_v`-component and its two `w`-coordinates
  have hdecomp : Cusp.cuspY v y
      = (⟪Cusp.cuspY v y, Cusp.slope v⟫_ℝ / ‖Cusp.slope v‖ ^ 2) • Cusp.slope v
        + (q 2 • Cusp.frame2 v + q 3 • Cusp.frame3 v) := by
    rw [show (⟪Cusp.cuspY v y, Cusp.slope v⟫_ℝ / ‖Cusp.slope v‖ ^ 2) • Cusp.slope v
          + (q 2 • Cusp.frame2 v + q 3 • Cusp.frame3 v)
        = ⟪Cusp.cuspY v y, Cusp.frame1 v⟫_ℝ • Cusp.frame1 v
          + ⟪Cusp.cuspY v y, Cusp.frame2 v⟫_ℝ • Cusp.frame2 v
          + ⟪Cusp.cuspY v y, Cusp.frame3 v⟫_ℝ • Cusp.frame3 v from by
      rw [Cusp.inner_slope_smul v (Cusp.cuspY v y), hW2', hW3']
      abel,
      Cusp.frame_expansion v (Cusp.cuspY v y)]
  rw [show Cusp.cuspX v uu y = uu • Cusp.slope v + Cusp.cuspY v y from rfl, hdecomp,
    ← add_assoc, ← add_smul, hu, uhsOf_polarToUHS_apply]
  rw [show (q 1 / (2 * Real.pi)) • Cusp.slope v
      = (‖Cusp.slope v‖ / (2 * Real.pi) * q 1) • Cusp.frame1 v from by
    rw [← Cusp.smul_frame1 v (q 1 / (2 * Real.pi))]
    congr 1
    ring]
  abel

/-- **The horizontal part of the junction identity**: the cusp coordinate of the pair recovered by
`cuspInvInner v` from `q` is the horizontal part of `polarToUHS v q`. -/
theorem cuspX_cuspUInv_cuspYInv (v : Fin 5) (q : Cusp.E4) :
    Cusp.cuspX v (cuspUInv v q) (cuspYInv v q) = uhsOf (Cusp.polarToUHS v q) := by
  refine cuspX_of_polar_wOf v q (cuspYInv v q) (cuspUInv v q) ?_ ?_
  · exact Cusp.wOf_invY v _
  · rw [cuspUInv]
    set c : ℝ := ⟪Cusp.cuspY v (cuspYInv v q), Cusp.slope v⟫_ℝ / ‖Cusp.slope v‖ ^ 2 with hc
    field_simp
    ring

/-! ### The radial part -/

/-- **The two layer parameters agree.**  The collar inverse recovers the layer parameter `t` from
the height `s = e^{R₀−q₀}` and the ceiling `b`; the polar inverse recovers it from the radius `q₀`
and the ceiling `b`.  Since `log s = R₀ − q₀` these are the same formula in the collar branch
(`q₀ > r_J`), and at the junction `q₀ = r_J` the collar formula evaluates to
`1 + (log s_J − log b)/(2(log b − log s_J)) = 1 − 1/2 = 1/2`, which is the value `r_J/(2 r_J)`
taken by the inner branch; here `log s_J = R₀ − r_J = 1/2`, and `b < s_J` gives `log b ≠ log s_J`,
so that the cancellation is legitimate. -/
theorem collar_t_eq (q : Cusp.E4) (b : ℝ) (hge : Cusp.rJ ≤ q 0) (hb : 0 < b)
    (hblt : b < Cusp.sJ) :
    1 + (Real.log (Real.exp (Cusp.R0 - q 0)) - Real.log b) / (2 * (Real.log b - Real.log Cusp.sJ))
      = (if q 0 ≤ Cusp.rJ then q 0 / (2 * Cusp.rJ)
         else 1 + (Cusp.R0 - q 0 - Real.log b) / (2 * (Real.log b - Real.log Cusp.sJ))) := by
  rw [Real.log_exp]
  by_cases h : q 0 ≤ Cusp.rJ
  · rw [ite_eq_left h]
    have hq : q 0 = Cusp.rJ := le_antisymm h hge
    rw [hq, Cusp.rJ, Cusp.R0, Cusp.sJ, Real.log_exp]
    have hlt : Real.log b < 1 / 2 := by
      have := Real.log_lt_log hb hblt
      rwa [Cusp.sJ, Real.log_exp] at this
    have hne : Real.log b - 1 / 2 ≠ 0 := by linarith
    have hD : (2 : ℝ) * (Real.log b - 1 / 2) ≠ 0 := mul_ne_zero (by norm_num) hne
    rw [show (7 / 2 : ℝ) - 3 - Real.log b = -(1 / 2) * (2 * (Real.log b - 1 / 2)) by ring,
      mul_div_cancel_right₀ (-(1 / 2)) hD]
    norm_num
  · rw [ite_eq_right h]

/-! ### The junction identity -/

/-- **The collar inverse and the polar inverse agree on the collar.**  For a polar point
`q = (r,θ,w₁,w₂)` with `r_J ≤ r` (i.e. on the collar side of the junction, where the collar
coordinates are the UHS model of the filling piece), the UHS coordinates `polarToUHS v q` of `q`
are sent back by `cuspInvOuter v` to the same pair `(p,y)` of layer parameter and torus coordinates
that the polar inverse `cuspInvInner v` recovers from `q`. -/
theorem cuspInvOuter_polarToUHS_eq (v : Work.Space.Cusp) {q : Work.Cusp.E4}
    (hge : Work.Cusp.rJ ≤ q 0) :
    Work.Cusp.cuspInvOuter v (Work.Cusp.polarToUHS v q) = Work.Cusp.cuspInvInner v q := by
  have hbpos : (0 : ℝ) < Cusp.beta (uhsOf (Cusp.polarToUHS v q)) := Cusp.beta_pos _
  have hblt : Cusp.beta (uhsOf (Cusp.polarToUHS v q)) < Cusp.sJ :=
    lt_of_le_of_lt (Cusp.beta_le_max _) Cusp.betaMax_lt_sJ
  -- the two parts of the cusp coordinate of the polar-inverse pair
  have hU : Cusp.outerU v (uhsOf (Cusp.polarToUHS v q)) = cuspUInv v q := by
    rw [← cuspX_cuspUInv_cuspYInv v q]
    exact Cusp.outerU_cuspX v _ _
  have hY : Cusp.outerY v (uhsOf (Cusp.polarToUHS v q)) = cuspYInv v q := by
    rw [← cuspX_cuspUInv_cuspYInv v q]
    exact Cusp.outerY_cuspX v _ _
  -- the equality of the two layer parameters
  have key := collar_t_eq q (Cusp.beta (uhsOf (Cusp.polarToUHS v q))) hge hbpos hblt
  -- name the pieces of `polarToUHS v q` and of the inner inverse
  have huhs : (!₂[(Cusp.polarToUHS v q).ofLp 0, (Cusp.polarToUHS v q).ofLp 1,
      (Cusp.polarToUHS v q).ofLp 2] : Cusp.E3) = uhsOf (Cusp.polarToUHS v q) := rfl
  have hexp : (Cusp.polarToUHS v q).ofLp 3 = Real.exp (Cusp.R0 - q 0) := rfl
  have hcu : ((q.ofLp 1 - 2 * π * (⟪Cusp.cuspY v (Cusp.invY v !₂[q.ofLp 2, q.ofLp 3]),
        Cusp.slope v⟫_ℝ / ‖Cusp.slope v‖ ^ 2)) / (2 * π)) = cuspUInv v q := rfl
  have hcy : (Cusp.invY v !₂[q.ofLp 2, q.ofLp 3] : Cusp.E2) = cuspYInv v q := rfl
  simp only [Cusp.cuspInvOuter, Cusp.cuspInvInner]
  rw [huhs, hexp, hcu, hcy, hU, hY, cuspX_cuspUInv_cuspYInv v q, key]

end Work.RTOWed
