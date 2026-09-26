import Mathlib

/-!
# Two lemmas for the angular velocity of a blurred curve

The low end of the chord sweep needs the *angular velocity* of the doubly blurred needle to be
positive about the centre of its lens (the hypothesis `hang` of
`Work.Drive.lowEnd_of_projection_starShaped`).  The needle is a weighted average of the raw
chamfered loops, so its angular-velocity numerator is the weighted average of the raw numerators
plus a "mismatch" term; this module contains the two *elementary* inputs of that computation (the
whole route is written up in `Submission/Work/Drive/ANGVEL_NOTES.md`):

* **`Work.Drive.concaveAngVelMargin`** — the *quantitative* secant–tangent inequality: for a concave
  `f` on a convex set `S`, a point `xc ∈ S` and a level `yc < f xc`, the angular-velocity numerator
  `(f x - yc) - deriv f x * (x - xc)` of the graph of `f` seen from `(xc, yc)` is at least
  `f xc - yc`.  This is the diagonal term's margin: it is the inradius-type quantity (the vertical
  distance from the centre to the chord of the lens) against which the smoothing error is compared.

* **`Work.Drive.prodIntegralDecomp`** — the diagonal decomposition of a product of two weighted
  averages.  For the product weight `b u * b v` with `∫ b = 1`,

      (∫ b α)(∫ b β) = ∫ b (α β) + ∫∫ b b (α u * (β v - β u)) .

  The first term is the weighted average of the pointwise products (the raw angular-velocity
  numerators) and the second is the mismatch, bounded by `Work.Drive.mismatchIntegralBound`:
  `|mismatch| ≤ A * J` for `|α| ≤ A` and `|β v - β u| ≤ J`.  On the window of the double convolution
  the oscillations are `O(δ₁ + δ₂)`, which is why the blurred angular velocity has the same sign as
  the raw one for small smoothing widths.

The proof of the identity is a pure "pull the constant in and out of the integral" computation: no
Fubini is needed, only `∫ b = 1`.
-/

noncomputable section
namespace Work.Drive

open scoped Real Topology intervalIntegral

/-! ## 1. The quantitative margin of a concave graph -/

/-- **The angular velocity numerator of a concave graph has the explicit margin `f xc - yc`.**
For a concave `f` on a convex set `S`, a point `xc ∈ S` and a level `yc < f xc`, the angular-velocity
numerator `(f x - yc) - deriv f x * (x - xc)` of the graph of `f` seen from `(xc, yc)` is at least
`f xc - yc`, uniformly in `x ∈ S \ {xc}`.  (The sharpening of
`Work.Drive.angularVelocity_num_pos_of_concaveOn`; both proofs are the two secant–tangent
inequalities for a concave function.) -/
theorem concaveAngVelMargin {f : ℝ → ℝ} {S : Set ℝ} {xc yc : ℝ}
    (hfc : ConcaveOn ℝ S f) (hxd : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hxc : xc ∈ S) (hyc : yc < f xc) :
    ∀ x ∈ S, x ≠ xc → f xc - yc ≤ (f x - yc) - deriv f x * (x - xc) := by
  -- the tangent at the left endpoint is above the graph
  have hleft : ∀ a b : ℝ, a ∈ S → b ∈ S → a < b → f b - f a ≤ deriv f a * (b - a) := by
    intro a b ha hb hab
    have h1 := hfc.slope_le_deriv ha hb hab (hxd a ha)
    rw [slope_def_field] at h1
    have h2 : 0 < b - a := sub_pos.mpr hab
    have h3 := mul_le_mul_of_nonneg_right h1 h2.le
    rwa [div_mul_cancel₀ _ (ne_of_gt h2)] at h3
  -- the secant is above the tangent at the right endpoint
  have hright : ∀ a b : ℝ, a ∈ S → b ∈ S → a < b → deriv f b * (b - a) ≤ f b - f a := by
    intro a b ha hb hab
    have h1 := hfc.deriv_le_slope ha hb hab (hxd b hb)
    rw [slope_def_field] at h1
    have h2 : 0 < b - a := sub_pos.mpr hab
    have h3 := mul_le_mul_of_nonneg_right h1 h2.le
    rwa [div_mul_cancel₀ _ (ne_of_gt h2)] at h3
  have hpos : 0 < f xc - yc := by linarith
  intro x hx hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := hleft x xc hx hxc hlt
    have h' : deriv f x * (xc - x) = -(deriv f x * (x - xc)) := by ring
    linarith [h, h', hpos]
  · have h := hright xc x hxc hx hgt
    linarith [h, hpos]

/-! ## 2. The diagonal decomposition of a product of weighted averages -/

/-- **The product of two weighted averages, decomposed along the diagonal.**  For a weight `b` with
`∫ b = 1`, the product of the two weighted averages of `α` and `β` is the weighted average of the
pointwise products plus the mismatch double integral in which the deviation of `β` from its diagonal
value is paired with `α`. -/
theorem prodIntegralDecomp {α β b : ℝ → ℝ} (hb : Continuous b)
    (hb0 : ∀ u : ℝ, 0 ≤ b u) (hb1 : (∫ u in (-1 : ℝ)..1, b u) = 1)
    (hα : Continuous α) (hβ : Continuous β) :
    (∫ u in (-1 : ℝ)..1, b u * α u) * (∫ u in (-1 : ℝ)..1, b u * β u)
      = (∫ u in (-1 : ℝ)..1, b u * (α u * β u))
        + ∫ u in (-1 : ℝ)..1, ∫ v in (-1 : ℝ)..1, b u * b v * (α u * (β v - β u)) := by
  have hleft : (∫ u in (-1 : ℝ)..1, b u * α u) * (∫ u in (-1 : ℝ)..1, b u * β u)
      = ∫ u in (-1 : ℝ)..1, b u * α u * (∫ v in (-1 : ℝ)..1, b v * β v) := by
    rw [← intervalIntegral.integral_mul_const (∫ v in (-1 : ℝ)..1, b v * β v)
      (fun u : ℝ => b u * α u)]
  have hdiag : (∫ u in (-1 : ℝ)..1, b u * (α u * β u))
      = ∫ u in (-1 : ℝ)..1, b u * α u * β u :=
    intervalIntegral.integral_congr (fun u _ => by ring)
  have hmismatch : (∫ u in (-1 : ℝ)..1, ∫ v in (-1 : ℝ)..1, b u * b v * (α u * (β v - β u)))
      = ∫ u in (-1 : ℝ)..1, b u * α u
          * ((∫ v in (-1 : ℝ)..1, b v * β v) - β u) := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [show (fun v : ℝ => b u * b v * (α u * (β v - β u)))
        = (fun v : ℝ => (b u * α u) * (b v * β v) - b v * ((b u * α u) * β u)) from by
      funext v; ring]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, hb1, one_mul]
    · ring
    · exact Continuous.intervalIntegrable (continuous_const.mul (hb.mul hβ)) _ _
    · exact Continuous.intervalIntegrable (hb.mul continuous_const) _ _
  rw [hleft, hdiag, hmismatch, ← intervalIntegral.integral_add]
  · exact intervalIntegral.integral_congr (fun u _ => by ring)
  · exact Continuous.intervalIntegrable ((hb.mul hα).mul hβ) _ _
  · exact Continuous.intervalIntegrable
      ((hb.mul hα).mul ((continuous_const).sub hβ)) _ _

/-! ## 3. The sharpened mismatch bound: oscillation instead of size -/

/-- **The mismatch integral is bounded by the product of the two oscillations.**  For the mismatch
`I := ∫∫ b u b v (α u * (β v - β u))` of `Work.Drive.prodIntegralDecomp` one has

    |I| ≤ (osc α) * (osc β) .

This is the bound the angular-velocity analysis actually needs, and it is *strictly sharper* than
`Work.Drive.mismatchIntegralBound` (which uses `sup |α|` instead of `osc α`): on the smoothing window
of the chord sweep the oscillation of the position coordinates is `O(δ)` while their *size* is `O(W)`,
and the velocity coordinates have oscillation `O(W)` while the diagonal term has margin `O(W³)`, so
only the oscillation-squared form `O(W²δ)` is small compared with `W³`.

The proof avoids Fubini: with `B := ∫ b β` one has `∫ v, b u b v (α u (β v - β u)) = b u α u (B - β u)`,
and `∫ u, b u (B - β u) = 0`, so `α` may be replaced by `α - c` for *any* constant `c`; choosing
`c := α (-1)` and bounding `|B - β u| ≤ osc β` finishes. -/
theorem mismatchOscBound {α β b : ℝ → ℝ} {A J : ℝ}
    (hb : Continuous b) (hb0 : ∀ u : ℝ, 0 ≤ b u)
    (hb1 : (∫ u in (-1 : ℝ)..1, b u) = 1)
    (hα : Continuous α) (hβ : Continuous β)
    (hA : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1, |α u - α v| ≤ A)
    (hJ : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1, |β v - β u| ≤ J) :
    |∫ u in (-1 : ℝ)..1, ∫ v in (-1 : ℝ)..1, b u * b v * (α u * (β v - β u))| ≤ A * J := by
  have hm1 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hm0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 0 hm0 0 hm0)
  have hJ0 : 0 ≤ J := le_trans (abs_nonneg _) (hJ 0 hm0 0 hm0)
  set B : ℝ := ∫ v in (-1 : ℝ)..1, b v * β v with hB
  -- the inner integral
  have hinner : ∀ u : ℝ, (∫ v in (-1 : ℝ)..1, b u * b v * (α u * (β v - β u)))
      = b u * α u * (B - β u) := by
    intro u
    rw [show (fun v : ℝ => b u * b v * (α u * (β v - β u)))
        = (fun v : ℝ => (b u * α u) * (b v * β v) - b v * ((b u * α u) * β u)) from by
      funext v; ring]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, hb1, one_mul, ← hB]
    ring
    · exact Continuous.intervalIntegrable (continuous_const.mul (hb.mul hβ)) _ _
    · exact Continuous.intervalIntegrable (hb.mul continuous_const) _ _
  -- the total mass of `B - β u` vanishes
  have hzero : (∫ u in (-1 : ℝ)..1, b u * (B - β u)) = 0 := by
    rw [show (fun u : ℝ => b u * (B - β u)) = (fun u : ℝ => b u * B - b u * β u) from by
      funext u; ring]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_mul_const, hb1, one_mul, ← hB]
    ring
    · exact Continuous.intervalIntegrable (hb.mul continuous_const) _ _
    · exact Continuous.intervalIntegrable (hb.mul hβ) _ _
  -- replacing `α` by `α - c` does not change the integral
  have hswap : (∫ u in (-1 : ℝ)..1, b u * α u * (B - β u))
      = ∫ u in (-1 : ℝ)..1, b u * (α u - α (-1)) * (B - β u) := by
    have hconst : (∫ u in (-1 : ℝ)..1, α (-1) * (b u * (B - β u))) = 0 := by
      rw [intervalIntegral.integral_const_mul, hzero, mul_zero]
    have h1 : (∫ u in (-1 : ℝ)..1, b u * α u * (B - β u))
        = (∫ u in (-1 : ℝ)..1, b u * (α u - α (-1)) * (B - β u))
          + ∫ u in (-1 : ℝ)..1, α (-1) * (b u * (B - β u)) := by
      rw [← intervalIntegral.integral_add]
      · exact intervalIntegral.integral_congr (fun u _ => by ring)
      · exact Continuous.intervalIntegrable
          ((hb.mul ((hα.sub continuous_const))).mul ((continuous_const).sub hβ)) _ _
      · exact Continuous.intervalIntegrable
          (continuous_const.mul (hb.mul ((continuous_const).sub hβ))) _ _
    rw [h1, hconst, add_zero]
  rw [intervalIntegral.integral_congr (fun u _ => hinner u), hswap]
  -- pointwise bound
  have hpt : ∀ u ∈ Set.Icc (-1 : ℝ) 1, |b u * (α u - α (-1)) * (B - β u)| ≤ b u * (A * J) := by
    intro u hu
    have hbu : 0 ≤ b u := hb0 u
    have h1 : |α u - α (-1)| ≤ A := hA u hu (-1) hm1
    have hBavg : B - β u = ∫ v in (-1 : ℝ)..1, b v * (β v - β u) := by
      rw [show (fun v : ℝ => b v * (β v - β u)) = (fun v : ℝ => b v * β v - b v * β u) from by
        funext v; ring]
      rw [intervalIntegral.integral_sub, intervalIntegral.integral_mul_const, ← hB, hb1, one_mul]
      · exact Continuous.intervalIntegrable (hb.mul hβ) _ _
      · exact Continuous.intervalIntegrable (hb.mul continuous_const) _ _
    have h2 : |B - β u| ≤ J := by
      rw [hBavg]
      have h3 : ‖∫ v in (-1 : ℝ)..1, b v * (β v - β u)‖
          ≤ ∫ v in (-1 : ℝ)..1, b v * J :=
        intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
          (Filter.Eventually.of_forall (fun v hv => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb0 v)]
            exact mul_le_mul_of_nonneg_left (hJ u hu v ⟨hv.1.le, hv.2⟩) (hb0 v)))
          (Continuous.intervalIntegrable (hb.mul continuous_const) _ _)
      rw [Real.norm_eq_abs, intervalIntegral.integral_mul_const, hb1, one_mul] at h3
      exact h3
    calc |b u * (α u - α (-1)) * (B - β u)| = b u * |α u - α (-1)| * |B - β u| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hbu]
      _ ≤ b u * (A * J) := by
          have h4 : |α u - α (-1)| * |B - β u| ≤ A * J :=
            mul_le_mul h1 h2 (abs_nonneg _) hA0
          nlinarith [hbu, h4]
  have hfin : ‖∫ u in (-1 : ℝ)..1, b u * (α u - α (-1)) * (B - β u)‖
      ≤ ∫ u in (-1 : ℝ)..1, b u * (A * J) :=
    intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (Filter.Eventually.of_forall (fun u hu => by
        rw [Real.norm_eq_abs]
        exact hpt u ⟨hu.1.le, hu.2⟩))
      (Continuous.intervalIntegrable (hb.mul continuous_const) _ _)
  rw [Real.norm_eq_abs] at hfin
  have hrhs : (∫ u in (-1 : ℝ)..1, b u * (A * J)) = A * J := by
    rw [intervalIntegral.integral_mul_const, hb1, one_mul]
  rw [hrhs] at hfin
  exact hfin

/-! ## 4. The product of two weighted averages versus the average of the products -/

/-- **The product of two weighted averages differs from the weighted average of the products by at
most the product of the two oscillations.**  For a nonnegative weight `b` of total mass `1` on
`[-1,1]` and two (merely integrable) functions `α`, `β` whose *oscillations* over the window are at
most `A` and `J`,

    |(∫ b α) * (∫ b β) - ∫ b (α β)| ≤ A * J .

This is the workhorse of the `hang` assembly: the angular-velocity numerator of an average of curves
is the average of the numerators plus a mismatch bounded by the products of the oscillations of the
individual coordinates, and this lemma turns each such comparison into a single estimate.  Its proof
is the "pull the constant in and out of the integral" identity with the cancellation
`∫ b (B - β) = 0` (`B := ∫ b β`), which lets `α` be replaced by `α - α (-1)`; no Fubini is used, and
the hypotheses on `α`, `β` are only the integrability of `b α`, `b β`, `b (α β)` (so the lemma
applies to the *piecewise* continuous velocity of the chamfered loop as well as to its continuous
position). -/
theorem meanProd_bound {α β b : ℝ → ℝ} {A J : ℝ}
    (hb : Continuous b) (hb0 : ∀ u : ℝ, 0 ≤ b u)
    (hb1 : (∫ u in (-1 : ℝ)..1, b u) = 1)
    (hbα : IntervalIntegrable (fun u : ℝ => b u * α u) MeasureTheory.volume (-1) 1)
    (hbβ : IntervalIntegrable (fun u : ℝ => b u * β u) MeasureTheory.volume (-1) 1)
    (hbαβ : IntervalIntegrable (fun u : ℝ => b u * (α u * β u)) MeasureTheory.volume (-1) 1)
    (hA : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1, |α u - α v| ≤ A)
    (hJ : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1, |β v - β u| ≤ J) :
    |(∫ u in (-1 : ℝ)..1, b u * α u) * (∫ u in (-1 : ℝ)..1, b u * β u)
      - (∫ u in (-1 : ℝ)..1, b u * (α u * β u))| ≤ A * J := by
  have hm1 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA (-1) hm1 (-1) hm1)
  have hJ0 : 0 ≤ J := le_trans (abs_nonneg _) (hJ (-1) hm1 (-1) hm1)
  set B : ℝ := ∫ v in (-1 : ℝ)..1, b v * β v with hB
  have hbInt : IntervalIntegrable b MeasureTheory.volume (-1) 1 := hb.intervalIntegrable _ _
  -- integrability of the two auxiliary integrands
  have hBint : IntervalIntegrable (fun u : ℝ => b u * (B - β u)) MeasureTheory.volume (-1) 1 := by
    have h := (hbInt.mul_const B).sub hbβ
    rw [show (fun u : ℝ => b u * B - b u * β u)
        = (fun u : ℝ => b u * (B - β u)) from by funext u; ring] at h
    exact h
  have hIint : IntervalIntegrable (fun u : ℝ => b u * α u * (B - β u))
      MeasureTheory.volume (-1) 1 := by
    have h := (hbα.mul_const B).sub hbαβ
    rw [show (fun u : ℝ => (b u * α u) * B - b u * (α u * β u))
        = (fun u : ℝ => b u * α u * (B - β u)) from by funext u; ring] at h
    exact h
  -- the base point cancels
  have hBeval : (∫ u in (-1 : ℝ)..1, b u * (B - β u)) = 0 := by
    have h1 : (∫ u in (-1 : ℝ)..1, b u * (B - β u))
        = (∫ u in (-1 : ℝ)..1, b u * B) - (∫ u in (-1 : ℝ)..1, b u * β u) := by
      rw [← intervalIntegral.integral_sub (hbInt.mul_const B) hbβ]
      exact intervalIntegral.integral_congr (fun u _ => by ring)
    have h2 : (∫ u in (-1 : ℝ)..1, b u * B) = B := by
      rw [intervalIntegral.integral_mul_const, hb1, one_mul]
    have h3 : (∫ u in (-1 : ℝ)..1, b u * β u) = B := hB.symm
    rw [h1, h2, h3]
    ring
  -- `α` may be replaced by `α - α (-1)`
  have hswap : (∫ u in (-1 : ℝ)..1, b u * α u * (B - β u))
      = ∫ u in (-1 : ℝ)..1, b u * (α u - α (-1)) * (B - β u) := by
    have hJint : IntervalIntegrable (fun u : ℝ => b u * (α u - α (-1)) * (B - β u))
        MeasureTheory.volume (-1) 1 := by
      have h := hIint.sub (hBint.const_mul (α (-1)))
      rw [show (fun u : ℝ => b u * α u * (B - β u) - α (-1) * (b u * (B - β u)))
          = (fun u : ℝ => b u * (α u - α (-1)) * (B - β u)) from by funext u; ring] at h
      exact h
    have h1 : (∫ u in (-1 : ℝ)..1, b u * α u * (B - β u))
        = (∫ u in (-1 : ℝ)..1, b u * (α u - α (-1)) * (B - β u))
          + ∫ u in (-1 : ℝ)..1, α (-1) * (b u * (B - β u)) := by
      rw [← intervalIntegral.integral_add hJint (hBint.const_mul (α (-1)))]
      exact intervalIntegral.integral_congr (fun u _ => by ring)
    have h2 : (∫ u in (-1 : ℝ)..1, α (-1) * (b u * (B - β u))) = 0 := by
      rw [intervalIntegral.integral_const_mul, hBeval, mul_zero]
    rw [h1, h2, add_zero]
  have hEq : (∫ u in (-1 : ℝ)..1, b u * α u) * (∫ u in (-1 : ℝ)..1, b u * β u)
      - (∫ u in (-1 : ℝ)..1, b u * (α u * β u))
      = ∫ u in (-1 : ℝ)..1, b u * (α u - α (-1)) * (B - β u) := by
    have hstep1 : (∫ u in (-1 : ℝ)..1, b u * α u) * (∫ u in (-1 : ℝ)..1, b u * β u)
        = ∫ u in (-1 : ℝ)..1, (b u * α u) * B := by
      rw [← hB, ← intervalIntegral.integral_mul_const (∫ v in (-1 : ℝ)..1, b v * β v)
        (fun u : ℝ => b u * α u)]
    have hstep2 : (∫ u in (-1 : ℝ)..1, (b u * α u) * B)
        - (∫ u in (-1 : ℝ)..1, b u * (α u * β u))
        = ∫ u in (-1 : ℝ)..1, b u * α u * (B - β u) := by
      rw [← intervalIntegral.integral_sub (hbα.mul_const B) hbαβ]
      exact intervalIntegral.integral_congr (fun u _ => by ring)
    rw [hstep1, hstep2, hswap]
  rw [hEq]
  -- the pointwise bound
  have hpt : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |b u * (α u - α (-1)) * (B - β u)| ≤ b u * (A * J) := by
    intro u hu
    have hbu : 0 ≤ b u := hb0 u
    have h1 : |α u - α (-1)| ≤ A := hA u hu (-1) hm1
    have hBeq : B - β u = ∫ v in (-1 : ℝ)..1, b v * (β v - β u) := by
      have h1' : (∫ v in (-1 : ℝ)..1, b v * (β v - β u))
          = (∫ v in (-1 : ℝ)..1, b v * β v) - (∫ v in (-1 : ℝ)..1, b v * β u) := by
        rw [← intervalIntegral.integral_sub hbβ (hbInt.mul_const (β u))]
        exact intervalIntegral.integral_congr (fun v _ => by ring)
      have h2' : (∫ v in (-1 : ℝ)..1, b v * β u) = (∫ v in (-1 : ℝ)..1, b v) * β u :=
        intervalIntegral.integral_mul_const (β u) (fun v : ℝ => b v)
      rw [h1', h2', hb1, one_mul, hB]
    have h2 : |B - β u| ≤ J := by
      rw [hBeq]
      have h3 : ‖∫ v in (-1 : ℝ)..1, b v * (β v - β u)‖ ≤ ∫ v in (-1 : ℝ)..1, b v * J :=
        intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
          (Filter.Eventually.of_forall (fun v hv => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb0 v)]
            exact mul_le_mul_of_nonneg_left (hJ u hu v ⟨hv.1.le, hv.2⟩) (hb0 v)))
          (hbInt.mul_const J)
      rw [Real.norm_eq_abs, intervalIntegral.integral_mul_const, hb1, one_mul] at h3
      exact h3
    calc |b u * (α u - α (-1)) * (B - β u)| = b u * |α u - α (-1)| * |B - β u| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hbu]
      _ ≤ b u * (A * J) := by
          have h4 : |α u - α (-1)| * |B - β u| ≤ A * J :=
            mul_le_mul h1 h2 (abs_nonneg _) hA0
          nlinarith [hbu, h4]
  have hfin : ‖∫ u in (-1 : ℝ)..1, b u * (α u - α (-1)) * (B - β u)‖
      ≤ ∫ u in (-1 : ℝ)..1, b u * (A * J) :=
    intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (Filter.Eventually.of_forall (fun u hu => by
        rw [Real.norm_eq_abs]
        exact hpt u ⟨hu.1.le, hu.2⟩))
      (hbInt.mul_const (A * J))
  rw [Real.norm_eq_abs] at hfin
  have hrhs : (∫ u in (-1 : ℝ)..1, b u * (A * J)) = A * J := by
    rw [intervalIntegral.integral_mul_const, hb1, one_mul]
  rw [hrhs] at hfin
  exact hfin

/-! ## 5. The two-variable form: the analytic core of the `hang` assembly -/

/-- **The two-variable product bound.**  The analogue of `Work.Drive.meanProd_bound` for the
*iterated* weighted average produced by the double convolution of the swept loop: for a nonnegative
weight `b` of total mass `1` on `[-1,1]` and two functions `α`, `β` of the two window parameters
whose *joint* oscillations are at most `A` and `J`,

    |(∫ b (∫ b α)) * (∫ b (∫ b β)) - ∫ b (∫ b (α β))| ≤ 2 * (A * J) .

This is the estimate that turns "the angular-velocity numerator of the doubly blurred curve" into
"the weighted average of the numerators of the individual curves plus a mismatch": applied with
`α` and `β` the two *coordinate functions* of the family of swept loops over the `(t, σ)`-window, the
left factor is the numerator of the needle (whose derivative is the double integral of the loop
velocities, `Work.Drive.sweepFam_double_blur_deriv`) and the right term is the diagonal.  The
factor `2` comes from the two comparisons (the inner average and the outer one) and is harmless.

The hypotheses are only *integrability* (of the two slice averages and of the three products
involved), so the lemma applies to the **velocity** coordinate of the chamfered loop — which is
piecewise continuous but not continuous — as well as to its continuous position coordinate:
boundedness plus measurability of those functions discharges them
(`MeasureTheory.IntegrableOn.of_bound`).  No Fubini is used: everything is the "pull the constant in
and out of the integral" identity together with the cancellation of the inner average. -/
theorem meanProd_bound₂ {α β : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {A J : ℝ}
    (hb : Continuous b) (hb0 : ∀ u : ℝ, 0 ≤ b u)
    (hb1 : (∫ u in (-1 : ℝ)..1, b u) = 1)
    (hαs : ∀ u : ℝ, IntervalIntegrable (fun v : ℝ => b v * α u v) MeasureTheory.volume (-1) 1)
    (hβs : ∀ u : ℝ, IntervalIntegrable (fun v : ℝ => b v * β u v) MeasureTheory.volume (-1) 1)
    (hαβs : ∀ u : ℝ, IntervalIntegrable (fun v : ℝ => b v * (α u v * β u v))
      MeasureTheory.volume (-1) 1)
    (hAs : IntervalIntegrable (fun u : ℝ => b u * (∫ v in (-1 : ℝ)..1, b v * α u v))
      MeasureTheory.volume (-1) 1)
    (hBs : IntervalIntegrable (fun u : ℝ => b u * (∫ v in (-1 : ℝ)..1, b v * β u v))
      MeasureTheory.volume (-1) 1)
    (hABs : IntervalIntegrable (fun u : ℝ => b u *
      ((∫ v in (-1 : ℝ)..1, b v * α u v) * (∫ v in (-1 : ℝ)..1, b v * β u v)))
      MeasureTheory.volume (-1) 1)
    (hCs : IntervalIntegrable (fun u : ℝ => b u *
      (∫ v in (-1 : ℝ)..1, b v * (α u v * β u v))) MeasureTheory.volume (-1) 1)
    (hA' : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u' ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1, |α u v - α u' v'| ≤ A)
    (hJ' : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u' ∈ Set.Icc (-1 : ℝ) 1, ∀ v' ∈ Set.Icc (-1 : ℝ) 1, |β u v - β u' v'| ≤ J) :
    |(∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * α u v))
      * (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * β u v))
      - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (α u v * β u v)))|
      ≤ 2 * (A * J) := by
  have hm1 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA' (-1) hm1 (-1) hm1 (-1) hm1 (-1) hm1)
  have hJ0 : 0 ≤ J := le_trans (abs_nonneg _) (hJ' (-1) hm1 (-1) hm1 (-1) hm1 (-1) hm1)
  have hbInt : IntervalIntegrable b MeasureTheory.volume (-1) 1 := hb.intervalIntegrable _ _
  -- the *slice* comparison
  have hslice : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |(∫ v in (-1 : ℝ)..1, b v * α u v) * (∫ v in (-1 : ℝ)..1, b v * β u v)
        - (∫ v in (-1 : ℝ)..1, b v * (α u v * β u v))| ≤ A * J := by
    intro u hu
    refine meanProd_bound hb hb0 hb1 (hαs u) (hβs u) (hαβs u) ?_ ?_
    · intro v hv v' hv'
      exact hA' u hu v hv u hu v' hv'
    · intro v hv v' hv'
      exact hJ' u hu v' hv' u hu v hv
  -- the slice averages oscillate by at most `A` and `J`
  have hoscA : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ u' ∈ Set.Icc (-1 : ℝ) 1,
      |(∫ v in (-1 : ℝ)..1, b v * α u v) - (∫ v in (-1 : ℝ)..1, b v * α u' v)| ≤ A := by
    intro u hu u' hu'
    have h1 : (∫ v in (-1 : ℝ)..1, b v * α u v) - (∫ v in (-1 : ℝ)..1, b v * α u' v)
        = ∫ v in (-1 : ℝ)..1, b v * (α u v - α u' v) := by
      rw [← intervalIntegral.integral_sub (hαs u) (hαs u')]
      exact intervalIntegral.integral_congr (fun v _ => by ring)
    have h2 : ‖∫ v in (-1 : ℝ)..1, b v * (α u v - α u' v)‖
        ≤ ∫ v in (-1 : ℝ)..1, b v * A :=
      intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        (Filter.Eventually.of_forall (fun v hv => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb0 v)]
          exact mul_le_mul_of_nonneg_left
            (hA' u hu v ⟨hv.1.le, hv.2⟩ u' hu' v ⟨hv.1.le, hv.2⟩) (hb0 v)))
        (hbInt.mul_const A)
    rw [Real.norm_eq_abs, intervalIntegral.integral_mul_const, hb1, one_mul] at h2
    rw [h1]
    exact h2
  have hoscB : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ u' ∈ Set.Icc (-1 : ℝ) 1,
      |(∫ v in (-1 : ℝ)..1, b v * β u' v) - (∫ v in (-1 : ℝ)..1, b v * β u v)| ≤ J := by
    intro u hu u' hu'
    have h1 : (∫ v in (-1 : ℝ)..1, b v * β u' v) - (∫ v in (-1 : ℝ)..1, b v * β u v)
        = ∫ v in (-1 : ℝ)..1, b v * (β u' v - β u v) := by
      rw [← intervalIntegral.integral_sub (hβs u') (hβs u)]
      exact intervalIntegral.integral_congr (fun v _ => by ring)
    have h2 : ‖∫ v in (-1 : ℝ)..1, b v * (β u' v - β u v)‖
        ≤ ∫ v in (-1 : ℝ)..1, b v * J :=
      intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        (Filter.Eventually.of_forall (fun v hv => by
          have hv' : v ∈ Set.Icc (-1 : ℝ) 1 := ⟨hv.1.le, hv.2⟩
          have h3 : |β u' v - β u v| ≤ J := by
            have h := hJ' u hu v hv' u' hu' v hv'
            rwa [abs_sub_comm] at h
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb0 v)]
          exact mul_le_mul_of_nonneg_left h3 (hb0 v)))
        (hbInt.mul_const J)
    rw [Real.norm_eq_abs, intervalIntegral.integral_mul_const, hb1, one_mul] at h2
    rw [h1]
    exact h2
  -- the outer comparison
  have houter : |(∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * α u v))
      * (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * β u v))
      - (∫ u in (-1 : ℝ)..1, b u *
          ((∫ v in (-1 : ℝ)..1, b v * α u v) * (∫ v in (-1 : ℝ)..1, b v * β u v)))|
      ≤ A * J :=
    meanProd_bound hb hb0 hb1 hAs hBs hABs hoscA hoscB
  -- the inner-slice comparison, integrated
  have hsecond : |(∫ u in (-1 : ℝ)..1, b u *
        ((∫ v in (-1 : ℝ)..1, b v * α u v) * (∫ v in (-1 : ℝ)..1, b v * β u v)))
      - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (α u v * β u v)))|
      ≤ A * J := by
    have hEq : (∫ u in (-1 : ℝ)..1, b u *
          ((∫ v in (-1 : ℝ)..1, b v * α u v) * (∫ v in (-1 : ℝ)..1, b v * β u v)))
        - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (α u v * β u v)))
        = ∫ u in (-1 : ℝ)..1, b u *
          ((∫ v in (-1 : ℝ)..1, b v * α u v) * (∫ v in (-1 : ℝ)..1, b v * β u v)
            - ∫ v in (-1 : ℝ)..1, b v * (α u v * β u v)) := by
      rw [← intervalIntegral.integral_sub hABs hCs]
      exact intervalIntegral.integral_congr (fun u _ => by ring)
    rw [hEq]
    have hpt : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        |b u * ((∫ v in (-1 : ℝ)..1, b v * α u v) * (∫ v in (-1 : ℝ)..1, b v * β u v)
          - ∫ v in (-1 : ℝ)..1, b v * (α u v * β u v))| ≤ b u * (A * J) := by
      intro u hu
      have h1 : |(∫ v in (-1 : ℝ)..1, b v * α u v) * (∫ v in (-1 : ℝ)..1, b v * β u v)
          - (∫ v in (-1 : ℝ)..1, b v * (α u v * β u v))| ≤ A * J := hslice u hu
      rw [abs_mul, abs_of_nonneg (hb0 u)]
      exact mul_le_mul_of_nonneg_left h1 (hb0 u)
    have hfin : ‖∫ u in (-1 : ℝ)..1, b u *
          ((∫ v in (-1 : ℝ)..1, b v * α u v) * (∫ v in (-1 : ℝ)..1, b v * β u v)
            - ∫ v in (-1 : ℝ)..1, b v * (α u v * β u v))‖
        ≤ ∫ u in (-1 : ℝ)..1, b u * (A * J) :=
      intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        (Filter.Eventually.of_forall (fun u hu => by
          rw [Real.norm_eq_abs]
          exact hpt u ⟨hu.1.le, hu.2⟩))
        (hbInt.mul_const (A * J))
    rw [Real.norm_eq_abs] at hfin
    rw [intervalIntegral.integral_mul_const, hb1, one_mul] at hfin
    exact hfin
  calc |(∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * α u v))
        * (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * β u v))
        - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (α u v * β u v)))|
      = |((∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * α u v))
          * (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * β u v))
          - (∫ u in (-1 : ℝ)..1, b u *
              ((∫ v in (-1 : ℝ)..1, b v * α u v) * (∫ v in (-1 : ℝ)..1, b v * β u v))))
        + ((∫ u in (-1 : ℝ)..1, b u *
              ((∫ v in (-1 : ℝ)..1, b v * α u v) * (∫ v in (-1 : ℝ)..1, b v * β u v)))
          - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (α u v * β u v))))| := by
        ring_nf
    _ ≤ |(∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * α u v))
          * (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * β u v))
          - (∫ u in (-1 : ℝ)..1, b u *
              ((∫ v in (-1 : ℝ)..1, b v * α u v) * (∫ v in (-1 : ℝ)..1, b v * β u v)))|
        + |(∫ u in (-1 : ℝ)..1, b u *
              ((∫ v in (-1 : ℝ)..1, b v * α u v) * (∫ v in (-1 : ℝ)..1, b v * β u v)))
          - (∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1, b v * (α u v * β u v)))| :=
        abs_add_le _ _
    _ ≤ A * J + A * J := add_le_add houter hsecond
    _ = 2 * (A * J) := by ring

end Work.Drive
