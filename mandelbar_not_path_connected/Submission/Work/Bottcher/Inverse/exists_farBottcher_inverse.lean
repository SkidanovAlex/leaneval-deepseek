/-
# A far inverse branch of the Böttcher coordinate (single-value form)

`Work.Bottcher.Inverse.exists_farBottcher_inverse`: for `1024 (1 + ‖c‖) + 1024 ≤ ‖u‖`
there is a *unique* `z` in the closed ball `{‖z - u‖ ≤ ‖u‖/8}` with `bottcher c z = u`,
and it satisfies `‖z - u‖ ≤ 4 (‖c‖² + 3‖c‖ + 1)/‖u‖`.

The construction is the Banach fixed point theorem for the map

`z ↦ u · exp (-(bottcherSeries c z))`

on the closed ball of radius `‖u‖/8` around `u`, exactly as in
`Work.Bottcher.Contraction.exists_farInverseBottcher`, together with the two
quantitative inputs already proved in the workspace:

* `norm_bottcherSeries_le_far` : `‖B_c z‖ ≤ (‖c‖²+3‖c‖+1)/‖z‖²` for `‖z‖ ≥ 64(1+‖c‖)+64`;
* `norm_bottcherSeries_sub_le` : `B_c` is `128 (‖c‖²+3‖c‖+1)/‖u‖³`-Lipschitz on the ball
  `{‖z - u‖ ≤ ‖u‖/8}`.

The only algebraic input is that `1024 K ≤ ‖u‖²` for `K = ‖c‖²+3‖c‖+1`, which is what makes
the map a contraction with constant `1/2` and confines its values to a ball of radius
`128 K/(49 ‖u‖) ≤ ‖u‖/8`.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Inverse.norm_bottcherSeries_le_far
import Submission.Work.Bottcher.Inverse.norm_bottcherSeries_sub_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Inverse

noncomputable section

open Metric

open scoped NNReal

/-! ### Elementary numerical consequences of the hypothesis -/

private lemma hu_pos (c u : ℂ) (hu : 1024 * (1 + ‖c‖) + 1024 ≤ ‖u‖) : (0 : ℝ) < ‖u‖ := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  nlinarith

private lemma hu_ge (c u : ℂ) (hu : 1024 * (1 + ‖c‖) + 1024 ≤ ‖u‖) : (1024 : ℝ) ≤ ‖u‖ := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  nlinarith

/-- The single algebraic input of the proof: `1024 (‖c‖² + 3‖c‖ + 1) ≤ ‖u‖²`.  It is what
turns the estimates `‖B_c z‖ ≤ K/‖z‖²` and `‖B_c x - B_c y‖ ≤ 128 K/‖u‖³ ‖x - y‖` into a
strict contraction with constant `1/2` on the ball of radius `‖u‖/8`. -/
private lemma key_1024 (c u : ℂ) (hu : 1024 * (1 + ‖c‖) + 1024 ≤ ‖u‖) :
    1024 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) ≤ ‖u‖ ^ 2 := by
  have ht : (1024 : ℝ) ≤ ‖u‖ := hu_ge c u hu
  have ht1 : (1 : ℝ) ≤ ‖u‖ := by linarith
  have hj0 : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have h1 : 1024 * ‖c‖ ≤ ‖u‖ := by linarith
  have h2 : (1024 * ‖c‖) ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : 1024 * ‖c‖ ^ 2 ≤ ‖u‖ ^ 2 / 1024 := by nlinarith [h2]
  have h4 : 3072 * ‖c‖ ≤ 3 * ‖u‖ := by linarith
  have h5 : (1024 : ℝ) ≤ ‖u‖ ^ 2 := by nlinarith [ht]
  nlinarith [h3, h4, ht, ht1, h5, sq_nonneg ‖u‖]

/-! ### The ball `{‖z - u‖ ≤ ‖u‖/8}` lies in the far region -/

private lemma ball_norm_ge {u z : ℂ} (hz : z ∈ Metric.closedBall u (‖u‖ / 8)) :
    (7 / 8 : ℝ) * ‖u‖ ≤ ‖z‖ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h := norm_sub_norm_le u z
  rw [norm_sub_rev u z] at h
  linarith

private lemma ball_far (c u z : ℂ) (hu : 1024 * (1 + ‖c‖) + 1024 ≤ ‖u‖)
    (hz : z ∈ Metric.closedBall u (‖u‖ / 8)) :
    64 * (1 + ‖c‖) + 64 ≤ ‖z‖ := by
  have ht : (1024 : ℝ) ≤ ‖u‖ := hu_ge c u hu
  have hz7 := ball_norm_ge hz
  have hj0 : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hj : ‖c‖ ≤ ‖u‖ / 1024 := by linarith
  nlinarith

/-! ### Bounds for the Böttcher series on the ball -/

/-- `‖B_c z‖ ≤ (64/49) K / ‖u‖²` on the ball, with `K = ‖c‖² + 3‖c‖ + 1`. -/
private lemma series_le_u (c u z : ℂ) (hu : 1024 * (1 + ‖c‖) + 1024 ≤ ‖u‖)
    (hz : z ∈ Metric.closedBall u (‖u‖ / 8)) :
    ‖Work.Bottcher.bottcherSeries c z‖ ≤
      (64 / 49 : ℝ) * ((‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖ ^ 2) := by
  have h1 := Work.Bottcher.Inverse.norm_bottcherSeries_le_far c z (ball_far c u z hu hz)
  have hz7 := ball_norm_ge hz
  have hu0 : (0 : ℝ) < ‖u‖ := hu_pos c u hu
  have hz0 : (0 : ℝ) < ‖z‖ := by linarith
  have hK0 : (0 : ℝ) ≤ ‖c‖ ^ 2 + 3 * ‖c‖ + 1 := by positivity
  have hzu : (49 / 64 : ℝ) * ‖u‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (7 / 8) * ‖u‖) hz7 2
    nlinarith [h, hu0]
  refine le_trans h1 ?_
  rw [show (64 / 49 : ℝ) * ((‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖ ^ 2)
        = 64 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / (49 * ‖u‖ ^ 2) by ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hzu, hK0]

/-- `‖B_c z‖ ≤ 1/2` on the ball. -/
private lemma series_le_half (c u z : ℂ) (hu : 1024 * (1 + ‖c‖) + 1024 ≤ ‖u‖)
    (hz : z ∈ Metric.closedBall u (‖u‖ / 8)) :
    ‖Work.Bottcher.bottcherSeries c z‖ ≤ 1 / 2 := by
  have hu0 : (0 : ℝ) < ‖u‖ := hu_pos c u hu
  refine le_trans (series_le_u c u z hu hz) ?_
  rw [show (64 / 49 : ℝ) * ((‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖ ^ 2)
        = 64 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / (49 * ‖u‖ ^ 2) by ring]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 49 * ‖u‖ ^ 2)]
  have h := key_1024 c u hu
  nlinarith [h]

/-! ### Elementary estimates for `exp` -/

private lemma norm_exp_neg_sub_one_le {a : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖Complex.exp (-a) - 1‖ ≤ 2 * ‖a‖ := by
  have h := Complex.norm_exp_sub_one_le (x := -a) (by rwa [norm_neg])
  rwa [norm_neg] at h

/-- Lipschitz estimate for `z ↦ exp (-z)` where the exponents are bounded by `1/2`. -/
private lemma norm_exp_neg_sub_le {a b : ℂ} (ha : ‖a‖ ≤ 1 / 2) (hb : ‖b‖ ≤ 1 / 2) :
    ‖Complex.exp (-a) - Complex.exp (-b)‖ ≤ 4 * ‖a - b‖ := by
  have key : Complex.exp (-a) - Complex.exp (-b)
      = Complex.exp (-b) * (Complex.exp (b - a) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    ring_nf
  have hba : ‖b - a‖ ≤ 1 := by
    have h := norm_sub_le b a
    have ha0 := norm_nonneg a
    have hb0 := norm_nonneg b
    linarith
  have h1 : ‖Complex.exp (-b)‖ ≤ 2 := by
    rw [Complex.norm_exp]
    have hre : (-b).re = -b.re := Complex.neg_re b
    rw [hre]
    have hb' : -b.re ≤ ‖b‖ := le_trans (neg_le_abs b.re) (Complex.abs_re_le_norm b)
    calc Real.exp (-b.re) ≤ Real.exp ‖b‖ := Real.exp_le_exp.mpr hb'
      _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hb
      _ ≤ 2 := by
          rw [← Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)]
          linarith [Real.log_two_gt_d9]
  have h2 : ‖Complex.exp (b - a) - 1‖ ≤ 2 * ‖b - a‖ := Complex.norm_exp_sub_one_le hba
  rw [key, norm_mul]
  calc ‖Complex.exp (-b)‖ * ‖Complex.exp (b - a) - 1‖
      ≤ 2 * (2 * ‖b - a‖) := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ = 4 * ‖a - b‖ := by rw [norm_sub_rev b a]; ring

/-! ### The fixed point map `z ↦ u · exp (-(B_c z))` -/

/-- `‖u · exp (-(B_c z)) - u‖ ≤ 128 K / (49 ‖u‖)` on the ball. -/
private lemma G_sub_le (c u z : ℂ) (hu : 1024 * (1 + ‖c‖) + 1024 ≤ ‖u‖)
    (hz : z ∈ Metric.closedBall u (‖u‖ / 8)) :
    ‖u * Complex.exp (-(Work.Bottcher.bottcherSeries c z)) - u‖
      ≤ 128 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / (49 * ‖u‖) := by
  have hβ1 : ‖Work.Bottcher.bottcherSeries c z‖ ≤ 1 := by
    have h := series_le_half c u z hu hz
    linarith
  have hexp : ‖Complex.exp (-(Work.Bottcher.bottcherSeries c z)) - 1‖
      ≤ 2 * ‖Work.Bottcher.bottcherSeries c z‖ := norm_exp_neg_sub_one_le hβ1
  have hsub : u * Complex.exp (-(Work.Bottcher.bottcherSeries c z)) - u
      = u * (Complex.exp (-(Work.Bottcher.bottcherSeries c z)) - 1) := by ring
  rw [hsub, norm_mul]
  have hu0 : (0 : ℝ) < ‖u‖ := hu_pos c u hu
  calc ‖u‖ * ‖Complex.exp (-(Work.Bottcher.bottcherSeries c z)) - 1‖
      ≤ ‖u‖ * (2 * ((64 / 49 : ℝ) * ((‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖ ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg u)
        have h := series_le_u c u z hu hz
        linarith [hexp]
    _ = 128 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / (49 * ‖u‖) := by
        field_simp
        ring

/-- The map `z ↦ u · exp (-(B_c z))` is `1/2`-Lipschitz on the ball. -/
private lemma G_lipschitz (c u : ℂ) (hu : 1024 * (1 + ‖c‖) + 1024 ≤ ‖u‖) :
    ∀ x y : ℂ, x ∈ Metric.closedBall u (‖u‖ / 8) → y ∈ Metric.closedBall u (‖u‖ / 8) →
      ‖u * Complex.exp (-(Work.Bottcher.bottcherSeries c x)) -
        u * Complex.exp (-(Work.Bottcher.bottcherSeries c y))‖ ≤ (1 / 2) * ‖x - y‖ := by
  intro x y hx hy
  have hj0 : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hβx := series_le_half c u x hu hx
  have hβy := series_le_half c u y hu hy
  have hexp := norm_exp_neg_sub_le hβx hβy
  have hLip := Work.Bottcher.Inverse.norm_bottcherSeries_sub_le c u (by linarith) hx hy
  have hsub : u * Complex.exp (-(Work.Bottcher.bottcherSeries c x)) -
        u * Complex.exp (-(Work.Bottcher.bottcherSeries c y))
      = u * (Complex.exp (-(Work.Bottcher.bottcherSeries c x)) -
        Complex.exp (-(Work.Bottcher.bottcherSeries c y))) := by ring
  rw [hsub, norm_mul]
  have hu0 : (0 : ℝ) < ‖u‖ := hu_pos c u hu
  have hxy0 : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
  have hkey : 512 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖ ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖u‖ ^ 2)]
    have h := key_1024 c u hu
    nlinarith [h]
  calc ‖u‖ * ‖Complex.exp (-(Work.Bottcher.bottcherSeries c x)) -
          Complex.exp (-(Work.Bottcher.bottcherSeries c y))‖
      ≤ ‖u‖ * (4 * (128 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖ ^ 3 * ‖x - y‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg u)
        linarith [hexp, hLip]
    _ = 512 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖ ^ 2 * ‖x - y‖ := by
        field_simp
        ring
    _ ≤ (1 / 2) * ‖x - y‖ := by
        nlinarith [hkey, hxy0]

/-! ### `bottcher c z = u` is equivalent to being a fixed point -/

private lemma bottcher_eq_iff (c z u : ℂ) :
    Work.Bottcher.bottcher c z = u ↔
      z = u * Complex.exp (-(Work.Bottcher.bottcherSeries c z)) := by
  constructor
  · intro h
    have h1 : z * Complex.exp (Work.Bottcher.bottcherSeries c z) = u := h
    calc z = z * 1 := (mul_one z).symm
      _ = z * (Complex.exp (Work.Bottcher.bottcherSeries c z) *
              Complex.exp (-(Work.Bottcher.bottcherSeries c z))) := by
            rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      _ = (z * Complex.exp (Work.Bottcher.bottcherSeries c z)) *
              Complex.exp (-(Work.Bottcher.bottcherSeries c z)) := by ring
      _ = u * Complex.exp (-(Work.Bottcher.bottcherSeries c z)) := by rw [h1]
  · intro h
    have h1 := congrArg (fun y => y * Complex.exp (Work.Bottcher.bottcherSeries c z)) h
    calc Work.Bottcher.bottcher c z = z * Complex.exp (Work.Bottcher.bottcherSeries c z) := rfl
      _ = (u * Complex.exp (-(Work.Bottcher.bottcherSeries c z))) *
              Complex.exp (Work.Bottcher.bottcherSeries c z) := h1
      _ = u * (Complex.exp (-(Work.Bottcher.bottcherSeries c z)) *
              Complex.exp (Work.Bottcher.bottcherSeries c z)) := by ring
      _ = u * 1 := by rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
      _ = u := mul_one u

/-! ### The far inverse branch -/

theorem exists_farBottcher_inverse (c u : ℂ) (hu : 1024 * (1 + ‖c‖) + 1024 ≤ ‖u‖) :
    ∃ z : ℂ, z ∈ Metric.closedBall u (‖u‖ / 8) ∧ Work.Bottcher.bottcher c z = u ∧
      ‖z - u‖ ≤ 4 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖ ∧
      ∀ x : ℂ, x ∈ Metric.closedBall u (‖u‖ / 8) → Work.Bottcher.bottcher c x = u → x = z := by
  have hu0 : (0 : ℝ) < ‖u‖ := hu_pos c u hu
  -- the map `F` maps the ball into itself ...
  have hmap : Set.MapsTo (fun z => u * Complex.exp (-(Work.Bottcher.bottcherSeries c z)))
      (Metric.closedBall u (‖u‖ / 8)) (Metric.closedBall u (‖u‖ / 8)) := by
    intro x hx
    have h1 := G_sub_le c u x hu hx
    have h2 : 128 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / (49 * ‖u‖) ≤ ‖u‖ / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 8)]
      have h := key_1024 c u hu
      nlinarith [h]
    rw [Metric.mem_closedBall, dist_eq_norm]
    linarith
  -- ... and is a strict contraction there
  have hcontr : ContractingWith (1 / 2 : ℝ≥0)
      (Set.MapsTo.restrict (fun z => u * Complex.exp (-(Work.Bottcher.bottcherSeries c z)))
        (Metric.closedBall u (‖u‖ / 8)) (Metric.closedBall u (‖u‖ / 8)) hmap) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simp only [Set.MapsTo.restrict, Subtype.map, Subtype.dist_eq]
    rw [dist_eq_norm, dist_eq_norm]
    have hxy := G_lipschitz c u hu (x : ℂ) (y : ℂ) x.2 y.2
    have hc : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
    rw [hc]
    linarith [hxy]
  obtain ⟨z, hzmem, hzfix, -⟩ := hcontr.exists_fixedPoint'
    (Metric.isClosed_closedBall.isComplete) hmap
    (x := u) (Metric.mem_closedBall_self (x := u) (ε := ‖u‖ / 8) (by positivity))
    (edist_ne_top _ _)
  have hfix : z = u * Complex.exp (-(Work.Bottcher.bottcherSeries c z)) := hzfix.symm
  refine ⟨z, hzmem, ?_, ?_, ?_⟩
  · exact (bottcher_eq_iff c z u).mpr hfix
  · -- the distance estimate
    calc ‖z - u‖ = ‖u * Complex.exp (-(Work.Bottcher.bottcherSeries c z)) - u‖ :=
          congrArg (fun w => ‖w - u‖) hfix
      _ ≤ 128 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / (49 * ‖u‖) := G_sub_le c u z hu hzmem
      _ ≤ 4 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖ := by
          have hK0 : (0 : ℝ) ≤ ‖c‖ ^ 2 + 3 * ‖c‖ + 1 := by positivity
          have h49 : (128 / 49 : ℝ) ≤ 4 := by norm_num
          have hsplit : 128 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / (49 * ‖u‖)
              = (128 / 49) * ((‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖) := by ring
          rw [hsplit]
          calc (128 / 49) * ((‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖)
              ≤ 4 * ((‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖) :=
                mul_le_mul_of_nonneg_right h49 (by positivity)
            _ = 4 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖u‖ := by ring
  · -- uniqueness
    intro x hx hbx
    have hxf : x = u * Complex.exp (-(Work.Bottcher.bottcherSeries c x)) :=
      (bottcher_eq_iff c x u).mp hbx
    have hfx : u * Complex.exp (-(Work.Bottcher.bottcherSeries c x)) = x := hxf.symm
    have hfz : u * Complex.exp (-(Work.Bottcher.bottcherSeries c z)) = z := hfix.symm
    have hl := G_lipschitz c u hu x z hx hzmem
    have hle : ‖x - z‖ ≤ (1 / 2) * ‖x - z‖ := by
      have heq : ‖u * Complex.exp (-(Work.Bottcher.bottcherSeries c x)) -
            u * Complex.exp (-(Work.Bottcher.bottcherSeries c z))‖ = ‖x - z‖ := by
        rw [hfx, hfz]
      rw [heq] at hl
      exact hl
    have h0 : (0 : ℝ) ≤ ‖x - z‖ := norm_nonneg _
    have hzero : ‖x - z‖ = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end

end Work.Bottcher.Inverse
