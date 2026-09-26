import Mathlib
import Submission.Work.CoreTopology.Disk

/-!
# The diameter bound for essential curves and Pardon's `positive_scale`

This file proves `Work.CoreTopology.positive_scale`: a closed ball of `ℝ³` that
contains an essential closed curve of the standard torus of revolution (major radius
`2`, minor radius `1`) has radius at least `1`.

The mathematical content is the **diameter bound for essential curves**: every
closed curve on the torus whose lift has nonzero winding vector has two points at
Euclidean distance at least `2`.  The two cases are:

* a nonzero *first* winding component `a`: the longitude parameter `Θ` of a lift
  advances by `|a|·2π ≥ 2π` over one period, so by the intermediate value theorem it
  takes two values differing by `π` (with either sign).  The corresponding points of
  the torus have opposite `xy`-projections of lengths `2 + cos φ₁` and `2 + cos φ₂`,
  hence are at distance at least `4 + cos φ₁ + cos φ₂ ≥ 2`;

* a nonzero *second* component `b`: the meridian parameter `Φ` sweeps an interval of
  length `≥ 2π`, hence takes values with `sin = 1` and with `sin = -1`.  The
  corresponding points of the torus have heights `±1`, so their distance is `≥ 2`.

Both estimates are proved below by direct computation with the components of
`Work.Core.torusMap`.  The final theorem `positive_scale` then combines the diameter
bound with the triangle inequality: if `γ` lies in the ball of radius `r` about `x`
then `2 ≤ dist (γ t₁) (γ t₂) ≤ 2r`, so `1 ≤ r`.

The auxiliary lemmas are collected in the namespace `Work.CoreTopology.PositiveScaleAux`
so as not to interfere with other developments in `Work.CoreTopology`.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.CoreTopology

namespace PositiveScaleAux

/-! ## Two elementary Euclidean-distance estimates for the standard torus -/

/-- The square of the Euclidean distance in `ℝ³` is the sum of the squares of the
three coordinate differences. -/
lemma dist_sq_components (p q : R3) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2 := by
  rw [dist_eq_norm]
  rw [PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 3 => ℝ) (p - q)]
  simp only [PiLp.sub_apply]
  rw [Fin.sum_univ_three]
  norm_num

/-- If the square of the distance between two points of `ℝ³` is at least `4` then
their distance is at least `2`. -/
lemma two_le_dist_of_four_le_sq (p q : R3) (h4 : (4 : ℝ) ≤ dist p q ^ 2) :
    2 ≤ dist p q := by
  have hd : (0 : ℝ) ≤ dist p q := dist_nonneg
  have h4' : (2 : ℝ) ^ 2 ≤ dist p q ^ 2 := by norm_num; exact h4
  have := (sq_le_sq.mp h4')
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_of_nonneg hd] at this
  exact this

/-- **First estimate.**  Two points of the standard torus whose longitude parameters
differ by `π` (i.e. have opposite cosine and sine) are at distance at least `2`:
their `xy`-projections are opposite multiples of the same unit vector, with lengths
`2 + cos φ₁` and `2 + cos φ₂ ≥ 1`, so the `xy`-part of the difference has length
`4 + cos φ₁ + cos φ₂ ≥ 2`. -/
lemma torusMap_antipodal_dist (θ₁ φ₁ θ₂ φ₂ : ℝ)
    (hcos : Real.cos θ₂ = -Real.cos θ₁) (hsin : Real.sin θ₂ = -Real.sin θ₁) :
    2 ≤ dist (Work.Core.torusMap θ₁ φ₁) (Work.Core.torusMap θ₂ φ₂) := by
  refine two_le_dist_of_four_le_sq _ _ ?_
  rw [dist_sq_components]
  have e0 : (Work.Core.torusMap θ₁ φ₁) 0 - (Work.Core.torusMap θ₂ φ₂) 0
      = (4 + Real.cos φ₁ + Real.cos φ₂) * Real.cos θ₁ := by
    rw [Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_zero, hcos]; ring
  have e1 : (Work.Core.torusMap θ₁ φ₁) 1 - (Work.Core.torusMap θ₂ φ₂) 1
      = (4 + Real.cos φ₁ + Real.cos φ₂) * Real.sin θ₁ := by
    rw [Work.Core.torusMap_apply_one, Work.Core.torusMap_apply_one, hsin]; ring
  have e2 : (Work.Core.torusMap θ₁ φ₁) 2 - (Work.Core.torusMap θ₂ φ₂) 2
      = Real.sin φ₁ - Real.sin φ₂ := by
    rw [Work.Core.torusMap_apply_two, Work.Core.torusMap_apply_two]
  rw [e0, e1, e2]
  set A : ℝ := 4 + Real.cos φ₁ + Real.cos φ₂ with hA
  have hAge : (2 : ℝ) ≤ A := by
    rw [hA]; linarith [Real.neg_one_le_cos φ₁, Real.neg_one_le_cos φ₂]
  have htrig' : Real.cos θ₁ ^ 2 + Real.sin θ₁ ^ 2 = 1 := by
    linarith [Real.sin_sq_add_cos_sq θ₁]
  have hmain : (4 : ℝ) ≤ A ^ 2 := by nlinarith [hAge, sq_nonneg A]
  have key : (A * Real.cos θ₁) ^ 2 + (A * Real.sin θ₁) ^ 2 = A ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, htrig', mul_one]
  rw [key]
  nlinarith [hmain, sq_nonneg (Real.sin φ₁ - Real.sin φ₂)]

/-- **Second estimate.**  Two points of the standard torus at heights `1` and `-1`
(meridian parameters with `sin = 1` and `sin = -1`) are at distance at least `2`,
because the third coordinate alone already differs by `2`. -/
lemma torusMap_height_dist (θ₁ φ₁ θ₂ φ₂ : ℝ)
    (h₁ : Real.sin φ₁ = 1) (h₂ : Real.sin φ₂ = -1) :
    2 ≤ dist (Work.Core.torusMap θ₁ φ₁) (Work.Core.torusMap θ₂ φ₂) := by
  rw [dist_eq_norm]
  have hle := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin 3 => ℝ)
    (Work.Core.torusMap θ₁ φ₁ - Work.Core.torusMap θ₂ φ₂) (2 : Fin 3)
  rw [PiLp.sub_apply, Work.Core.torusMap_apply_two, Work.Core.torusMap_apply_two,
    Real.norm_eq_abs] at hle
  rw [h₁, h₂] at hle
  norm_num at hle
  exact hle

/-! ## Sweeping the meridian parameter: `sin` takes both extreme values -/

/-- An interval of length at least `2π` contains a point where `sin` equals `1`. -/
lemma exists_sin_eq_one_Icc {u v : ℝ} (h : u + 2 * Real.pi ≤ v) :
    ∃ s ∈ Set.Icc u v, Real.sin s = 1 := by
  refine ⟨Real.pi / 2 + ((⌈(u - Real.pi / 2) / (2 * Real.pi)⌉ : ℤ) : ℝ) * (2 * Real.pi),
    ⟨?_, ?_⟩, ?_⟩
  · have h1 : (u - Real.pi / 2) / (2 * Real.pi) ≤
        ((⌈(u - Real.pi / 2) / (2 * Real.pi)⌉ : ℤ) : ℝ) := Int.le_ceil _
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    have h2 := (div_le_iff₀ hp).mp h1
    linarith
  · have h1 : ((⌈(u - Real.pi / 2) / (2 * Real.pi)⌉ : ℤ) : ℝ) <
        (u - Real.pi / 2) / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    have hmul := mul_lt_mul_of_pos_right h1 hp
    have hsimp : ((u - Real.pi / 2) / (2 * Real.pi) + 1) * (2 * Real.pi)
        = (u - Real.pi / 2) + 2 * Real.pi := by
      field_simp
    rw [hsimp] at hmul
    linarith
  · rw [Real.sin_add_int_mul_two_pi, Real.sin_pi_div_two]

/-- An interval of length at least `2π` contains a point where `sin` equals `-1`. -/
lemma exists_sin_eq_neg_one_Icc {u v : ℝ} (h : u + 2 * Real.pi ≤ v) :
    ∃ s ∈ Set.Icc u v, Real.sin s = -1 := by
  refine ⟨-Real.pi / 2 + ((⌈(u + Real.pi / 2) / (2 * Real.pi)⌉ : ℤ) : ℝ) * (2 * Real.pi),
    ⟨?_, ?_⟩, ?_⟩
  · have h1 : (u + Real.pi / 2) / (2 * Real.pi) ≤
        ((⌈(u + Real.pi / 2) / (2 * Real.pi)⌉ : ℤ) : ℝ) := Int.le_ceil _
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    have h2 := (div_le_iff₀ hp).mp h1
    linarith
  · have h1 : ((⌈(u + Real.pi / 2) / (2 * Real.pi)⌉ : ℤ) : ℝ) <
        (u + Real.pi / 2) / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    have hmul := mul_lt_mul_of_pos_right h1 hp
    have hsimp : ((u + Real.pi / 2) / (2 * Real.pi) + 1) * (2 * Real.pi)
        = (u + Real.pi / 2) + 2 * Real.pi := by
      field_simp
    rw [hsimp] at hmul
    linarith
  · rw [Real.sin_add_int_mul_two_pi]
    have hre : -Real.pi / 2 = -(Real.pi / 2) := by ring
    rw [hre, Real.sin_neg, Real.sin_pi_div_two]

/-- **Sweeping the meridian parameter.**  If a continuous `Φ` advances by a nonzero
integer multiple of `2π` over one period, then it takes values with `sin = 1` and
with `sin = -1` (the interval it sweeps over has length at least `2π`). -/
lemma exists_sin_extremes (Φ : ℝ → ℝ) (hcont : Continuous Φ) (b : ℤ) (hb : b ≠ 0)
    (hper : Φ (2 * Real.pi) = Φ 0 + (b : ℝ) * (2 * Real.pi)) :
    ∃ t₁ t₂ : ℝ, Real.sin (Φ t₁) = 1 ∧ Real.sin (Φ t₂) = -1 := by
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · have hb1 : b ≤ -1 := by omega
    have hcast : (b : ℝ) ≤ -1 := by exact_mod_cast hb1
    have hlen : Φ (2 * Real.pi) + 2 * Real.pi ≤ Φ 0 := by
      rw [hper]; nlinarith [Real.pi_pos]
    obtain ⟨s, hs, hsin⟩ := exists_sin_eq_one_Icc hlen
    obtain ⟨s', hs', hsin'⟩ := exists_sin_eq_neg_one_Icc hlen
    have hsub := intermediate_value_univ (2 * Real.pi) 0 hcont
    obtain ⟨t₁, ht₁⟩ := hsub hs
    obtain ⟨t₂, ht₂⟩ := hsub hs'
    exact ⟨t₁, t₂, by rw [ht₁, hsin], by rw [ht₂, hsin']⟩
  · have hb1 : (1 : ℤ) ≤ b := by omega
    have hcast : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    have hlen : Φ 0 + 2 * Real.pi ≤ Φ (2 * Real.pi) := by
      rw [hper]; nlinarith [Real.pi_pos]
    obtain ⟨s, hs, hsin⟩ := exists_sin_eq_one_Icc hlen
    obtain ⟨s', hs', hsin'⟩ := exists_sin_eq_neg_one_Icc hlen
    have hsub := intermediate_value_univ 0 (2 * Real.pi) hcont
    obtain ⟨t₁, ht₁⟩ := hsub hs
    obtain ⟨t₂, ht₂⟩ := hsub hs'
    exact ⟨t₁, t₂, by rw [ht₁, hsin], by rw [ht₂, hsin']⟩

/-! ## Sweeping the longitude parameter: an antipodal pair -/

/-- **Sweeping the longitude parameter.**  If a continuous `Θ` advances by a nonzero
integer multiple of `2π` over one period, then it takes a value equal to `Θ 0 + π` or
to `Θ 0 - π`: the interval it sweeps has length at least `2π`, in particular at least
`π` in the direction in which it goes. -/
lemma exists_antipodal_theta (Θ : ℝ → ℝ) (hcont : Continuous Θ) (a : ℤ) (ha : a ≠ 0)
    (hper : Θ (2 * Real.pi) = Θ 0 + (a : ℝ) * (2 * Real.pi)) :
    ∃ t : ℝ, Θ t = Θ 0 + Real.pi ∨ Θ t = Θ 0 - Real.pi := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have ha1 : a ≤ -1 := by omega
    have hcast : (a : ℝ) ≤ -1 := by exact_mod_cast ha1
    have hsub := intermediate_value_univ (2 * Real.pi) 0 hcont
    have hmem : Θ 0 - Real.pi ∈ Set.Icc (Θ (2 * Real.pi)) (Θ 0) := by
      refine ⟨?_, by linarith [Real.pi_pos]⟩
      rw [hper]; nlinarith [Real.pi_pos]
    obtain ⟨t, ht⟩ := hsub hmem
    exact ⟨t, Or.inr ht⟩
  · have ha1 : (1 : ℤ) ≤ a := by omega
    have hcast : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    have hsub := intermediate_value_univ 0 (2 * Real.pi) hcont
    have hmem : Θ 0 + Real.pi ∈ Set.Icc (Θ 0) (Θ (2 * Real.pi)) := by
      refine ⟨by linarith [Real.pi_pos], ?_⟩
      rw [hper]; nlinarith [Real.pi_pos]
    obtain ⟨t, ht⟩ := hsub hmem
    exact ⟨t, Or.inl ht⟩

/-! ## The diameter bound for essential curves -/

/-- **Diameter bound for essential curves on the standard torus.**  A closed curve on
the standard torus whose lift has nonzero winding vector has two points at Euclidean
distance at least `2`.

If the first winding component is nonzero, the longitude parameter of the lift takes
two values differing by `π`, and the corresponding points of the torus have opposite
`xy`-projections and so are at distance `≥ 2`; if the second component is nonzero, the
meridian parameter takes values with `sin = ±1`, and the two corresponding heights
differ by `2`. -/
theorem diameter_ge_two_of_lift (γ : ClosedCurve standard) (L : LiftOf standard γ)
    (hw : L.winding ≠ (0, 0)) : ∃ t₁ t₂ : ℝ, 2 ≤ dist (γ t₁) (γ t₂) := by
  have hspec := L.winding_spec
  rcases eq_or_ne L.winding.1 0 with h1 | h1
  · -- the meridian (second) component is nonzero: use the heights `±1`
    have h2 : L.winding.2 ≠ 0 := by
      intro h2
      exact hw (Prod.ext h1 h2)
    obtain ⟨t₁, t₂, hs₁, hs₂⟩ :=
      exists_sin_extremes L.Φ L.contΦ L.winding.2 h2 hspec.2
    refine ⟨t₁, t₂, ?_⟩
    rw [← L.lifts t₁, ← L.lifts t₂]
    exact torusMap_height_dist _ _ _ _ hs₁ hs₂
  · -- the longitude (first) component is nonzero: use the antipodal pair
    obtain ⟨t, ht | ht⟩ := exists_antipodal_theta L.Θ L.contΘ L.winding.1 h1 hspec.1
    · refine ⟨t, 0, ?_⟩
      rw [← L.lifts t, ← L.lifts 0]
      refine torusMap_antipodal_dist _ _ _ _ ?_ ?_
      · rw [ht, Real.cos_add_pi]; ring
      · rw [ht, Real.sin_add_pi]; ring
    · refine ⟨t, 0, ?_⟩
      rw [← L.lifts t, ← L.lifts 0]
      refine torusMap_antipodal_dist _ _ _ _ ?_ ?_
      · rw [ht, Real.cos_sub_pi]; ring
      · rw [ht, Real.sin_sub_pi]; ring

end PositiveScaleAux

/-- **Pardon's Lemma 4 (`positive_scale`) for the standard torus.** There is a positive lower bound for the radius of a ball that can contain an essential loop of the torus: if a closed ball of radius `r` of `ℝ³` contains a closed curve `γ` on the standard torus whose winding vector is nonzero (i.e. `γ` is essential), then `r ≥ 1`. Consequently the set of such radii has positive infimum `≥ 1`. The proof uses the diameter bound for essential curves: a nonzero first winding component makes the lifted longitude parameter sweep an interval of length `≥ 2π`, so `γ` has two points with opposite projections to the `xy`-plane at distance `≥ 4 + cos φ₁ + cos φ₂ ≥ 2`; a nonzero second component makes the lifted height `sin Φ` take the values `±1`, so again two points are at distance `≥ 2`. -/
theorem positive_scale (x : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (γ : ClosedCurve standard)
    (hess : IsEssential standard γ) (h : ∀ t : ℝ, γ t ∈ Metric.closedBall x r) :
    1 ≤ r := by
  obtain ⟨L, hw⟩ := hess
  obtain ⟨t₁, t₂, hdiam⟩ := PositiveScaleAux.diameter_ge_two_of_lift γ L hw
  have h₁ : dist (γ t₁) x ≤ r := Metric.mem_closedBall.mp (h t₁)
  have h₂ : dist (γ t₂) x ≤ r := Metric.mem_closedBall.mp (h t₂)
  have htri : dist (γ t₁) (γ t₂) ≤ dist (γ t₁) x + dist (γ t₂) x := by
    calc dist (γ t₁) (γ t₂) ≤ dist (γ t₁) x + dist x (γ t₂) := dist_triangle _ _ _
      _ = dist (γ t₁) x + dist (γ t₂) x := by rw [dist_comm x (γ t₂)]
  linarith

end Work.CoreTopology
