import Mathlib
import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Bubble.windingOf_standard_fst_eq_zero_of_y_ne
import Submission.Work.BoxShrink.Bubble.Equivalence
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_iff_realizedWindings

/-!
# The counterexample to the field `BubbleInput.bubble`: the formal proof

This file proves `Work.BoxShrink.Bubble.standard_counterexample`: with the standard torus, the
coordinate permutation `σ = Equiv.swap 1 2` (so that the cut plane is `{y = 0}`), `c = 0`,
`u = 0`, `s = 5/2`, the region inside the box contains an essential loop (the longitude circle
`{z = -1}`, of winding `(1,0)`) which is *not* realised away from the slicing plane, so
`SlicePushOff` fails; and neither the box sphere `∂PBox` nor the slice carries an essential loop,
so both hypotheses of the field hold.

The file is organised as:

* `cex_swap_zero/one/two`: the values of `σ` on `0, 1, 2`;
* `cex_boxNorm`, `cex_mem_PBox`: the box norm and the box for this `σ`;
* `cex_rpow_two_thirds_gt` and the coordinate bounds of `torusMap`;
* `cex_boxNorm_eq_torusMap`, `cex_boxNorm_lt_torusMap` (and their versions for an arbitrary point
  of the carrier): the box norm of a point of the standard torus is controlled by its `x`
  coordinate (`|x|`), the other two coordinates being automatically small enough;
* the general "periodic confinement" lemmas
  `exists_mem_periodic_Icc`, `abs_sub_lt_of_forall_notMem_Icc`,
  `abs_sub_lt_pi_of_cos_ne_zero`, `abs_sub_lt_four_thirds_pi_of_cos_lt_half`, and the integer
  winding lemma `int_eq_zero_of_abs_mul_two_pi_lt`;
* `cex_longitudeCurve_mem`, `cex_windingOf_longitudeCurve`: the longitude circle `{z = -1}`
  lies in the box and has winding `(1,0)`;
* `cex_onezero_not_mem_realizedWindings`: no loop avoiding the plane `{y = 0}` realises `(1,0)`
  (this is `windingOf_standard_fst_eq_zero_of_y_ne`);
* the three parts of the theorem.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

/-! ## The permutation and the concrete box -/

lemma cex_swap_zero : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
lemma cex_swap_one : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
lemma cex_swap_two : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide

/-- The box norm for the permutation `swap 1 2`: only the `x` coordinate and the (harmless)
`z`- and `y`-coordinates appear. -/
lemma cex_boxNorm (y : R3) :
    Submission.boxNorm 0 (Equiv.swap (1 : Fin 3) 2) y =
      max (max |y 0| (|y 2| / (2 : ℝ) ^ (1 / 3 : ℝ))) (|y 1| / (2 : ℝ) ^ (2 / 3 : ℝ)) := by
  rw [Submission.boxNorm, cex_swap_zero, cex_swap_one, cex_swap_two, Submission.boxSide_zero,
    Submission.boxSide_one, Submission.boxSide_two]
  simp

/-- The box `PBox s 0 (swap 1 2)` in coordinates. -/
lemma cex_mem_PBox (s : ℝ) (y : R3) :
    y ∈ Submission.PBox s 0 (Equiv.swap (1 : Fin 3) 2) ↔
      |y 0| < s ∧ |y 2| < (2 : ℝ) ^ (1 / 3 : ℝ) * s ∧
        |y 1| < (2 : ℝ) ^ (2 / 3 : ℝ) * s := by
  rw [Submission.mem_PBox]
  constructor
  · intro h
    exact ⟨by simpa [cex_swap_zero] using h 0, by simpa [cex_swap_one] using h 1,
      by simpa [cex_swap_two] using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa [cex_swap_zero] using h0
    · simpa [cex_swap_one] using h1
    · simpa [cex_swap_two] using h2

/-! ## Numeric bounds -/

/-- `6/5 < 2^{2/3}`: the `y`-direction of the box of size `5/2` is longer than the diameter of
the torus in that direction. -/
lemma cex_rpow_two_thirds_gt : (6 / 5 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := by
  have hcube : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (2 / 3 : ℝ)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  by_contra h
  push Not at h
  have h4 : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 ≤ (6 / 5 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h 3
  rw [hcube] at h4
  norm_num at h4

/-! ## Coordinate bounds on the standard torus -/

lemma cex_torusMap_bound_zero (θ φ : ℝ) : |(Work.Core.torusMap θ φ) 0| ≤ 3 := by
  rw [Work.CoreTopology.torusMap_apply_zero, abs_mul]
  have h1 : |2 + Real.cos φ| ≤ 3 := by
    rw [abs_of_nonneg (by linarith [Real.neg_one_le_cos φ])]
    linarith [Real.cos_le_one φ]
  calc |2 + Real.cos φ| * |Real.cos θ| ≤ 3 * 1 :=
        mul_le_mul h1 (Real.abs_cos_le_one θ) (abs_nonneg _) (by norm_num)
    _ = 3 := by ring

lemma cex_torusMap_bound_one (θ φ : ℝ) : |(Work.Core.torusMap θ φ) 1| ≤ 3 := by
  rw [Work.CoreTopology.torusMap_apply_one, abs_mul]
  have h1 : |2 + Real.cos φ| ≤ 3 := by
    rw [abs_of_nonneg (by linarith [Real.neg_one_le_cos φ])]
    linarith [Real.cos_le_one φ]
  calc |2 + Real.cos φ| * |Real.sin θ| ≤ 3 * 1 :=
        mul_le_mul h1 (Real.abs_sin_le_one θ) (abs_nonneg _) (by norm_num)
    _ = 3 := by ring

lemma cex_torusMap_bound_two (θ φ : ℝ) : |(Work.Core.torusMap θ φ) 2| ≤ 1 := by
  rw [Work.CoreTopology.torusMap_apply_two]
  exact Real.abs_sin_le_one φ

/-- The two "harmless" coordinates of a point of the standard torus are automatically below the
box thresholds `(5/2)·2^{1/3}` and `(5/2)·2^{2/3}`. -/
lemma cex_coord_two_lt (θ φ : ℝ) :
    |(Work.Core.torusMap θ φ) 2| / (2 : ℝ) ^ (1 / 3 : ℝ) < 5 / 2 := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) := by positivity
  rw [div_lt_iff₀ hp]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / 3 : ℝ) := Submission.one_le_rpow_third
  have hb := cex_torusMap_bound_two θ φ
  nlinarith

lemma cex_coord_one_lt (θ φ : ℝ) :
    |(Work.Core.torusMap θ φ) 1| / (2 : ℝ) ^ (2 / 3 : ℝ) < 5 / 2 := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := by positivity
  rw [div_lt_iff₀ hp]
  have hb := cex_torusMap_bound_one θ φ
  have hgt : (3 : ℝ) < (5 / 2) * (2 : ℝ) ^ (2 / 3 : ℝ) := by
    have h := cex_rpow_two_thirds_gt; nlinarith
  linarith

/-- **The box norm of a point of the standard torus is controlled by `|x|`**: on the torus the
`y`- and `z`-coordinates are automatically inside the box of size `5/2`. -/
lemma cex_boxNorm_lt_torusMap (θ φ : ℝ) :
    Submission.boxNorm 0 (Equiv.swap (1 : Fin 3) 2) (Work.Core.torusMap θ φ) < 5 / 2 ↔
      |(Work.Core.torusMap θ φ) 0| < 5 / 2 := by
  rw [cex_boxNorm, max_lt_iff, max_lt_iff]
  have h2 := cex_coord_two_lt θ φ
  have h1 := cex_coord_one_lt θ φ
  tauto

/-- On the box sphere, a point of the standard torus has `|x| = 5/2`. -/
lemma cex_boxNorm_eq_torusMap (θ φ : ℝ) :
    Submission.boxNorm 0 (Equiv.swap (1 : Fin 3) 2) (Work.Core.torusMap θ φ) = 5 / 2 ↔
      |(Work.Core.torusMap θ φ) 0| = 5 / 2 := by
  rw [cex_boxNorm]
  have h2 := cex_coord_two_lt θ φ
  have h1 := cex_coord_one_lt θ φ
  constructor
  · intro h
    have ha_le : |(Work.Core.torusMap θ φ) 0| ≤ 5 / 2 := by
      rw [← h]; exact le_trans (le_max_left _ _) (le_max_left _ _)
    have ha_ge : 5 / 2 ≤ |(Work.Core.torusMap θ φ) 0| := by
      by_contra hc
      push Not at hc
      have hlt : max (max |(Work.Core.torusMap θ φ) 0|
          (|(Work.Core.torusMap θ φ) 2| / (2 : ℝ) ^ (1 / 3 : ℝ)))
          (|(Work.Core.torusMap θ φ) 1| / (2 : ℝ) ^ (2 / 3 : ℝ)) < 5 / 2 :=
        max_lt (max_lt hc h2) h1
      rw [h] at hlt
      exact lt_irrefl _ hlt
    exact le_antisymm ha_le ha_ge
  · intro h
    rw [h, max_eq_left (le_of_lt h2), max_eq_left (le_of_lt h1)]

/-- The `x` coordinate of a point of the torus lying on the box sphere. -/
lemma cex_fst_eq_of_boxNorm_eq {y : R3} (hy : y ∈ Work.CoreTopology.standard.carrier)
    (h : Submission.boxNorm 0 (Equiv.swap (1 : Fin 3) 2) y = 5 / 2) : |y 0| = 5 / 2 := by
  obtain ⟨θ, φ, hθφ⟩ :=
    (Work.CoreTopology.ParamTorus.mem_carrier_iff Work.CoreTopology.standard y).mp hy
  rw [← hθφ] at h ⊢
  simpa only [Work.CoreTopology.standard_psi] using (cex_boxNorm_eq_torusMap θ φ).mp h

/-- The `x` coordinate of a point of the torus inside the box. -/
lemma cex_fst_lt_of_boxNorm_lt {y : R3} (hy : y ∈ Work.CoreTopology.standard.carrier)
    (h : Submission.boxNorm 0 (Equiv.swap (1 : Fin 3) 2) y < 5 / 2) : |y 0| < 5 / 2 := by
  obtain ⟨θ, φ, hθφ⟩ :=
    (Work.CoreTopology.ParamTorus.mem_carrier_iff Work.CoreTopology.standard y).mp hy
  rw [← hθφ] at h ⊢
  simpa only [Work.CoreTopology.standard_psi] using (cex_boxNorm_lt_torusMap θ φ).mp h

/-! ## Periodicity: a continuous function avoiding a periodic union of intervals is confined -/

/-- **A closed interval of length `L - (b - a)` meets some translate of `[a, b] + Lℤ`.**  This is
the elementary "pigeon-hole" fact behind all confinement statements below: the complement of
`⋃_k [a + kL, b + kL]` is a union of open intervals of length exactly `L - (b - a)`, so a closed
interval of at least that length cannot be contained in one of them. -/
lemma cex_exists_mem_periodic_Icc {L a b p q : ℝ} (hL : 0 < L) (haba : a ≤ b)
    (hab : b - a < L) (hpq : L - (b - a) ≤ q - p) :
    ∃ k : ℤ, (Set.Icc p q ∩ Set.Icc (a + (k : ℝ) * L) (b + (k : ℝ) * L)).Nonempty := by
  have hpq' : p ≤ q := by linarith
  set k : ℤ := ⌈(p - b) / L⌉ with hk
  have hk_le : (p - b) / L ≤ (k : ℝ) := by rw [hk]; exact Int.le_ceil _
  have hk_lt : (k : ℝ) < (p - b) / L + 1 := by rw [hk]; exact Int.ceil_lt_add_one _
  have hb1 : p ≤ b + (k : ℝ) * L := by
    have := (div_le_iff₀ hL).mp hk_le
    linarith
  have hb2 : b + ((k : ℝ) - 1) * L < p := by
    have h1 : (k : ℝ) * L < (p - b) + L := by
      have hmul := mul_lt_mul_of_pos_right hk_lt hL
      rwa [add_mul, div_mul_cancel₀ _ (ne_of_gt hL), one_mul] at hmul
    linarith
  refine ⟨k, max p (a + (k : ℝ) * L), ⟨le_max_left _ _, ?_⟩, ⟨le_max_right _ _, ?_⟩⟩
  · rcases max_cases p (a + (k : ℝ) * L) with h1 | h1
    · rw [h1.1]; exact hpq'
    · rw [h1.1]
      have : a + (k : ℝ) * L = b + ((k : ℝ) - 1) * L + (L - (b - a)) := by ring
      rw [this]; linarith
  · rcases max_cases p (a + (k : ℝ) * L) with h1 | h1
    · rw [h1.1]; linarith
    · rw [h1.1]; linarith

/-- **Periodic confinement.**  A continuous real function which avoids every translate
`[a + kL, b + kL]` takes two values at distance `< L - (b - a)`. -/
lemma cex_abs_sub_lt_of_forall_notMem_Icc {f : ℝ → ℝ} (hf : Continuous f) {L a b : ℝ}
    (hL : 0 < L) (haba : a ≤ b) (hab : b - a < L)
    (h : ∀ t : ℝ, ∀ k : ℤ, f t ∉ Set.Icc (a + (k : ℝ) * L) (b + (k : ℝ) * L)) :
    ∀ s t : ℝ, |f t - f s| < L - (b - a) := by
  intro s t
  rcases le_total (f s) (f t) with hle | hle
  · by_contra hcon
    push Not at hcon
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ f t - f s)] at hcon
    obtain ⟨k, hk⟩ := cex_exists_mem_periodic_Icc hL haba hab (p := f s) (q := f t) hcon
    obtain ⟨z, hz1, hz2⟩ := hk
    obtain ⟨c, hc⟩ := intermediate_value_univ s t hf hz1
    exact h c k (by rw [hc]; exact hz2)
  · have h1 : |f t - f s| = |f s - f t| := abs_sub_comm _ _
    rw [h1]
    have habs : |f s - f t| = f s - f t := abs_of_nonneg (by linarith)
    by_contra hcon
    push Not at hcon
    rw [habs] at hcon
    obtain ⟨k, hk⟩ := cex_exists_mem_periodic_Icc hL haba hab (p := f t) (q := f s) hcon
    obtain ⟨z, hz1, hz2⟩ := hk
    obtain ⟨c, hc⟩ := intermediate_value_univ t s hf hz1
    exact h c k (by rw [hc]; exact hz2)

/-- A continuous function whose cosine never vanishes is confined to an interval of length `π`
(its image lies in a single component of `{cos ≠ 0}`). -/
lemma cex_abs_sub_lt_pi_of_cos_ne_zero {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ t : ℝ, Real.cos (f t) ≠ 0) : ∀ s t : ℝ, |f t - f s| < Real.pi := by
  have hmain : ∀ s t : ℝ, |f t - f s| < Real.pi - (Real.pi / 2 - Real.pi / 2) :=
    cex_abs_sub_lt_of_forall_notMem_Icc (f := f) hf (L := Real.pi) (a := Real.pi / 2)
      (b := Real.pi / 2) Real.pi_pos (le_refl _) (by linarith [Real.pi_pos]) (by
        intro t k hmem
        apply h t
        have heq : f t = Real.pi / 2 + (k : ℝ) * Real.pi := le_antisymm hmem.2 hmem.1
        rw [heq, Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero])
  intro s t
  have := hmain s t
  linarith

/-- A continuous function with `cos < 1/2` is confined to an interval of length `4π/3`. -/
lemma cex_abs_sub_lt_four_thirds_pi_of_cos_lt_half {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ t : ℝ, Real.cos (f t) < 1 / 2) : ∀ s t : ℝ, |f t - f s| < 4 * Real.pi / 3 := by
  have hmain : ∀ s t : ℝ, |f t - f s| < 2 * Real.pi - (Real.pi / 3 - -(Real.pi / 3)) :=
    cex_abs_sub_lt_of_forall_notMem_Icc (f := f) hf (L := 2 * Real.pi) (a := -(Real.pi / 3))
      (b := Real.pi / 3) (by positivity) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) (by
        intro t k hmem
        apply not_le.mpr (h t)
        have hmem' : f t - (k : ℝ) * (2 * Real.pi) ∈ Set.Icc (-(Real.pi / 3)) (Real.pi / 3) := by
          constructor <;> · have := hmem.1; have := hmem.2; ring_nf at this ⊢; linarith
        have hy : |f t - (k : ℝ) * (2 * Real.pi)| ≤ Real.pi / 3 := by
          rw [abs_le]; exact ⟨hmem'.1, hmem'.2⟩
        have hcos : Real.cos (f t) = Real.cos (f t - (k : ℝ) * (2 * Real.pi)) := by
          conv_lhs => rw [show f t = (f t - (k : ℝ) * (2 * Real.pi)) + (k : ℝ) * (2 * Real.pi)
            by ring]
          rw [Real.cos_add_int_mul_two_pi]
        rw [hcos]
        have := Real.cos_le_cos_of_nonneg_of_le_pi (x := |f t - (k : ℝ) * (2 * Real.pi)|)
          (y := Real.pi / 3) (abs_nonneg _) (by linarith [Real.pi_pos]) hy
        rwa [Real.cos_abs, Real.cos_pi_div_three] at this)
  intro s t
  have := hmain s t
  linarith

/-- An integer winding increment of size `< 2π` vanishes. -/
lemma cex_int_eq_zero_of_abs_lt_one {m : ℤ} (h : |(m : ℝ)| < 1) : m = 0 := by
  have hlt := abs_lt.mp h
  have hz1 : (-1 : ℤ) < m := by
    have : ((-1 : ℤ) : ℝ) < (m : ℝ) := by push_cast; linarith [hlt.1]
    exact_mod_cast this
  have hz2 : m < 1 := by
    have : (m : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith [hlt.2]
    exact_mod_cast this
  omega

/-- An integer multiple of `2π` of absolute value `< b ≤ 2π` vanishes. -/
lemma cex_int_eq_zero_of_abs_mul_two_pi_lt {m : ℤ} {b : ℝ} (hb : b ≤ 2 * Real.pi)
    (h : |(m : ℝ) * (2 * Real.pi)| < b) : m = 0 := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : |(m : ℝ) * (2 * Real.pi)| < 2 * Real.pi := lt_of_lt_of_le h hb
  rw [abs_mul, abs_of_pos hp] at h1
  apply cex_int_eq_zero_of_abs_lt_one
  by_contra hc
  push Not at hc
  nlinarith [abs_nonneg (m : ℝ)]

/-! ## The longitude circle `{z = -1}` -/

/-- The longitude circle at meridian parameter `3π/2` (the circle `{z = -1}`, of radius `2`) lies
inside the box of size `5/2`. -/
lemma cex_longitudeCurve_mem :
    ∀ t : ℝ, (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (3 * Real.pi / 2)) t ∈
      Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (5 / 2) 0
        (Equiv.swap (1 : Fin 3) 2) := by
  intro t
  refine ⟨(Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (3 * Real.pi / 2)).mem t, ?_⟩
  rw [cex_mem_PBox]
  have hx : (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (3 * Real.pi / 2)) t 0
      = (2 + Real.cos (3 * Real.pi / 2)) * Real.cos t := by
    rw [Work.CoreTopology.longitudeCurve_apply, Work.CoreTopology.standard_psi,
      Work.CoreTopology.torusMap_apply_zero]
  have hy : (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (3 * Real.pi / 2)) t 1
      = (2 + Real.cos (3 * Real.pi / 2)) * Real.sin t := by
    rw [Work.CoreTopology.longitudeCurve_apply, Work.CoreTopology.standard_psi,
      Work.CoreTopology.torusMap_apply_one]
  have hz : (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (3 * Real.pi / 2)) t 2
      = Real.sin (3 * Real.pi / 2) := by
    rw [Work.CoreTopology.longitudeCurve_apply, Work.CoreTopology.standard_psi,
      Work.CoreTopology.torusMap_apply_two]
  have hc : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi,
      Real.cos_pi_div_two, neg_zero]
  have hs : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi,
      Real.sin_pi_div_two]
  rw [hx, hy, hz, hc, hs]
  refine ⟨?_, ?_, ?_⟩
  · rw [add_zero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.abs_cos_le_one t]
  · rw [abs_neg, abs_one]
    have h : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / 3 : ℝ) := Submission.one_le_rpow_third
    nlinarith
  · rw [add_zero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.abs_sin_le_one t, Submission.one_le_rpow_two_thirds]

lemma cex_windingOf_longitudeCurve :
    Work.SurgeryInvariance.windingOf Work.CoreTopology.standard
      (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard (3 * Real.pi / 2)) = (1, 0) := by
  rw [Work.SurgeryInvariance.windingOf_eq _ _ (Work.CoreTopology.longitudeLift _ _),
    Work.CoreTopology.longitudeLift_winding]

/-- **(1,0) is realised inside the box.** -/
lemma cex_onezero_mem_realizedWindings :
    (1, 0) ∈ RealizedWindings Work.CoreTopology.standard
      (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (5 / 2) 0
        (Equiv.swap (1 : Fin 3) 2)) :=
  ⟨_, cex_longitudeCurve_mem, cex_windingOf_longitudeCurve⟩

/-- **(1,0) is not realised off the plane `{y = 0}`**: every loop of the two half-regions has
vanishing first winding coordinate. -/
lemma cex_onezero_not_mem_realizedWindings :
    (1, 0) ∉ RealizedWindings Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0 ∪
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0) := by
  rintro ⟨γ, hγ, hw⟩
  have hy : ∀ t : ℝ, (γ.γ t) 1 ≠ 0 := by
    intro t
    have hu := hγ t
    rw [Set.mem_union] at hu
    rcases hu with h | h
    · rw [Work.BoxShrink.Core.mem_upperRegion] at h
      have hh : (0 : ℝ) < (γ.γ t) 1 := by simpa [cex_swap_two] using h.2.2
      linarith
    · rw [Work.BoxShrink.Core.mem_lowerRegion] at h
      have hh : (γ.γ t) 1 < 0 := by simpa [cex_swap_two] using h.2.2
      linarith
  have hzero := windingOf_standard_fst_eq_zero_of_y_ne hy
  rw [hw] at hzero
  norm_num at hzero

/-! ## The three parts of the counterexample -/

/-- No essential loop lies on the box sphere `∂PBox (5/2) 0 (swap 1 2)`: every point of the
sphere that lies on the torus has `|x| = 5/2`, so both angle coordinates avoid the zeros of
`cos`, hence both winding coordinates vanish. -/
theorem cex_not_containsEssentialLoop_sphereSet :
    ¬ Work.CoreTopology.standard.ContainsEssentialLoop
        (Work.BoxShrink.Core.sphereSet 0 (Equiv.swap (1 : Fin 3) 2) (5 / 2)) := by
  rintro ⟨γ, hess, hmem⟩
  obtain ⟨L, hL⟩ := hess
  have hcoord0 : ∀ t : ℝ, (γ.γ t) 0 = (2 + Real.cos (L.Φ t)) * Real.cos (L.Θ t) := by
    intro t
    have hl := congrArg (fun u : R3 => u 0) (L.lifts t)
    simpa only [Work.CoreTopology.standard_psi, Work.CoreTopology.torusMap_apply_zero] using hl.symm
  have hfst : ∀ t : ℝ, |(γ.γ t) 0| = 5 / 2 := fun t =>
    cex_fst_eq_of_boxNorm_eq (γ.mem t) (Work.BoxShrink.Core.mem_sphereSet.mp (hmem t))
  have hcosΘ : ∀ t : ℝ, Real.cos (L.Θ t) ≠ 0 := by
    intro t hc
    have h0 := hfst t
    rw [hcoord0 t, hc, mul_zero, abs_zero] at h0
    norm_num at h0
  have hcosΦ : ∀ t : ℝ, Real.cos (L.Φ t) ≠ 0 := by
    intro t
    have h0 := hfst t
    rw [hcoord0 t, abs_mul] at h0
    have hle : |Real.cos (L.Θ t)| ≤ 1 := Real.abs_cos_le_one _
    have hge : 5 / 2 ≤ |2 + Real.cos (L.Φ t)| := by
      nlinarith [abs_nonneg (Real.cos (L.Θ t)), abs_nonneg (2 + Real.cos (L.Φ t))]
    have hpos : (0 : ℝ) < 2 + Real.cos (L.Φ t) := by linarith [Real.neg_one_le_cos (L.Φ t)]
    rw [abs_of_pos hpos] at hge
    linarith
  have hΘ := cex_abs_sub_lt_pi_of_cos_ne_zero L.contΘ hcosΘ
  have hΦ := cex_abs_sub_lt_pi_of_cos_ne_zero L.contΦ hcosΦ
  have hw1 : (L.winding).1 = 0 := by
    apply cex_int_eq_zero_of_abs_mul_two_pi_lt (b := Real.pi) (by linarith [Real.pi_pos])
    have hb := hΘ 0 (2 * Real.pi)
    rw [L.winding_spec.1, add_sub_cancel_left] at hb
    exact hb
  have hw2 : (L.winding).2 = 0 := by
    apply cex_int_eq_zero_of_abs_mul_two_pi_lt (b := Real.pi) (by linarith [Real.pi_pos])
    have hb := hΦ 0 (2 * Real.pi)
    rw [L.winding_spec.2, add_sub_cancel_left] at hb
    exact hb
  exact hL (Prod.ext hw1 hw2)

/-- No essential loop lies in the slice: the slice lies in `{y = 0}`, so its longitude component
vanishes; and inside the box its `x`-coordinate is `< 5/2`, so `cos` of the meridian parameter is
`< 1/2` and the meridian component is confined to an interval of length `4π/3`, hence vanishes
too. -/
theorem cex_not_containsEssentialLoop_sliceRegion :
    ¬ Work.CoreTopology.standard.ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0) := by
  rintro ⟨γ, hess, hmem⟩
  obtain ⟨L, hL⟩ := hess
  have hPBox : ∀ t : ℝ, Submission.boxNorm 0 (Equiv.swap (1 : Fin 3) 2) (γ.γ t) < 5 / 2 := by
    intro t
    have h := (Work.BoxShrink.Core.mem_sliceRegion.mp (hmem t)).2.1
    rwa [Submission.mem_PBox_iff] at h
  have hcut : ∀ t : ℝ, (γ.γ t) 1 = 0 := by
    intro t
    have h := (Work.BoxShrink.Core.mem_sliceRegion.mp (hmem t)).2.2
    simpa [cex_swap_two] using h
  have hcoord0 : ∀ t : ℝ, (γ.γ t) 0 = (2 + Real.cos (L.Φ t)) * Real.cos (L.Θ t) := by
    intro t
    have hl := congrArg (fun u : R3 => u 0) (L.lifts t)
    simpa only [Work.CoreTopology.standard_psi, Work.CoreTopology.torusMap_apply_zero] using hl.symm
  have hcoord1 : ∀ t : ℝ, (γ.γ t) 1 = (2 + Real.cos (L.Φ t)) * Real.sin (L.Θ t) := by
    intro t
    have hl := congrArg (fun u : R3 => u 1) (L.lifts t)
    simpa only [Work.CoreTopology.standard_psi, Work.CoreTopology.torusMap_apply_one] using hl.symm
  have hsin : ∀ t : ℝ, Real.sin (L.Θ t) = 0 := by
    intro t
    have h := hcut t
    rw [hcoord1 t] at h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (by linarith [Real.neg_one_le_cos (L.Φ t)])
    · exact h
  have hcosΘ : ∀ t : ℝ, Real.cos (L.Θ t) ≠ 0 := by
    intro t hc
    have hs := hsin t
    have h := Real.sin_sq_add_cos_sq (L.Θ t)
    rw [hs, hc] at h
    norm_num at h
  have hcosΦ : ∀ t : ℝ, Real.cos (L.Φ t) < 1 / 2 := by
    intro t
    have h0 := cex_fst_lt_of_boxNorm_lt (γ.mem t) (hPBox t)
    rw [hcoord0 t, abs_mul] at h0
    have hcabs : |Real.cos (L.Θ t)| = 1 := by
      have hs := hsin t
      have h := Real.sin_sq_add_cos_sq (L.Θ t)
      have h2 : Real.cos (L.Θ t) ^ 2 = 1 := by
        rw [hs] at h
        simpa using h
      have h3 : |Real.cos (L.Θ t)| ^ 2 = 1 := by rw [sq_abs, h2]
      nlinarith [abs_nonneg (Real.cos (L.Θ t))]
    have hpos : (0 : ℝ) < 2 + Real.cos (L.Φ t) := by linarith [Real.neg_one_le_cos (L.Φ t)]
    rw [abs_of_pos hpos, hcabs, mul_one] at h0
    linarith
  have hΘ := cex_abs_sub_lt_pi_of_cos_ne_zero L.contΘ hcosΘ
  have hΦ := cex_abs_sub_lt_four_thirds_pi_of_cos_lt_half L.contΦ hcosΦ
  have hw1 : (L.winding).1 = 0 := by
    apply cex_int_eq_zero_of_abs_mul_two_pi_lt (b := Real.pi) (by linarith [Real.pi_pos])
    have hb := hΘ 0 (2 * Real.pi)
    rw [L.winding_spec.1, add_sub_cancel_left] at hb
    exact hb
  have hw2 : (L.winding).2 = 0 := by
    apply cex_int_eq_zero_of_abs_mul_two_pi_lt (b := 4 * Real.pi / 3)
      (by linarith [Real.pi_pos])
    have hb := hΦ 0 (2 * Real.pi)
    rw [L.winding_spec.2, add_sub_cancel_left] at hb
    exact hb
  exact hL (Prod.ext hw1 hw2)

/-- The push-off fails for the concrete configuration. -/
theorem cex_not_slicePushOff :
    ¬ SlicePushOff Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 :=
  fun h => cex_onezero_not_mem_realizedWindings (h cex_onezero_mem_realizedWindings)

/-- **The counterexample to the field `BubbleInput.bubble`** (`PLAN.md`, stretch 16).  Take the
standard torus, `σ := Equiv.swap 1 2` (so `σ 2 = 1`: the cut plane is `{y = 0}`), `c := 0`,
`u := 0`, `s := 5/2`.  Then `PBox (5/2) 0 σ = {|x| < 5/2, |y| < (5/2)·2^{2/3}, |z| < (5/2)·2^{1/3}}`,
and (`F` = `standard.carrier`):

* `F ∖ PBox = {|x| ≥ 5/2} ∩ F` is **two discs** (since `|y| ≤ 3` and `|z| ≤ 1` are automatic), so
  `F ∩ ∂PBox` is two circles each bounding a disc in `F`: every loop of `F` inside `sphereSet` has
  zero winding (`hS`);
* writing `ψ(p.1,p.2) = torusMap p.1 p.2` (so `y = (2+cos p.2)·sin p.1`, `z = sin p.2`),
  `F ∩ {y = 0}` is `{p.1 = 0} ∪ {p.1 = π}`, and the box cuts each to the arc `p.2 ∈ (π/3, 5π/3)`
  (`|x| = |2+cos p.2| < 5/2`): the slice is **two arcs**, so every loop of `F` inside `sliceRegion`
  has zero winding (`hZ`: its lift has `Θ` in `2πℤ` hence constant, and `Φ` in one coset of
  `(π/3,5π/3)`, so both winding coordinates vanish);
* the curve `t ↦ ψ t (3π/2)` (the circle `{z = -1}`, of radius 2) lies in `PBox` and has winding
  `(1,0)` (`longitudeLift_winding`), while every loop of `upperRegion ∪ lowerRegion` lies in `{y > 0}`
  or in `{y < 0}` (both open in the surface and disjoint: `Span.curve_subset_of_union`) and therefore
  has vanishing **first** winding coordinate (`windingOf_standard_fst_eq_zero_of_y_ne`); hence
  `(1,0) ∈ RealizedWindings boxRegion ∖ RealizedWindings (upperRegion ∪ lowerRegion)` and the
  push-off fails. -/
theorem standard_counterexample :
    ¬ Work.CoreTopology.standard.ContainsEssentialLoop
        (Work.BoxShrink.Core.sphereSet 0 (Equiv.swap (1 : Fin 3) 2) (5 / 2)) ∧
      ¬ Work.CoreTopology.standard.ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion Work.CoreTopology.standard (5 / 2) 0
          (Equiv.swap (1 : Fin 3) 2) 0) ∧
      ¬ SlicePushOff Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 :=
  ⟨cex_not_containsEssentialLoop_sphereSet, cex_not_containsEssentialLoop_sliceRegion,
    cex_not_slicePushOff⟩

end

end Work.BoxShrink.Bubble
