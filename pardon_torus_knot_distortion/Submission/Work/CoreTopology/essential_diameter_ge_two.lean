import Mathlib
import Submission.Work.CoreTopology.Disk

/-!
# An essential closed curve on the standard torus has diameter at least `2`

Let `γ : ℝ → ℝ³` be a closed curve on the standard torus of revolution
(major radius `2`, minor radius `1`), i.e. `γ t = (2 + cos φ) cos θ,
(2 + cos φ) sin θ, sin φ)` for a lift `t ↦ (θ t, φ t)` of `γ` to the parameter
plane, and suppose the winding vector of the lift is nonzero.

* If the *meridian* component `b` of the winding vector is nonzero, the meridian
  angle `φ` sweeps an interval of length `≥ 2π` over one period, so it attains
  values congruent to `π/2` and `-π/2` modulo `2π`; the corresponding points of
  `γ` have `z`-coordinates `±1` and hence are at distance at least `2`.
* If the *longitude* component `a` is nonzero, the longitude angle `θ` sweeps an
  interval of length `≥ 2π` over one period, so it attains two values differing
  by exactly `π`; the `xy`-projections of the two corresponding points are then
  opposite multiples of a unit vector with factors `2 + cos φ₁`, `2 + cos φ₂`,
  whose sum is at least `2`.

This is the geometric input that makes a non-contractible curve on the standard
torus have positive Euclidean diameter, used in Pardon's argument to convert the
topological invariant `I(F, β)` into a lower bound for the distortion.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- Every real number has an integer translate of the form `x + k·2π` lying in any
interval of length `2π`.  (This is the elementary fact that `2πℤ` is a discrete
lattice with fundamental domain any half-open interval of length `2π`.) -/
lemma exists_int_mul_two_pi_add_mem_Icc (x c : ℝ) :
    ∃ k : ℤ, x + (k : ℝ) * (2 * Real.pi) ∈ Set.Icc c (c + 2 * Real.pi) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  refine ⟨⌈(c - x) / (2 * Real.pi)⌉, ?_, ?_⟩
  · have h1 : (c - x) / (2 * Real.pi) ≤ ((⌈(c - x) / (2 * Real.pi)⌉ : ℤ) : ℝ) :=
      Int.le_ceil _
    have h2 : (c - x) / (2 * Real.pi) * (2 * Real.pi) ≤
        ((⌈(c - x) / (2 * Real.pi)⌉ : ℤ) : ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hπ)
    rw [div_mul_cancel₀ _ (ne_of_gt hπ)] at h2
    linarith
  · have h1 : ((⌈(c - x) / (2 * Real.pi)⌉ : ℤ) : ℝ) < (c - x) / (2 * Real.pi) + 1 :=
      Int.ceil_lt_add_one _
    have h2 : ((⌈(c - x) / (2 * Real.pi)⌉ : ℤ) : ℝ) * (2 * Real.pi) <
        ((c - x) / (2 * Real.pi) + 1) * (2 * Real.pi) := mul_lt_mul_of_pos_right h1 hπ
    have h3 : ((c - x) / (2 * Real.pi) + 1) * (2 * Real.pi) = c - x + 2 * Real.pi := by
      field_simp
    linarith

/-- If a continuous function `f` on the fundamental interval advances by a nonzero
integer multiple of `2π` over one period, `f (2π) = f 0 + m · 2π` with `m ≠ 0`,
then `f` meets every residue class modulo `2π`: for every `ρ` there are `t` and `k`
with `f t = ρ + k · 2π`.

Indeed, the image of `[0, 2π]` is an interval containing `f 0` and `f 0 + m·2π`,
which has length at least `2π` no matter the sign of `m`. -/
lemma exists_eq_shift_of_winding (f : ℝ → ℝ) (hf : Continuous f) {m : ℤ} (hm : m ≠ 0)
    (hshift : f (2 * Real.pi) = f 0 + (m : ℝ) * (2 * Real.pi)) (ρ : ℝ) :
    ∃ t : ℝ, ∃ k : ℤ, f t = ρ + (k : ℝ) * (2 * Real.pi) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have h0 : (0 : ℝ) ≤ 2 * Real.pi := le_of_lt hπ
  rcases lt_or_gt_of_ne (Ne.symm hm) with hmpos | hmneg
  · obtain ⟨k, hk⟩ := exists_int_mul_two_pi_add_mem_Icc ρ (f 0)
    have hle : f 0 + 2 * Real.pi ≤ f (2 * Real.pi) := by
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ m)
      rw [hshift]; nlinarith [hπ]
    have hy : ρ + (k : ℝ) * (2 * Real.pi) ∈ Set.Icc (f 0) (f (2 * Real.pi)) :=
      ⟨hk.1, le_trans hk.2 hle⟩
    obtain ⟨t, -, ht⟩ := (intermediate_value_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)
      h0 hf.continuousOn) hy
    exact ⟨t, k, ht⟩
  · obtain ⟨k, hk⟩ := exists_int_mul_two_pi_add_mem_Icc ρ (f 0 - 2 * Real.pi)
    have hle : f (2 * Real.pi) ≤ f 0 - 2 * Real.pi := by
      have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ (-1 : ℤ))
      rw [hshift]; nlinarith [hπ]
    have hy : ρ + (k : ℝ) * (2 * Real.pi) ∈ Set.Icc (f (2 * Real.pi)) (f 0) :=
      ⟨le_trans hle hk.1, by linarith [hk.2]⟩
    obtain ⟨t, -, ht⟩ := (intermediate_value_Icc' (a := (0 : ℝ)) (b := 2 * Real.pi)
      h0 hf.continuousOn) hy
    exact ⟨t, k, ht⟩

/-- If a continuous function `f` on the fundamental interval advances by a nonzero
integer multiple of `2π` over one period, then it takes two values differing by
exactly `π`: `f t₂ = f t₁ + π` for suitable `t₁`, `t₂`.

The image of `[0, 2π]` contains an interval of length `2π` (in one direction or
the other), hence contains a pair of points differing by `π`. -/
lemma exists_eq_add_pi_of_winding (f : ℝ → ℝ) (hf : Continuous f) {m : ℤ} (hm : m ≠ 0)
    (hshift : f (2 * Real.pi) = f 0 + (m : ℝ) * (2 * Real.pi)) :
    ∃ t₁ t₂ : ℝ, f t₂ = f t₁ + Real.pi := by
  have hπ : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have h0 : (0 : ℝ) ≤ 2 * Real.pi := le_of_lt hπ
  rcases lt_or_gt_of_ne (Ne.symm hm) with hmpos | hmneg
  · have hle : f 0 + 2 * Real.pi ≤ f (2 * Real.pi) := by
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ m)
      rw [hshift]; nlinarith [hπ]
    have hy : f 0 + Real.pi ∈ Set.Icc (f 0) (f (2 * Real.pi)) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    obtain ⟨t, -, ht⟩ := (intermediate_value_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)
      h0 hf.continuousOn) hy
    exact ⟨0, t, by rw [ht]⟩
  · have hle : f (2 * Real.pi) ≤ f 0 - 2 * Real.pi := by
      have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ (-1 : ℤ))
      rw [hshift]; nlinarith [hπ]
    have hy : f 0 - Real.pi ∈ Set.Icc (f (2 * Real.pi)) (f 0) :=
      ⟨by linarith [hle], by linarith [Real.pi_pos]⟩
    obtain ⟨t, -, ht⟩ := (intermediate_value_Icc' (a := (0 : ℝ)) (b := 2 * Real.pi)
      h0 hf.continuousOn) hy
    exact ⟨t, 0, by rw [ht]; ring⟩

/-- An essential closed curve on the standard torus of revolution has Euclidean diameter at least `2`: if `γ` is a closed curve on the torus and `L` is a lift of `γ` whose winding vector is nonzero, then there are two parameters whose images are at distance at least `2`. Concretely, a nonzero first component makes the longitude parameter range over an interval of length `≥ 2π`, so it takes two values differing by `π`, and the corresponding points of the torus have `xy`-projections of length `4 + cos φ₁ + cos φ₂ ≥ 2`. A nonzero second component makes the height `sin Φ` take the values `±1`, again giving distance `2`. -/
theorem essential_diameter_ge_two (γ : ClosedCurve standard) (L : LiftOf standard γ)
    (hw : L.winding ≠ (0, 0)) : ∃ t₁ t₂ : ℝ, 2 ≤ dist (γ t₁) (γ t₂) := by
  -- the three coordinates of `γ`, read off from the lift
  have hcomp0 : ∀ t : ℝ, γ t 0 = (2 + Real.cos (L.Φ t)) * Real.cos (L.Θ t) := fun t => by
    rw [show γ t = Work.Core.torusMap (L.Θ t) (L.Φ t) from (L.lifts t).symm]; rfl
  have hcomp1 : ∀ t : ℝ, γ t 1 = (2 + Real.cos (L.Φ t)) * Real.sin (L.Θ t) := fun t => by
    rw [show γ t = Work.Core.torusMap (L.Θ t) (L.Φ t) from (L.lifts t).symm]; rfl
  have hcomp2 : ∀ t : ℝ, γ t 2 = Real.sin (L.Φ t) := fun t => by
    rw [show γ t = Work.Core.torusMap (L.Θ t) (L.Φ t) from (L.lifts t).symm]; rfl
  rcases eq_or_ne L.winding.2 0 with hb0 | hb
  · -- the meridian component of the winding vector vanishes, so the longitude
    -- component is nonzero
    have ha : L.winding.1 ≠ 0 := fun h => hw (Prod.ext h hb0)
    obtain ⟨t₁, t₂, hΘ⟩ :=
      exists_eq_add_pi_of_winding L.Θ L.contΘ (m := L.winding.1) ha (L.winding_spec).1
    refine ⟨t₁, t₂, ?_⟩
    rw [dist_eq_norm]
    -- `Θ` takes two values differing by `π`, so the `xy`-projections are opposite
    have hcos : Real.cos (L.Θ t₂) = -Real.cos (L.Θ t₁) := by rw [hΘ, Real.cos_add_pi]
    have hsin : Real.sin (L.Θ t₂) = -Real.sin (L.Θ t₁) := by rw [hΘ, Real.sin_add_pi]
    have hsq : ‖γ t₁ - γ t₂‖ ^ 2 = (4 + Real.cos (L.Φ t₁) + Real.cos (L.Φ t₂)) ^ 2
        + (Real.sin (L.Φ t₁) - Real.sin (L.Φ t₂)) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
      simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, hcomp0, hcomp1, hcomp2]
      rw [hcos, hsin]
      linear_combination ((4 + Real.cos (L.Φ t₁) + Real.cos (L.Φ t₂)) ^ 2)
        * Real.cos_sq_add_sin_sq (L.Θ t₁)
    have hD : 2 ≤ 4 + Real.cos (L.Φ t₁) + Real.cos (L.Φ t₂) := by
      linarith [Real.neg_one_le_cos (L.Φ t₁), Real.neg_one_le_cos (L.Φ t₂)]
    have hbig : 4 ≤ ‖γ t₁ - γ t₂‖ ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg (Real.sin (L.Φ t₁) - Real.sin (L.Φ t₂))]
    nlinarith [norm_nonneg (γ t₁ - γ t₂)]
  · -- the meridian component of the winding vector does not vanish: the height `sin Φ`
    -- takes the values `±1` at two different parameters
    obtain ⟨t₁, k₁, h₁⟩ := exists_eq_shift_of_winding L.Φ L.contΦ (m := L.winding.2) hb
      (L.winding_spec).2 (Real.pi / 2)
    obtain ⟨t₂, k₂, h₂⟩ := exists_eq_shift_of_winding L.Φ L.contΦ (m := L.winding.2) hb
      (L.winding_spec).2 (-(Real.pi / 2))
    have hs₁ : Real.sin (L.Φ t₁) = 1 := by
      rw [h₁, Real.sin_add_int_mul_two_pi, Real.sin_pi_div_two]
    have hs₂ : Real.sin (L.Φ t₂) = -1 := by
      rw [h₂, Real.sin_add_int_mul_two_pi, Real.sin_neg, Real.sin_pi_div_two]
    refine ⟨t₁, t₂, ?_⟩
    rw [dist_eq_norm]
    have hsq : ‖γ t₁ - γ t₂‖ ^ 2 = (γ t₁ 0 - γ t₂ 0) ^ 2 + (γ t₁ 1 - γ t₂ 1) ^ 2
        + (Real.sin (L.Φ t₁) - Real.sin (L.Φ t₂)) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
      simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, hcomp2]
    have hbig : 4 ≤ ‖γ t₁ - γ t₂‖ ^ 2 := by
      rw [hsq, hs₁, hs₂]
      nlinarith [sq_nonneg (γ t₁ 0 - γ t₂ 0), sq_nonneg (γ t₁ 1 - γ t₂ 1)]
    nlinarith [norm_nonneg (γ t₁ - γ t₂)]

end

end Work.CoreTopology
