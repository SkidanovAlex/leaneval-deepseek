import Mathlib
import Submission.Work.Orient.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Data for the homotopy of the punctured half-ball core

This file contains the *data* of the geometric construction used to prove
`Work.Orient.Boundary.halfBallPuncturedCore`.

Let `N = n + 1`, `H = EuclideanHalfSpace N` the half-space model, `x ∈ H` with `0 < x 0` (an
interior point), `c ∈ H` and `ρ > 0` with `dist x c ≤ ρ`.  Put

* `Y = {y : H | y ≠ x}` (the model half-space punctured at `x`) and
* `Z = {y : Y | ¬ (dist y c ≤ ρ ∧ 0 < y 0)} ⊆ Y` (the complement in `Y` of the *punctured
  half-ball* `{y : Y | dist y c ≤ ρ ∧ 0 < y 0}`).

The geometric heart of `halfBallPuncturedCore` is that the inclusion `Z ↪ Y` is a **homotopy
equivalence** (as a map of pairs, so that `Work.Cohomology.isZero_relChains_of_homotopyEquiv_incl`
applies and gives `H_{n+1}(Y,Z) = 0`).

## The construction

It is the half-space analogue of `Work.Cohomology.isZero_relChains_punctured_euclid`: push every
point *away from* `x`, along the ray from `x` through `y`, until it is at distance at least
`C = ρ + dist x c + 1` from `x`; then project back into the half-space by `coreClamp`
(`p ↦ p` with the first coordinate replaced by its positive part).  Explicitly

`corePath ρ c x t y = coreClamp (x + μ(t,y) • (y - x))`,  `μ(t,y) = (1-t) + t · max 1 (C/‖y-x‖)`

so that `μ(t,y) ≥ 1`, `corePath ρ c x 0 y = y` and `corePath ρ c x 1 y` is the pushed point.

Why this works:

* the clamped point always lies in the half-space (its first coordinate is a maximum with `0`) and
  differs from `x`, because `μ ≥ 1 > 0` makes `x + μ • (y - x) = x` impossible for `y ≠ x`;
* **for `y ∈ Z` the whole path stays in `Z`**: if `y 0 = 0` the ray leaves the half-space at once,
  so the clamped point is on the hyperplane `{y 0 = 0} ⊆ Z`; if instead `dist y c > ρ ≥ dist x c`
  then the map `μ ↦ ‖x + μ • (y - x) - c‖` is increasing for `μ ≥ 1` (its derivative is
  `2⟨y - c, y - x⟩ ≥ 2 ‖y-c‖ (‖y-c‖ - ‖x-c‖) > 0`), so the distance never drops to `ρ`;
* the endpoint of a point `y ∉ Z` (i.e. `dist y c ≤ ρ`, `y 0 > 0`) lies in `Z`: either the clamp is
  active, in which case the first coordinate is `0`, or `dist (x + λ • (y-x)) c ≥ λ‖y-x‖ - dist x c
  ≥ C - dist x c = ρ + 1 > ρ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-! ## The clamping map -/

/-- The projection of an ambient point back into the half-space: replace the first coordinate by
its positive part, leaving the other coordinates alone. -/
def coreClamp (n : ℕ) (p : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  p + (max 0 (p 0) - p 0) • EuclideanSpace.single 0 (1 : ℝ)

/-- The clamped point agrees with the original point as soon as the first coordinate is
nonnegative. -/
theorem coreClamp_of_nonneg (n : ℕ) (p : EuclideanSpace ℝ (Fin (n + 1))) (hp : 0 ≤ p 0) :
    coreClamp n p = p := by
  rw [coreClamp, max_eq_right hp, sub_self, zero_smul, add_zero]

/-- The first coordinate of the clamped point is the positive part. -/
theorem coreClamp_apply_zero (n : ℕ) (p : EuclideanSpace ℝ (Fin (n + 1))) :
    coreClamp n p 0 = max 0 (p 0) := by
  simp [coreClamp, PiLp.add_apply, PiLp.smul_apply]

/-- The clamped point has nonnegative first coordinate. -/
theorem coreClamp_nonneg (n : ℕ) (p : EuclideanSpace ℝ (Fin (n + 1))) : 0 ≤ coreClamp n p 0 := by
  rw [coreClamp_apply_zero]; exact le_max_left _ _

/-- The clamp does not change the coordinates other than the first. -/
theorem coreClamp_apply_of_ne (n : ℕ) (p : EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ≠ 0) : coreClamp n p i = p i := by
  simp [coreClamp, PiLp.add_apply, PiLp.smul_apply, hi]

/-- The clamp is continuous. -/
theorem continuous_coreClamp (n : ℕ) : Continuous (coreClamp n) := by
  unfold coreClamp
  fun_prop

/-! ## The push away from the puncture -/

/-- The constant controlling the size of the push. -/
def coreC (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1)) : ℝ := ρ + dist x.1 c.1 + 1

/-- The scaling factor of the push away from the puncture: `max 1 (C/‖y - x‖)`. -/
def coreScale (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1))
    (y : {y : EuclideanHalfSpace (n + 1) | y ≠ x}) : ℝ :=
  max 1 (coreC n ρ c x / ‖y.1.1 - x.1‖)

/-- The radius along the ray from `x` through `y` at time `t`: the convex combination of `1` and
the scaling factor. -/
def coreMu (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1)) (t : ℝ)
    (y : {y : EuclideanHalfSpace (n + 1) | y ≠ x}) : ℝ :=
  (1 - t) + t * coreScale n ρ c x y

/-- The point of the homotopy at time `t`. -/
def corePath (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1)) (t : ℝ)
    (y : {y : EuclideanHalfSpace (n + 1) | y ≠ x}) : EuclideanSpace ℝ (Fin (n + 1)) :=
  coreClamp n ((x.1 + coreMu n ρ c x t y • (y.1.1 - x.1) : EuclideanSpace ℝ (Fin (n + 1))))

/-! ## Elementary properties -/

theorem coreScale_one_le (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1))
    (y : {y : EuclideanHalfSpace (n + 1) | y ≠ x}) : 1 ≤ coreScale n ρ c x y :=
  le_max_left _ _

/-- The scaling factor is large enough: `C ≤ coreScale · ‖y - x‖`. -/
theorem coreScale_mul_norm_ge (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1))
    (y : {y : EuclideanHalfSpace (n + 1) | y ≠ x}) :
    coreC n ρ c x ≤ coreScale n ρ c x y * ‖y.1.1 - x.1‖ := by
  have hne : y.1.1 ≠ x.1 := fun h => y.2 (Subtype.ext h)
  have hd : ‖y.1.1 - x.1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  rw [coreScale, max_mul_of_nonneg _ _ (norm_nonneg _), div_mul_cancel₀ _ hd]
  exact le_max_right _ _

theorem coreMu_ge_one (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (y : {y : EuclideanHalfSpace (n + 1) | y ≠ x}) :
    1 ≤ coreMu n ρ c x t y := by
  have h := coreScale_one_le n ρ c x y
  have h1 : 0 ≤ 1 - t := by linarith
  have h2 : 1 - t + t * 1 ≤ 1 - t + t * coreScale n ρ c x y := by
    have := mul_le_mul_of_nonneg_left h ht0
    linarith
  have h3 : 1 - t + t * 1 = 1 := by ring
  simp only [coreMu]
  linarith

theorem coreMu_pos (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (y : {y : EuclideanHalfSpace (n + 1) | y ≠ x}) :
    0 < coreMu n ρ c x t y := by
  have := coreMu_ge_one n ρ c x ht0 ht1 y
  linarith

/-- The path starts at the point itself. -/
theorem corePath_zero (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1))
    (y : {y : EuclideanHalfSpace (n + 1) | y ≠ x}) :
    corePath n ρ c x 0 y = y.1.1 := by
  have hmu : coreMu n ρ c x 0 y = 1 := by simp [coreMu]
  rw [corePath, hmu, one_smul, add_sub_cancel]
  exact coreClamp_of_nonneg n y.1.1 y.1.2

theorem continuous_coreScale (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1)) :
    Continuous (coreScale n ρ c x) := by
  have hne : ∀ y : {y : EuclideanHalfSpace (n + 1) | y ≠ x}, ‖y.1.1 - x.1‖ ≠ 0 := by
    intro y h
    refine y.2 (Subtype.ext ?_)
    exact sub_eq_zero.mp (norm_eq_zero.mp h)
  unfold coreScale coreC
  refine continuous_const.max (continuous_const.div (by fun_prop) hne)

theorem continuous_coreMu (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1)) :
    Continuous fun q : ℝ × {y : EuclideanHalfSpace (n + 1) | y ≠ x} =>
      coreMu n ρ c x q.1 q.2 := by
  unfold coreMu
  exact (continuous_const.sub continuous_fst).add
    (continuous_fst.mul ((continuous_coreScale n ρ c x).comp continuous_snd))

theorem continuous_corePath (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1)) :
    Continuous fun q : ℝ × {y : EuclideanHalfSpace (n + 1) | y ≠ x} =>
      corePath n ρ c x q.1 q.2 := by
  have hmu : Continuous fun q : ℝ × {y : EuclideanHalfSpace (n + 1) | y ≠ x} =>
      coreMu n ρ c x q.1 q.2 := continuous_coreMu n ρ c x
  have hdir : Continuous fun q : ℝ × {y : EuclideanHalfSpace (n + 1) | y ≠ x} =>
      q.2.1.1 - x.1 := by fun_prop
  unfold corePath
  exact (continuous_coreClamp n).comp
    (continuous_const.add (hmu.smul hdir))

/-! ## The three membership facts -/

/-- The point of the path always lies in the punctured half-space. -/
theorem corePath_mem_halfspace (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1))
    (y : {y : EuclideanHalfSpace (n + 1) | y ≠ x}) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ corePath n ρ c x t y 0 ∧ corePath n ρ c x t y ≠ x.1 := by
  have hmu : 0 < coreMu n ρ c x t y := coreMu_pos n ρ c x ht0 ht1 y
  set p : EuclideanSpace ℝ (Fin (n + 1)) :=
    x.1 + coreMu n ρ c x t y • (y.1.1 - x.1) with hp
  have hcp : corePath n ρ c x t y = coreClamp n p := by rw [corePath, ← hp]
  have hp0 : p 0 = x.1 0 + coreMu n ρ c x t y * (y.1.1 0 - x.1 0) := by
    rw [hp]
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    try ring
  constructor
  · rw [corePath, coreClamp_apply_zero]
    exact le_max_left _ _
  · intro h
    have hcl : coreClamp n p = x.1 := by rw [← hcp]; exact h
    have hc0 : max 0 (p 0) = x.1 0 := by
      have := congrArg (fun q : EuclideanSpace ℝ (Fin (n + 1)) => q 0) hcl
      rwa [coreClamp_apply_zero] at this
    have hcoords : ∀ i : Fin (n + 1), i ≠ 0 → y.1.1 i = x.1 i := by
      intro i hi
      have h2 : p i = x.1 i := by
        have h2' : coreClamp n p i = x.1 i :=
          congrArg (fun q : EuclideanSpace ℝ (Fin (n + 1)) => q i) hcl
        rwa [coreClamp_apply_of_ne n p i hi] at h2'
      have h3 : p i = x.1 i + coreMu n ρ c x t y * (y.1.1 i - x.1 i) := by
        rw [hp]
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        try ring
      rw [h3] at h2
      have h4 : coreMu n ρ c x t y * (y.1.1 i - x.1 i) = 0 := by linarith
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd h5 hmu.ne'
      · exact sub_eq_zero.mp h5
    have h0 : y.1.1 0 = x.1 0 := by
      by_cases hple : 0 ≤ p 0
      · have hp' : p 0 = x.1 0 := by rw [max_eq_right hple] at hc0; exact hc0
        rw [hp0] at hp'
        have h4 : coreMu n ρ c x t y * (y.1.1 0 - x.1 0) = 0 := by linarith
        rcases mul_eq_zero.mp h4 with h5 | h5
        · exact absurd h5 hmu.ne'
        · exact sub_eq_zero.mp h5
      · have hpneg : p 0 < 0 := not_le.mp hple
        have hx0 : x.1 0 = 0 := by
          rw [max_eq_left (le_of_lt hpneg)] at hc0
          exact hc0.symm
        rw [hp0, hx0, zero_add] at hpneg
        have hy0 : 0 ≤ y.1.1 0 := y.1.2
        nlinarith [hmu]
    refine y.2 (Subtype.ext ?_)
    rw [WithLp.ext_iff]
    funext i
    by_cases hi : i = 0
    · subst hi; exact h0
    · exact hcoords i hi

/-- **The path of a point of the core `Z` stays in the core.** -/
theorem corePath_mem_core (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1))
    (hx : dist x.1 c.1 ≤ ρ) (y : {y : EuclideanHalfSpace (n + 1) | y ≠ x})
    (hy : ¬ (dist y.1.1 c.1 ≤ ρ ∧ 0 < y.1.1 0)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ¬ (dist (corePath n ρ c x t y) c.1 ≤ ρ ∧ 0 < corePath n ρ c x t y 0) := by
  have hmu : 1 ≤ coreMu n ρ c x t y := coreMu_ge_one n ρ c x ht0 ht1 y
  set p : EuclideanSpace ℝ (Fin (n + 1)) :=
    x.1 + coreMu n ρ c x t y • (y.1.1 - x.1) with hp
  have hcp : corePath n ρ c x t y = coreClamp n p := by rw [corePath, ← hp]
  rintro ⟨hd, hpos⟩
  have hp0 : 0 ≤ p 0 := by
    by_contra hcon
    have hneg : p 0 < 0 := not_le.mp hcon
    rw [hcp, coreClamp_apply_zero, max_eq_left (le_of_lt hneg)] at hpos
    exact absurd hpos (lt_irrefl 0)
  rw [hcp, coreClamp_of_nonneg n p hp0] at hd
  rcases eq_or_lt_of_le (y.1.2 : 0 ≤ y.1.1 0) with hy0 | hy0pos
  · -- the point lies on the hyperplane
    have hy0' : y.1.1 0 = 0 := hy0.symm
    have hpz : p 0 = x.1 0 * (1 - coreMu n ρ c x t y) := by
      have h1 : p 0 = x.1 0 + coreMu n ρ c x t y * (y.1.1 0 - x.1 0) := by
        rw [hp]
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        try ring
      rw [h1, hy0']; ring
    have hx0 : 0 ≤ x.1 0 := x.2
    have hple : p 0 ≤ 0 := by nlinarith [hpz, hx0, hmu]
    have hpeq : p 0 = 0 := le_antisymm hple hp0
    rw [hcp, coreClamp_apply_zero, max_eq_right hp0, hpeq] at hpos
    exact absurd hpos (lt_irrefl 0)
  · -- the point lies strictly outside the ball
    have hyd : ρ < dist y.1.1 c.1 := by
      by_contra hcon
      exact hy ⟨not_lt.mp hcon, hy0pos⟩
    have hdecomp : p - c.1 = (y.1.1 - c.1) + (coreMu n ρ c x t y - 1) • (y.1.1 - x.1) := by
      rw [hp, sub_eq_add_neg, smul_sub, smul_sub]
      module
    have hinner : 0 ≤ inner ℝ (y.1.1 - c.1) (y.1.1 - x.1) := by
      have hsplit : y.1.1 - x.1 = (y.1.1 - c.1) - (x.1 - c.1) := by abel
      rw [hsplit, inner_sub_right, real_inner_self_eq_norm_sq]
      have h1 : inner ℝ (y.1.1 - c.1) (x.1 - c.1) ≤ ‖y.1.1 - c.1‖ * ‖x.1 - c.1‖ :=
        real_inner_le_norm _ _
      have h2 : ‖x.1 - c.1‖ ≤ ‖y.1.1 - c.1‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm]; linarith
      have h3 : 0 ≤ ‖y.1.1 - c.1‖ := norm_nonneg _
      nlinarith [h1, h2, h3]
    have hs : 0 ≤ coreMu n ρ c x t y - 1 := by linarith
    have hsq : ‖y.1.1 - c.1‖ ^ 2 ≤ ‖p - c.1‖ ^ 2 := by
      rw [hdecomp, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hs, mul_pow]
      nlinarith [hinner, hs, sq_nonneg (coreMu n ρ c x t y - 1), sq_nonneg ‖y.1.1 - x.1‖]
    have hle : ‖y.1.1 - c.1‖ ≤ ‖p - c.1‖ := by
      nlinarith [norm_nonneg (y.1.1 - c.1), norm_nonneg (p - c.1), hsq]
    rw [dist_eq_norm] at hd hyd
    linarith

/-- **The endpoint of the path of any point lies in the core `Z`.** -/
theorem corePath_one_mem_core (n : ℕ) (ρ : ℝ) (c x : EuclideanHalfSpace (n + 1)) (hρ : 0 < ρ)
    (hx : dist x.1 c.1 ≤ ρ) (y : {y : EuclideanHalfSpace (n + 1) | y ≠ x}) :
    ¬ (dist (corePath n ρ c x 1 y) c.1 ≤ ρ ∧ 0 < corePath n ρ c x 1 y 0) := by
  have hscale := coreScale_mul_norm_ge n ρ c x y
  have hmu1 : coreMu n ρ c x 1 y = coreScale n ρ c x y := by simp [coreMu]
  set p : EuclideanSpace ℝ (Fin (n + 1)) :=
    x.1 + coreScale n ρ c x y • (y.1.1 - x.1) with hp
  have hcp : corePath n ρ c x 1 y = coreClamp n p := by rw [corePath, hmu1, ← hp]
  rintro ⟨hd, hpos⟩
  have hp0 : 0 ≤ p 0 := by
    by_contra hcon
    have hneg : p 0 < 0 := not_le.mp hcon
    rw [hcp, coreClamp_apply_zero, max_eq_left (le_of_lt hneg)] at hpos
    exact absurd hpos (lt_irrefl 0)
  rw [hcp, coreClamp_of_nonneg n p hp0, dist_eq_norm] at hd
  have hdecomp : p - c.1 = (x.1 - c.1) + coreScale n ρ c x y • (y.1.1 - x.1) := by
    rw [hp, sub_eq_add_neg, smul_sub]
    module
  have htri : ‖coreScale n ρ c x y • (y.1.1 - x.1)‖ - ‖c.1 - x.1‖ ≤ ‖p - c.1‖ := by
    rw [hdecomp]
    have : (x.1 - c.1) + coreScale n ρ c x y • (y.1.1 - x.1)
        = coreScale n ρ c x y • (y.1.1 - x.1) - (c.1 - x.1) := by abel
    rw [this]
    exact norm_sub_norm_le _ _
  have hnorm : ‖coreScale n ρ c x y • (y.1.1 - x.1)‖ = coreScale n ρ c x y * ‖y.1.1 - x.1‖ := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_trans zero_le_one (coreScale_one_le n ρ c x y))]
  have hcx : ‖c.1 - x.1‖ = dist x.1 c.1 := by rw [dist_eq_norm, norm_sub_rev]
  rw [hnorm, hcx] at htri
  have hC : coreC n ρ c x = ρ + dist x.1 c.1 + 1 := rfl
  linarith [htri, hscale, hd, hC, hx]


end

end Work.Orient.Boundary
