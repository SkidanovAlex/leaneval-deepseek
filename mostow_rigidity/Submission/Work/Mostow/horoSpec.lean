import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula

/-!
# Horospherical coordinates `(lev, yc, wc)` and the chart point `hptOf`

At a boundary point `ξ ∈ Sph n` (so `‖ξ‖ = 1`) a point `u : E n` has

* level `lev ξ u = tpart u - ⟪u,ξ⟫`,
* `ξ^⊥`-coordinate `wc ξ u = u - ⟪u,ξ⟫ • ξ`,
* normalised flat coordinate `yc ξ u = (lev ξ u)⁻¹ • wc ξ u`,

and `hptOf ξ y D = ((1 + D² ‖y‖²)/(2D) - D/2) • ξ + D • y` is the point of level `D`
whose flat coordinate is `y`.  `horoSpec` is the resulting dictionary between a point, its
horospherical data, and its hyperboloid lift:

* `lev`, `yc`, `wc` of `hptOf ξ y D` are `D`, `y`, `D • y` (for `y ⟂ ξ`, `D > 0`);
* `hptOf ξ (yc ξ u) (lev ξ u) = u`;
* `hlift u = ((1 + ‖wc ξ u‖²)/(2 lev ξ u)) • n_ξ + (lev ξ u/2) • n'_ξ + (wc ξ u, 0)`.

Everything is the elementary computation `tpart u² - ⟪u,ξ⟫² = (tpart u - ⟪u,ξ⟫)(tpart u + ⟪u,ξ⟫)`
(`one_add_norm_wc_sq`) together with the definitional expansion of `hptOf`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-- `ξ ∈ Sph n` as `⟪ξ,ξ⟫ = 1`. -/
lemma inner_self_of_mem_Sph {ξ : E n} (hξ : ξ ∈ Sph n) : inner ℝ ξ ξ = 1 := by
  rw [real_inner_self_eq_norm_sq]
  have h : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  rw [h]; norm_num

/-- The coefficient of `hptOf` written with `wc`:
`(1 + ‖wc ξ u‖²)/(2 lev ξ u) = (tpart u + ⟪u,ξ⟫)/2`. -/
lemma hptA {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) :
    (1 + ‖wc ξ u‖ ^ 2) / (2 * lev ξ u) = (tpart u + inner ℝ u ξ) / 2 := by
  have hL : lev ξ u ≠ 0 := ne_of_gt (lev_pos ξ hξ u)
  rw [one_add_norm_wc_sq hξ u]
  field_simp
  try ring

/-- `(1 + ‖wc ξ u‖²)/(2 lev ξ u) - lev ξ u/2 = ⟪u,ξ⟫`. -/
lemma hptA_sub {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) :
    (1 + ‖wc ξ u‖ ^ 2) / (2 * lev ξ u) - lev ξ u / 2 = inner ℝ u ξ := by
  rw [hptA hξ u, lev]; ring

/-- `(1 + ‖wc ξ u‖²)/(2 lev ξ u) + lev ξ u/2 = tpart u`. -/
lemma hptA_add {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) :
    (1 + ‖wc ξ u‖ ^ 2) / (2 * lev ξ u) + lev ξ u / 2 = tpart u := by
  rw [hptA hξ u, lev]; ring

/-- `lev ξ u ^ 2 * ‖yc ξ u‖ ^ 2 = ‖wc ξ u‖ ^ 2`: the level scales the flat coordinate. -/
lemma lev_sq_norm_yc {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) :
    lev ξ u ^ 2 * ‖yc ξ u‖ ^ 2 = ‖wc ξ u‖ ^ 2 := by
  have hL : lev ξ u ≠ 0 := ne_of_gt (lev_pos ξ hξ u)
  rw [yc, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hL, one_pow, one_mul]

/-- `hptOf ξ (yc ξ u) (lev ξ u) = u`. -/
lemma hptOf_yc_lev {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) :
    hptOf ξ (yc ξ u) (lev ξ u) = u := by
  have hcoef : (1 + lev ξ u ^ 2 * ‖yc ξ u‖ ^ 2) / (2 * lev ξ u) - lev ξ u / 2
      = inner ℝ u ξ := by
    rw [lev_sq_norm_yc hξ u, hptA_sub hξ u]
  have hL : lev ξ u ≠ 0 := ne_of_gt (lev_pos ξ hξ u)
  have hsl : lev ξ u • yc ξ u = wc ξ u := by
    rw [yc, smul_smul, mul_inv_cancel₀ hL, one_smul]
  rw [hptOf, hcoef, hsl, wc]; abel

/-- The point of level `D` with flat coordinate `y` (for `y ⟂ ξ`, `D > 0`) has horospherical
data `(D, y, D • y)`. -/
lemma hptOf_lev_yc_wc {ξ : E n} (hξ : ξ ∈ Sph n) {y : E n} {D : ℝ}
    (hy : inner ℝ y ξ = 0) (hD : 0 < D) :
    lev ξ (hptOf ξ y D) = D ∧ yc ξ (hptOf ξ y D) = y ∧ wc ξ (hptOf ξ y D) = D • y := by
  have hDne : D ≠ 0 := ne_of_gt hD
  set a : ℝ := (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2 with ha
  have hp : hptOf ξ y D = a • ξ + D • y := by rw [hptOf, ha]
  have hξ1 : inner ℝ ξ ξ = 1 := inner_self_of_mem_Sph hξ
  have hξy : inner ℝ ξ y = 0 := by rw [real_inner_comm]; exact hy
  have hyy : inner ℝ y y = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
  have hinner : inner ℝ (hptOf ξ y D) ξ = a := by
    rw [hp, inner_add_left, real_inner_smul_left, real_inner_smul_left, hξ1, hy]
    ring
  have hnorm : ‖hptOf ξ y D‖ ^ 2 = a ^ 2 + D ^ 2 * ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hp]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hξ1, hy, hξy, hyy]
    ring
  have h2aD : 2 * a * D = 1 + D ^ 2 * ‖y‖ ^ 2 - D ^ 2 := by
    rw [ha]; field_simp; try ring
  have hDa_pos : 0 < D + a := by
    have h : D + a = (1 + D ^ 2 * ‖y‖ ^ 2 + D ^ 2) / (2 * D) := by
      rw [ha]; field_simp; try ring
    rw [h]; positivity
  have hsq : 1 + (a ^ 2 + D ^ 2 * ‖y‖ ^ 2) = (D + a) ^ 2 := by
    nlinarith [h2aD]
  have htpart : tpart (hptOf ξ y D) = D + a := by
    rw [tpart, hnorm, hsq, Real.sqrt_sq (le_of_lt hDa_pos)]
  have hlev : lev ξ (hptOf ξ y D) = D := by
    rw [lev, htpart, hinner]; ring
  have hwc : wc ξ (hptOf ξ y D) = D • y := by
    rw [wc, hinner, hp]; abel
  have hyc : yc ξ (hptOf ξ y D) = y := by
    rw [yc, hlev, hwc, inv_smul_smul₀ hDne]
  exact ⟨hlev, hyc, hwc⟩

theorem horoSpec {n : ℕ} {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n) :
    (∀ (y : Submission.Mostow.E n) (D : ℝ), inner ℝ y ξ = 0 → 0 < D →
      Work.Mostow.lev ξ (Work.Mostow.hptOf ξ y D) = D ∧
      Work.Mostow.yc ξ (Work.Mostow.hptOf ξ y D) = y ∧
      Work.Mostow.wc ξ (Work.Mostow.hptOf ξ y D) = D • y) ∧
    (∀ u : Submission.Mostow.E n, Work.Mostow.hptOf ξ (Work.Mostow.yc ξ u) (Work.Mostow.lev ξ u) = u) ∧
    (∀ u : Submission.Mostow.E n, Submission.Mostow.hlift u =
      ((1 + ‖Work.Mostow.wc ξ u‖ ^ 2) / (2 * Work.Mostow.lev ξ u)) • Work.Mostow.nvec ξ +
      (Work.Mostow.lev ξ u / 2) • Work.Mostow.nvec' ξ + Work.Mostow.wvec (Work.Mostow.wc ξ u)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y D hy hD
    exact hptOf_lev_yc_wc hξ hy hD
  · intro u
    exact hptOf_yc_lev hξ u
  · intro u
    have hsum := hptA_add hξ u
    have hdiff := hptA_sub hξ u
    funext x
    rcases x with i | j
    · have hui : u i = wc ξ u i + inner ℝ u ξ * ξ i := by
        rw [wc]
        simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      simp only [hlift, nvec, nvec', wvec, Sum.elim_inl, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hui, ← hdiff]
      ring
    · simp only [hlift, nvec, nvec', wvec, Sum.elim_inr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith [hsum]

end Work.Mostow
