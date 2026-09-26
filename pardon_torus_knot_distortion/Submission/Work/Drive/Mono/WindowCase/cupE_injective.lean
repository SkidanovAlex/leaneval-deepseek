import Mathlib
import Submission.Work.Drive.Mono.WindowCase.CupDefs
import Submission.Work.Drive.Mono.CylRegionDefs
import Submission.Work.CoreTopology.Disk

/-!
# Injectivity of the collapse-aware parametrisation of the cup

`Work.Drive.Mono.WindowCase.cupE e g` parametrises the cup over the plane disc `K = range e`
(see `CupDefs`): the "bottom" branch `z ↦ cmk (e (z / max (G z) ‖z‖)) 0` for `‖z‖ ≤ G z`, and the
"wall" branch

`z ↦ cmk (e (cupDir z)) (g (e (cupDir z)) * ((‖z‖ - G z) / (1 - G z)))` for `G z < ‖z‖`,

where `G z = cupG e g z = 1/2 + 1/(2 * (1 + g (e (cupDir z)))) ∈ (1/2, 1]` depends on `z` only
through its radial direction `cupDir z`.

This file proves that `cupE e g` is injective when `e` is injective and `g ≥ 0` on `K`.  The
argument is a case analysis on the two branches.

* On the bottom branch the map is `z ↦ z / G z` followed by the injective map `e`.  Since `G`
  depends only on the *direction* of `z`, and scaling by the positive number `1 / G` does not
  change the direction, the map `z ↦ z / G z` is injective: the direction of `z / G z` is the
  direction of `z`, hence `G z = G z'`, and then `z = G z * (z / G z) = G z' * (z' / G z') = z'`.
* On the wall branch, equal images first give `e (cupDir z) = e (cupDir z')`, hence `cupDir z =
  cupDir z'` and `G z = G z'`; the heights then force `‖z‖ = ‖z'‖` (the factor `g (e (cupDir z))`
  is nonzero on the wall, since `G z < 1` there), and a point of `ℂ` is determined by its direction
  and its norm.
* A bottom point has height `0`, while on the wall the height is nonzero, so the two branches
  cannot collide.
-/

namespace Work.Drive.Mono.WindowCase

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

local notation "𝔻" => Metric.closedBall (0 : ℂ) 1

/-- Every point of the closed unit disc has norm at most one. -/
lemma norm_le_one (z : 𝔻) : ‖(z : ℂ)‖ ≤ 1 := by
  have h := z.2
  rwa [Metric.mem_closedBall, dist_zero_right] at h

/-- `cupScaled` rescales by the *positive* real number `1 / max (G z) ‖z‖`, so it does not change
the radial direction: `cupDir (cupScaled e g z) = cupDir z`. -/
theorem cupDir_cupScaled {e : C(𝔻, EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    {z : 𝔻} (hm : 0 ≤ g (e (cupDir z))) :
    cupDir (cupScaled e g z) = cupDir z := by
  have hG : 0 < cupG e g z := cupG_pos hm
  have hmpos : 0 < max (cupG e g z) ‖(z : ℂ)‖ := lt_of_lt_of_le hG (le_max_left _ _)
  have hmne : ((max (cupG e g z) ‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hmpos
  refine Subtype.ext ?_
  rw [cupDir_coe, cupDir_coe, cupScaled_coe]
  rw [show ‖(z : ℂ) / ↑(max (cupG e g z) ‖(z : ℂ)‖)‖
      = (‖(z : ℂ)‖ / max (cupG e g z) ‖(z : ℂ)‖ : ℝ) by
    rw [norm_div, Complex.norm_of_nonneg (le_of_lt hmpos)]]
  push_cast
  exact div_div_div_cancel_right₀ hmne _ _

/-- On the region `‖z‖ ≤ G z` the rescaled point `cupScaled e g z = z / G z` determines `z`. -/
theorem eq_of_cupScaled_eq {e : C(𝔻, EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} {z z' : 𝔻}
    (hm : 0 ≤ g (e (cupDir z))) (hm' : 0 ≤ g (e (cupDir z')))
    (hz : ‖(z : ℂ)‖ ≤ cupG e g z) (hz' : ‖(z' : ℂ)‖ ≤ cupG e g z')
    (h : cupScaled e g z = cupScaled e g z') : z = z' := by
  have hdir : cupDir z = cupDir z' := by
    rw [← cupDir_cupScaled hm, ← cupDir_cupScaled hm', h]
  have hG : cupG e g z = cupG e g z' := by simp only [cupG]; rw [hdir]
  have hcoe : (cupScaled e g z : ℂ) = (cupScaled e g z' : ℂ) := congrArg Subtype.val h
  rw [cupScaled_of_le hz, cupScaled_of_le hz'] at hcoe
  have hz0 : ((cupG e g z : ℝ) : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt (cupG_pos hm)
  have hz0' : ((cupG e g z' : ℝ) : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt (cupG_pos hm')
  refine Subtype.ext ?_
  calc (z : ℂ) = ↑(cupG e g z) * ((z : ℂ) / ↑(cupG e g z)) := (mul_div_cancel₀ _ hz0).symm
    _ = ↑(cupG e g z') * ((z' : ℂ) / ↑(cupG e g z')) := by rw [hcoe, hG]
    _ = (z' : ℂ) := mul_div_cancel₀ _ hz0'

/-- A point of the plane is determined by its radial direction and its norm. -/
theorem eq_of_cupDir_eq_of_norm_eq {z z' : 𝔻} (hdir : cupDir z = cupDir z')
    (hr : ‖(z : ℂ)‖ = ‖(z' : ℂ)‖) : z = z' := by
  have hcoe : (z : ℂ) / ‖(z : ℂ)‖ = (z' : ℂ) / ‖(z' : ℂ)‖ := by
    rw [← cupDir_coe z, ← cupDir_coe z', hdir]
  refine Subtype.ext ?_
  by_cases hz : (z : ℂ) = 0
  · have : (z' : ℂ) = 0 := by
      rw [← norm_eq_zero, ← hr, norm_eq_zero]; exact hz
    rw [hz, this]
  · have hrne : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
      rw [ne_eq, Complex.ofReal_eq_zero]; exact norm_ne_zero_iff.mpr hz
    have hrne' : ((‖(z' : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
      rw [ne_eq, Complex.ofReal_eq_zero]; rw [← hr]; exact norm_ne_zero_iff.mpr hz
    calc (z : ℂ) = ↑‖(z : ℂ)‖ * ((z : ℂ) / ‖(z : ℂ)‖) := (mul_div_cancel₀ _ hrne).symm
      _ = ↑‖(z' : ℂ)‖ * ((z' : ℂ) / ‖(z' : ℂ)‖) := by rw [hcoe, hr]
      _ = (z' : ℂ) := mul_div_cancel₀ _ hrne'

/-- On the wall `G z < ‖z‖` the height of the wall point is nonzero. -/
theorem mul_height_ne_zero {e : C(𝔻, EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} {z : 𝔻} (hm : 0 ≤ g (e (cupDir z)))
    (hz : cupG e g z < ‖(z : ℂ)‖) :
    g (e (cupDir z)) * ((‖(z : ℂ)‖ - cupG e g z) / (1 - cupG e g z)) ≠ 0 := by
  have hlt : cupG e g z < 1 := lt_of_lt_of_le hz (norm_le_one z)
  have hden : 0 < 1 - cupG e g z := sub_pos.mpr hlt
  have hnum : 0 < ‖(z : ℂ)‖ - cupG e g z := sub_pos.mpr hz
  have ht : 0 < (‖(z : ℂ)‖ - cupG e g z) / (1 - cupG e g z) := div_pos hnum hden
  have hg : g (e (cupDir z)) ≠ 0 := by
    intro h0
    have h1 : cupG e g z = 1 := (cupG_eq_one_iff hm).mpr h0
    linarith
  exact mul_ne_zero hg (ne_of_gt ht)

/-- On the region `G z < ‖z‖` the wall point `cupWall e g z` determines `z` (for `e` injective). -/
theorem eq_of_cupWall_eq {e : C(𝔻, EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} {z z' : 𝔻}
    (he_inj : Function.Injective e) (hm : 0 ≤ g (e (cupDir z)))
    (hz : cupG e g z < ‖(z : ℂ)‖) (h : cupWall e g z = cupWall e g z') : z = z' := by
  have hdir : cupDir z = cupDir z' :=
    he_inj (by simpa only [cproj_cupWall] using congrArg cproj h)
  have hG : cupG e g z = cupG e g z' := by simp only [cupG]; rw [hdir]
  have hgt : g (e (cupDir z)) * ((‖(z : ℂ)‖ - cupG e g z) / (1 - cupG e g z))
      = g (e (cupDir z')) * ((‖(z' : ℂ)‖ - cupG e g z') / (1 - cupG e g z')) := by
    simpa only [clast_cupWall] using congrArg clast h
  rw [← hdir, ← hG] at hgt
  have hlt : cupG e g z < 1 := lt_of_lt_of_le hz (norm_le_one z)
  have hden : 1 - cupG e g z ≠ 0 := by linarith
  have hgne : g (e (cupDir z)) ≠ 0 := by
    intro h0
    have h1 : cupG e g z = 1 := (cupG_eq_one_iff hm).mpr h0
    linarith
  have ht := mul_left_cancel₀ hgne hgt
  have hr : ‖(z : ℂ)‖ = ‖(z' : ℂ)‖ := by
    rw [div_eq_div_iff hden hden] at ht
    have h2 := mul_right_cancel₀ hden ht
    linarith
  exact eq_of_cupDir_eq_of_norm_eq hdir hr

theorem cupE_injective
    {K : Set (EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)))
    (he_inj : Function.Injective e) (he_range : Set.range e = K)
    (he_bdry : Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K)
    (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) :
    Function.Injective (Work.Drive.Mono.WindowCase.cupE e g) := by
  have hm : ∀ w : 𝔻, 0 ≤ g (e (cupDir w)) := fun w =>
    hg0 _ (by rw [← he_range]; exact Set.mem_range_self _)
  intro z z' h
  rcases le_or_gt ‖(z : ℂ)‖ (cupG e g z) with hz | hz
  · rcases le_or_gt ‖(z' : ℂ)‖ (cupG e g z') with hz' | hz'
    · rw [cupE_of_le hz, cupE_of_le hz'] at h
      have hsc : cupScaled e g z = cupScaled e g z' :=
        he_inj (by simpa only [cproj_cupBottom] using congrArg cproj h)
      exact eq_of_cupScaled_eq (hm z) (hm z') hz hz' hsc
    · exfalso
      rw [cupE_of_le hz, cupE_of_gt hz'] at h
      have hh := congrArg clast h
      simp only [clast_cupBottom, clast_cupWall] at hh
      exact absurd hh.symm (mul_height_ne_zero (hm z') hz')
  · rcases le_or_gt ‖(z' : ℂ)‖ (cupG e g z') with hz' | hz'
    · exfalso
      rw [cupE_of_gt hz, cupE_of_le hz'] at h
      have hh := congrArg clast h
      simp only [clast_cupBottom, clast_cupWall] at hh
      exact absurd hh (mul_height_ne_zero (hm z) hz)
    · rw [cupE_of_gt hz, cupE_of_gt hz'] at h
      exact eq_of_cupWall_eq he_inj (hm z) hz h

end

end Work.Drive.Mono.WindowCase
