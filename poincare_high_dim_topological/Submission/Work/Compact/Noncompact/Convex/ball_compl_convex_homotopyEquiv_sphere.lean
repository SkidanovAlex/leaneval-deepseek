import Mathlib

namespace Work.Compact.Noncompact.Convex

/-!  Auxiliary lemmas about radial rescaling. -/

private lemma dist_radial_aux {n : ℕ} (c y : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    dist (c + a • (y - c)) c = ‖a‖ * ‖y - c‖ := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul]

private lemma dist_radial_scaled {n : ℕ} {c y : EuclideanSpace ℝ (Fin n)} {d e : ℝ}
    (hd : d = ‖y - c‖) (hd0 : 0 < d) (he : 0 ≤ e) :
    dist (c + (e / d) • (y - c)) c = e := by
  rw [dist_radial_aux, Real.norm_eq_abs, abs_of_nonneg (div_nonneg he (le_of_lt hd0)),
    ← hd, div_mul_cancel₀ _ (ne_of_gt hd0)]

private lemma interp_nonneg {n : ℕ} {y c : EuclideanSpace ℝ (Fin n)} {R' t : ℝ} (_hR' : 0 ≤ R')
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (1 - t) * R' + t * ‖y - c‖ := by
  nlinarith [norm_nonneg (y - c)]

private lemma interp_lt {n : ℕ} {y c : EuclideanSpace ℝ (Fin n)} {R' R t : ℝ} (_hR' : 0 < R')
    (hR'R : R' < R) (hdR : ‖y - c‖ < R) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * R' + t * ‖y - c‖ < R := by
  rcases lt_or_eq_of_le ht1 with h | h
  · have h1 : (1 - t) * R' < (1 - t) * R := mul_lt_mul_of_pos_left hR'R (by linarith)
    have h2 : t * ‖y - c‖ ≤ t * R := mul_le_mul_of_nonneg_left (le_of_lt hdR) ht0
    nlinarith [h1, h2]
  · rw [h]; simp [hdR]

private lemma radial_case {d R' t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    R' ≤ (1 - t) * R' + t * d ∨ d ≤ (1 - t) * R' + t * d := by
  rcases le_total R' d with h | h
  · left; nlinarith
  · right; nlinarith

private lemma radial_notMem_C {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))} (hCvx : Convex ℝ C)
    {c y : EuclideanSpace ℝ (Fin n)} (hc : c ∈ C) (hy : y ∉ C) {R' a : ℝ}
    (hCsub : C ⊆ Metric.ball c R')
    (ha : 0 ≤ a) (h : 1 ≤ a ∨ R' ≤ a * ‖y - c‖) :
    c + a • (y - c) ∉ C := by
  rintro hzC
  rcases h with ha1 | hR'
  · have ha0 : a ≠ 0 := by linarith
    have h1 : (0 : ℝ) ≤ 1 - a⁻¹ := by
      have : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
      linarith
    have h2 : (0 : ℝ) ≤ a⁻¹ := inv_nonneg.mpr ha
    have h3 : (1 - a⁻¹) + a⁻¹ = 1 := by ring
    have hmem := (hCvx.starConvex hc) hzC h1 h2 h3
    have hident : (1 - a⁻¹) • c + a⁻¹ • (c + a • (y - c)) = y := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      module
    exact hy (hident ▸ hmem)
  · have hzlim : R' ≤ dist (c + a • (y - c)) c := by
      rw [dist_radial_aux, Real.norm_of_nonneg ha]
      exact hR'
    exact absurd (hCsub hzC) (not_lt.mpr hzlim)

private lemma radial_interp_notMem_C {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hCvx : Convex ℝ C) {c y : EuclideanSpace ℝ (Fin n)} (hc : c ∈ C) (hy : y ∉ C)
    {R' t : ℝ} (hCsub : C ⊆ Metric.ball c R') (hR' : 0 < R') (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    c + (((1 - t) * R' + t * ‖y - c‖) / ‖y - c‖) • (y - c) ∉ C := by
  have hd0 : 0 < ‖y - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hy (by rw [h]; exact hc)))
  have he0 : 0 ≤ (1 - t) * R' + t * ‖y - c‖ := interp_nonneg hR'.le ht0 ht1
  rcases radial_case (d := ‖y - c‖) ht0 ht1 with h | h
  · refine radial_notMem_C hCvx hc hy hCsub (div_nonneg he0 (le_of_lt hd0)) (Or.inr ?_)
    rw [div_mul_cancel₀ _ (ne_of_gt hd0)]
    exact h
  · refine radial_notMem_C hCvx hc hy hCsub (div_nonneg he0 (le_of_lt hd0)) (Or.inl ?_)
    rw [le_div_iff₀ hd0]
    simpa using h

private lemma radial_mem_ball {n : ℕ} {c y : EuclideanSpace ℝ (Fin n)} {R R' t : ℝ}
    (hR' : 0 < R') (hR'R : R' < R) (hy : y ∈ Metric.ball c R) (hne : y ≠ c)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    c + (((1 - t) * R' + t * ‖y - c‖) / ‖y - c‖) • (y - c) ∈ Metric.ball c R := by
  have hd0 : 0 < ‖y - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hdR : ‖y - c‖ < R := by
    have h := hy; rw [Metric.mem_ball, dist_eq_norm] at h; exact h
  refine Metric.mem_ball.mpr ?_
  rw [dist_radial_scaled rfl hd0 (interp_nonneg hR'.le ht0 ht1)]
  exact interp_lt hR' hR'R hdR ht0 ht1

private lemma radial_mem_sphere {n : ℕ} {c y : EuclideanSpace ℝ (Fin n)} {R' : ℝ}
    (hR' : 0 < R') (hne : y ≠ c) :
    c + (R' / ‖y - c‖) • (y - c) ∈ Metric.sphere c R' := by
  have hd0 : 0 < ‖y - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [Metric.mem_sphere]
  exact dist_radial_scaled rfl hd0 hR'.le

/-- Points of `ball c R` outside `C`. -/
abbrev PunctBall {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n))
    (R : ℝ) := {y : ↥(Metric.ball c R) // (y : EuclideanSpace ℝ (Fin n)) ∉ C}

/-- The sphere of radius `R'` around `c`. -/
abbrev Sph {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) (R' : ℝ) := ↥(Metric.sphere c R')

/-- **The complement of a convex set in a ball retracts onto a concentric sphere.**

Let `C ⊆ ℝⁿ` be convex with `c ∈ C` and `C ⊆ Metric.ball c R'` for reals `0 < R' < R`.  Then the
radial projection away from `c` onto the sphere of radius `R'`,
`y ↦ c + (R'/‖y - c‖) • (y - c)`, is a homotopy inverse (up to homotopy) of the inclusion
`sphere c R' ↪ ball c R ∖ C`; the homotopy is the radial interpolation
`y ↦ c + ((1 - t)‖y - c‖ + t R')/‖y - c‖ • (y - c)`.

Well-defined because `C ⊆ ball c R'`: for `y ∈ ball c R ∖ C` the denominator `‖y - c‖ > 0` since
`c ∈ C`; every interpolated point `z` stays in `ball c R` (its distance to `c` lies between
`‖y - c‖` and `R'`, both `< R`) and stays outside `C`: if `‖y - c‖ ≤ R'` then `z` lies on the ray
from `c` through `y` at distance `≥ ‖y - c‖`, so `z ∈ C` would force `y` into the segment
`[c, z] ⊆ C` by convexity (using `c ∈ C`); while if `‖y - c‖ > R'` then `dist z c ≥ R' > dist x c`
for every `x ∈ C` since `C ⊆ ball c R'`.

Route: build `f : C({y : ↥(ball c R) // (y : ℝⁿ) ∉ C}, ↥(sphere c R'))` (the radial projection) and
`g : C(↥(sphere c R'), {y : ↥(ball c R) // (y : ℝⁿ) ∉ C})` (the inclusion, well defined since
`sphere c R' ⊆ ball c R ∖ C`) and the two homotopies explicitly.  Continuity of the interpolation:
`Continuous.div` with the nonvanishing continuous denominator `‖y - c‖` on the subtype, then
`Continuous.subtype_mk` for the codomain subtype.  Membership: `Metric.mem_ball`,
`Metric.mem_closedBall`, convexity of `C`.  Package with `ContinuousMap.HomotopyEquiv.mk`, using
`ContinuousMap.Homotopy.mk`, `map_zero_left`, `map_one_left`. -/
theorem ball_compl_convex_homotopyEquiv_sphere {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCvx : Convex ℝ C)
    {c : EuclideanSpace ℝ (Fin n)} (hc : c ∈ C) {R' R : ℝ} (hR' : 0 < R') (hR'R : R' < R)
    (hCsub : C ⊆ Metric.ball c R') :
    Nonempty (ContinuousMap.HomotopyEquiv
      {y : ↥(Metric.ball c R) // (y : EuclideanSpace ℝ (Fin n)) ∉ C}
      ↥(Metric.sphere c R')) := by
  change Nonempty (ContinuousMap.HomotopyEquiv (PunctBall C c R) (Sph c R'))
  have hden : ∀ y : PunctBall C c R, ‖(y : EuclideanSpace ℝ (Fin n)) - c‖ ≠ 0 := fun y =>
    norm_ne_zero_iff.mpr (fun h => y.2 (by rw [sub_eq_zero.mp h]; exact hc))
  have hne : ∀ y : PunctBall C c R, (y : EuclideanSpace ℝ (Fin n)) ≠ c := fun y h =>
    y.2 (by rw [h]; exact hc)
  have hf_cont : Continuous fun y : PunctBall C c R =>
      c + (R' / ‖(y : EuclideanSpace ℝ (Fin n)) - c‖) • ((y : EuclideanSpace ℝ (Fin n)) - c) := by
    have hsub : Continuous fun y : PunctBall C c R =>
        ((y : EuclideanSpace ℝ (Fin n)) - c) := by fun_prop
    have hnorm : Continuous fun y : PunctBall C c R =>
        ‖(y : EuclideanSpace ℝ (Fin n)) - c‖ := hsub.norm
    exact continuous_const.add ((continuous_const.div hnorm hden).smul hsub)
  have hf_mem : ∀ y : PunctBall C c R, c + (R' / ‖(y : EuclideanSpace ℝ (Fin n)) - c‖) •
      ((y : EuclideanSpace ℝ (Fin n)) - c) ∈ Metric.sphere c R' :=
    fun y => radial_mem_sphere hR' (hne y)
  let F : PunctBall C c R → Sph c R' := fun y => ⟨c +
      (R' / ‖(y : EuclideanSpace ℝ (Fin n)) - c‖) • ((y : EuclideanSpace ℝ (Fin n)) - c),
    hf_mem y⟩
  have hF_cont : Continuous F := Continuous.subtype_mk hf_cont hf_mem
  let f : C(PunctBall C c R, Sph c R') := ⟨F, hF_cont⟩
  have hg_mem : ∀ y : Sph c R', (y : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball c R ∧
      (y : EuclideanSpace ℝ (Fin n)) ∉ C := by
    intro y
    have hy : dist (y : EuclideanSpace ℝ (Fin n)) c = R' := Metric.mem_sphere.mp y.2
    refine ⟨Metric.mem_ball.mpr (by rw [hy]; exact hR'R), fun hCy => ?_⟩
    have h2 := hCsub hCy
    rw [Metric.mem_ball, hy] at h2
    exact absurd h2 (lt_irrefl R')
  let G : Sph c R' → PunctBall C c R := fun y =>
    ⟨⟨(y : EuclideanSpace ℝ (Fin n)), (hg_mem y).1⟩, (hg_mem y).2⟩
  have hG_cont : Continuous G :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val (fun y => (hg_mem y).1))
      (fun y => (hg_mem y).2)
  let g : C(Sph c R', PunctBall C c R) := ⟨G, hG_cont⟩
  have hH_cont₀ : Continuous fun p : unitInterval × PunctBall C c R =>
      c + (((1 - (p.1 : ℝ)) * R' + (p.1 : ℝ) * ‖(p.2 : EuclideanSpace ℝ (Fin n)) - c‖) /
        ‖(p.2 : EuclideanSpace ℝ (Fin n)) - c‖) • ((p.2 : EuclideanSpace ℝ (Fin n)) - c) := by
    have hsub : Continuous fun p : unitInterval × PunctBall C c R =>
        ((p.2 : EuclideanSpace ℝ (Fin n)) - c) := by fun_prop
    have hnorm : Continuous fun p : unitInterval × PunctBall C c R =>
        ‖(p.2 : EuclideanSpace ℝ (Fin n)) - c‖ := hsub.norm
    have hne' : ∀ p : unitInterval × PunctBall C c R,
        ‖(p.2 : EuclideanSpace ℝ (Fin n)) - c‖ ≠ 0 := fun p => hden p.2
    have hnum : Continuous fun p : unitInterval × PunctBall C c R =>
        ((1 - (p.1 : ℝ)) * R' + (p.1 : ℝ) * ‖(p.2 : EuclideanSpace ℝ (Fin n)) - c‖) := by
      fun_prop
    exact continuous_const.add ((hnum.div hnorm hne').smul hsub)
  have hH_ball : ∀ p : unitInterval × PunctBall C c R,
      c + (((1 - (p.1 : ℝ)) * R' + (p.1 : ℝ) * ‖(p.2 : EuclideanSpace ℝ (Fin n)) - c‖) /
        ‖(p.2 : EuclideanSpace ℝ (Fin n)) - c‖) • ((p.2 : EuclideanSpace ℝ (Fin n)) - c)
      ∈ Metric.ball c R :=
    fun p => radial_mem_ball hR' hR'R p.2.1.2 (hne p.2) p.1.2.1 p.1.2.2
  have hH_notC : ∀ p : unitInterval × PunctBall C c R,
      c + (((1 - (p.1 : ℝ)) * R' + (p.1 : ℝ) * ‖(p.2 : EuclideanSpace ℝ (Fin n)) - c‖) /
        ‖(p.2 : EuclideanSpace ℝ (Fin n)) - c‖) • ((p.2 : EuclideanSpace ℝ (Fin n)) - c) ∉ C :=
    fun p => radial_interp_notMem_C hCvx hc p.2.2 hCsub hR' p.1.2.1 p.1.2.2
  let Hfun : unitInterval × PunctBall C c R → PunctBall C c R := fun p =>
    ⟨⟨c + (((1 - (p.1 : ℝ)) * R' + (p.1 : ℝ) * ‖(p.2 : EuclideanSpace ℝ (Fin n)) - c‖) /
        ‖(p.2 : EuclideanSpace ℝ (Fin n)) - c‖) • ((p.2 : EuclideanSpace ℝ (Fin n)) - c),
      hH_ball p⟩, hH_notC p⟩
  have hHfun_cont : Continuous Hfun :=
    Continuous.subtype_mk (Continuous.subtype_mk hH_cont₀ (fun p => hH_ball p))
      (fun p => hH_notC p)
  let H : C(unitInterval × PunctBall C c R, PunctBall C c R) := ⟨Hfun, hHfun_cont⟩
  have hmap0 : ∀ x : PunctBall C c R, H (0, x) = (g.comp f) x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    show c + (((1 - (0 : ℝ)) * R' + (0 : ℝ) * ‖(x : EuclideanSpace ℝ (Fin n)) - c‖) /
        ‖(x : EuclideanSpace ℝ (Fin n)) - c‖) • ((x : EuclideanSpace ℝ (Fin n)) - c)
      = c + (R' / ‖(x : EuclideanSpace ℝ (Fin n)) - c‖) • ((x : EuclideanSpace ℝ (Fin n)) - c)
    simp
  have hmap1 : ∀ x : PunctBall C c R, H (1, x) = (ContinuousMap.id (PunctBall C c R)) x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    show c + (((1 - (1 : ℝ)) * R' + (1 : ℝ) * ‖(x : EuclideanSpace ℝ (Fin n)) - c‖) /
        ‖(x : EuclideanSpace ℝ (Fin n)) - c‖) • ((x : EuclideanSpace ℝ (Fin n)) - c)
      = (x : EuclideanSpace ℝ (Fin n))
    rw [sub_self, zero_mul, zero_add, one_mul, div_self (hden x), one_smul]
    abel
  have hfg : f.comp g = ContinuousMap.id (Sph c R') := by
    apply ContinuousMap.ext
    intro y
    apply Subtype.ext
    have hy : ‖(y : EuclideanSpace ℝ (Fin n)) - c‖ = R' := by
      rw [← dist_eq_norm]; exact Metric.mem_sphere.mp y.2
    show c + (R' / ‖(y : EuclideanSpace ℝ (Fin n)) - c‖) • ((y : EuclideanSpace ℝ (Fin n)) - c)
      = (y : EuclideanSpace ℝ (Fin n))
    rw [hy, div_self (ne_of_gt hR'), one_smul]
    abel
  refine ⟨ContinuousMap.HomotopyEquiv.mk f g ⟨ContinuousMap.Homotopy.mk H hmap0 hmap1⟩ ?_⟩
  rw [hfg]

end Work.Compact.Noncompact.Convex
