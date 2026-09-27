import Mathlib
import Submission.Work.Conn.Basic

namespace Work.Conn.Sard

open Metric (sphere)

/-!
# Sard-type dimension count for maps `𝕊ᵏ → 𝕊ⁿ` with `k < n`

This file proves `Work.Conn.Sard.exists_sphere_notMem_range`: a smooth map
`P : ℝᵏ⁺¹ → ℝⁿ⁺¹` that is bounded between `3/4` and `5/4` on the unit sphere induces a
normalised map `𝕊ᵏ → 𝕊ⁿ` which is not surjective, provided `k < n`.

The proof follows the classical Sard dimension count.  A smooth cutoff `cutoff` (built from
`Real.smoothTransition`) which vanishes on `(-∞, 1/4]` and equals `1` on `[1/3, 3]` is used to
build the smooth map

`auxMap P x = cutoff ‖x‖ • (‖x‖ • P (‖x‖⁻¹ • x))`,

which equals `t • P y` for every `t ∈ [1/3, 3]` and `y ∈ 𝕊ᵏ`.  Since the source has strictly
smaller dimension than the target, `Differentiable.dense_compl_range_of_finrank_lt_finrank`
shows that the interior of the range of `auxMap P` is empty.  If the normalised map were
surjective then the whole annulus `{z | 1/2 ≤ ‖z‖ ≤ 2}` would be contained in `range (auxMap P)`,
contradicting the nonempty interior of the annulus.
-/

/-- A smooth cutoff function, equal to `0` on `(-∞, 1/4]` and to `1` on `[1/3, 3]`. -/
noncomputable def cutoff (t : ℝ) : ℝ :=
  Real.smoothTransition ((t - 1 / 4) * 12) * Real.smoothTransition (4 - t)

theorem cutoff_eq_zero {t : ℝ} (ht : t ≤ 1 / 4) : cutoff t = 0 := by
  unfold cutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem cutoff_eq_one {t : ℝ} (h1 : 1 / 3 ≤ t) (h2 : t ≤ 3) : cutoff t = 1 := by
  unfold cutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

/-- The modified map `x ↦ cutoff ‖x‖ • (‖x‖ • P (‖x‖⁻¹ • x))`, smooth on all of `ℝᵏ⁺¹`
(it vanishes near the origin) and agreeing with `t • P y` on the relevant annulus of radii. -/
noncomputable def auxMap {k n : ℕ}
    (P : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (x : EuclideanSpace ℝ (Fin (k + 1))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  cutoff ‖x‖ • (‖x‖ • P ((‖x‖)⁻¹ • x))

/-- On the sphere, `auxMap P` is homogeneous of degree one. -/
theorem auxMap_smul {k n : ℕ}
    {P : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {t : ℝ} (ht : 0 < t) (hcut : cutoff t = 1) (y : Sph k) :
    auxMap P (t • (y : EuclideanSpace ℝ (Fin (k + 1)))) =
      t • P (y : EuclideanSpace ℝ (Fin (k + 1))) := by
  have hnorm : ‖t • (y : EuclideanSpace ℝ (Fin (k + 1)))‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mem_Sph_iff.mp y.2, mul_one]
  have hsmul : (‖t • (y : EuclideanSpace ℝ (Fin (k + 1)))‖)⁻¹ •
      (t • (y : EuclideanSpace ℝ (Fin (k + 1)))) = (y : EuclideanSpace ℝ (Fin (k + 1))) := by
    rw [hnorm, inv_smul_smul₀ (ne_of_gt ht)]
  show cutoff ‖t • (y : EuclideanSpace ℝ (Fin (k + 1)))‖ •
      (‖t • (y : EuclideanSpace ℝ (Fin (k + 1)))‖ •
        P ((‖t • (y : EuclideanSpace ℝ (Fin (k + 1)))‖)⁻¹ •
          (t • (y : EuclideanSpace ℝ (Fin (k + 1)))))) =
    t • P (y : EuclideanSpace ℝ (Fin (k + 1)))
  rw [hsmul, hnorm, hcut, one_smul]

/-- `auxMap P` is `C¹` away from the origin. -/
theorem auxMap_contDiffAt {k n : ℕ}
    {P : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hP : ContDiff ℝ ⊤ P) {x : EuclideanSpace ℝ (Fin (k + 1))} (hx : x ≠ 0) :
    ContDiffAt ℝ 1 (auxMap P) x := by
  change ContDiffAt ℝ 1 (fun y : EuclideanSpace ℝ (Fin (k + 1)) =>
    cutoff ‖y‖ • (‖y‖ • P ((‖y‖)⁻¹ • y))) x
  have hnorm : ContDiffAt ℝ 1 (fun y : EuclideanSpace ℝ (Fin (k + 1)) => ‖y‖) x :=
    contDiffAt_norm ℝ hx
  have hinv : ContDiffAt ℝ 1 (fun y : EuclideanSpace ℝ (Fin (k + 1)) => (‖y‖)⁻¹) x :=
    hnorm.inv (norm_ne_zero_iff.mpr hx)
  have hsl : ContDiffAt ℝ 1 (fun y : EuclideanSpace ℝ (Fin (k + 1)) => (‖y‖)⁻¹ • y) x :=
    hinv.smul contDiffAt_id
  have hcomp : ContDiffAt ℝ 1 (fun y : EuclideanSpace ℝ (Fin (k + 1)) => P ((‖y‖)⁻¹ • y)) x :=
    (hP.of_le le_top).contDiffAt.comp x hsl
  have h2 : ContDiffAt ℝ 1
      (fun y : EuclideanSpace ℝ (Fin (k + 1)) => ‖y‖ • P ((‖y‖)⁻¹ • y)) x :=
    hnorm.smul hcomp
  have hc : ContDiff ℝ 1 cutoff := by unfold cutoff; fun_prop
  have hchi : ContDiffAt ℝ 1
      (fun y : EuclideanSpace ℝ (Fin (k + 1)) => cutoff ‖y‖) x :=
    hc.contDiffAt.comp x hnorm
  exact hchi.smul h2

/-- `auxMap P` is differentiable on all of `ℝᵏ⁺¹`: away from the origin it is `C¹` by the chain
rule, and near the origin it vanishes identically. -/
theorem differentiable_auxMap {k n : ℕ}
    {P : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hP : ContDiff ℝ ⊤ P) : Differentiable ℝ (auxMap P) := by
  intro x
  by_cases hx : x = 0
  · subst hx
    refine DifferentiableAt.congr_of_eventuallyEq
      (differentiableAt_const (0 : EuclideanSpace ℝ (Fin (n + 1)))) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin (k + 1)))
      (by norm_num : (0 : ℝ) < 1 / 4)] with y hy
    have hy' : ‖y‖ < 1 / 4 := by
      have h := Metric.mem_ball.mp hy
      rwa [dist_eq_norm, sub_zero] at h
    simp [auxMap, cutoff_eq_zero (le_of_lt hy')]
  · exact (auxMap_contDiffAt hP hx).differentiableAt (by norm_num)

/-- **Sard-type dimension count, case `k < n`.**  If `P : ℝᵏ⁺¹ → ℝⁿ⁺¹` is smooth and
`3/4 ≤ ‖P x‖ ≤ 5/4` for all `x` on the unit sphere, then the normalised map
`x ↦ ‖P x‖⁻¹ • P x`, viewed as a map `𝕊ᵏ → 𝕊ⁿ`, misses a point of `𝕊ⁿ`.

Route: pick `χ : ℝ → ℝ` smooth with `χ = 0` on `(-∞, 1/4]` and `χ = 1` on `[1/3, 3]`, e.g.
`χ t = Real.smoothTransition (24 * t - 6) * Real.smoothTransition (4 - t)`, and set
`H x = χ ‖x‖ • (‖x‖ • P (‖x‖⁻¹ • x))`; then `H = 0` for `‖x‖ ≤ 1/4` and `H (t • y) = t • P y`
for `t > 0`, `y ∈ 𝕊ᵏ` with `χ t = 1`.  `H` is smooth on all of `ℝᵏ⁺¹`
(`contDiffOn_of_locally_contDiffOn` glues the smooth formula away from `0` with `H = 0` near
`0`), so `Differentiable.dense_compl_range_of_finrank_lt_finrank` applies
(`finrank ℝ ℝᵏ⁺¹ = k + 1 < n + 1`) and the complement of `range H` is dense; hence
`interior (range H) = ∅` (`dense_iff_interior_compl`).  If the normalised map hit every point of
`𝕊ⁿ`, then each `z` with `1/2 ≤ ‖z‖ ≤ 2` would equal `t • P x` for some `x ∈ 𝕊ᵏ` and some
`t ∈ [2/5, 8/3] ⊆ [1/3, 3]`, i.e. `z = H (t • x)`; the closed annulus `{z | 1/2 ≤ ‖z‖ ≤ 2}`,
whose interior is nonempty, would then lie in `range H`, contradicting `interior (range H) = ∅`. -/
theorem exists_sphere_notMem_range {k n : ℕ} (hkn : k < n)
    {P : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hP : ContDiff ℝ ⊤ P)
    (hlo : ∀ x : Sph k, (3 : ℝ) / 4 ≤ ‖P x‖) (hhi : ∀ x : Sph k, ‖P x‖ ≤ (5 : ℝ) / 4) :
    ∃ q : Sph n, ∀ x : Sph k, (‖P x‖)⁻¹ • P x ≠ (q : EuclideanSpace ℝ (Fin (n + 1))) := by
  by_contra hcon
  push Not at hcon
  have hdiff : Differentiable ℝ (auxMap P) := differentiable_auxMap hP
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) <
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    exact Nat.succ_lt_succ hkn
  have hdense : Dense (Set.range (auxMap P))ᶜ :=
    hdiff.dense_compl_range_of_finrank_lt_finrank hfr
  have hemp : interior (Set.range (auxMap P)) = ∅ := by
    have h := hdense.interior_compl
    rwa [compl_compl] at h
  -- the closed annulus is contained in the range of `auxMap P`
  have hsub : {z : EuclideanSpace ℝ (Fin (n + 1)) | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2} ⊆
      Set.range (auxMap P) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz1
    have hzne : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hzpos)
    have hqmem : (‖z‖)⁻¹ • z ∈ Sph n :=
      mem_Sph_iff.mpr (norm_inv_norm_smul hzne)
    obtain ⟨x, hx⟩ := hcon ⟨(‖z‖)⁻¹ • z, hqmem⟩
    have hx' : (‖P x‖)⁻¹ • P x = (‖z‖)⁻¹ • z := hx
    have hPxpos : 0 < ‖P x‖ := lt_of_lt_of_le (by norm_num) (hlo x)
    set t : ℝ := ‖z‖ * (‖P x‖)⁻¹ with ht
    have htpos : 0 < t := by rw [ht]; exact mul_pos hzpos (inv_pos.mpr hPxpos)
    have hinv_lo : (4 : ℝ) / 5 ≤ (‖P x‖)⁻¹ := by
      have h := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 5 / 4) hPxpos).mpr (hhi x)
      norm_num at h; exact h
    have hinv_hi : (‖P x‖)⁻¹ ≤ (4 : ℝ) / 3 := by
      have h := (inv_le_inv₀ hPxpos (by norm_num : (0 : ℝ) < 3 / 4)).mpr (hlo x)
      norm_num at h; exact h
    have htlo : 1 / 3 ≤ t := by
      rw [ht]
      nlinarith [mul_le_mul hz1 hinv_lo (by norm_num : (0 : ℝ) ≤ 4 / 5) (norm_nonneg z)]
    have hthi : t ≤ 3 := by
      rw [ht]
      nlinarith [mul_le_mul hz2 hinv_hi (inv_nonneg.mpr hPxpos.le) (by norm_num : (0 : ℝ) ≤ 2)]
    have hcut : cutoff t = 1 := cutoff_eq_one htlo hthi
    have h2 : ‖z‖ • ((‖P x‖)⁻¹ • P x) = z := by
      rw [hx', smul_inv_smul₀ (ne_of_gt hzpos)]
    have hzt : z = t • P x := by
      rw [ht, ← smul_smul]
      exact h2.symm
    refine ⟨t • (x : EuclideanSpace ℝ (Fin (k + 1))), ?_⟩
    rw [auxMap_smul htpos hcut x]
    exact hzt.symm
  -- a point of the sphere lies in the interior of the annulus
  obtain ⟨z₀, hz₀⟩ :=
    (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin (n + 1))))).mpr
      (show (0 : ℝ) ≤ 1 by norm_num)
  have hz₀norm : ‖z₀‖ = 1 := by
    have h := Metric.mem_sphere.mp hz₀
    rw [dist_eq_norm, sub_zero] at h
    exact h
  have hz₀int : z₀ ∈ interior {z : EuclideanSpace ℝ (Fin (n + 1)) | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2} := by
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset (Metric.ball_mem_nhds z₀ (by norm_num : (0 : ℝ) < 1 / 4)) ?_
    intro w hw
    rw [Metric.mem_ball] at hw
    have hwn : ‖w - z₀‖ < 1 / 4 := by rwa [dist_eq_norm] at hw
    constructor
    · have h1 := abs_norm_sub_norm_le w z₀
      linarith [neg_abs_le (‖w‖ - ‖z₀‖)]
    · have h1 := abs_norm_sub_norm_le w z₀
      linarith [le_abs_self (‖w‖ - ‖z₀‖)]
  have hmem : z₀ ∈ interior (Set.range (auxMap P)) := interior_mono hsub hz₀int
  rw [hemp] at hmem
  simp at hmem

end Work.Conn.Sard
