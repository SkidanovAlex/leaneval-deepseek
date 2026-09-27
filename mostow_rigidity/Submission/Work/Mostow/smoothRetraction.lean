import Mathlib
import Submission.Work.Mostow.smoothRetractionDefs
import Submission.Work.Mostow.contDiffOn_invNorm_smul
import Submission.Work.Mostow.exists_contDiff_dist_le_on_closedBall

set_option linter.unusedVariables false

namespace Work.Mostow

open Metric
open scoped ContDiff

/-- A continuous retraction of the closed unit ball of `ℝⁿ` (`n ≥ 1`) onto its boundary sphere
can be smoothed to a `C¹` retraction (same values, still the identity on the sphere).

NOTE: the three hypotheses can never hold simultaneously (that is the whole point: this result is
used, by contradiction, together with `noRetractionSmooth`). So the proof must be the explicit
construction, never a derivation of `False` from the hypotheses.

Construction: `r` is extended to `u x = r (ballProj x)` on all of `ℝⁿ` (`ballProj` the radial
projection onto the closed unit ball); `u` is continuous and `Sⁿ⁻¹`-valued. It is uniformly
approximated on the closed unit ball by a smooth `G` (`exists_contDiff_dist_le_on_closedBall`).
With `χ` a `ContDiffBump` supported in `‖x‖ ≥ 1 - δ` and equal to `1` near the centre, put
`h x = (1 - χ(‖x‖²)) • x + χ(‖x‖²) • G x` and `f x = (‖h x‖)⁻¹ • h x`. On the sphere `χ = 0`, so
`h x = x` and `f x = x`; and `‖h x‖ ≥ 1/2` everywhere, so `f` is `C¹` and sphere-valued. -/
theorem smoothRetraction (n : ℕ) (hn : 1 ≤ n)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hr : ContinuousOn r (closedBall 0 1)) (hm : Set.MapsTo r (closedBall 0 1) (sphere 0 1))
    (hid : ∀ x ∈ sphere 0 1, r x = x) :
    ∃ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContDiff ℝ 1 f ∧ (∀ x ∈ closedBall 0 1, f x ∈ sphere 0 1) ∧
        ∀ x ∈ sphere 0 1, f x = x := by
  have hu_cont : Continuous (fun x : EuclideanSpace ℝ (Fin n) => r (ballProj x)) :=
    hr.comp_continuous ballProj_continuous (fun x => ballProj_mem_closedBall x)
  have hu_norm : ∀ x : EuclideanSpace ℝ (Fin n), ‖r (ballProj x)‖ = 1 := by
    intro x
    have h := hm (ballProj_mem_closedBall x)
    rwa [mem_sphere_iff_norm, sub_zero] at h
  obtain ⟨G, hGcd, hGapprox⟩ :=
    exists_contDiff_dist_le_on_closedBall n (fun x => r (ballProj x)) hu_cont (1/8) (by norm_num)
  have hG_close : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      dist (G x) (r (ballProj x)) ≤ 1/8 := by
    intro x hx
    apply hGapprox
    rw [mem_closedBall_zero_iff] at hx ⊢
    linarith
  have hucr : UniformContinuousOn r (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (1:ℝ)).uniformContinuousOn_of_continuous hr
  obtain ⟨δu, hδu_pos, hδu⟩ := (uniformContinuousOn_iff.mp hucr) (1/8) (by norm_num)
  set δc : ℝ := min (δu / 2) (1 / 16) with hδcdef
  have hδc_pos : 0 < δc := lt_min (half_pos hδu_pos) (by norm_num)
  have hδc_le : δc ≤ δu / 2 := min_le_left _ _
  have hδc_le' : δc ≤ 1 / 16 := min_le_right _ _
  have hδc_lt : δc < 1 / 4 := lt_of_le_of_lt hδc_le' (by norm_num)
  let χ : ContDiffBump (0 : ℝ) :=
    ⟨(1 - 2 * δc) ^ 2, (1 - δc) ^ 2,
      by
        have : 0 < 1 - 2 * δc := by linarith
        positivity,
      by
        have h1 : 0 < 1 - 2 * δc := by linarith
        nlinarith [hδc_pos, hδc_lt, h1]⟩
  let χs : EuclideanSpace ℝ (Fin n) → ℝ := fun x => χ (‖x‖ ^ 2)
  let h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => (1 - χs x) • x + χs x • G x
  let f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => (‖h x‖)⁻¹ • h x
  have hχ_one : ∀ {t : ℝ}, |t| ≤ (1 - 2 * δc) ^ 2 → χ t = 1 := by
    intro t ht
    refine χ.one_of_mem_closedBall ?_
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
    simpa using ht
  have hχ_zero : ∀ {t : ℝ}, (1 - δc) ^ 2 ≤ |t| → χ t = 0 := by
    intro t ht
    refine χ.zero_of_le_dist ?_
    rw [dist_zero_right, Real.norm_eq_abs]
    simpa using ht
  have key : ∀ x : EuclideanSpace ℝ (Fin n), (1/2 : ℝ) ≤ ‖h x‖ := by
    intro x
    by_cases h1 : ‖x‖ ≤ 1 - 2 * δc
    · have hsq : ‖x‖ ^ 2 ≤ (1 - 2 * δc) ^ 2 := by
        have := norm_nonneg x
        nlinarith [h1, this]
      have hχx : χs x = 1 := by
        show χ (‖x‖ ^ 2) = 1
        exact hχ_one (by rw [abs_of_nonneg (sq_nonneg ‖x‖)]; exact hsq)
      have hhx : h x = G x := by
        show (1 - χs x) • x + χs x • G x = G x
        rw [hχx]; simp
      rw [hhx]
      have hx_mem : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        rw [mem_closedBall_zero_iff]; linarith [h1, hδc_pos]
      have hd : dist (G x) (r (ballProj x)) ≤ 1/8 := hG_close x hx_mem
      rw [dist_eq_norm] at hd
      have hu1 : ‖r (ballProj x)‖ = 1 := hu_norm x
      have hnu : ‖r (ballProj x)‖ ≤ ‖G x‖ + ‖G x - r (ballProj x)‖ := by
        calc ‖r (ballProj x)‖ = ‖G x - (G x - r (ballProj x))‖ := by rw [sub_sub_cancel]
          _ ≤ ‖G x‖ + ‖G x - r (ballProj x)‖ := norm_sub_le _ _
      linarith
    · by_cases h2 : 1 - δc ≤ ‖x‖
      · have hsq : (1 - δc) ^ 2 ≤ ‖x‖ ^ 2 := by
          have := norm_nonneg x
          nlinarith [h2, this, hδc_pos, hδc_lt]
        have hχx : χs x = 0 := by
          show χ (‖x‖ ^ 2) = 0
          exact hχ_zero (by rw [abs_of_nonneg (sq_nonneg ‖x‖)]; exact hsq)
        have hhx : h x = x := by
          show (1 - χs x) • x + χs x • G x = x
          rw [hχx]; simp
        rw [hhx]
        linarith [h2, hδc_le']
      · push Not at h2
        have h1' : 1 - 2 * δc < ‖x‖ := not_le.mp h1
        have hxnorm_pos : 0 < ‖x‖ := by linarith
        have hx_mem : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
          rw [mem_closedBall_zero_iff]; linarith [h2, hδc_pos]
        set y : EuclideanSpace ℝ (Fin n) := ‖x‖⁻¹ • x with hy
        have hy_norm : ‖y‖ = 1 := by
          rw [hy, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hxnorm_pos,
            inv_mul_cancel₀ hxnorm_pos.ne']
        have hy_mem : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
          rw [mem_closedBall_zero_iff]
          exact hy_norm.le
        have hxyval : dist x y = 1 - ‖x‖ := by
          have hsub : x - y = (1 - ‖x‖⁻¹) • x := by rw [hy, sub_smul, one_smul]
          have hlt : 1 - ‖x‖⁻¹ < 0 := by
            have : 1 < ‖x‖⁻¹ := (one_lt_inv₀ hxnorm_pos).mpr (by linarith [h2, hδc_pos])
            linarith
          rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_neg hlt, neg_sub, sub_mul,
            inv_mul_cancel₀ hxnorm_pos.ne', one_mul]
        have hxy_lt : dist x y < δu := by rw [hxyval]; linarith [h1', hδc_le]
        have hy_sphere : y ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
          rw [mem_sphere_iff_norm, sub_zero]
          exact hy_norm
        have hclose1 : dist (r x) y < 1/8 := by
          have hh := hδu x hx_mem y hy_mem hxy_lt
          rwa [hid y hy_sphere] at hh
        have hry_dist : ‖r x - x‖ ≤ 1/4 := by
          have htri := dist_triangle (r x) y x
          rw [dist_comm y x] at htri
          have h2' : dist x y < 2 * δc := by rw [hxyval]; linarith [h1']
          have hlt : dist (r x) x < 1/8 + 2 * δc := lt_of_le_of_lt htri (add_lt_add hclose1 h2')
          simp only [dist_eq_norm] at hlt
          linarith [hlt, hδc_le']
        have hGx_close : ‖G x - x‖ ≤ 3/8 := by
          have hd : dist (G x) (r (ballProj x)) ≤ 1/8 := hG_close x hx_mem
          have hbx : ballProj x = x := ballProj_eq_self hx_mem
          simp only [dist_eq_norm, hbx] at hd
          have htri : ‖G x - x‖ ≤ ‖G x - r x‖ + ‖r x - x‖ :=
            dist_triangle (G x) (r x) x
          linarith [htri, hd, hry_dist]
        have hχx_le : χs x ≤ 1 := χ.le_one
        have hχx_nn : 0 ≤ χs x := χ.nonneg
        have hhx : h x = x + χs x • (G x - x) := by
          show (1 - χs x) • x + χs x • G x = x + χs x • (G x - x)
          rw [smul_sub, sub_smul, one_smul]
          abel
        rw [hhx]
        have hsm : ‖χs x • (G x - x)‖ ≤ ‖G x - x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hχx_nn]
          exact mul_le_of_le_one_left (norm_nonneg _) hχx_le
        have htnorm : ‖x‖ - ‖G x - x‖ ≤ ‖x + χs x • (G x - x)‖ := by
          have hle : ‖x‖ ≤ ‖x + χs x • (G x - x)‖ + ‖χs x • (G x - x)‖ := by
            calc ‖x‖ = ‖(x + χs x • (G x - x)) - χs x • (G x - x)‖ := by rw [add_sub_cancel_right]
              _ ≤ ‖x + χs x • (G x - x)‖ + ‖χs x • (G x - x)‖ := norm_sub_le _ _
          linarith
        linarith [htnorm, hGx_close, h1', hδc_le']
  have hχs_cd : ContDiff ℝ 1 χs := by
    show ContDiff ℝ 1 fun x : EuclideanSpace ℝ (Fin n) => χ (‖x‖ ^ 2)
    exact (χ.contDiff).comp (contDiff_norm_sq ℝ)
  have hh_cd : ContDiff ℝ 1 h := by
    show ContDiff ℝ 1 fun x : EuclideanSpace ℝ (Fin n) => (1 - χs x) • x + χs x • G x
    exact ((contDiff_const.sub hχs_cd).smul contDiff_id).add (hχs_cd.smul hGcd)
  have hf_cd : ContDiff ℝ 1 f := by
    have hmaps : Set.MapsTo h Set.univ {y : EuclideanSpace ℝ (Fin n) | (1/4:ℝ) < ‖y‖} := by
      intro x hx
      show (1/4:ℝ) < ‖h x‖
      linarith [key x]
    have hcomp := (contDiffOn_invNorm_smul (n := n) (c := (1/4:ℝ)) (by norm_num)).comp
      hh_cd.contDiffOn hmaps
    rw [contDiffOn_univ] at hcomp
    exact hcomp
  have hf_norm : ∀ x : EuclideanSpace ℝ (Fin n), ‖f x‖ = 1 := by
    intro x
    have hpos : 0 < ‖h x‖ := lt_of_lt_of_le (by norm_num) (key x)
    show ‖(‖h x‖)⁻¹ • h x‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
  have hf_sphere : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, f x ∈ sphere 0 1 := by
    intro x hx
    rw [mem_sphere_iff_norm, sub_zero]
    exact hf_norm x
  have hf_id : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1, f x = x := by
    intro x hx
    have hnx : ‖x‖ = 1 := by
      have := mem_sphere_iff_norm.mp hx
      rwa [sub_zero] at this
    have hχ0 : χs x = 0 := by
      show χ (‖x‖ ^ 2) = 0
      refine hχ_zero ?_
      rw [hnx, one_pow, abs_one]
      nlinarith [hδc_pos, hδc_lt]
    have hx_h : h x = x := by
      show (1 - χs x) • x + χs x • G x = x
      rw [hχ0]; simp
    show (‖h x‖)⁻¹ • h x = x
    rw [hx_h, hnx]
    simp
  exact ⟨f, hf_cd, hf_sphere, hf_id⟩

end Work.Mostow
