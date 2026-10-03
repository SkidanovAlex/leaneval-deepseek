import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Motion.schwarz_pick_deriv

/-!
# The Schwarz deficit bound

For a function `h` holomorphic on a ball `Metric.ball z₀ R` and bounded by `M` there,
the Schwarz–Pick lemma gives the *deficit* estimate

`‖deriv h z₀‖ ≤ (M ^ 2 - ‖h z₀‖ ^ 2) / (M * R) ≤ 2 * (M - ‖h z₀‖) / R`.

The proof is the classical one: normalise the ball to the unit disc, move `h z₀ / M` to `0` by
the disc automorphism `mob` of `Submission.Work.Motion`, apply the Schwarz lemma
(`Complex.norm_deriv_le_one_of_mapsTo_ball`) and read off the derivative via the chain rule.
The closed-ball hypothesis is handled with an `ε`-argument replacing `M` by `M + δ`.
-/

namespace Work.FatouL1

open Metric Set
open scoped ComplexConjugate

/-- The disc automorphism `mob a` of `Submission.Work.Motion` maps the *closed* unit disc into
itself: for `‖a‖ < 1` and `‖t‖ ≤ 1` one has `‖mob a t‖ ≤ 1`. -/
theorem norm_mob_le_one {a t : ℂ} (ha : ‖a‖ < 1) (ht : ‖t‖ ≤ 1) :
    ‖Work.Motion.mob a t‖ ≤ 1 := by
  have haSq : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have htSq : Complex.normSq t ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg t]
  have hle : Complex.normSq (t - a) ≤ Complex.normSq (1 - conj a * t) := by
    have h := Work.Motion.normSq_one_sub_conj_mul a t
    have h2 : 0 ≤ (1 - Complex.normSq a) * (1 - Complex.normSq t) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hden : 1 - conj a * t ≠ 0 := by
    intro h
    have h1 : conj a * t = 1 := (sub_eq_zero.mp h).symm
    have h2 : ‖(1 : ℂ)‖ = ‖conj a * t‖ := by rw [h1]
    rw [norm_one, norm_mul, Complex.norm_conj] at h2
    have h3 : ‖a‖ * ‖t‖ < 1 := by nlinarith [ha, ht, norm_nonneg a, norm_nonneg t]
    linarith
  rw [Work.Motion.mob_apply, norm_div, div_le_one (norm_pos_iff.mpr hden)]
  have hnormsq : ‖t - a‖ ^ 2 ≤ ‖1 - conj a * t‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    exact hle
  have hsq := sq_le_sq.mp hnormsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at hsq

/-- **Sharp Schwarz–Pick deficit bound.** If `f` is holomorphic on `Metric.ball c R` and
`‖f z‖ < M` there with `M > 0`, then `‖deriv f c‖ ≤ (M ^ 2 - ‖f c‖ ^ 2) / (M * R)`. -/
theorem schwarzDeficitSharp {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c R)) (hM : 0 < M)
    (hbdd : ∀ z ∈ Metric.ball c R, ‖f z‖ < M) :
    ‖deriv f c‖ ≤ (M ^ 2 - ‖f c‖ ^ 2) / (M * R) := by
  have hMnorm : ‖(M : ℂ)‖ = M := by
    have h : ‖(M : ℂ)‖ = |M| := RCLike.norm_ofReal M
    rw [abs_of_pos hM] at h
    exact h
  have hRnorm : ‖(R : ℂ)‖ = R := by
    have h : ‖(R : ℂ)‖ = |R| := RCLike.norm_ofReal R
    rw [abs_of_pos hR] at h
    exact h
  have hc : c ∈ Metric.ball c R := mem_ball_self hR
  have hfc : DifferentiableAt ℂ f c := hf.differentiableAt (isOpen_ball.mem_nhds hc)
  -- the normalised origin of the target disc
  set a : ℂ := f c / (M : ℂ) with ha_def
  have ha_norm : ‖a‖ = ‖f c‖ / M := by
    rw [ha_def, norm_div, hMnorm]
  have ha_lt : ‖a‖ < 1 := by
    rw [ha_norm, div_lt_one hM]
    exact hbdd c hc
  have ha_mem : a ∈ Metric.ball 0 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact ha_lt
  -- the rescaled map on the unit disc
  have hmap : Set.MapsTo (fun u : ℂ => c + (R : ℂ) * u) (Metric.ball 0 1) (Metric.ball c R) := by
    intro u hu
    rw [Metric.mem_ball, dist_zero_right] at hu
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, hRnorm]
    nlinarith [norm_nonneg u]
  set F : ℂ → ℂ := fun u => f (c + (R : ℂ) * u) / (M : ℂ) with hF_def
  have hF_diff : DifferentiableOn ℂ F (Metric.ball 0 1) := by
    have h1 : DifferentiableOn ℂ (fun u : ℂ => f (c + (R : ℂ) * u)) (Metric.ball 0 1) :=
      hf.comp (by fun_prop) hmap
    exact h1.div_const (M : ℂ)
  have hF_lt : ∀ u ∈ Metric.ball 0 1, ‖F u‖ < 1 := by
    intro u hu
    rw [hF_def, norm_div, hMnorm, div_lt_one hM]
    exact hbdd _ (hmap hu)
  have hF0 : F 0 = a := by rw [hF_def, ha_def]; simp
  have himg : Set.MapsTo F (Metric.ball 0 1) (Metric.ball 0 1) := by
    intro u hu
    rw [Metric.mem_ball, dist_zero_right]
    exact hF_lt u hu
  -- the Möbius-normalised map
  have hmob_a : Work.Motion.mob a a = 0 := by
    rw [Work.Motion.mob_apply]; simp
  have hG_diff : DifferentiableOn ℂ (fun u => Work.Motion.mob a (F u)) (Metric.ball 0 1) :=
    ((Work.Motion.mob_disc ha_lt).2.1).comp hF_diff himg
  have hSch : ‖deriv (fun u => Work.Motion.mob a (F u)) 0‖ ≤ 1 := by
    refine Complex.norm_deriv_le_one_of_mapsTo_ball hG_diff ?_ (by norm_num : (0:ℝ) < 1)
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm]
    show ‖Work.Motion.mob a (F u) - Work.Motion.mob a (F 0)‖ ≤ 1
    rw [hF0, hmob_a, sub_zero]
    exact norm_mob_le_one ha_lt (hF_lt u hu).le
  -- the derivative of the rescaled map
  have hd' : HasDerivAt f (deriv f c) (c + (R : ℂ) * 0) := by simpa using hfc.hasDerivAt
  have hFderiv : deriv F 0 = deriv f c * (R : ℂ) / (M : ℂ) := by
    have h1 : HasDerivAt (fun u : ℂ => f (c + (R : ℂ) * u)) (deriv f c * (R : ℂ)) 0 :=
      hd'.comp 0 (Work.Motion.hasDerivAt_affine c R 0)
    have h2 : HasDerivAt F (deriv f c * (R : ℂ) / (M : ℂ)) 0 := by
      simpa [hF_def] using h1.div_const (M : ℂ)
    exact h2.deriv
  have hmob_diff : DifferentiableAt ℂ (Work.Motion.mob a) (F 0) := by
    rw [hF0]
    exact (Work.Motion.mob_disc ha_lt).2.1.differentiableAt (isOpen_ball.mem_nhds ha_mem)
  have hF_diff0 : DifferentiableAt ℂ F 0 := hF_diff.differentiableAt (ball_mem_nhds 0 one_pos)
  have hGderiv : deriv (fun u => Work.Motion.mob a (F u)) 0
      = deriv (Work.Motion.mob a) (F 0) * deriv F 0 := by
    have hd := deriv_comp (h := F) (h₂ := Work.Motion.mob a) 0 hmob_diff hF_diff0
    simpa only [Function.comp_def] using hd
  have hnorm_mob : ‖deriv (Work.Motion.mob a) a‖ = (1 - ‖a‖ ^ 2)⁻¹ :=
    (Work.Motion.norm_deriv_mob_aux ha_lt).1
  have hGderiv_norm : ‖deriv (fun u => Work.Motion.mob a (F u)) 0‖
      = (1 - ‖a‖ ^ 2)⁻¹ * (‖deriv f c‖ * R / M) := by
    rw [hGderiv, hF0, norm_mul, hnorm_mob, hFderiv]
    congr 1
    simp only [norm_div, norm_mul, hRnorm, hMnorm]
  -- extract the estimate
  have hpos : 0 < 1 - ‖a‖ ^ 2 := by
    have : ‖a‖ ^ 2 < 1 := by nlinarith [norm_nonneg a, ha_lt]
    linarith
  have hX : ‖deriv f c‖ * R / M ≤ 1 - ‖a‖ ^ 2 := by
    have h1 : (1 - ‖a‖ ^ 2)⁻¹ * (‖deriv f c‖ * R / M) ≤ 1 := by
      rw [← hGderiv_norm]; exact hSch
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hpos)
    have h3 : (1 - ‖a‖ ^ 2) * ((1 - ‖a‖ ^ 2)⁻¹ * (‖deriv f c‖ * R / M))
        = ‖deriv f c‖ * R / M := by
      field_simp
    linarith [h2, h3.le, h3.symm.le]
  have hA2 : 1 - ‖a‖ ^ 2 = (M ^ 2 - ‖f c‖ ^ 2) / M ^ 2 := by
    rw [ha_norm]
    field_simp
  rw [hA2] at hX
  have key : M ^ 2 * (‖deriv f c‖ * R / M) ≤ M ^ 2 - ‖f c‖ ^ 2 := by
    have h2 := mul_le_mul_of_nonneg_left hX (by positivity : (0:ℝ) ≤ M ^ 2)
    have h3 : ((M ^ 2 - ‖f c‖ ^ 2) / M ^ 2) * M ^ 2 = M ^ 2 - ‖f c‖ ^ 2 := by
      field_simp
    linarith [h2, h3.le, h3.symm.le]
  rw [le_div_iff₀ (mul_pos hM hR)]
  have h4 : M ^ 2 * (‖deriv f c‖ * R / M) = ‖deriv f c‖ * (M * R) := by
    field_simp
  linarith [key, h4]

theorem schwarzDeficitBound {h : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R)
    (hhol : DifferentiableOn ℂ h (Metric.ball z₀ R))
    (hbdd : ∀ z ∈ Metric.ball z₀ R, ‖h z‖ ≤ M) :
    ‖deriv h z₀‖ ≤ 2 * (M - ‖h z₀‖) / R := by
  have hz₀ : z₀ ∈ Metric.ball z₀ R := mem_ball_self hR
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  set δ : ℝ := ε * R / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hMδ : 0 < M + δ := by linarith [norm_nonneg (h z₀), hbdd z₀ hz₀]
  have hlt : ‖h z₀‖ < M + δ := by linarith [hbdd z₀ hz₀]
  have hsharp := schwarzDeficitSharp (f := h) (c := z₀) (R := R) (M := M + δ)
    hR hhol hMδ (fun z hz => by linarith [hbdd z hz])
  have hstep : ((M + δ) ^ 2 - ‖h z₀‖ ^ 2) / ((M + δ) * R) ≤ 2 * (M - ‖h z₀‖) / R + ε := by
    have hA : ‖h z₀‖ ≤ M + δ := hlt.le
    have hnum : (M + δ) ^ 2 - ‖h z₀‖ ^ 2 ≤ 2 * (M + δ - ‖h z₀‖) * (M + δ) := by
      nlinarith [hA]
    have hδM : 0 < M + δ := hMδ
    have hdiv : ((M + δ) ^ 2 - ‖h z₀‖ ^ 2) / ((M + δ) * R)
        ≤ 2 * (M + δ - ‖h z₀‖) / R := by
      rw [div_le_div_iff₀ (mul_pos hδM hR) hR]
      nlinarith [hnum, hR]
    have heq : 2 * (M + δ - ‖h z₀‖) / R = 2 * (M - ‖h z₀‖) / R + ε := by
      rw [hδ]; field_simp; try ring
    linarith [hdiv, heq.le, heq.symm.le]
  linarith [hsharp, hstep]

end Work.FatouL1
