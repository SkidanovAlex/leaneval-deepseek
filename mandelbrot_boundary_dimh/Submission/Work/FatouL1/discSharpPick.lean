import Mathlib
import Submission.Work.FatouL1.schwarzDeficitBound
import Submission.Work.Motion.schwarz_pick_deriv

/-!
# The sharp Schwarz–Pick estimate on the unit disc

A holomorphic map of the unit disc into the *closed* unit disc satisfies, at every point `ζ`
of the disc,
`‖deriv F ζ‖ ≤ (1 - ‖F ζ‖ ^ 2) / (1 - ‖ζ‖ ^ 2)`.

The proof is the classical Schwarz–Pick reduction: if `‖F ζ‖ < 1`, conjugate `F` by the disc
automorphisms `mob (F ζ)` and `mob (-ζ)`; the composite fixes `0` and maps the disc into itself,
so the Schwarz lemma (`Complex.norm_deriv_le_one_of_mapsTo_ball`) applies at the centre, and the
chain rule together with `Work.Motion.norm_deriv_mob_aux` gives the estimate.  The boundary case
`‖F ζ‖ = 1` is handled by applying the previous case to the scaled maps `r * F`, `r < 1`, and
letting `r → 1⁻`.
-/

namespace Work.FatouL1

open Metric Set
open scoped ComplexConjugate

/-- Schwarz–Pick in the case where the value stays strictly inside the disc. -/
theorem discSharpPickAux {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hmap : Set.MapsTo F (Metric.ball 0 1) (Metric.closedBall 0 1))
    {ζ : ℂ} (hζ : ζ ∈ Metric.ball 0 1) (ha : ‖F ζ‖ < 1) :
    ‖deriv F ζ‖ ≤ (1 - ‖F ζ‖ ^ 2) / (1 - ‖ζ‖ ^ 2) := by
  have hζ1 : ‖ζ‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hζ
  have hamem : F ζ ∈ Metric.ball 0 1 := by rw [Metric.mem_ball, dist_zero_right]; exact ha
  obtain ⟨_, hdm, hm0⟩ := Work.Motion.mob_disc ha
  have hneg : ‖-ζ‖ < 1 := by rwa [norm_neg]
  obtain ⟨hmapw, hdw, _⟩ := Work.Motion.mob_disc hneg
  have hmobw0 : Work.Motion.mob (-ζ) 0 = ζ := by simp [Work.Motion.mob]
  have hda : ‖deriv (Work.Motion.mob (F ζ)) (F ζ)‖ = (1 - ‖F ζ‖ ^ 2)⁻¹ :=
    (Work.Motion.norm_deriv_mob_aux ha).1
  have hdw0 : ‖deriv (Work.Motion.mob (-ζ)) 0‖ = 1 - ‖ζ‖ ^ 2 := by
    have h := (Work.Motion.norm_deriv_mob_aux hneg).2
    rwa [norm_neg] at h
  let G : ℂ → ℂ := fun t => Work.Motion.mob (F ζ) (F (Work.Motion.mob (-ζ) t))
  have hcomp : DifferentiableOn ℂ (F ∘ (Work.Motion.mob (-ζ))) (Metric.ball 0 1) :=
    hF.comp hdw hmapw
  have hGdiff : DifferentiableOn ℂ G (Metric.ball 0 1) := by
    change DifferentiableOn ℂ (fun t => (F (Work.Motion.mob (-ζ) t) - F ζ)
      / (1 - conj (F ζ) * F (Work.Motion.mob (-ζ) t))) (Metric.ball 0 1)
    refine (hcomp.sub_const (F ζ)).div
      ((differentiableOn_const (1 : ℂ)).sub ((differentiableOn_const (conj (F ζ))).mul hcomp)) ?_
    intro t ht hzero
    have h1 : conj (F ζ) * F (Work.Motion.mob (-ζ) t) = 1 := (sub_eq_zero.mp hzero).symm
    have h2 : ‖conj (F ζ) * F (Work.Motion.mob (-ζ) t)‖ = 1 := by rw [h1, norm_one]
    rw [norm_mul, Complex.norm_conj] at h2
    have hFw : ‖F (Work.Motion.mob (-ζ) t)‖ ≤ 1 :=
      mem_closedBall_zero_iff.mp (hmap (hmapw ht))
    nlinarith [ha, hFw, norm_nonneg (F ζ)]
  have hG0 : G 0 = 0 := by
    change (F (Work.Motion.mob (-ζ) 0) - F ζ) / (1 - conj (F ζ) * F (Work.Motion.mob (-ζ) 0)) = 0
    rw [hmobw0, sub_self, zero_div]
  have hGmap : Set.MapsTo G (Metric.ball 0 1) (Metric.closedBall (G 0) 1) := by
    intro t ht
    rw [hG0, Metric.mem_closedBall, dist_zero_right]
    change ‖Work.Motion.mob (F ζ) (F (Work.Motion.mob (-ζ) t))‖ ≤ 1
    exact norm_mob_le_one ha (mem_closedBall_zero_iff.mp (hmap (hmapw ht)))
  have hSch : ‖deriv G 0‖ ≤ 1 :=
    Complex.norm_deriv_le_one_of_mapsTo_ball hGdiff hGmap (by norm_num)
  have hFcomp_diff : DifferentiableAt ℂ (F ∘ (Work.Motion.mob (-ζ))) 0 := by
    have h1 : DifferentiableAt ℂ (Work.Motion.mob (-ζ)) 0 :=
      hdw.differentiableAt (Metric.ball_mem_nhds 0 zero_lt_one)
    have h2 : DifferentiableAt ℂ F ((Work.Motion.mob (-ζ)) 0) := by
      rw [hmobw0]; exact hF.differentiableAt (Metric.isOpen_ball.mem_nhds hζ)
    exact h2.comp 0 h1
  have hmoba_diff : DifferentiableAt ℂ (Work.Motion.mob (F ζ)) ((F ∘ (Work.Motion.mob (-ζ))) 0) := by
    have hpt : (F ∘ (Work.Motion.mob (-ζ))) 0 = F ζ := by
      simp only [Function.comp_apply, hmobw0]
    rw [hpt]
    exact hdm.differentiableAt (Metric.isOpen_ball.mem_nhds hamem)
  have hGderiv : deriv G 0
      = deriv (Work.Motion.mob (F ζ)) (F ζ) * (deriv F ζ * deriv (Work.Motion.mob (-ζ)) 0) := by
    have hinner : deriv (F ∘ (Work.Motion.mob (-ζ))) 0
        = deriv F ζ * deriv (Work.Motion.mob (-ζ)) 0 := by
      have h := deriv_comp (h := Work.Motion.mob (-ζ)) (h₂ := F) 0
        (by rw [hmobw0]; exact hF.differentiableAt (Metric.isOpen_ball.mem_nhds hζ))
        (hdw.differentiableAt (Metric.ball_mem_nhds 0 zero_lt_one))
      rwa [hmobw0] at h
    have houter := deriv_comp (h := F ∘ (Work.Motion.mob (-ζ)))
      (h₂ := Work.Motion.mob (F ζ)) 0 hmoba_diff hFcomp_diff
    rw [hinner] at houter
    simp only [Function.comp_apply, hmobw0] at houter
    change deriv ((Work.Motion.mob (F ζ)) ∘ (F ∘ (Work.Motion.mob (-ζ)))) 0 = _
    rw [houter]
  have hnorm : ‖deriv G 0‖ = (1 - ‖F ζ‖ ^ 2)⁻¹ * (‖deriv F ζ‖ * (1 - ‖ζ‖ ^ 2)) := by
    rw [hGderiv, norm_mul, norm_mul, hda, hdw0]
  have hFwpos : 0 < 1 - ‖F ζ‖ ^ 2 := by nlinarith [norm_nonneg (F ζ)]
  have hX : ‖deriv F ζ‖ * (1 - ‖ζ‖ ^ 2) ≤ 1 - ‖F ζ‖ ^ 2 := by
    have h1 : (1 - ‖F ζ‖ ^ 2)⁻¹ * (‖deriv F ζ‖ * (1 - ‖ζ‖ ^ 2)) ≤ 1 := by
      rw [← hnorm]; exact hSch
    rw [inv_mul_eq_div] at h1
    exact (div_le_one hFwpos).mp h1
  have hzpos : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  rw [le_div_iff₀ hzpos]
  exact hX

/-- **Sharp Schwarz–Pick estimate.** A holomorphic map of the unit disc into the closed unit disc
satisfies `‖deriv F ζ‖ ≤ (1 - ‖F ζ‖ ^ 2) / (1 - ‖ζ‖ ^ 2)` at every point `ζ` of the disc. -/
theorem discSharpPick {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hmap : Set.MapsTo F (Metric.ball 0 1) (Metric.closedBall 0 1))
    {ζ : ℂ} (hζ : ζ ∈ Metric.ball 0 1) :
    ‖deriv F ζ‖ ≤ (1 - ‖F ζ‖ ^ 2) / (1 - ‖ζ‖ ^ 2) := by
  have hζnorm : ‖ζ‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hζ
  have hQpos : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have hPnonneg : 0 ≤ ‖F ζ‖ ^ 2 := sq_nonneg _
  have hPle : ‖F ζ‖ ^ 2 ≤ 1 := by
    have h := hmap hζ
    rw [Metric.mem_closedBall, dist_zero_right] at h
    nlinarith [norm_nonneg (F ζ)]
  have hscale : ∀ r : ℝ, 0 < r → r < 1 →
      r * ‖deriv F ζ‖ ≤ (1 - r ^ 2 * ‖F ζ‖ ^ 2) / (1 - ‖ζ‖ ^ 2) := by
    intro r hr0 hr1
    have hr : ‖(r : ℂ)‖ = r := (RCLike.norm_ofReal r).trans (abs_of_pos hr0)
    have hFd : DifferentiableOn ℂ (fun z : ℂ => (r : ℂ) * F z) (Metric.ball 0 1) :=
      hF.const_mul (r : ℂ)
    have hFm : Set.MapsTo (fun z : ℂ => (r : ℂ) * F z) (Metric.ball 0 1)
        (Metric.closedBall 0 1) := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul, hr]
      have hz1 : ‖F z‖ ≤ 1 := by
        have h := hmap hz
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      nlinarith
    have ha : ‖(r : ℂ) * F ζ‖ < 1 := by
      rw [norm_mul, hr]
      nlinarith [norm_nonneg (F ζ), hPle]
    have hA := discSharpPickAux hFd hFm hζ ha
    have hderiv : deriv (fun z : ℂ => (r : ℂ) * F z) ζ = (r : ℂ) * deriv F ζ :=
      deriv_const_mul (r : ℂ) (hF.differentiableAt (Metric.isOpen_ball.mem_nhds hζ))
    have hnorm : ‖deriv (fun z : ℂ => (r : ℂ) * F z) ζ‖ = r * ‖deriv F ζ‖ := by
      rw [hderiv, norm_mul, hr]
    have hnorm2 : ‖(r : ℂ) * F ζ‖ ^ 2 = r ^ 2 * ‖F ζ‖ ^ 2 := by
      rw [norm_mul, hr]; ring
    rw [hnorm, hnorm2] at hA
    exact hA
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  set Q : ℝ := 1 - ‖ζ‖ ^ 2 with hQdef
  set P : ℝ := ‖F ζ‖ ^ 2 with hPdef
  have hQp : 0 < Q := by rw [hQdef]; exact hQpos
  have hPp : 0 ≤ P := by rw [hPdef]; exact hPnonneg
  have hPl : P ≤ 1 := by rw [hPdef]; exact hPle
  set δ : ℝ := ε * Q / (2 + ε * Q) with hδdef
  have hden : 0 < 2 + ε * Q := by positivity
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδlt : δ < 1 := by
    rw [hδdef, div_lt_one hden]; linarith
  have hb := hscale (1 - δ) (by linarith) (by linarith)
  have hstep : 2 * δ ≤ ε * Q * (1 - δ) := by
    have h : δ * (2 + ε * Q) = ε * Q := by rw [hδdef]; field_simp
    nlinarith [h]
  have hkey2 : δ * (1 + P * (1 - δ)) ≤ ε * Q * (1 - δ) := by
    have hPd : P * (1 - δ) ≤ 1 := by nlinarith [hPp, hPl, hδpos, hδlt]
    have h1 : 1 + P * (1 - δ) ≤ 2 := by linarith
    have h2 : δ * (1 + P * (1 - δ)) ≤ δ * 2 := mul_le_mul_of_nonneg_left h1 hδpos.le
    linarith
  have hfinal : 1 - (1 - δ) ^ 2 * P ≤ (1 - δ) * ((1 - P) + ε * Q) := by
    nlinarith [hkey2]
  have hkey : (1 - (1 - δ) ^ 2 * P) / Q ≤ (1 - δ) * ((1 - P) / Q + ε) := by
    rw [div_le_iff₀ hQp]
    have h5 : ((1 - δ) * ((1 - P) / Q + ε)) * Q = (1 - δ) * ((1 - P) + ε * Q) := by
      rw [mul_assoc, add_mul, div_mul_cancel₀ _ hQp.ne']
    rw [h5]
    exact hfinal
  have hmain : (1 - δ) * ‖deriv F ζ‖ ≤ (1 - δ) * ((1 - P) / Q + ε) := le_trans hb hkey
  exact le_of_mul_le_mul_left hmain (by linarith)

end Work.FatouL1
