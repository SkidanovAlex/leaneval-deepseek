import Mathlib
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.isOpen_Zc
import Submission.Work.Drive.cone_chain
import Submission.Work.Drive.tendsto_slope_diag
import Submission.Work.Drive.secant_len_lower

/-!
# The diagonal limit of the strip data

`Work.Drive.stripData γ (mk2 u v)` is the capping data `(r, d, η)` of the chord of `γ` with
parameters `(u, v)` (radius, normalised midpoint in the disk, doubled chord direction).  On the
diagonal `u = v` the chord degenerates and the raw formula is meaningless; this file computes the
limit of `s ↦ stripData γ (mk2 (a + s) (a - s))` as `s → 0⁺`, which is the value the (continuous)
extension at the diagonal must take:

* the radius tends to `‖γ (exp a)‖` (Euclidean norm),
* the disk coordinate tends to the unit vector in the direction of the midpoint `γ (exp a)`
  (and to `0` when `γ (exp a) = 0`, i.e. `⟨γ (exp a).1, γ (exp a).2⟩ / ‖γ (exp a)‖ = 0/0 = 0`),
* the doubled direction tends to the doubled direction of the tangent
  `deriv (fun t => γ (exp t)) a`.

The first two coordinates are continuity statements; the third is the (filter form of the) secant
slope limit `Work.Drive.secant_dirC_limit` / `Work.Drive.tendsto_slope_diag`.  The only delicate
point is the disk coordinate when the curve passes through the origin: there the numerator and the
denominator both vanish, and one needs the *second order* (in fact only the little-o `o (s)`)
statement that the symmetric second difference `F (a + s) + F (a - s) - 2 F a` is `o (s)`, together
with the lower bound `c s ≤ ‖F (a + s) - F (a - s)‖` for the secant length
(`Work.Drive.secant_len_lower`).
-/

namespace Work.Drive

open Filter Set Manifold
open scoped Topology ContDiff Manifold
open Submission.Geometry
open Submission.Collision (dirC)

noncomputable section

variable {γ : Circle → ℝ × ℝ}

/-! ## Euclidean-norm helpers -/

/-- Continuity of the Euclidean norm of `ℝ × ℝ`. -/
lemma continuous_eucNorm : Continuous (fun p : ℝ × ℝ => eucNorm p) := by
  have h : (fun p : ℝ × ℝ => eucNorm p) = fun p => Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
    funext p
    simp [eucNorm, eucDot_self]
  rw [h]
  exact Real.continuous_sqrt.comp (by fun_prop)

/-- Halving the argument halves the Euclidean norm. -/
lemma eucNorm_div_two (U : ℝ × ℝ) : eucNorm (U / 2) = eucNorm U / 2 := by
  have h : U / 2 = (2 : ℝ)⁻¹ • U := by
    refine Prod.ext ?_ ?_
    · change (U.1 / 2 : ℝ) = (2 : ℝ)⁻¹ • U.1
      rw [div_eq_mul_inv, smul_eq_mul, mul_comm]
    · change (U.2 / 2 : ℝ) = (2 : ℝ)⁻¹ • U.2
      rw [div_eq_mul_inv, smul_eq_mul, mul_comm]
  rw [h, Submission.Configuration.eucNorm_smul,
    abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹), inv_mul_eq_div]

/-! ## The strip coordinates on the diagonal -/

/-- The squared radius of the configuration point is the sum of the squared midpoint and the squared
chord length. -/
lemma stripA_eq (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    stripA γ w = eucNorm (stripMid γ w) ^ 2
      + eucNorm (γ (Circle.exp (w 0)) - γ (Circle.exp (w 1))) ^ 2 := by
  have h : Complex.normSq (chordC γ (w 0, w 1))
      = eucNorm (γ (Circle.exp (w 0)) - γ (Circle.exp (w 1))) ^ 2 := by
    rw [← Submission.Collision.normC_eq_eucNorm, Complex.normSq_eq_norm_sq, chordC]
  rw [stripA, stripChord, h, ← eucDot_self, ← eucNorm_sq]

/-- The strip radius dominates the chord length. -/
lemma chord_le_stripR (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    eucNorm (γ (Circle.exp (w 0)) - γ (Circle.exp (w 1))) ≤ stripR γ w := by
  change eucNorm (γ (Circle.exp (w 0)) - γ (Circle.exp (w 1))) ≤ Real.sqrt (stripA γ w)
  rw [stripA_eq]
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (eucNorm (stripMid γ w))])

/-- The numerator of the disk coordinate of the strip, as a complex number. -/
def stripNum (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  ((stripMid γ w).1 : ℂ) + ((stripMid γ w).2 : ℂ) * Complex.I

/-- The disk coordinate of the strip is the quotient of `stripNum` by the radius. -/
lemma stripD_eq_stripNum (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    stripD γ w = stripNum γ w / (((stripR γ w : ℝ)) : ℂ) := rfl

/-- The modulus of the disk coordinate: the Euclidean norm of the midpoint divided by the radius
(so that `ℝ × ℝ` is measured with the *Euclidean* norm here, not the sup norm). -/
lemma norm_stripD (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    ‖stripD γ w‖ = eucNorm (stripMid γ w) / stripR γ w := by
  have h1 : ‖stripNum γ w‖ = eucNorm (stripMid γ w) := by
    rw [stripNum, ← complex_mk_eq_add_mul_I, Submission.Collision.normC_eq_eucNorm]
  have h2 : ‖(((stripR γ w : ℝ)) : ℂ)‖ = stripR γ w := by
    have h3 : ‖(((stripR γ w : ℝ)) : ℂ)‖ ^ 2 = stripR γ w ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    have h4 : 0 ≤ ‖(((stripR γ w : ℝ)) : ℂ)‖ := norm_nonneg _
    have h5 : 0 ≤ stripR γ w := Real.sqrt_nonneg _
    have h6 : |‖(((stripR γ w : ℝ)) : ℂ)‖| = |stripR γ w| :=
      (sq_eq_sq_iff_abs_eq_abs _ _).mp h3
    rwa [abs_of_nonneg h4, abs_of_nonneg h5] at h6
  rw [stripD_eq_stripNum, norm_div, h1, h2]

/-- The midpoint of the diagonal pair. -/
lemma stripMid_diag_eq (γ : Circle → ℝ × ℝ) (a s : ℝ) :
    stripMid γ (mk2 (a + s) (a - s)) = (curve γ (a + s) + curve γ (a - s)) / 2 := by
  simp [stripMid, mk2_apply_zero, mk2_apply_one, curve]

/-! ## The diagonal limit -/

theorem tendsto_stripData_diag (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (a : ℝ) :
    Filter.Tendsto (fun s : ℝ => Work.Drive.stripData γ (Work.Drive.mk2 (a + s) (a - s)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Submission.Geometry.eucNorm (γ (Circle.exp a)),
           ((⟨(γ (Circle.exp a)).1, (γ (Circle.exp a)).2⟩ : ℂ)) /
             ((Submission.Geometry.eucNorm (γ (Circle.exp a)) : ℝ) : ℂ),
           Submission.Collision.dirC (deriv (fun t : ℝ => γ (Circle.exp t)) a))) := by
  have hFtop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (curve γ) :=
    (hγ.contMDiff.comp contMDiff_circleExp).contDiff
  have hF1 : ContDiff ℝ 1 (curve γ) := hFtop.of_le (by simp)
  have hFc : Continuous (curve γ) := hFtop.continuous
  have hnear : Continuous (fun s : ℝ => curve γ (a + s)) :=
    hFc.comp (continuous_const.add continuous_id)
  have hfar : Continuous (fun s : ℝ => curve γ (a - s)) :=
    hFc.comp (continuous_const.sub continuous_id)
  have hsub : Continuous (fun s : ℝ => curve γ (a + s) - curve γ (a - s)) := hnear.sub hfar
  -- ## the midpoint
  have hmid : Tendsto (fun s : ℝ => stripMid γ (mk2 (a + s) (a - s)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (curve γ a)) := by
    have hcont : Continuous (fun s : ℝ => stripMid γ (mk2 (a + s) (a - s))) := by
      have heq : (fun s : ℝ => stripMid γ (mk2 (a + s) (a - s)))
          = fun s => (curve γ (a + s) + curve γ (a - s)) / 2 := by
        funext s
        exact stripMid_diag_eq γ a s
      rw [heq]
      exact (hnear.add hfar).div_const 2
    have h0 : stripMid γ (mk2 (a + 0) (a - 0)) = curve γ a := by
      rw [stripMid_diag_eq]
      simp [add_self_div_two_prod]
    rw [← h0]
    exact Tendsto.mono_left (ContinuousAt.tendsto (hcont.continuousAt (x := (0 : ℝ))))
      nhdsWithin_le_nhds
  -- ## the chord
  have hchord : Tendsto (fun s : ℝ => stripChord γ (mk2 (a + s) (a - s)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    have hpair : Tendsto (fun s : ℝ => curve γ (a + s) - curve γ (a - s))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
      simpa using Tendsto.mono_left
        (ContinuousAt.tendsto (hsub.continuousAt (x := (0 : ℝ)))) nhdsWithin_le_nhds
    have hcp : Continuous (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by fun_prop
    have hval := (hcp.continuousAt (x := (0 : ℝ × ℝ))).tendsto.comp hpair
    have heq : ((fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) ∘
          (fun s : ℝ => curve γ (a + s) - curve γ (a - s)))
        = fun s : ℝ => stripChord γ (mk2 (a + s) (a - s)) := by
      funext s
      simp only [Function.comp_apply, stripChord, chordC, mk2_apply_zero, mk2_apply_one, curve,
        complex_mk_eq_add_mul_I]
    simpa only [heq, Prod.fst_zero, Prod.snd_zero, Complex.ofReal_zero, zero_mul, add_zero]
      using hval
  -- ## the radial coordinate
  have hR : Tendsto (fun s : ℝ => stripR γ (mk2 (a + s) (a - s)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (eucNorm (curve γ a))) := by
    have hpair2 : Tendsto (fun s : ℝ => (stripMid γ (mk2 (a + s) (a - s)),
        stripChord γ (mk2 (a + s) (a - s)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (curve γ a, 0)) := by
      rw [nhds_prod_eq]
      exact hmid.prodMk hchord
    have hAlg : Continuous (fun p : (ℝ × ℝ) × ℂ => p.1.1 ^ 2 + p.1.2 ^ 2 + Complex.normSq p.2) := by
      fun_prop
    have hA := (hAlg.continuousAt (x := (curve γ a, 0))).tendsto.comp hpair2
    have hval2 : ((curve γ a).1 ^ 2 + (curve γ a).2 ^ 2 + Complex.normSq (0 : ℂ))
        = eucNorm (curve γ a) ^ 2 := by
      rw [Complex.normSq_zero, add_zero, eucNorm_sq, eucDot_self]
    rw [hval2] at hA
    have hsqrt := Tendsto.comp (ContinuousAt.tendsto (Real.continuous_sqrt.continuousAt
      (x := eucNorm (curve γ a) ^ 2))) hA
    have hs : Real.sqrt (eucNorm (curve γ a) ^ 2) = eucNorm (curve γ a) :=
      Real.sqrt_sq (eucNorm_nonneg _)
    rw [hs] at hsqrt
    simpa only [Function.comp_def, stripR, stripA, curve] using hsqrt
  have h1 : Tendsto (fun s : ℝ => (stripData γ (mk2 (a + s) (a - s))).1)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (eucNorm (curve γ a))) := by
    simpa only [stripData_fst] using hR
  -- ## the doubled direction
  have hslope : Tendsto (fun s : ℝ => ((a + s) - (a - s))⁻¹ • (curve γ (a + s) - curve γ (a - s)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (deriv (curve γ) a)) := by
    have hq : Tendsto (fun s : ℝ => (a - s, a + s)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin (a, a) {q : ℝ × ℝ | q.1 < q.2}) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hp : Continuous (fun s : ℝ => (a - s, a + s)) :=
          (continuous_const.sub continuous_id).prodMk (continuous_const.add continuous_id)
        simpa using Tendsto.mono_left (ContinuousAt.tendsto (hp.continuousAt (x := (0 : ℝ))))
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have hs' : (0 : ℝ) < s := hs
        show a - s < a + s
        linarith
    have h := (tendsto_slope_diag (curve γ) hF1 a).comp hq
    simpa only [Function.comp_def] using h
  have hdirC : Tendsto (fun s : ℝ => (stripData γ (mk2 (a + s) (a - s))).2.2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (dirC (deriv (curve γ) a))) := by
    have hne : deriv (curve γ) a ≠ 0 := curve_deriv_ne_zero γ hγ a
    have hcont : ContinuousAt dirC (deriv (curve γ) a) :=
      Submission.Configuration.continuousOn_dirC.continuousAt
        ((isOpen_ne (x := (0 : ℝ × ℝ))).mem_nhds hne)
    have hcomp : Tendsto
        (fun s : ℝ => dirC (((a + s) - (a - s))⁻¹ • (curve γ (a + s) - curve γ (a - s))))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (dirC (deriv (curve γ) a))) :=
      hcont.tendsto.comp hslope
    have heq : (fun s : ℝ => dirC (((a + s) - (a - s))⁻¹ • (curve γ (a + s) - curve γ (a - s))))
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun s : ℝ => dirC (curve γ (a + s) - curve γ (a - s)) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : (0 : ℝ) < s := hs
      have h2s : (a + s) - (a - s) ≠ 0 := by linarith
      exact dirC_smul_ne (inv_ne_zero h2s) _
    have hdirC' := Tendsto.congr' heq hcomp
    have heq2 : (fun s : ℝ => (stripData γ (mk2 (a + s) (a - s))).2.2)
        = fun s : ℝ => dirC (curve γ (a + s) - curve γ (a - s)) := by
      funext s
      simp only [stripData_thd, mk2_apply_zero, mk2_apply_one, curve]
    rw [heq2]
    exact hdirC'
  -- ## the disk coordinate
  have hD : Tendsto (fun s : ℝ => (stripData γ (mk2 (a + s) (a - s))).2.1)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (⟨(curve γ a).1, (curve γ a).2⟩ / ((eucNorm (curve γ a) : ℝ) : ℂ))) := by
    simp only [stripData_snd]
    by_cases hFa : curve γ a = 0
    · -- the curve passes through the origin: the limit is `0`
      have hzero : (⟨(curve γ a).1, (curve γ a).2⟩ : ℂ) / ((eucNorm (curve γ a) : ℝ) : ℂ) = 0 := by
        have h3 : eucNorm (curve γ a) = 0 := eucNorm_eq_zero.mpr hFa
        simp [h3]
      rw [hzero]
      have hcpos : 0 < eucNorm (deriv (curve γ) a) :=
        eucNorm_pos (curve_deriv_ne_zero γ hγ a)
      -- the symmetric second difference of the curve is `o (s)`
      set φ : ℝ → ℝ × ℝ := ((fun y : ℝ => curve γ (a + y)) + (fun y : ℝ => curve γ (a - y))
        - fun _ : ℝ => (2 : ℝ) • curve γ a) with hφdef
      have hPhi : HasDerivAt φ 0 0 := by
        have hdd : HasDerivAt (curve γ) (deriv (curve γ) a) a :=
          (((hF1.differentiable (by norm_num))).differentiableAt (x := a)).hasDerivAt
        have hd1 : HasDerivAt (curve γ) (deriv (curve γ) a) (a + 0) := by
          simpa using hdd
        have hd2 : HasDerivAt (curve γ) (deriv (curve γ) a) (a - 0) := by
          simpa using hdd
        have hh1 : HasDerivAt (fun y : ℝ => a + y) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add a
        have hA : HasDerivAt (fun y : ℝ => curve γ (a + y)) (deriv (curve γ) a) 0 := by
          have h := hd1.scomp (x := (0 : ℝ)) hh1
          simpa only [Function.comp_def, one_smul] using h
        have hh2 : HasDerivAt (fun y : ℝ => a - y) (-1) 0 := (hasDerivAt_id (0 : ℝ)).const_sub a
        have hB : HasDerivAt (fun y : ℝ => curve γ (a - y)) (-(deriv (curve γ) a)) 0 := by
          have h := hd2.scomp (x := (0 : ℝ)) hh2
          simpa only [Function.comp_def, neg_one_smul] using h
        have hC : HasDerivAt (fun _ : ℝ => (2 : ℝ) • curve γ a) 0 0 :=
          hasDerivAt_const (0 : ℝ) ((2 : ℝ) • curve γ a)
        have h4 := (hA.add hB).sub hC
        have h5 : deriv (curve γ) a + -deriv (curve γ) a - 0 = (0 : ℝ × ℝ) := by simp
        rw [h5] at h4
        rw [hφdef]
        exact h4
      have hslope0 : Tendsto (fun t : ℝ => t⁻¹ • (φ (0 + t) - φ 0))
          (nhdsWithin (0 : ℝ) ({0}ᶜ)) (𝓝 0) := hPhi.tendsto_slope_zero
      have heqφ : (fun t : ℝ => t⁻¹ • (φ (0 + t) - φ 0))
          = fun t : ℝ => t⁻¹ • (curve γ (a + t) + curve γ (a - t)) := by
        funext t
        rw [hφdef]
        simp only [Pi.add_apply, Pi.sub_apply, zero_add, sub_zero, hFa,
          smul_zero, sub_self, add_zero]
      have hsum : Tendsto (fun t : ℝ => t⁻¹ • (curve γ (a + t) + curve γ (a - t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
        have hmono := hslope0.mono_left
          (nhdsWithin_mono (0 : ℝ) (by intro x hx; exact ne_of_gt hx))
        rw [heqφ] at hmono
        exact hmono
      have heuc : Tendsto (fun t : ℝ => eucNorm (t⁻¹ • (curve γ (a + t) + curve γ (a - t))))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
        have h0 : eucNorm (0 : ℝ × ℝ) = 0 := by simp [eucNorm, eucDot_self]
        have h := (continuous_eucNorm.continuousAt (x := (0 : ℝ × ℝ))).tendsto.comp hsum
        simpa only [h0, Function.comp_def] using h
      have hratio : Tendsto (fun s : ℝ => eucNorm (stripMid γ (mk2 (a + s) (a - s))) / s)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
        have h2 : Tendsto (fun s : ℝ => (1 / 2 : ℝ) *
            eucNorm (s⁻¹ • (curve γ (a + s) + curve γ (a - s))))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 ((1 / 2 : ℝ) * 0)) :=
          heuc.const_mul (1 / 2)
        rw [mul_zero] at h2
        refine Tendsto.congr' ?_ h2
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hs' : (0 : ℝ) < s := hs
        rw [stripMid_diag_eq, eucNorm_div_two, Submission.Configuration.eucNorm_smul,
          abs_of_pos (inv_pos.mpr hs'), div_eq_mul_inv]
        ring
      have hlb : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          eucNorm (deriv (curve γ) a) * s ≤ stripR γ (mk2 (a + s) (a - s)) := by
        obtain ⟨δ, hδpos, hδ⟩ := secant_len_lower γ hγ a
        have hδev : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), s < δ := by
          rw [eventually_nhdsWithin_iff]
          filter_upwards [eventually_lt_nhds hδpos] with s hs _
          exact hs
        filter_upwards [hδev, self_mem_nhdsWithin] with s hsδ hspos
        have hspos' : (0 : ℝ) < s := hspos
        exact le_trans (hδ s hspos' hsδ) (chord_le_stripR γ (mk2 (a + s) (a - s)))
      have hupper : Tendsto (fun s : ℝ => eucNorm (stripMid γ (mk2 (a + s) (a - s))) /
          (eucNorm (deriv (curve γ) a) * s)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
        have h2 : Tendsto (fun s : ℝ => (eucNorm (stripMid γ (mk2 (a + s) (a - s))) / s) /
            eucNorm (deriv (curve γ) a)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (𝓝 (0 / eucNorm (deriv (curve γ) a))) := hratio.div_const _
        rw [zero_div] at h2
        refine Tendsto.congr' ?_ h2
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hspos : (0 : ℝ) < s := hs
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
        ring
      have hsqueeze : Tendsto (fun s : ℝ => ‖stripD γ (mk2 (a + s) (a - s))‖)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
        · filter_upwards with s
          exact norm_nonneg _
        · filter_upwards [hlb, self_mem_nhdsWithin] with s hlb' hspos
          have hspos' : (0 : ℝ) < s := hspos
          rw [norm_stripD]
          exact div_le_div_of_nonneg_left (eucNorm_nonneg _) (by positivity) hlb'
      exact tendsto_zero_iff_norm_tendsto_zero.mpr hsqueeze
    · -- the curve avoids the origin: continuity of the quotient
      have hnum : Tendsto (fun s : ℝ => stripNum γ (mk2 (a + s) (a - s)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (⟨(curve γ a).1, (curve γ a).2⟩ : ℂ)) := by
        have hcp : Continuous (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by fun_prop
        have h := (hcp.continuousAt (x := (curve γ a))).tendsto.comp hmid
        simpa only [Function.comp_def, stripNum, complex_mk_eq_add_mul_I] using h
      have hRc : Tendsto (fun s : ℝ => ((stripR γ (mk2 (a + s) (a - s)) : ℝ) : ℂ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 ((eucNorm (curve γ a) : ℝ) : ℂ)) := by
        have h := (Complex.continuous_ofReal.tendsto (eucNorm (curve γ a))).comp hR
        simpa only [Function.comp_def] using h
      have hneR : eucNorm (curve γ a) ≠ 0 := fun h => hFa (eucNorm_eq_zero.mp h)
      have hne : ((eucNorm (curve γ a) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hneR
      have hres : Tendsto (fun s : ℝ => stripNum γ (mk2 (a + s) (a - s)) /
          ((stripR γ (mk2 (a + s) (a - s)) : ℝ) : ℂ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (𝓝 (⟨(curve γ a).1, (curve γ a).2⟩ / ((eucNorm (curve γ a) : ℝ) : ℂ))) :=
        hnum.div hRc hne
      simpa only [Function.comp_def, stripD_eq_stripNum] using hres
  -- ## assembly
  have htriple : Tendsto (fun s : ℝ => ((stripData γ (mk2 (a + s) (a - s))).1,
      ((stripData γ (mk2 (a + s) (a - s))).2.1, (stripData γ (mk2 (a + s) (a - s))).2.2)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (eucNorm (curve γ a),
        (⟨(curve γ a).1, (curve γ a).2⟩ / ((eucNorm (curve γ a) : ℝ) : ℂ),
          dirC (deriv (curve γ) a)))) := by
    simp only [nhds_prod_eq]
    exact h1.prodMk (hD.prodMk hdirC)
  refine Tendsto.congr' (Eventually.of_forall (fun s => rfl)) htriple

end

end Work.Drive
