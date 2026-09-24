import Mathlib
import Submission.Work.Potential.Defs
import Submission.Work.Potential.annulus_barrier_le
import Submission.Commons.Analysis.Complex.Dirichlet.dirichlet_ball
import Submission.Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le
import Submission.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

/-!
# Removable singularity for a harmonic function bounded near a point

`Work.Potential.removable_singularity_of_bounded_near`: a function `u` on a complex
one-manifold `X` which is harmonic off a point `z₀` and bounded in a punctured neighbourhood
of `z₀` extends to a function harmonic on all of `X`.

## Strategy

Write `c := chartAt ℂ z₀` for the preferred chart at `z₀` and `w := u ∘ c.symm`.  Choosing the
radius `ρ > 0` so that the Euclidean ball `Metric.ball (c z₀) ρ` lies in `c.target` and its
`c.symm`-image lies inside the neighbourhood on which `u` is bounded by `M`, the planar input
`punctured_ball_harmonic_extension` below (a function on `ℂ` harmonic and bounded by `M` on the
punctured ball `0 < ‖z - a‖ < ρ` extends to a function `h` harmonic on the whole ball
`‖z - a‖ < ρ`, agreeing with `w` off `a`) produces `h`.  The extension on `X` is then the
harmonic replacement `U := Submission.replaceOnDisc c (c z₀) ρ h u` (already in the
workspace): it equals `h ∘ c` inside the chart ball and `u` outside it.  Since `h ∘ c = u` on
the punctured chart ball, `U` agrees with `u` off `z₀`, and it is harmonic everywhere: at `z₀`
because near `z₀` its `c`-pullback is `h`, on the open chart ball because there it is `h ∘ c`
(chart independence of harmonicity), and outside the closed chart ball because there it is `u`.

## The planar core

`0 < ρ' < ρ`, `w` harmonic and bounded by `M` on the punctured ball `0 < ‖z - a‖ < ρ`.  On the
smaller ball of radius `ρ'` take the Dirichlet solution `v` of `w` (commons
`dirichlet_ball`), whose glued extension to the closed ball is continuous.  Applying the
maximum principle (commons `harmonic_le_of_boundary_le`) to `v` and to `-v` gives `|v| ≤ |M|`
on the ball.  The difference `Φ := gluedBall v w a ρ' - w` is harmonic and bounded on the
punctured annuli, vanishes on the outer circle `‖z - a‖ = ρ'` (continuity of the glued
function) and is bounded by `2|M|` on the inner circle; the logarithmic-barrier estimate
`Work.Potential.annulus_barrier_le` on `{δ < ‖z - a‖ < ρ'}` therefore gives
`|Φ y| ≤ 2|M| · log (ρ'/‖y-a‖) / log (ρ'/δ)` for every `δ > 0`, and the right-hand side tends
to `0` with `δ`, whence `v = w` on the punctured ball.  (Taking the Dirichlet radius strictly
smaller than `ρ` is what makes the *outer* circle lie in the region where `w` is harmonic, so
that the glued difference is genuinely continuous up to it.)
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
open Filter Set

noncomputable section

namespace Work.Potential

/-- Membership in a Euclidean ball, in the norm notation used for the harmonicity hypotheses. -/
theorem mem_ball_norm_iff {a z : ℂ} {ρ : ℝ} : z ∈ Metric.ball a ρ ↔ ‖z - a‖ < ρ := by
  rw [Metric.mem_ball, dist_eq_norm]

/-- `y + a = a` forces `y = 0`. -/
theorem eq_zero_of_add_eq_self {y a : ℂ} (h : y + a = a) : y = 0 := by
  have h' : y + a = (0 : ℂ) + a := by rw [zero_add]; exact h
  exact add_right_cancel h'

/-- The glued function written with the norm notation used throughout this file. -/
theorem gluedBall_apply_norm (u F : ℂ → ℝ) (a : ℂ) (ρ : ℝ) :
    Submission.gluedBall u F a ρ = fun z => if ‖z - a‖ < ρ then u z else F z := by
  funext z
  rw [Submission.gluedBall_apply, Metric.mem_ball, dist_eq_norm]

/-- Negating a glued function negates it pointwise. -/
theorem gluedBall_neg (a : ℂ) (R : ℝ) (v w : ℂ → ℝ) :
    Submission.gluedBall (fun z : ℂ => -v z) (fun z : ℂ => -w z) a R
      = fun z : ℂ => -(Submission.gluedBall v w a R z) := by
  funext z
  rw [Submission.gluedBall_apply, Submission.gluedBall_apply]
  by_cases hz : z ∈ Metric.ball a R <;> simp [hz]

/-! ## The planar core -/

/-- For `0 < t < R` and `ε > 0` there is `δ ∈ (0, t)` with `log (R/t) / log (R/δ) ≤ ε`. -/
theorem exists_log_div_le {R t ε : ℝ} (ht : 0 < t) (htR : t < R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < t ∧ Real.log (R / t) / Real.log (R / δ) ≤ ε := by
  have hR : 0 < R := lt_trans ht htR
  have hlogt : 0 < Real.log (R / t) := Real.log_pos ((one_lt_div ht).mpr htR)
  set L : ℝ := Real.log (R / t) / ε with hLdef
  have hLpos : 0 < L := div_pos hlogt hε
  refine ⟨(t / 2) * Real.exp (-(L + 1)), ?_, ?_, ?_⟩
  · positivity
  · have hexp : Real.exp (-(L + 1)) ≤ 1 := by
      have h1 : Real.exp (-(L + 1)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      simpa using h1
    calc (t / 2) * Real.exp (-(L + 1)) ≤ (t / 2) * 1 :=
          mul_le_mul_of_nonneg_left hexp (by linarith)
      _ < t := by linarith
  · have hδpos : 0 < (t / 2) * Real.exp (-(L + 1)) := by positivity
    have hlogδ : Real.log (R / ((t / 2) * Real.exp (-(L + 1))))
        = Real.log (R / (t / 2)) + (L + 1) := by
      rw [Real.log_div (ne_of_gt hR) (ne_of_gt hδpos),
        Real.log_mul (by linarith : (t / 2) ≠ 0) (Real.exp_pos _).ne', Real.log_exp]
      rw [Real.log_div (ne_of_gt hR) (by linarith : (t / 2) ≠ 0)]
      ring
    have hge : L ≤ Real.log (R / ((t / 2) * Real.exp (-(L + 1)))) := by
      rw [hlogδ]
      have hnn : 0 ≤ Real.log (R / (t / 2)) :=
        Real.log_nonneg ((one_le_div (by linarith)).mpr (by linarith))
      linarith
    calc Real.log (R / t) / Real.log (R / ((t / 2) * Real.exp (-(L + 1))))
        ≤ Real.log (R / t) / L := div_le_div_of_nonneg_left hlogt.le hLpos hge
      _ = ε := by
        rw [hLdef]
        field_simp

/-- **One-sided comparison estimate.**  Let `v` be the Dirichlet solution in the ball of radius
`R` around `a` for the boundary data `w`, with `|v| ≤ B` on that ball and `|w| ≤ B` on the
punctured ball of the larger radius `ρ` (and `w` harmonic there).  Then for every `0 < δ < R`
the difference `gluedBall v w a R - w` is bounded by the logarithmic barrier
`2B · log (R/δ)⁻¹ · log (R/‖y‖)` on the closed annulus `δ ≤ ‖y‖ ≤ R` (translated by `a`). -/
theorem gluedBall_sub_le {a : ℂ} {R ρ B δ : ℝ} (hR : 0 < R) (hRρ : R < ρ) (hδ : 0 < δ)
    (hδR : δ < R) (hB : 0 ≤ B) {v w : ℂ → ℝ}
    (hv : ∀ z : ℂ, ‖z - a‖ < R → InnerProductSpace.HarmonicAt v z)
    (hG : ContinuousOn (Submission.gluedBall v w a R) (Metric.closedBall a R))
    (hw : ∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → InnerProductSpace.HarmonicAt w z)
    (hvb : ∀ z : ℂ, ‖z - a‖ < R → |v z| ≤ B)
    (hwb : ∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → |w z| ≤ B) :
    ∀ y : ℂ, δ ≤ ‖y‖ → ‖y‖ ≤ R →
      Submission.gluedBall v w a R (y + a) - w (y + a)
        ≤ (2 * B) * (Real.log (R / δ))⁻¹ * Real.log (R / ‖y‖) := by
  classical
  set Φ : ℂ → ℝ := fun z => Submission.gluedBall v w a R z - w z with hΦdef
  refine Work.Potential.annulus_barrier_le (W := fun y : ℂ => Φ (y + a)) (δ := δ) (ρ := R)
    (B := 2 * B) hδ hδR (by linarith) ?_ ?_ ?_ ?_
  · -- harmonicity on the open annulus
    intro y hy1 hy2
    have hf : AnalyticAt ℂ (fun z : ℂ => z + a) y :=
      analyticAt_id.add (analyticAt_const (v := a) (x := y))
    have heq : (fun z : ℂ => Φ (z + a)) =ᶠ[𝓝 y]
        (fun z : ℂ => v (z + a) - w (z + a)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds
        (by rw [Metric.mem_ball, dist_zero_right]; exact hy2)] with z hz
      have hzR : ‖z‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      simp only [hΦdef]
      rw [Submission.gluedBall_of_mem (by rw [Metric.mem_ball, dist_eq_norm]; simpa using hzR)]
    exact (InnerProductSpace.harmonicAt_congr_nhds heq).mpr
      ((Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic hf
        (hv (y + a) (by simpa using hy2))).sub
        (Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic hf
          (hw (y + a) (by simpa using lt_trans hy2 hRρ) (by
            intro h
            have h0 : ‖y‖ = 0 := by rw [eq_zero_of_add_eq_self h, norm_zero]
            linarith [hy1, hδ]))))
  · -- continuity on the closed annulus
    have h1 : ContinuousOn (fun y : ℂ => Submission.gluedBall v w a R (y + a))
        {y : ℂ | δ ≤ ‖y‖ ∧ ‖y‖ ≤ R} :=
      hG.comp (continuousOn_id.add continuousOn_const) (fun y hy => by
        simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right]
        exact hy.2)
    have h2 : ContinuousOn (fun y : ℂ => w (y + a)) {y : ℂ | δ ≤ ‖y‖ ∧ ‖y‖ ≤ R} := by
      refine fun y hy => ?_
      have hyρ : ‖(y + a) - a‖ < ρ := by
        rw [add_sub_cancel_right]
        exact lt_of_le_of_lt hy.2 hRρ
      have hyne : y + a ≠ a := by
        intro h
        have h0 : ‖y‖ = 0 := by rw [eq_zero_of_add_eq_self h, norm_zero]
        linarith [hy.1, hδ]
      have hca : ContinuousAt (fun z : ℂ => w (z + a)) y :=
        ContinuousAt.comp (g := w) (f := fun z : ℂ => z + a)
          ((hw (y + a) hyρ hyne).1.continuousAt)
          (continuousAt_id.add continuousAt_const)
      exact hca.continuousWithinAt
    exact (h1.sub h2).congr (fun y _ => by simp only [hΦdef, Pi.sub_apply])
  · -- bound on the inner circle
    intro y hy
    have hgl : Submission.gluedBall v w a R (y + a) = v (y + a) :=
      Submission.gluedBall_of_mem (by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, hy]; exact hδR)
    have hyv : v (y + a) ≤ B :=
      le_trans (le_abs_self _) (hvb (y + a) (by rw [add_sub_cancel_right, hy]; exact hδR))
    have hyw : -w (y + a) ≤ B :=
      le_trans (neg_le_abs _) (hwb (y + a)
        (by rw [add_sub_cancel_right, hy]; exact lt_trans hδR hRρ)
        (by intro h; have h0 : ‖y‖ = 0 := by rw [eq_zero_of_add_eq_self h, norm_zero]
            linarith [hy, hδ]))
    simp only [hΦdef, hgl]
    linarith
  · -- vanishing on the outer circle
    intro y hy
    have hgl : Submission.gluedBall v w a R (y + a) = w (y + a) :=
      Submission.gluedBall_of_not_mem (by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, hy]; exact lt_irrefl R)
    simp only [hΦdef, hgl, sub_self]
    exact le_rfl

/-- **Two-sided comparison.**  Under the hypotheses of `gluedBall_sub_le`, the Dirichlet solution
`v` agrees with `w` on the punctured ball of radius `R`. -/
theorem gluedBall_eq_left_of_bounded {a : ℂ} {R ρ B : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (hB : 0 ≤ B) {v w : ℂ → ℝ}
    (hv : ∀ z : ℂ, ‖z - a‖ < R → InnerProductSpace.HarmonicAt v z)
    (hG : ContinuousOn (Submission.gluedBall v w a R) (Metric.closedBall a R))
    (hw : ∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → InnerProductSpace.HarmonicAt w z)
    (hvb : ∀ z : ℂ, ‖z - a‖ < R → |v z| ≤ B)
    (hwb : ∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → |w z| ≤ B) :
    ∀ p : ℂ, ‖p - a‖ < R → p ≠ a → v p = w p := by
  classical
  have hv' : ∀ z : ℂ, ‖z - a‖ < R → InnerProductSpace.HarmonicAt (fun z : ℂ => -v z) z :=
    fun z hz => (hv z hz).neg
  have hw' : ∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → InnerProductSpace.HarmonicAt (fun z : ℂ => -w z) z :=
    fun z hz hze => (hw z hz hze).neg
  have hvb' : ∀ z : ℂ, ‖z - a‖ < R → |(fun z : ℂ => -v z) z| ≤ B := fun z hz => by
    simpa using hvb z hz
  have hwb' : ∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → |(fun z : ℂ => -w z) z| ≤ B := fun z hz hze => by
    simpa using hwb z hz hze
  have hG' : ContinuousOn (Submission.gluedBall (fun z : ℂ => -v z) (fun z : ℂ => -w z) a R)
      (Metric.closedBall a R) := by
    rw [gluedBall_neg]
    exact hG.neg
  intro p hp hpa
  have ht : 0 < ‖p - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpa)
  have hbound : ∀ δ : ℝ, 0 < δ → δ < ‖p - a‖ →
      |Submission.gluedBall v w a R p - w p|
        ≤ (2 * B) * (Real.log (R / δ))⁻¹ * Real.log (R / ‖p - a‖) := by
    intro δ hδ hδt
    have hδR : δ < R := lt_trans hδt hp
    have h1 := gluedBall_sub_le hR hRρ hδ hδR hB hv hG hw hvb hwb (p - a) hδt.le hp.le
    have h2 := gluedBall_sub_le hR hRρ hδ hδR hB hv' hG' hw' hvb' hwb' (p - a) hδt.le hp.le
    rw [sub_add_cancel] at h1
    simp only [gluedBall_neg] at h2
    rw [sub_add_cancel] at h2
    have h2' : -(Submission.gluedBall v w a R p - w p)
        ≤ (2 * B) * (Real.log (R / δ))⁻¹ * Real.log (R / ‖p - a‖) := by
      linarith [h2]
    exact abs_le.mpr ⟨by linarith [h2'], h1⟩
  have hzero : |Submission.gluedBall v w a R p - w p| = 0 := by
    refine le_antisymm ?_ (abs_nonneg _)
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    by_cases hB0 : B = 0
    · have hb := hbound (‖p - a‖ / 2) (by linarith) (by linarith)
      have hz : |Submission.gluedBall v w a R p - w p| ≤ 0 := by
        simpa [hB0] using hb
      linarith
    · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
      have h2B : 0 < 2 * B := by linarith
      obtain ⟨δ, hδ0, hδt, hδle⟩ :=
        exists_log_div_le (R := R) (t := ‖p - a‖) (ε := ε / (2 * B)) ht hp (div_pos hε h2B)
      have hb := hbound δ hδ0 hδt
      have hstep : (2 * B) * (Real.log (R / δ))⁻¹ * Real.log (R / ‖p - a‖)
          = (2 * B) * (Real.log (R / ‖p - a‖) / Real.log (R / δ)) := by
        rw [mul_assoc, inv_mul_eq_div]
      rw [hstep] at hb
      have hle : (2 * B) * (Real.log (R / ‖p - a‖) / Real.log (R / δ)) ≤ ε := by
        calc (2 * B) * (Real.log (R / ‖p - a‖) / Real.log (R / δ))
            ≤ (2 * B) * (ε / (2 * B)) := mul_le_mul_of_nonneg_left hδle (by linarith)
          _ = ε := by
              rw [← mul_div_assoc, mul_div_cancel_left₀ ε (ne_of_gt h2B)]
      linarith [hb, hle]
  have hgl : Submission.gluedBall v w a R p = v p :=
    Submission.gluedBall_of_mem (mem_ball_norm_iff.mpr hp)
  rw [hgl] at hzero
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- **Removable singularity on a punctured Euclidean ball.**  A function harmonic and bounded on
the punctured ball `0 < ‖z - a‖ < ρ` extends to a function harmonic on the whole ball
`‖z - a‖ < ρ`, agreeing with it off the centre. -/
theorem punctured_ball_harmonic_extension {a : ℂ} {ρ M : ℝ} (hρ : 0 < ρ) {w : ℂ → ℝ}
    (hw : ∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → InnerProductSpace.HarmonicAt w z)
    (hb : ∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → |w z| ≤ M) :
    ∃ h : ℂ → ℝ,
      (∀ z : ℂ, ‖z - a‖ < ρ → InnerProductSpace.HarmonicAt h z) ∧
      (∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → h z = w z) := by
  classical
  set R : ℝ := ρ / 2 with hRdef
  have hR : 0 < R := by rw [hRdef]; linarith
  have hRρ : R < ρ := by rw [hRdef]; linarith
  -- the boundary data is continuous on the outer circle of the small ball
  have hFcont : ContinuousOn w (Metric.sphere a R) := by
    refine fun z hz => ?_
    have hzn : ‖z - a‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hzne : z ≠ a := by
      intro h
      rw [h, sub_self, norm_zero] at hzn
      linarith
    exact ((hw z (by rw [hzn]; exact hRρ) hzne).1.continuousAt).continuousWithinAt
  -- the Dirichlet solution on the small ball
  obtain ⟨v, hv, hG⟩ :=
    Commons.Analysis.Complex.Dirichlet.dirichlet_ball (c := a) (R := R) (F := w) hR hFcont
  have hG' : ContinuousOn (Submission.gluedBall v w a R) (Metric.closedBall a R) := by
    simpa only [gluedBall_apply_norm] using hG
  have hB : 0 ≤ |M| := abs_nonneg M
  have hsphere : ∀ y : ℂ, y ∈ Metric.sphere a R → |w y| ≤ M := by
    intro y hy
    have hyn : ‖y - a‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hy
    have hyne : y ≠ a := by
      intro h
      rw [h, sub_self, norm_zero] at hyn
      linarith
    exact hb y (by rw [hyn]; exact hRρ) hyne
  -- `|v| ≤ |M|` on the small ball
  have hvbound : ∀ z : ℂ, ‖z - a‖ < R → |v z| ≤ |M| := by
    intro z hz
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hneg : ∀ y : ℂ, ‖y - a‖ < R → (fun y : ℂ => -v y) y ≤ |M| := by
        refine Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le (c := a) (R := R)
          (M := |M|) (F := fun y : ℂ => -w y) (u := fun y : ℂ => -v y) hR ?_ ?_ ?_
        · intro y hy
          have h1 : -w y ≤ |M| := by linarith [hsphere y hy, neg_le_abs (w y), le_abs_self M]
          simpa using h1
        · intro y hy
          exact (hv y hy).neg
        · have h2 : ContinuousOn
              (Submission.gluedBall (fun y : ℂ => -v y) (fun y : ℂ => -w y) a R)
              (Metric.closedBall a R) := by
            rw [gluedBall_neg]
            exact hG'.neg
          simpa only [gluedBall_apply_norm] using h2
      linarith [hneg z hz]
    · refine Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le (c := a) (R := R)
        (M := |M|) (F := w) (u := v) hR (fun y hy => ?_) (fun y hy => hv y hy) ?_ z hz
      · exact le_trans (le_abs_self (w y)) (le_trans (hsphere y hy) (le_abs_self M))
      · simpa only [gluedBall_apply_norm] using hG'
  -- the Dirichlet solution agrees with `w` off the centre
  have heq : ∀ p : ℂ, ‖p - a‖ < R → p ≠ a → v p = w p :=
    gluedBall_eq_left_of_bounded (B := |M|) hR hRρ hB hv hG' hw hvbound
      (fun z hz hze => le_trans (hb z hz hze) (le_abs_self M))
  refine ⟨fun z => if z = a then v a else w z, ?_, ?_⟩
  · -- harmonicity everywhere
    intro z hz
    by_cases hza : z = a
    · have heq' : (fun z : ℂ => if z = a then v a else w z) =ᶠ[𝓝 a] v := by
        filter_upwards [Metric.ball_mem_nhds a hR] with y hy
        by_cases hya : y = a
        · simp [hya]
        · have hyR : ‖y - a‖ < R := mem_ball_norm_iff.mp hy
          simp only [hya, if_false]
          exact (heq y hyR hya).symm
      have hva : InnerProductSpace.HarmonicAt v a := hv a (by rw [sub_self, norm_zero]; exact hR)
      rw [hza]
      exact (InnerProductSpace.harmonicAt_congr_nhds heq').mpr hva
    · have heq' : (fun z : ℂ => if z = a then v a else w z) =ᶠ[𝓝 z] w := by
        filter_upwards [isOpen_ne.mem_nhds hza] with y hya
        simp only [hya, if_false]
      exact (InnerProductSpace.harmonicAt_congr_nhds heq').mpr (hw z hz hza)
  · intro z hz hza
    simp only [hza, if_false]

/-! ## Harmonicity is local -/

/-- Harmonicity at a point of a complex manifold is a local condition: a function agreeing with a
harmonic function on a neighbourhood of `x` is harmonic at `x`. -/
theorem harmonicOnXAt_congr {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u v : X → ℝ} {x : X} (h : Submission.HarmonicOnXAt u x) (huv : u =ᶠ[𝓝 x] v) :
    Submission.HarmonicOnXAt v x := by
  rw [Submission.HarmonicOnXAt] at h ⊢
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hpre : (fun z : ℂ => u ((chartAt ℂ x).symm z)) =ᶠ[𝓝 ((chartAt ℂ x) x)]
      (fun z : ℂ => v ((chartAt ℂ x).symm z)) := by
    have h1 : Filter.Tendsto (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) x)) (𝓝 x) := by
      have h2 := ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hxsrc)).tendsto
      rwa [(chartAt ℂ x).left_inv hxsrc] at h2
    exact h1.eventually huv
  exact (InnerProductSpace.harmonicAt_congr_nhds hpre).mp h

/-! ## The manifold level -/

theorem removable_singularity_of_bounded_near
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {z₀ : X} {u : X → ℝ}
    (hu : Submission.HarmonicOnX u (Set.univ \ {z₀}))
    (hb : ∃ M : ℝ, ∃ V : Set X, V ∈ nhds z₀ ∧ ∀ x ∈ V, x ≠ z₀ → |u x| ≤ M) :
    ∃ U : X → ℝ, Submission.HarmonicOnX U Set.univ ∧ ∀ x, x ≠ z₀ → U x = u x := by
  classical
  obtain ⟨M, V, hVmem, hVb⟩ := hb
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ z₀
  have hz₀src : z₀ ∈ c.source := mem_chart_source ℂ z₀
  have hw₀tgt : c z₀ ∈ c.target := c.map_source hz₀src
  -- radii: the closed chart ball lies in the chart target, and the open chart ball lies in `V`
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds hw₀tgt)
  have hsymm_nhds : {z : ℂ | c.symm z ∈ V} ∈ 𝓝 (c z₀) := by
    have h1 : V ∈ 𝓝 (c.symm (c z₀)) := by rw [c.left_inv hz₀src]; exact hVmem
    exact (c.continuousAt_symm hw₀tgt).eventually h1
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.mem_nhds_iff.mp hsymm_nhds
  set ρ : ℝ := min (ρ₁ / 2) (ρ₂ / 2) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min (half_pos hρ₁) (half_pos hρ₂)
  have hρ_lt₁ : ρ < ρ₁ := by
    rw [hρdef]
    linarith [min_le_left (ρ₁ / 2) (ρ₂ / 2)]
  have hρ_le₂ : ρ ≤ ρ₂ := by
    rw [hρdef]
    linarith [min_le_right (ρ₁ / 2) (ρ₂ / 2)]
  have hclsub : Metric.closedBall (c z₀) ρ ⊆ c.target :=
    (Metric.closedBall_subset_ball hρ_lt₁).trans hρ₁sub
  have hballsub : Metric.ball (c z₀) ρ ⊆ c.target := Metric.ball_subset_closedBall.trans hclsub
  have hρV : ∀ z : ℂ, ‖z - c z₀‖ < ρ → c.symm z ∈ V := by
    intro z hz
    refine hρ₂sub ?_
    exact mem_ball_norm_iff.mpr (lt_of_lt_of_le hz hρ_le₂)
  -- harmonicity and boundedness of the pulled-back function on the punctured chart ball
  have hwharm : ∀ z : ℂ, ‖z - c z₀‖ < ρ → z ≠ c z₀ →
      InnerProductSpace.HarmonicAt (fun y : ℂ => u (c.symm y)) z := by
    intro z hz hzne
    have hzt : z ∈ c.target := hρ₁sub (mem_ball_norm_iff.mpr (lt_trans hz hρ_lt₁))
    have hcs : c.symm z ∈ (chartAt ℂ z₀).source := c.map_target hzt
    have hne : c.symm z ≠ z₀ := by
      intro h
      exact hzne (by rw [← c.right_inv hzt, h])
    have h1 : Submission.HarmonicOnXAt u (c.symm z) := hu (c.symm z) ⟨mem_univ _, hne⟩
    have h2 := (Submission.HarmonicOnXAt_iff_chart (u := u) (x := c.symm z) (y := z₀) hcs).mp h1
    rw [show z = (chartAt ℂ z₀) (c.symm z) from (c.right_inv hzt).symm]
    exact h2
  have hwbnd : ∀ z : ℂ, ‖z - c z₀‖ < ρ → z ≠ c z₀ → |u (c.symm z)| ≤ M := by
    intro z hz hzne
    have hzt : z ∈ c.target := hρ₁sub (mem_ball_norm_iff.mpr (lt_trans hz hρ_lt₁))
    refine hVb (c.symm z) (hρV z hz) ?_
    intro h
    exact hzne (by rw [← c.right_inv hzt, h])
  -- the planar input
  obtain ⟨h, hharm, heq⟩ := punctured_ball_harmonic_extension (a := c z₀) (ρ := ρ) (M := M)
    hρpos hwharm hwbnd
  refine ⟨Submission.replaceOnDisc c (c z₀) ρ h u, ?_, ?_⟩
  · -- harmonicity on all of `X`
    intro x _
    by_cases hx0 : x = z₀
    · -- at the puncture: the `c`-pullback of `U` is `h` near `c z₀`
      rw [hx0, Submission.HarmonicOnXAt]
      have heq'' : h =ᶠ[𝓝 ((chartAt ℂ z₀) z₀)]
          ((Submission.replaceOnDisc c (c z₀) ρ h u) ∘ (chartAt ℂ z₀).symm) := by
        filter_upwards [Metric.ball_mem_nhds (c z₀) hρpos] with z hz
        show h z = Submission.replaceOnDisc c (c z₀) ρ h u (c.symm z)
        rw [Submission.replaceOnDisc_pullback_of_mem hballsub hz]
      exact (InnerProductSpace.harmonicAt_congr_nhds heq'').mp
        (hharm (c z₀) (mem_ball_norm_iff.mp (Metric.mem_ball_self hρpos)))
    · -- away from the puncture, `U` agrees with `u` on a neighbourhood
      have heq'' : u =ᶠ[𝓝 x] Submission.replaceOnDisc c (c z₀) ρ h u := by
        filter_upwards [isOpen_ne.mem_nhds hx0] with y hyne
        by_cases hyb : y ∈ Submission.chartBall c (c z₀) ρ
        · rw [Submission.replaceOnDisc_of_mem_chartBall hyb]
          have hyne' : c y ≠ c z₀ := fun hh => hyne (c.injOn hyb.1 hz₀src hh)
          have h1 := heq (c y) (mem_ball_norm_iff.mp hyb.2) hyne'
          rw [c.left_inv hyb.1] at h1
          exact h1.symm
        · exact (Submission.replaceOnDisc_of_not_mem_chartBall hyb).symm
      exact harmonicOnXAt_congr (hu x ⟨mem_univ x, hx0⟩) heq''
  · -- agreement off the puncture
    intro x hxne
    by_cases hxb : x ∈ Submission.chartBall c (c z₀) ρ
    · have hxsrc : x ∈ c.source := hxb.1
      have hcxne : c x ≠ c z₀ := fun hh => hxne (c.injOn hxsrc hz₀src hh)
      rw [Submission.replaceOnDisc_of_mem_chartBall hxb,
        heq (c x) (mem_ball_norm_iff.mp hxb.2) hcxne, c.left_inv hxsrc]
    · rw [Submission.replaceOnDisc_of_not_mem_chartBall hxb]

end Work.Potential
