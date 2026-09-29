import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.tendsto_log_at_neg_real

/-!
# `Work.A14D.log_relations_at_real`

**Boundary values on the real axis.**  `X` is holomorphic on the ball `ball (1/9) δ` and `B` is
holomorphic on the punctured ball, and the function `z ↦ κ·X z·log (z − 1/9) + B z` vanishes on
the upper (resp. lower) half of that ball.  Then the relation also holds at every *real* point
`x` of the punctured ball which lies to the left of the singularity `1/9`: approaching such a
point from the upper half-plane the principal branch of `Complex.log` takes the boundary value
`log|x − 1/9| + πi`, and from the lower half-plane the value `log|x − 1/9| − πi`.

The proof is the one-sided limit along the curves `ε ↦ x ± ε i` (`ε → 0⁺`): on those curves the
identity holds eventually, the sum `κ·X·log (· − 1/9) + B` is continuous there, and the limit is
computed with the boundary values of `Complex.log` at the negative real axis
(`Work.A14D.tendsto_log_at_neg_real`).  Uniqueness of limits then gives the two claimed relations.
-/

open Complex Metric Filter
open scoped Topology

noncomputable section

namespace Work.A14D

/-- Boundary value of `log (· − 1/9)` at a real point `x < 1/9`, approached from the upper
half-plane: `log ((x + εi) − 1/9) → log ‖x − 1/9‖ + πi`. -/
private lemma tendsto_log_curve_U {x : ℝ} (hx : x < 1 / 9) :
    Tendsto (fun ε : ℝ => Complex.log (((x : ℂ) + ε * Complex.I) - ninth)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log ‖(x : ℂ) - ninth‖ + Real.pi * Complex.I)) := by
  have h := (tendsto_log_at_neg_real (a := x - 1 / 9) (by linarith)).1
  have hfun : ∀ ε : ℝ, Complex.log (((x - 1 / 9 : ℝ) : ℂ) + ε * Complex.I)
      = Complex.log (((x : ℂ) + ε * Complex.I) - ninth) := by
    intro ε; congr 1
    rw [ninth]; push_cast; ring
  have hval : Real.log (-(x - 1 / 9)) = Real.log ‖(x : ℂ) - ninth‖ := by
    congr 1
    rw [show (x : ℂ) - ninth = ((x - 1 / 9 : ℝ) : ℂ) by rw [ninth]; push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
  simpa only [hval] using h.congr' (Eventually.of_forall hfun)

/-- Boundary value of `log (· − 1/9)` at a real point `x < 1/9`, approached from the lower
half-plane: `log ((x − εi) − 1/9) → log ‖x − 1/9‖ − πi`. -/
private lemma tendsto_log_curve_L {x : ℝ} (hx : x < 1 / 9) :
    Tendsto (fun ε : ℝ => Complex.log (((x : ℂ) - ε * Complex.I) - ninth)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log ‖(x : ℂ) - ninth‖ - Real.pi * Complex.I)) := by
  have h := (tendsto_log_at_neg_real (a := x - 1 / 9) (by linarith)).2
  have hfun : ∀ ε : ℝ, Complex.log (((x - 1 / 9 : ℝ) : ℂ) - ε * Complex.I)
      = Complex.log (((x : ℂ) - ε * Complex.I) - ninth) := by
    intro ε; congr 1
    rw [ninth]; push_cast; ring
  have hval : Real.log (-(x - 1 / 9)) = Real.log ‖(x : ℂ) - ninth‖ := by
    congr 1
    rw [show (x : ℂ) - ninth = ((x - 1 / 9 : ℝ) : ℂ) by rw [ninth]; push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
  simpa only [hval] using h.congr' (Eventually.of_forall hfun)

theorem log_relations_at_real {δ : ℝ} (hδ : 0 < δ) {X B : ℂ → ℂ} {κU κL : ℂ}
    (hX : DifferentiableOn ℂ X (Metric.ball ninth δ))
    (hB : DifferentiableOn ℂ B (Metric.ball ninth δ \ {ninth}))
    (hU : ∀ z ∈ halfU δ, κU * X z * Complex.log (z - ninth) + B z = 0)
    (hL : ∀ z ∈ halfL δ, κL * X z * Complex.log (z - ninth) + B z = 0) :
    ∀ x : ℝ, 1 / 9 - δ < x → x < 1 / 9 →
      (κU * X (x : ℂ) * (Real.log ‖(x : ℂ) - ninth‖ + Real.pi * Complex.I) + B (x : ℂ) = 0) ∧
      (κL * X (x : ℂ) * (Real.log ‖(x : ℂ) - ninth‖ - Real.pi * Complex.I) + B (x : ℂ) = 0) := by
  intro x hx1 hx2
  -- the point `x` lies in the punctured ball around `1/9`
  have hball : ‖(x : ℂ) - ninth‖ < δ := by
    have h1 : (x : ℂ) - ninth = ((x - 1 / 9 : ℝ) : ℂ) := by
      rw [ninth]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hxU : (x : ℂ) ∈ Metric.ball ninth δ := by
    rw [Metric.mem_ball]; rwa [dist_eq_norm]
  have hxne : (x : ℂ) ≠ ninth := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re, ninth, Complex.div_ofNat_re] at hre
    norm_num at hre
    linarith
  -- continuity of `X` and `B` at the real point
  have hXc : ContinuousAt X (x : ℂ) :=
    hX.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hxU)
  have hBc : ContinuousAt B (x : ℂ) :=
    hB.continuousOn.continuousAt
      ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hxU, by simpa using hxne⟩)
  -- the two curves `ε ↦ x ± εi` tend to `x`
  have hcurveU : Tendsto (fun ε : ℝ => (x : ℂ) + ε * Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
    have h1 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).ofReal
    simpa using (h1.mul_const Complex.I).const_add (x : ℂ)
  have hcurveL : Tendsto (fun ε : ℝ => (x : ℂ) - ε * Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
    have h1 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).ofReal
    simpa [sub_eq_add_neg] using ((h1.mul_const Complex.I).neg).const_add (x : ℂ)
  have hXt : Tendsto (fun ε : ℝ => X ((x : ℂ) + ε * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 (X (x : ℂ))) :=
    hXc.tendsto.comp hcurveU
  have hBt : Tendsto (fun ε : ℝ => B ((x : ℂ) + ε * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 (B (x : ℂ))) :=
    hBc.tendsto.comp hcurveU
  have hXtL : Tendsto (fun ε : ℝ => X ((x : ℂ) - ε * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 (X (x : ℂ))) :=
    hXc.tendsto.comp hcurveL
  have hBtL : Tendsto (fun ε : ℝ => B ((x : ℂ) - ε * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 (B (x : ℂ))) :=
    hBc.tendsto.comp hcurveL
  -- the curves lie in the two half-balls, close to `ε = 0⁺`
  have hmemU : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ), (x : ℂ) + ε * Complex.I ∈ halfU δ := by
    have hcont : ContinuousAt (fun ε : ℝ => (x : ℂ) + ε * Complex.I) 0 :=
      (by fun_prop : Continuous (fun ε : ℝ => (x : ℂ) + ε * Complex.I)).continuousAt
    have hb : ∀ᶠ (ε : ℝ) in 𝓝 (0 : ℝ),
        (x : ℂ) + ε * Complex.I ∈ Metric.ball ninth δ :=
      hcont.tendsto.eventually
        (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball]; simpa [dist_eq_norm] using hball))
    filter_upwards [hb.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ε hεb hεpos
    exact ⟨hεb, by simpa using hεpos⟩
  have hmemL : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ), (x : ℂ) - ε * Complex.I ∈ halfL δ := by
    have hcont : ContinuousAt (fun ε : ℝ => (x : ℂ) - ε * Complex.I) 0 :=
      (by fun_prop : Continuous (fun ε : ℝ => (x : ℂ) - ε * Complex.I)).continuousAt
    have hb : ∀ᶠ (ε : ℝ) in 𝓝 (0 : ℝ),
        (x : ℂ) - ε * Complex.I ∈ Metric.ball ninth δ :=
      hcont.tendsto.eventually
        (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball]; simpa [dist_eq_norm] using hball))
    filter_upwards [hb.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ε hεb hεpos
    refine ⟨hεb, ?_⟩
    have hεpos' : (0 : ℝ) < ε := hεpos
    show ((x : ℂ) - ε * Complex.I).im < 0
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re]
    linarith
  constructor
  · -- upper half-plane
    have hzero : Tendsto (fun ε : ℝ => κU * X ((x : ℂ) + ε * Complex.I)
        * Complex.log (((x : ℂ) + ε * Complex.I) - ninth) + B ((x : ℂ) + ε * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (tendsto_const_nhds (x := (0 : ℂ))).congr' (hmemU.mono (fun ε hε => (hU _ hε).symm))
    have hlim : Tendsto (fun ε : ℝ => κU * X ((x : ℂ) + ε * Complex.I)
        * Complex.log (((x : ℂ) + ε * Complex.I) - ninth) + B ((x : ℂ) + ε * Complex.I))
        (𝓝[>] (0 : ℝ))
        (𝓝 (κU * X (x : ℂ) * (Real.log ‖(x : ℂ) - ninth‖ + Real.pi * Complex.I) + B (x : ℂ))) :=
      (((tendsto_const_nhds).mul hXt).mul (tendsto_log_curve_U hx2)).add hBt
    exact (tendsto_nhds_unique hzero hlim).symm
  · -- lower half-plane
    have hzero : Tendsto (fun ε : ℝ => κL * X ((x : ℂ) - ε * Complex.I)
        * Complex.log (((x : ℂ) - ε * Complex.I) - ninth) + B ((x : ℂ) - ε * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (tendsto_const_nhds (x := (0 : ℂ))).congr' (hmemL.mono (fun ε hε => (hL _ hε).symm))
    have hlim : Tendsto (fun ε : ℝ => κL * X ((x : ℂ) - ε * Complex.I)
        * Complex.log (((x : ℂ) - ε * Complex.I) - ninth) + B ((x : ℂ) - ε * Complex.I))
        (𝓝[>] (0 : ℝ))
        (𝓝 (κL * X (x : ℂ) * (Real.log ‖(x : ℂ) - ninth‖ - Real.pi * Complex.I) + B (x : ℂ))) :=
      (((tendsto_const_nhds).mul hXtL).mul (tendsto_log_curve_L hx2)).add hBtL
    exact (tendsto_nhds_unique hzero hlim).symm

end Work.A14D
