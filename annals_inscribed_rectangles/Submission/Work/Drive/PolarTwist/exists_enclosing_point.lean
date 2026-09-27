import Mathlib
import Submission.Work.Drive.capAngleOfSmooth
import Submission.Work.Drive.contDiffOn_localArg
import Submission.Work.Drive.cappingPolar_identification

/-!
# An enclosing point of a smooth Jordan curve

`Work.Drive.PolarTwist.exists_enclosing_point`: for a smooth embedding `γ : Circle → ℝ × ℝ` there is a
point `p` of the plane off the curve and a `C^∞` function `U : ℝ → ℝ` with `U (t + 2π) = U t + ε · 2π`
for `ε = ±1` such that the polar coordinates of `γ (exp t) - p` are `(|γ (exp t) - p|, U t)`.
Equivalently, `p` lies in the bounded component of the complement of the curve, and `U` is a global
`C^∞` lift of its argument, turning exactly once over a period.

The point `p` and the *continuous* angle lift with monodromy `±2π` come from the capping chapter
(`Work.Drive.exists_periodic_cap_angle_polar`, whose `ε = ±1` is the Jordan input that the position
angle winds exactly once around an interior point).  The work here is the *smoothness* of that lift:
a continuous lift of the argument of a `C^∞` non-vanishing plane curve is `C^∞`, because locally it
differs from the smooth branch of the logarithm by a constant integer.
-/

namespace Work.Drive.PolarTwist

open scoped ContDiff Topology
open Filter

noncomputable section

/-! ## The polar parametrisation as a complex number -/

/-- The point `polarLift (r, θ) = (r cos (2πθ), r sin (2πθ))` as a complex number is
`r · exp (2πθ i)`. -/
lemma polarLift_complex_exp (r θ : ℝ) :
    Work.Drive.toC (Work.Drive.polarLift (r, θ))
      = (r : ℂ) * Complex.exp (↑(2 * Real.pi * θ) * Complex.I) := by
  simp only [Work.Drive.toC, Work.Drive.polarLift, Complex.exp_ofReal_mul_I]
  push_cast
  ring

/-- The polar parametrisation does not vanish for positive radius. -/
lemma polarLift_ne_zero_of_pos {r θ : ℝ} (hr : 0 < r) : Work.Drive.polarLift (r, θ) ≠ 0 := by
  intro h
  have h1 : r * Real.cos (2 * Real.pi * θ) = 0 := by
    simpa [Work.Drive.polarLift] using congrArg Prod.fst h
  have h2 : r * Real.sin (2 * Real.pi * θ) = 0 := by
    simpa [Work.Drive.polarLift] using congrArg Prod.snd h
  have hc : Real.cos (2 * Real.pi * θ) = 0 := (mul_eq_zero.mp h1).resolve_left (ne_of_gt hr)
  have hs : Real.sin (2 * Real.pi * θ) = 0 := (mul_eq_zero.mp h2).resolve_left (ne_of_gt hr)
  have h3 := Real.cos_sq_add_sin_sq (2 * Real.pi * θ)
  rw [hc, hs] at h3
  norm_num at h3

/-- The exponential of the imaginary part of the logarithm of a non-zero complex number is its
argument as a unit vector. -/
lemma exp_im_log_of_ne_zero (z : ℂ) (hz : z ≠ 0) :
    Complex.exp ((Complex.log z).im * Complex.I) = z / (↑‖z‖ : ℂ) := by
  rw [Complex.log_im]
  rw [eq_div_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)), mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- The unit vector `b / ‖b‖` composed with `a / b` (in the unnormalised form used to compare two
lifts). -/
lemma unit_mul_unit (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (b / (↑‖b‖ : ℂ)) * ((a / b) / (↑‖a / b‖ : ℂ)) = a / (↑‖a‖ : ℂ) := by
  have hbn : (↑‖b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb)
  have han : (↑‖a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)
  rw [Complex.norm_div]
  have hab : (↑(‖a‖ / ‖b‖) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_ne_zero (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb))
  push_cast
  field_simp

/-! ## The polar angle of a smooth plane curve is smooth -/

/-- **A continuous lift of the argument of a `C^∞` non-vanishing plane curve is `C^∞`.**

If `v : ℝ → ℝ × ℝ` is a `C^∞` curve avoiding the origin and `ρ > 0`, `Θ` are such that
`polarLift (ρ t, Θ t) = v t` for all `t`, then `Θ` is `C^∞`.  Indeed `Θ` is determined modulo `1` by
`v`, and near a base parameter it differs from the smooth local branch of the argument by a constant
integer. -/
theorem contDiff_polarAngle_top {v : ℝ → ℝ × ℝ} {ρ Θ : ℝ → ℝ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (hne : ∀ t, v t ≠ 0)
    (hρ : ∀ t, 0 < ρ t) (hΘ : Continuous Θ)
    (hlift : ∀ t : ℝ, Work.Drive.polarLift (ρ t, Θ t) = v t) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ := by
  -- the curve as a complex-valued curve
  set w : ℝ → ℂ := fun t => Work.Drive.toC (v t) with hwdef
  have hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : ℝ => ((v t).1 : ℂ) :=
      Complex.ofRealCLM.contDiff.comp hv.fst
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : ℝ => ((v t).2 : ℂ) :=
      Complex.ofRealCLM.contDiff.comp hv.snd
    exact h1.add (h2.mul contDiff_const)
  have hwne : ∀ t, w t ≠ 0 := by
    intro t h
    have h1 : (v t).1 = 0 := by
      have := congrArg Complex.re h
      simpa [hwdef, Work.Drive.toC] using this
    have h2 : (v t).2 = 0 := by
      have := congrArg Complex.im h
      simpa [hwdef, Work.Drive.toC] using this
    exact hne t (Prod.ext h1 h2)
  -- `exp (2πΘ t i)` is the unit vector of `w t`
  have hexp : ∀ t, Complex.exp (↑(2 * Real.pi * Θ t) * Complex.I)
      = w t / (↑‖w t‖ : ℂ) := by
    intro t
    have h1 : w t = (ρ t : ℂ) * Complex.exp (↑(2 * Real.pi * Θ t) * Complex.I) := by
      have h := polarLift_complex_exp (ρ t) (Θ t)
      rw [hlift t] at h
      simpa [hwdef] using h
    have hnorm : ‖w t‖ = ρ t := by
      rw [h1, norm_mul, Work.Drive.norm_ofReal_complex, abs_of_pos (hρ t), Complex.norm_exp]
      simp
    rw [hnorm, h1]
    exact (mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (hρ t)))).symm
  rw [contDiff_iff_contDiffAt]
  intro t₀
  have hwt0 : w t₀ ≠ 0 := hwne t₀
  set A : Set ℝ := {s | w s / w t₀ ∈ Complex.slitPlane} with hAdef
  have hAopen : IsOpen A := Complex.isOpen_slitPlane.preimage (hw.continuous.div_const _)
  have hAmem : t₀ ∈ A := by
    rw [hAdef]
    simp only [Set.mem_ofPred_eq]
    rw [div_self hwt0]
    exact Complex.one_mem_slitPlane
  -- the local smooth lift based at `t₀`
  set ψ : ℝ → ℝ := fun s => Θ t₀ + (Complex.log (w s / w t₀)).im / (2 * Real.pi) with hψdef
  have hψ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ A := by
    have hg := Work.Drive.contDiffOn_localArg hw t₀
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ =>
        ((Complex.arg (w t₀) + (Complex.log (w s / w t₀)).im) / Real.pi) / 2
          + (Θ t₀ - Complex.arg (w t₀) / (2 * Real.pi))) A :=
      (hg.div_const 2).add (contDiffOn_const (c := Θ t₀ - Complex.arg (w t₀) / (2 * Real.pi)))
    refine h2.congr ?_
    intro s _
    simp only [hψdef]
    field_simp
    ring
  -- the difference with `Θ` is locally an integer
  have hint : ∀ s ∈ A, ∃ k : ℤ, ψ s - Θ s = (k : ℝ) := by
    intro s hs
    have hzs : w s / w t₀ ≠ 0 := fun h => Complex.zero_notMem_slitPlane (h ▸ hs)
    have h1 : Complex.exp (↑(2 * Real.pi * ψ s) * Complex.I)
        = Complex.exp (↑(2 * Real.pi * Θ t₀) * Complex.I)
          * Complex.exp ((Complex.log (w s / w t₀)).im * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      have harg : 2 * Real.pi * ψ s
          = 2 * Real.pi * Θ t₀ + (Complex.log (w s / w t₀)).im := by
        simp only [hψdef]
        field_simp
      rw [harg]
      push_cast
      ring
    have h2 : Complex.exp (↑(2 * Real.pi * ψ s) * Complex.I)
        = Complex.exp (↑(2 * Real.pi * Θ s) * Complex.I) := by
      rw [h1, exp_im_log_of_ne_zero _ hzs, hexp t₀, hexp s]
      exact unit_mul_unit (w s) (w t₀) (hwne s) hwt0
    have hcirc : Circle.exp (2 * Real.pi * ψ s) = Circle.exp (2 * Real.pi * Θ s) := by
      apply Subtype.ext
      rw [Circle.coe_exp, Circle.coe_exp]
      exact h2
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hcirc
    refine ⟨n, ?_⟩
    have hπ : (2 * Real.pi) ≠ 0 := by positivity
    have hzero : (2 * Real.pi) * (ψ s - Θ s - (n : ℝ)) = 0 := by linarith [hn]
    have := (mul_eq_zero.mp hzero).resolve_left hπ
    linarith
  -- continuity at `t₀` and constancy of the integer difference
  have hψcontAt : ContinuousAt ψ t₀ := (hψ.contDiffAt (hAopen.mem_nhds hAmem)).continuousAt
  have hFcontAt : ContinuousAt (fun s : ℝ => ψ s - Θ s) t₀ := hψcontAt.sub hΘ.continuousAt
  obtain ⟨δ, hδ, hδU⟩ := Metric.continuousAt_iff.mp hFcontAt 1 zero_lt_one
  have hev : (fun s : ℝ => ψ s - Θ s) =ᶠ[𝓝 t₀] (fun _ => ψ t₀ - Θ t₀) := by
    filter_upwards [Metric.ball_mem_nhds t₀ hδ, hAopen.mem_nhds hAmem] with s hs hsA
    obtain ⟨k, hk⟩ := hint s hsA
    obtain ⟨l, hl⟩ := hint t₀ hAmem
    have h2 : |(k : ℝ) - (l : ℝ)| < 1 := by
      have h3 := hδU (Metric.mem_ball.mp hs)
      rw [Real.dist_eq, hk, hl] at h3
      exact h3
    rw [hk, hl, Work.Drive.int_eq_of_abs_sub_lt_one h2]
  have hψat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ t₀ := hψ.contDiffAt (hAopen.mem_nhds hAmem)
  have hev2 : Θ =ᶠ[𝓝 t₀] (fun s : ℝ => ψ s - (ψ t₀ - Θ t₀)) := by
    filter_upwards [hev] with s hs
    linarith
  exact (hψat.sub contDiffAt_const).congr_of_eventuallyEq hev2

/-! ## The enclosing point -/

theorem exists_enclosing_point (gamma : Circle → ℝ × ℝ)
    (hgamma : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) gamma) :
    ∃ (p : ℝ × ℝ), p ∉ Set.range gamma ∧
      ∃ (eps : ℝ) (U : ℝ → ℝ), (eps = 1 ∨ eps = -1) ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U ∧
        (∀ t : ℝ, U (t + 2 * Real.pi) = U t + eps * (2 * Real.pi)) ∧
        (∀ t : ℝ, gamma (Circle.exp t) - p =
          (Real.sqrt (((gamma (Circle.exp t)).1 - p.1) ^ 2 + ((gamma (Circle.exp t)).2 - p.2) ^ 2)
              * Real.cos (U t),
           Real.sqrt (((gamma (Circle.exp t)).1 - p.1) ^ 2 + ((gamma (Circle.exp t)).2 - p.2) ^ 2)
              * Real.sin (U t))) := by
  obtain ⟨c, ρ, Θ, Ψ, Φ, Θc, hρc, hΘc, hΨc, hΦc, hΘcc, hρpos, hlift, hΨ, hΦ, hΘclass, hεd, hΘcper,
    hΘcrel⟩ := Work.Drive.exists_periodic_cap_angle_polar gamma hgamma
  obtain ⟨ε, hε, hΘtot, hΨtot, hΦtot⟩ := hεd
  -- `c` is off the curve
  have hpc : c ∉ Set.range gamma := by
    rintro ⟨x, hx⟩
    obtain ⟨t, rfl⟩ := Circle.exp_surjective x
    exact polarLift_ne_zero_of_pos (hρpos t) (by rw [hlift t, ← hx, sub_self])
  -- the translated curve
  have hγsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : ℝ => gamma (Circle.exp t) :=
    (hgamma.contMDiff.comp contMDiff_circleExp).contDiff
  have hvsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : ℝ => gamma (Circle.exp t) - c :=
    hγsm.sub contDiff_const
  have hvne : ∀ t : ℝ, gamma (Circle.exp t) - c ≠ 0 :=
    fun t h => hpc ⟨Circle.exp t, sub_eq_zero.mp h⟩
  have hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ :=
    contDiff_polarAngle_top hvsm hvne hρpos hΘc hlift
  -- the monodromy of `Θ` is `ε` (for every `t`)
  have hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) - Θ t = (ε : ℝ) := by
    have hint : ∀ t : ℝ, ∃ k : ℤ, Θ (t + 2 * Real.pi) - Θ t = (k : ℝ) := by
      intro t
      obtain ⟨k, hk⟩ :=
        (Work.Drive.coe_eq_coe_iff_int (Θ (t + 2 * Real.pi)) (Θ t)).mp (hΘclass t)
      exact ⟨k, hk.symm⟩
    intro t
    rw [Work.Drive.monodromy_const_of_int_valued hΘc hint t, hΘtot]
  refine ⟨c, hpc, (ε : ℝ), fun t => 2 * Real.pi * Θ t, ?_, ?_, ?_, ?_⟩
  · rcases hε with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  · exact contDiff_const.mul hΘsm
  · intro t
    have h := hΘper t
    show 2 * Real.pi * Θ (t + 2 * Real.pi) = 2 * Real.pi * Θ t + (ε : ℝ) * (2 * Real.pi)
    rw [show Θ (t + 2 * Real.pi) = Θ t + (ε : ℝ) by linarith]
    ring
  · intro t
    have h1 : (gamma (Circle.exp t)).1 - c.1 = ρ t * Real.cos (2 * Real.pi * Θ t) := by
      have h := congrArg Prod.fst (hlift t)
      simpa [Work.Drive.polarLift] using h.symm
    have h2 : (gamma (Circle.exp t)).2 - c.2 = ρ t * Real.sin (2 * Real.pi * Θ t) := by
      have h := congrArg Prod.snd (hlift t)
      simpa [Work.Drive.polarLift] using h.symm
    have hA : ((gamma (Circle.exp t)).1 - c.1) ^ 2 + ((gamma (Circle.exp t)).2 - c.2) ^ 2
        = (ρ t) ^ 2 := by
      linear_combination (ρ t ^ 2) * Real.cos_sq_add_sin_sq (2 * Real.pi * Θ t)
        + (ρ t * Real.cos (2 * Real.pi * Θ t) + ((gamma (Circle.exp t)).1 - c.1)) * h1
        + (ρ t * Real.sin (2 * Real.pi * Θ t) + ((gamma (Circle.exp t)).2 - c.2)) * h2
    have hsqrt : Real.sqrt (((gamma (Circle.exp t)).1 - c.1) ^ 2
        + ((gamma (Circle.exp t)).2 - c.2) ^ 2) = ρ t := by
      rw [hA, Real.sqrt_sq (le_of_lt (hρpos t))]
    ext
    · rw [hsqrt]; exact h1
    · rw [hsqrt]; exact h2

end

end Work.Drive.PolarTwist
