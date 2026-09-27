import Mathlib
import Submission.Work.Drive.directionStabilization
import Submission.Work.Drive.argumentLift_annulus
import Submission.Work.Drive.bandData

namespace Work.Drive

open scoped ContDiff

noncomputable section

/-!
# The direction datum of the plane chart, made constant at a prescribed level

`Work.Drive.exists_directionStabilization` (`directionStabilization.lean`) is the corrected version of
the stabilisation device of `PLANE_CHART_FINAL.md` §9.2: a *unit* correction factor
`exp (i · b τ · ζ x · ψ x)` of the halving datum `W`, which leaves `‖W‖`, the radius `A = ‖M‖² + τ‖W‖²`
and the disk coordinate `D = M/√A` untouched, and turns the direction datum
`w_h = dirDatum M W` into a constant at the level `τ₁`.

Everything there is an identity of the data `(M, W)` *given* the argument `ψ` of the stabilising loop
`x ↦ c · conj (w_h (x,τ₁))`.  This file supplies that `ψ` from the only thing the geometry provides:
the *null-homotopy* of the loop, i.e. a continuous unit-valued `G` on the disc of radius `1/4` agreeing
with the loop on the circle of radius `1/4` (the winding-zero condition `deg w_h = ε − m = 0` of §9.1,
available under `Work.Drive.WrapData`).

## The construction

The loop is `g x = c * star (dirDatum M W (x, τ₁))`; by hypothesis it is unit-valued and smooth on
`{x : 1/4 ≤ ‖x‖}` (the data are non-vanishing there, and non-vanishing plus continuity makes the datum
`M/‖M‖` smooth *in the ambient sense* at every point of that closed set — this is what makes the
argument below work without any flat-pasting lemma), and it is extended over the disc by `G`.  Patch
the two to a continuous non-vanishing map `F` of the plane and lift it through the covering map
`Complex.exp`; the imaginary part `ψ₀` of the lift is a continuous argument of `g` on `{1/4 ≤ ‖x‖}`,
smooth there because `g` is smooth there (this is `contDiffOn_of_exp_lift_of_contDiffAt`).

Then `ψ := χ · ψ₀` with `χ = pStep (7/16) (1/2) ‖·‖` is `C^∞`: on the open set `{3/8 < ‖x‖}` both
factors are smooth, and on `{‖x‖ < 7/16}` the cutoff vanishes identically.  These two open sets cover
the plane (`3/8 < 7/16`), so `contDiff_of_contDiffOn_union_of_isOpen` applies — **no gluing lemma is
needed**, the cutoff was chosen so that its vanishing region strictly contains the region where the
argument is only known to be continuous.  On `{1/2 ≤ ‖x‖}` we have `χ = 1`, hence `exp (i ψ x) = g x`,
which is exactly the hypothesis `hψspec` of `exists_directionStabilization`.
-/

/-- **`Work.Drive.ArgLift.contDiffOn_of_exp_lift` with the smoothness of `g` assumed only at the
points of `D`** — which is all that the proof of the original lemma uses (it only ever evaluates `g`
at the point `x₀ ∈ D` under consideration).  This is the form needed when the unit loop is smooth on
a closed set only, as for the direction datum of the plane chart. -/
theorem contDiffOn_of_exp_lift_of_contDiffAt {g : ℂ → ℂ} {ψ : ℂ → ℝ} {D : Set ℂ}
    (hg : ∀ x ∈ D, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g x) (hψ : Continuous ψ)
    (hunit : ∀ x ∈ D, ‖g x‖ = 1)
    (hlift : ∀ x ∈ D, Complex.exp (((ψ x : ℝ) : ℂ) * Complex.I) = g x) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ D := by
  intro x₀ hx₀
  have hgx₀ : g x₀ ≠ 0 := by
    intro h
    have := hunit x₀ hx₀
    rw [h, norm_zero] at this
    norm_num at this
  -- the smooth local branch of the argument of `g` based at `x₀`
  set φ : ℂ → ℝ := fun y => (Complex.log (g y / g x₀)).im with hφdef
  have hφsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ x₀ := by
    have hmem : g x₀ / g x₀ ∈ Complex.slitPlane := by
      rw [div_self hgx₀]
      exact Complex.one_mem_slitPlane
    have hdiv : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => g y / g x₀) x₀ :=
      (hg x₀ hx₀).div_const _
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.log (g x₀ / g x₀) :=
      (Complex.contDiffAt_log hmem).restrict_scalars ℝ
    have hlog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ℂ => Complex.log (g y / g x₀)) x₀ := by
      show ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Complex.log ∘ fun y : ℂ => g y / g x₀) x₀
      exact h1.comp x₀ hdiv
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.im (Complex.log (g x₀ / g x₀)) :=
      Complex.imCLM.contDiff.contDiffAt
    have hcomp2 := h2.comp x₀ hlog
    exact hcomp2
  have hφ0 : φ x₀ = 0 := by
    simp [hφdef, div_self hgx₀]
  -- `exp (ψ - φ - ψ x₀) = 1` on `D`
  have hint : ∀ y ∈ D, ∃ k : ℤ, ψ y - φ y - ψ x₀ = (k : ℝ) * (2 * Real.pi) := by
    intro y hy
    have hyne : g y ≠ 0 := by
      intro h
      have := hunit y hy
      rw [h, norm_zero] at this
      norm_num at this
    have hφ : Complex.exp (((φ y : ℝ) : ℂ) * Complex.I) = g y / g x₀ := by
      have h := ArgLift.exp_im_log_mul_I (g y / g x₀) (div_ne_zero hyne hgx₀)
      have hnorm : ‖g y / g x₀‖ = 1 := by
        rw [norm_div, hunit y hy, hunit x₀ hx₀]
        norm_num
      rw [hnorm] at h
      rw [hφdef]
      simpa using h
    have hexp1 : Complex.exp (((ψ y - φ y - ψ x₀ : ℝ) : ℂ) * Complex.I) = 1 := by
      have harg : (((ψ y - φ y - ψ x₀ : ℝ)) : ℂ) * Complex.I
          = ((ψ y : ℝ) : ℂ) * Complex.I - ((φ y : ℝ) : ℂ) * Complex.I
            - ((ψ x₀ : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg, Complex.exp_sub, Complex.exp_sub, hlift y hy, hφ, hlift x₀ hx₀]
      field_simp
    have hcirc : Circle.exp (ψ y - φ y - ψ x₀) = Circle.exp 0 := by
      apply Subtype.ext
      rw [Circle.coe_exp, Circle.coe_exp, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      exact hexp1
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hcirc
    exact ⟨k, by simpa using hk⟩
  -- `ψ - φ - ψ x₀` is continuous, integer valued and `0` at `x₀`
  have hcont : ContinuousAt (fun y : ℂ => ψ y - φ y - ψ x₀) x₀ :=
    (hψ.continuousAt.sub hφsm.continuousAt).sub continuousAt_const
  obtain ⟨δ, hδ, hδU⟩ := Metric.continuousAt_iff.mp hcont (2 * Real.pi) (by positivity)
  have hδU' : ∀ y : ℂ, dist y x₀ < δ → |ψ y - φ y - ψ x₀| < 2 * Real.pi := by
    intro y hy
    simpa [Real.dist_eq, hφ0] using hδU hy
  have hev : ∀ᶠ y in nhdsWithin x₀ D, ψ y - φ y - ψ x₀ = 0 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds x₀ hδ] with y hy hyD
    obtain ⟨k, hk⟩ := hint y hyD
    have h2 : |ψ y - φ y - ψ x₀| < 2 * Real.pi := hδU' y (Metric.mem_ball.mp hy)
    rw [hk] at h2
    have hk0 : k = 0 := by
      have h3 : |(k : ℝ)| < 1 := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h2
        nlinarith [Real.pi_pos]
      have h4 : ((k : ℤ) : ℝ) < 1 := (abs_lt.mp h3).2
      have h5 : (-1 : ℝ) < ((k : ℤ) : ℝ) := (abs_lt.mp h3).1
      have h6 : k < 1 := by exact_mod_cast h4
      have h7 : -1 < k := by exact_mod_cast h5
      omega
    rw [hk0] at hk
    simpa using hk
  have hsm : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => ψ x₀ + φ y) D x₀ :=
    (contDiffAt_const.add hφsm).contDiffWithinAt
  refine hsm.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hev] with y hy
    linarith
  · rw [hφ0, add_zero]

/-- **The correction factor of `PLANE_CHART_FINAL.md` §9.2 exists from the geometric hypothesis
alone.**  From `(M, W)` smooth and non-vanishing on `{τ ≤ 0} × {1/4 ≤ ‖x‖}`, a level `τ₁ < 0`, a unit
constant `c`, and the *null-homotopy* of the loop `x ↦ c * conj (w_h (x,τ₁))` over the disc of radius
`1/4`, there is `W'` differing from `W` by a smooth unit factor, equal to `W` for `τ ≥ 0`, with the same
norm and non-vanishing as `W` on `{τ ≤ 0} × {1/4 ≤ ‖x‖}`, and with direction datum exactly `c` at the
level `τ₁` on `1/2 ≤ ‖x‖`.  This discharges §9.1's vanishing obligation `w z ≠ 0` for the plane chart
down to `Work.Drive.WrapData` (which supplies the null-homotopy). -/
theorem directionStabilization_of_nullhomotopic (M W : ℂ × ℝ → ℂ)
    (hM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hMne : ∀ p : ℂ × ℝ, p.2 ≤ 0 → 1 / 4 ≤ ‖p.1‖ → M p ≠ 0)
    (hWne : ∀ p : ℂ × ℝ, p.2 ≤ 0 → 1 / 4 ≤ ‖p.1‖ → W p ≠ 0)
    {τ₁ : ℝ} (hτ₁ : τ₁ < 0) (c : ℂ) (hc : ‖c‖ = 1)
    (hloop : ∃ G : ℂ → ℂ, Continuous G ∧ (∀ x : ℂ, ‖x‖ ≤ 1 / 4 → ‖G x‖ = 1) ∧
      (∀ x : ℂ, 1 / 4 ≤ ‖x‖ → G x = c * star (Work.Drive.dirDatum M W (x, τ₁)))) :
    ∃ W' : ℂ × ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W' ∧
      (∀ p : ℂ × ℝ, 0 ≤ p.2 → W' p = W p) ∧
      (∀ p : ℂ × ℝ, p.2 ≤ 0 → 1 / 4 ≤ ‖p.1‖ → W' p ≠ 0) ∧
      (∀ p : ℂ × ℝ, p.2 ≤ 0 → 1 / 4 ≤ ‖p.1‖ → ‖W' p‖ = ‖W p‖) ∧
      (∀ x : ℂ, 1 / 2 ≤ ‖x‖ → Work.Drive.dirDatum M W' (x, τ₁) = c) := by
  classical
  obtain ⟨G, hGc, hGu, hGg⟩ := hloop
  -- the unit loop `x ↦ c * conj (w_h (x, τ₁))`
  set g : ℂ → ℂ := fun x => c * star (Work.Drive.dirDatum M W (x, τ₁)) with hgdef
  have hunit : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖g x‖ = 1 := by
    intro x hx
    have hMx : M (x, τ₁) ≠ 0 := hMne (x, τ₁) hτ₁.le hx
    have hWx : W (x, τ₁) ≠ 0 := hWne (x, τ₁) hτ₁.le hx
    rw [hgdef, norm_mul, hc, norm_star, Work.Drive.norm_dirDatum hMx hWx, one_mul]
  have hne : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → g x ≠ 0 := by
    intro x hx h
    have h1 := hunit x hx
    rw [h, norm_zero] at h1
    norm_num at h1
  -- `g` is smooth (in the ambient sense) at every point of `{1/4 ≤ ‖x‖}`
  have hMcont : Continuous fun x : ℂ => M (x, τ₁) :=
    hM.continuous.comp (continuous_id.prodMk continuous_const)
  have hWcont : Continuous fun x : ℂ => W (x, τ₁) :=
    hW.continuous.comp (continuous_id.prodMk continuous_const)
  have hMsmooth : ∀ x : ℂ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => M (y, τ₁)) x :=
    fun x => hM.contDiffAt.comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hWsmooth : ∀ x : ℂ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => W (y, τ₁)) x :=
    fun x => hW.contDiffAt.comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hgsmooth : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g x := by
    intro x hx
    have hMx : M (x, τ₁) ≠ 0 := hMne (x, τ₁) hτ₁.le hx
    have hWx : W (x, τ₁) ≠ 0 := hWne (x, τ₁) hτ₁.le hx
    have hMn0 : ‖M (x, τ₁)‖ ≠ 0 := norm_ne_zero_iff.mpr hMx
    have hWn0 : ‖W (x, τ₁)‖ ≠ 0 := norm_ne_zero_iff.mpr hWx
    have hMn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => ‖M (y, τ₁)‖) x :=
      ContDiffAt.norm ℝ (hMsmooth x) hMx
    have hWn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => ‖W (y, τ₁)‖) x :=
      ContDiffAt.norm ℝ (hWsmooth x) hWx
    have hMunit : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ℂ => M (y, τ₁) / ((‖M (y, τ₁)‖ : ℝ) : ℂ)) x := by
      refine ((hMsmooth x).mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp x (hMn.inv hMn0))).congr_of_eventuallyEq ?_
      filter_upwards with y
      rw [Function.comp_apply, Pi.inv_apply, Complex.ofRealCLM_apply, Complex.ofReal_inv,
        div_eq_mul_inv]
    have hWunit : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ℂ => W (y, τ₁) / ((‖W (y, τ₁)‖ : ℝ) : ℂ)) x := by
      refine ((hWsmooth x).mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp x (hWn.inv hWn0))).congr_of_eventuallyEq ?_
      filter_upwards with y
      rw [Function.comp_apply, Pi.inv_apply, Complex.ofRealCLM_apply, Complex.ofReal_inv,
        div_eq_mul_inv]
    have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ℂ => star (W (y, τ₁) / ((‖W (y, τ₁)‖ : ℝ) : ℂ))) x :=
      Complex.conjCLE.contDiff.contDiffAt.comp x hWunit
    rw [hgdef]
    simp only [Work.Drive.dirDatum, star_mul, star_star]
    exact contDiffAt_const.mul (hMunit.mul h3)
  -- continuity of `g` on the closed exterior
  have hgcont : ContinuousOn g {x : ℂ | 1 / 4 ≤ ‖x‖} := by
    intro x hx
    exact (hgsmooth x hx).continuousAt.continuousWithinAt
  -- the patched map
  set s : Set ℂ := Metric.closedBall (0 : ℂ) (1 / 4) with hsdef
  set F : ℂ → ℂ := s.piecewise G g with hFdef
  have hFmem : ∀ x ∈ s, F x = G x := fun x hx => Set.piecewise_eq_of_mem s G g hx
  have hFnot : ∀ x ∉ s, F x = g x := fun x hx => Set.piecewise_eq_of_notMem s G g hx
  have hcompl_sub : sᶜ ⊆ {x : ℂ | 1 / 4 ≤ ‖x‖} := by
    intro y hy
    simp only [hsdef, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hy
    exact le_of_lt hy
  have hFcont : Continuous F := by
    rw [hFdef]
    refine continuous_piecewise (fun a ha => ?_) hGc.continuousOn ?_
    · have hnorm : ‖a‖ = 1 / 4 := by
        have h := ha
        rw [hsdef, frontier_closedBall (0 : ℂ) (by norm_num : (1 / 4 : ℝ) ≠ 0),
          Metric.mem_sphere] at h
        simpa [dist_eq_norm] using h
      exact hGg a (le_of_eq hnorm.symm)
    · exact hgcont.mono
        (closure_minimal hcompl_sub (isClosed_le continuous_const continuous_norm))
  have hFne : ∀ x, F x ≠ 0 := by
    intro x
    by_cases hx : x ∈ s
    · rw [hFmem x hx]
      intro h
      have h1 := hGu x (by
        simp only [hsdef, Metric.mem_closedBall, dist_zero_right] at hx
        exact hx)
      rw [h, norm_zero] at h1
      norm_num at h1
    · rw [hFnot x hx]
      exact hne x (hcompl_sub (by simpa using hx))
  -- lift the patched map through the covering map `Complex.exp`
  obtain ⟨Ftilde, ⟨-, hFtilde_exp⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    (f := ⟨F, hFcont⟩) (a₀ := 0) (e₀ := Complex.log (F 0))
    (Complex.exp_log (hFne 0)) (fun a => hFne a)
  have hFtilde_exp' : ∀ x, Complex.exp (Ftilde x) = F x := fun x => congrFun hFtilde_exp x
  set ψ₀ : ℂ → ℝ := fun x => (Ftilde x).im with hψ₀def
  have hψ₀c : Continuous ψ₀ := Complex.continuous_im.comp Ftilde.continuous
  -- `ψ₀` is an argument of `g` on the exterior
  have hFnorm : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖F x‖ = 1 := by
    intro x hx
    by_cases hxs : x ∈ s
    · rw [hFmem x hxs]
      exact hGu x (by
        simp only [hsdef, Metric.mem_closedBall, dist_zero_right] at hxs
        exact hxs)
    · rw [hFnot x hxs]
      exact hunit x hx
  have hψ₀val : ∀ x : ℂ, ψ₀ x = (Ftilde x).im := fun x => by rw [hψ₀def]
  have hψ₀spec : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → Complex.exp (((ψ₀ x : ℝ) : ℂ) * Complex.I) = g x := by
    intro x hx
    rw [hψ₀val x, ArgLift.exp_im_mul_I_eq (Ftilde x), hFtilde_exp' x, hFnorm x hx,
      show ((1 : ℝ) : ℂ) = 1 from rfl, div_one]
    by_cases hxs : x ∈ s
    · rw [hFmem x hxs]
      exact hGg x hx
    · exact hFnot x hxs
  -- `ψ₀` is smooth on the (open) set where `g` is smooth and unit
  have hψ₀sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀ {x : ℂ | 3 / 8 < ‖x‖} :=
    contDiffOn_of_exp_lift_of_contDiffAt
      (D := {x : ℂ | 3 / 8 < ‖x‖})
      (fun x hx => hgsmooth x (by have h := hx; simp only [Set.mem_setOf_eq] at h; linarith))
      hψ₀c
      (fun x hx => by
        have h := hx
        simp only [Set.mem_setOf_eq] at h
        exact hunit x (by linarith))
      (fun x hx => by
        have h := hx
        simp only [Set.mem_setOf_eq] at h
        exact hψ₀spec x (by linarith))
  -- the cutoff and the resulting globally smooth argument
  set χ : ℂ → ℝ := fun x => pStep (7 / 16) (1 / 2) ‖x‖ with hχdef
  have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    rw [hχdef]
    exact contDiff_pStep_norm (by norm_num) (by norm_num)
  have hχone : ∀ x : ℂ, 1 / 2 ≤ ‖x‖ → χ x = 1 := by
    intro x hx
    rw [hχdef]
    exact pStep_eq_one (by norm_num) hx
  have hχzero : ∀ x : ℂ, ‖x‖ < 7 / 16 → χ x = 0 := by
    intro x hx
    rw [hχdef]
    exact pStep_eq_zero (by norm_num) (le_of_lt hx)
  set ψ : ℂ → ℝ := fun x => χ x * ψ₀ x with hψdef
  have hψsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    refine contDiff_of_contDiffOn_union_of_isOpen (s := {x : ℂ | 3 / 8 < ‖x‖})
      (t := {x : ℂ | ‖x‖ < 7 / 16}) ?_ ?_ ?_ ?_ ?_
    · rw [hψdef]
      exact hχsm.contDiffOn.mul hψ₀sm
    · rw [hψdef]
      refine ContDiffOn.congr (contDiffOn_const :
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℂ => (0 : ℝ)) {x : ℂ | ‖x‖ < 7 / 16})
        (fun x hx => ?_)
      simp only [Set.mem_setOf_eq] at hx
      rw [hχzero x hx, zero_mul]
    · ext x
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      by_cases h : 3 / 8 < ‖x‖
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · exact isOpen_lt continuous_const continuous_norm
    · exact isOpen_lt continuous_norm continuous_const
  -- `ψ` is an argument of `g` on the exterior, because the cutoff is `1` there
  have hψspec : ∀ x : ℂ, 1 / 2 ≤ ‖x‖ →
      Complex.exp (((ψ x : ℝ) : ℂ) * Complex.I) = c * star (Work.Drive.dirDatum M W (x, τ₁)) := by
    intro x hx
    have hval : ψ x = ψ₀ x := by
      rw [hψdef]
      simp only [hχone x hx, one_mul]
    rw [hval, hψ₀spec x (by linarith), hgdef]
  exact exists_directionStabilization M W hM hW hMne hWne hτ₁ c hc ψ hψsm hψspec

end

end Work.Drive
