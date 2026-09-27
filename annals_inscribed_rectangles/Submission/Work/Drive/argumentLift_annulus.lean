import Mathlib

/-!
# A `C^∞` argument lift of a smooth unit-valued map on the exterior of a disc

`Work.Drive.argumentLift_annulus`: let `g : ℂ → ℂ` be `C^∞` and of modulus one on the exterior
`D = {x : ℂ | 1/2 ≤ ‖x‖}` of the disc of radius `1/2`, and suppose that `g` agrees on the boundary
circle with a *continuous* unit-valued map `G` defined on the disc (so that the winding number of
`g` around the hole of the annulus `D` is zero).  Then there is a `C^∞` function `ψ : ℂ → ℝ` on `D`
with `exp (ψ x * I) = g x` for `x ∈ D`.

The construction patches `G` (on the disc) with `g` (outside) to a continuous non-vanishing map
`F : ℂ → ℂ`; since `ℂ` is simply connected, `F` lifts through the covering map `Complex.exp`, say
`F = exp ∘ Ftilde` with `Ftilde` continuous, and `ψ := im Ftilde` is the desired angle (on `D` we have
`F = g`, `‖g‖ = 1`).  `ψ` is smooth because a continuous argument of a smooth non-vanishing map is
smooth: locally it differs from the smooth branch `y ↦ im (log (g y / g x₀))` of the argument by a
continuous `2πℤ`-valued function, which therefore vanishes near `x₀`.
-/

namespace Work.Drive

open scoped ContDiff

namespace ArgLift

/-- The exponential of the imaginary part of `z` is the unit vector of `exp z`. -/
theorem exp_im_mul_I_eq (z : ℂ) :
    Complex.exp ((z.im : ℂ) * Complex.I) = Complex.exp z / ((‖Complex.exp z‖ : ℝ) : ℂ) := by
  have h1 : Complex.exp z
      = ((Real.exp z.re : ℝ) : ℂ) * Complex.exp ((z.im : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [Complex.exp_add, ← Complex.ofReal_exp]
  have h2 : (‖Complex.exp z‖ : ℝ) = Real.exp z.re := Complex.norm_exp z
  rw [h2, h1]
  have hne : (((Real.exp z.re : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  field_simp

/-- For `w ≠ 0` the imaginary part of `log w` is an argument of `w`. -/
theorem exp_im_log_mul_I (w : ℂ) (hw : w ≠ 0) :
    Complex.exp (((Complex.log w).im : ℂ) * Complex.I) = w / ((‖w‖ : ℝ) : ℂ) := by
  have h := exp_im_mul_I_eq (Complex.log w)
  rwa [Complex.exp_log hw] at h

/-- **A continuous argument of a smooth non-vanishing unit-modulus map is smooth.**

If `ψ : ℂ → ℝ` is continuous and `exp (ψ x * I) = g x` for `x` in a set `D` on which `g` has
modulus one, and `g` is `C^∞`, then `ψ` is `C^∞` on `D`. -/
theorem contDiffOn_of_exp_lift {g : ℂ → ℂ} {ψ : ℂ → ℝ} {D : Set ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hψ : Continuous ψ)
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
      hg.contDiffAt.div_const _
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.log (g x₀ / g x₀) :=
      (Complex.contDiffAt_log hmem).restrict_scalars ℝ
    have hcomp := h1.comp x₀ hdiv
    have hlog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ℂ => Complex.log (g y / g x₀)) x₀ := hcomp
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.im
        (Complex.log (g x₀ / g x₀)) := Complex.imCLM.contDiff.contDiffAt
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
      have h := exp_im_log_mul_I (g y / g x₀) (div_ne_zero hyne hgx₀)
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

end ArgLift

open ArgLift

theorem argumentLift_annulus (g : ℂ → ℂ)
    (hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgunit : ∀ x : ℂ, 1 / 2 ≤ ‖x‖ → ‖g x‖ = 1)
    (hext : ∃ G : ℂ → ℂ, Continuous G ∧ (∀ x : ℂ, ‖x‖ ≤ 1 / 2 → ‖G x‖ = 1) ∧
      (∀ x : ℂ, 1 / 2 ≤ ‖x‖ → G x = g x)) :
    ∃ ψ : ℂ → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ {x : ℂ | 1 / 2 ≤ ‖x‖} ∧
      ∀ x : ℂ, 1 / 2 ≤ ‖x‖ → Complex.exp (((ψ x : ℝ) : ℂ) * Complex.I) = g x := by
  classical
  obtain ⟨G, hGc, hGu, hGg⟩ := hext
  set D : Set ℂ := {x : ℂ | 1 / 2 ≤ ‖x‖} with hDdef
  set s : Set ℂ := {x : ℂ | ‖x‖ ≤ 1 / 2} with hsdef
  -- the patched map, continuous and nowhere vanishing
  set F : ℂ → ℂ := s.piecewise G g with hFdef
  have hFmem : ∀ x ∈ s, F x = G x := fun x hx => Set.piecewise_eq_of_mem s G g hx
  have hFnot : ∀ x ∉ s, F x = g x := fun x hx => Set.piecewise_eq_of_notMem s G g hx
  have hFcont : Continuous F := by
    have hfront : ∀ a ∈ frontier s, G a = g a := by
      intro a ha
      have hseq : s = Metric.closedBall (0 : ℂ) (1 / 2) := by
        ext x
        rw [hsdef, Metric.mem_closedBall, dist_zero_right]
        rfl
      have hnorm : ‖a‖ = 1 / 2 := by
        have h := ha
        rw [hseq, frontier_closedBall (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0),
          Metric.mem_sphere] at h
        simpa [dist_eq_norm] using h
      exact hGg a (le_of_eq hnorm.symm)
    exact continuous_piecewise hfront hGc.continuousOn hgsm.continuous.continuousOn
  have hFne : ∀ x, F x ≠ 0 := by
    intro x
    by_cases hx : x ∈ s
    · rw [hFmem x hx]
      intro h
      have := hGu x hx
      rw [h, norm_zero] at this
      norm_num at this
    · rw [hFnot x hx]
      have hxle : 1 / 2 ≤ ‖x‖ := by
        rw [hsdef] at hx
        simp only [Set.mem_ofPred_eq, not_le] at hx
        exact le_of_lt hx
      intro h
      have := hgunit x hxle
      rw [h, norm_zero] at this
      norm_num at this
  -- lift the patched map through the covering map `Complex.exp`
  obtain ⟨Ftilde, ⟨-, hFtilde_exp⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    (f := ⟨F, hFcont⟩) (a₀ := 0) (e₀ := Complex.log (F 0))
    (Complex.exp_log (hFne 0)) (fun a => hFne a)
  have hFtilde_exp' : ∀ x, Complex.exp (Ftilde x) = F x := fun x => congrFun hFtilde_exp x
  have hψc : Continuous fun x : ℂ => (Ftilde x).im := Complex.continuous_im.comp Ftilde.continuous
  have hrel : ∀ x ∈ D, Complex.exp ((((Ftilde x).im : ℝ) : ℂ) * Complex.I) = g x := by
    intro x hx
    have hFx : F x = g x := by
      by_cases hxs : x ∈ s
      · rw [hFmem x hxs]
        have hnorm : ‖x‖ = 1 / 2 := by
          rw [hsdef] at hxs
          simp only [Set.mem_ofPred_eq] at hxs
          exact le_antisymm hxs hx
        exact hGg x (le_of_eq hnorm.symm)
      · exact hFnot x hxs
    rw [exp_im_mul_I_eq (Ftilde x), hFtilde_exp' x, hFx]
    have hnorm : ‖g x‖ = 1 := hgunit x hx
    rw [hnorm]
    simp
  exact ⟨fun x => (Ftilde x).im, contDiffOn_of_exp_lift hgsm hψc hgunit hrel, hrel⟩

end Work.Drive
