import Mathlib
import Submission.Work.Drive.bandLoop_nullhomotopic
import Submission.Work.Drive.argumentLift_annulus
import Submission.Work.Drive.directionStabilization_of_nullhomotopic

namespace Work.Drive

open scoped ContDiff

noncomputable section

/-!
# A smooth unit extension of an annulus map whose inner circle has a periodic argument

The main theorem of this file, `Work.Drive.smoothUnit_eqOn_annulus_of_periodicArgument`, says: if
`w : ℂ → ℂ` is `C^∞` and of modulus one on the closed annulus `{ρ₀ ≤ ‖z‖ ≤ ρ₃}`, and the map
`σ ↦ w (ρ₀ e^{iσ})` on the inner circle has a continuous `2π`-periodic real argument `θ`, then `w`
agrees on the middle annulus `{ρ₁ ≤ ‖z‖ ≤ ρ₂}` with a *globally* `C^∞`, unit-valued map `Ω`.

## The construction

1. *The argument on an open annulus, from the homotopy lifting property.*  On the open annulus
   `A = {ρ₀ < ‖z‖ < ρ₃}` the radial homotopy

   `H (t, z) = w (((1 - t) ρ₀ + t ‖z‖) · z / ‖z‖)`

   joins the inner-circle loop `z ↦ w (ρ₀ z/‖z‖) = exp (i θ (arg z))` (which has the continuous lift
   `z ↦ θ (arg z)` by the periodicity of `θ`) to `w`.  All its values lie on the unit circle, so it is
   a `Circle`-valued homotopy, and the homotopy lifting property of the covering
   `Circle.exp : ℝ → Circle` (`IsCoveringMap.liftHomotopy`) lifts it to a continuous
   `L : I × A → ℝ` with `L (0, z) = θ (arg z)` and `exp (i L (t,z)) = H (t,z)`.  In particular
   `ψ z := L (1, z)` is an *argument* of `w` on `A`.

2. *Smoothness of the argument.*  A continuous argument of a smooth unit-modulus map is smooth: it
   differs locally from the smooth branch `y ↦ im (log (w y / w x₀))` by a continuous, integer valued
   multiple of `2π`, hence locally coincides with it
   (`Work.Drive.contDiffWithinAt_of_exp_lift` below, the within-set form of
   `Work.Drive.contDiffOn_of_exp_lift_of_ContDiffAt`).

3. *The cutoff.*  For `ρ₀ < rl < ρ₁ ≤ ρ₂ < rh < ρ₃` put

   `χ z = pStep rl ρ₁ ‖z‖ - pStep ρ₂ rh ‖z‖`,

   which is `1` on `{ρ₁ ≤ ‖z‖ ≤ ρ₂}` and `0` off `{rl < ‖z‖ < rh}`.  Then `z ↦ χ z * ψ z` is `C^∞`
   (smooth on the open set `{rl < ‖z‖ < rh}` because both factors are, and locally `0` off it), and
   `Ω z := exp (i · χ z · ψ z)` is a globally `C^∞`, unit valued map which on `{ρ₁ ≤ ‖z‖ ≤ ρ₂}`
   equals `exp (i ψ z) = w z`.
-/

/-- **Local smoothness of an argument.**  If `g` is `C^∞` at `x₀ ∈ D`, if `ψ` is continuous at `x₀`
within `D`, and if on `D` the map `g` is of modulus one and `exp (i ψ) = g`, then `ψ` is `C^∞` at `x₀`
within `D`.

(Only the continuity of `ψ` at the point under consideration is used: the difference of `ψ` from the
smooth local branch `y ↦ im (log (g y / g x₀))` is continuous, integer valued and vanishes at `x₀`,
hence is locally `0`.) -/
theorem contDiffWithinAt_of_exp_lift {g : ℂ → ℂ} {ψ : ℂ → ℝ} {D : Set ℂ} {x₀ : ℂ}
    (hx₀ : x₀ ∈ D) (hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g x₀)
    (hψ : ContinuousWithinAt ψ D x₀)
    (hunit : ∀ y ∈ D, ‖g y‖ = 1)
    (hlift : ∀ y ∈ D, Complex.exp (((ψ y : ℝ) : ℂ) * Complex.I) = g y) :
    ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ D x₀ := by
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
      (hg).div_const _
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
  -- `ψ - φ - ψ x₀` is continuous at `x₀` within `D`, integer valued and `0` at `x₀`
  have hcont : ContinuousWithinAt (fun y : ℂ => ψ y - φ y - ψ x₀) D x₀ :=
    (hψ.sub hφsm.continuousAt.continuousWithinAt).sub continuousWithinAt_const
  obtain ⟨δ, hδ, hδU⟩ :=
    (Metric.continuousWithinAt_iff.mp hcont) (2 * Real.pi) (by positivity)
  have hδU' : ∀ y ∈ D, dist y x₀ < δ → |ψ y - φ y - ψ x₀| < 2 * Real.pi := by
    intro y hy hyδ
    have h := hδU hy hyδ
    simpa [Real.dist_eq, hφ0] using h
  have hev : ∀ᶠ y in nhdsWithin x₀ D, ψ y - φ y - ψ x₀ = 0 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds x₀ hδ] with y hy hyD
    obtain ⟨k, hk⟩ := hint y hyD
    have h2 : |ψ y - φ y - ψ x₀| < 2 * Real.pi := hδU' y hyD (Metric.mem_ball.mp hy)
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
    (contDiffWithinAt_const.add hφsm.contDiffWithinAt)
  refine hsm.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hev] with y hy
    linarith
  · rw [hφ0, add_zero]

theorem smoothUnit_eqOn_annulus_of_periodicArgument {ρ₀ ρ₁ ρ₂ ρ₃ : ℝ}
    (hρ₀ : 0 < ρ₀) (h₀₁ : ρ₀ < ρ₁) (h₁₂ : ρ₁ < ρ₂) (h₂₃ : ρ₂ < ρ₃)
    {w : ℂ → ℂ}
    (hwsm : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ ρ₃ → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w z)
    (hwunit : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ ρ₃ → ‖w z‖ = 1)
    {θ : ℝ → ℝ} (hθc : Continuous θ) (hθper : Function.Periodic θ (2 * Real.pi))
    (hθ : ∀ σ : ℝ, Complex.exp (((θ σ : ℝ) : ℂ) * Complex.I)
      = w ((ρ₀ : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I))) :
    ∃ Ω : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ω ∧ (∀ z : ℂ, ‖Ω z‖ = 1) ∧
      (∀ z : ℂ, ρ₁ ≤ ‖z‖ → ‖z‖ ≤ ρ₂ → Ω z = w z) := by
  classical
  have hρ₁ : 0 < ρ₁ := lt_trans hρ₀ h₀₁
  have hρ₂ : 0 < ρ₂ := lt_trans hρ₁ h₁₂
  obtain ⟨rl, hr₀, hr₁⟩ := exists_between h₀₁
  obtain ⟨rh, hr₂, hr₃⟩ := exists_between h₂₃
  -- the open annulus on which the argument is constructed
  set A : Set ℂ := {z : ℂ | ρ₀ < ‖z‖ ∧ ‖z‖ < ρ₃} with hA
  have hAmem : ∀ z : ℂ, z ∈ A ↔ ρ₀ < ‖z‖ ∧ ‖z‖ < ρ₃ := by
    intro z
    rw [hA]
    exact Iff.rfl
  have hAne : ∀ z : ℂ, z ∈ A → z ≠ 0 := by
    intro z hz h0
    have h1 := (hAmem z).mp hz
    rw [h0, norm_zero] at h1
    exact absurd h1.1 (not_lt.mpr (le_of_lt hρ₀))
  -- the radial interpolation
  set rad : ↑unitInterval × A → ℂ := fun p =>
    ((((1 - (p.1 : ℝ)) * ρ₀ + (p.1 : ℝ) * ‖(p.2 : ℂ)‖ : ℝ)) : ℂ)
      * ((p.2 : ℂ) / ((‖(p.2 : ℂ)‖ : ℝ) : ℂ)) with hrad
  have hrad_zn : ∀ p : ↑unitInterval × A, ‖(p.2 : ℂ)‖ ≠ 0 := by
    intro p
    exact norm_ne_zero_iff.mpr (hAne _ p.2.2)
  have hrad_nn : ∀ p : ↑unitInterval × A,
      0 ≤ (1 - (p.1 : ℝ)) * ρ₀ + (p.1 : ℝ) * ‖(p.2 : ℂ)‖ := by
    intro p
    have ht0 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2.1
    have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
    have hz : 0 < ‖(p.2 : ℂ)‖ := lt_trans hρ₀ ((hAmem _).mp p.2.2).1
    nlinarith
  have hrad_norm : ∀ p : ↑unitInterval × A,
      ‖rad p‖ = (1 - (p.1 : ℝ)) * ρ₀ + (p.1 : ℝ) * ‖(p.2 : ℂ)‖ := by
    intro p
    rw [hrad]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hrad_nn p), norm_div, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), div_self (hrad_zn p), mul_one]
  have hrad_mem : ∀ p : ↑unitInterval × A, ρ₀ ≤ ‖rad p‖ ∧ ‖rad p‖ ≤ ρ₃ := by
    intro p
    have ht0 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2.1
    have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
    have hz1 : ρ₀ ≤ ‖(p.2 : ℂ)‖ := le_of_lt ((hAmem _).mp p.2.2).1
    have hz2 : ‖(p.2 : ℂ)‖ ≤ ρ₃ := le_of_lt ((hAmem _).mp p.2.2).2
    rw [hrad_norm p]
    constructor <;> nlinarith
  have hrad_cont : Continuous rad := by
    rw [hrad]
    have h1 : Continuous fun p : ↑unitInterval × A => (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have h2 : Continuous fun p : ↑unitInterval × A => ‖(p.2 : ℂ)‖ :=
      continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
    have h3 : Continuous fun p : ↑unitInterval × A =>
        ((1 - (p.1 : ℝ)) * ρ₀ + (p.1 : ℝ) * ‖(p.2 : ℂ)‖ : ℝ) :=
      ((continuous_const.sub h1).mul continuous_const).add (h1.mul h2)
    have h4 : Continuous fun p : ↑unitInterval × A =>
        (p.2 : ℂ) / ((‖(p.2 : ℂ)‖ : ℝ) : ℂ) :=
      (continuous_subtype_val.comp continuous_snd).div
        (Complex.ofRealCLM.continuous.comp h2)
        (fun p => by simpa using (Complex.ofReal_ne_zero.mpr (hrad_zn p)))
    exact (Complex.ofRealCLM.continuous.comp h3).mul h4
  have hwrad_cont : Continuous fun p : ↑unitInterval × A => w (rad p) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact ((hwsm (rad p) (hrad_mem p).1 (hrad_mem p).2).continuousAt).comp hrad_cont.continuousAt
  have hunit_rad : ∀ p : ↑unitInterval × A, ‖w (rad p)‖ = 1 := fun p =>
    hwunit (rad p) (hrad_mem p).1 (hrad_mem p).2
  -- the `Circle`-valued homotopy and the lift of its starting slice
  set Hc : C(↑unitInterval × A, Circle) :=
    ⟨fun p => ⟨w (rad p), mem_sphere_zero_iff_norm.mpr (hunit_rad p)⟩,
      hwrad_cont.subtype_mk _⟩ with hHc
  have hf₀c : Continuous fun a : A => θ ((a : ℂ).arg) :=
    ((continuousOn_comp_arg hθc hθper).mono (fun z hz => hAne z hz)).domRestrict.congr
      (fun a => by rw [Set.domRestrict_apply])
  set f₀ : C(A, ℝ) := ⟨fun a : A => θ ((a : ℂ).arg), hf₀c⟩ with hf₀
  have hH0 : ∀ a : A, Hc (0, a) = Circle.exp (f₀ a) := by
    intro a
    apply Circle.ext
    rw [hHc, hf₀]
    rw [Circle.coe_exp]
    show w (rad (0, a)) = Complex.exp (((θ ((a : ℂ).arg) : ℝ) : ℂ) * Complex.I)
    rw [hθ ((a : ℂ).arg)]
    congr 1
    rw [exp_arg_eq_div (a : ℂ) (hAne _ a.2), hrad]
    show ((((1 - (((0 : ↑unitInterval)) : ℝ)) * ρ₀
        + (((0 : ↑unitInterval)) : ℝ) * ‖(a : ℂ)‖ : ℝ)) : ℂ)
      * ((a : ℂ) / ((‖(a : ℂ)‖ : ℝ) : ℂ))
      = (ρ₀ : ℂ) * ((a : ℂ) / ((‖(a : ℂ)‖ : ℝ) : ℂ))
    norm_num
  set L : C(↑unitInterval × A, ℝ) := Circle.isCoveringMap_exp.liftHomotopy Hc f₀ hH0 with hL
  have hLlifts : ⇑Circle.exp ∘ ⇑L = ⇑Hc := by
    rw [hL]
    exact IsCoveringMap.liftHomotopy_lifts Circle.isCoveringMap_exp Hc f₀ hH0
  -- the argument of `w` on `A`
  set ψ : ℂ → ℝ := fun z => if hz : z ∈ A then L (1, ⟨z, hz⟩) else 0 with hψ
  have hψeq : ∀ a : A, ψ (a : ℂ) = L (1, a) := by
    intro a
    rw [hψ]
    simp only [dif_pos a.2]
  have hψlift : ∀ z : ℂ, z ∈ A → Complex.exp (((ψ z : ℝ) : ℂ) * Complex.I) = w z := by
    intro z hz
    have h1 : ψ z = L (1, ⟨z, hz⟩) := by
      rw [hψ]
      simp only [dif_pos hz]
    have h2 : Circle.exp (L (1, ⟨z, hz⟩)) = Hc (1, ⟨z, hz⟩) :=
      congr_fun hLlifts (1, ⟨z, hz⟩)
    have h3 : ((Hc (1, ⟨z, hz⟩)) : ℂ) = w z := by
      rw [hHc]
      show w (rad (1, ⟨z, hz⟩)) = w z
      congr 1
      rw [hrad]
      show ((((1 - (((1 : ↑unitInterval)) : ℝ)) * ρ₀
          + (((1 : ↑unitInterval)) : ℝ) * ‖z‖ : ℝ)) : ℂ)
        * (z / ((‖z‖ : ℝ) : ℂ)) = z
      rw [Set.Icc.coe_one, sub_self, zero_mul, zero_add, one_mul]
      rw [mul_div_cancel₀ _ (by
        simp only [Complex.ofReal_ne_zero]
        exact norm_ne_zero_iff.mpr (hAne z hz))]
    rw [h1, ← Circle.coe_exp (L (1, ⟨z, hz⟩)), h2]
    exact h3
  have hψon : Continuous fun a : A => ψ (a : ℂ) := by
    have hLc : Continuous fun a : A => L (1, a) :=
      L.continuous.comp (continuous_const.prodMk continuous_id)
    exact hLc.congr (fun a => (hψeq a).symm)
  have hψsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ A := by
    intro z hz
    refine contDiffWithinAt_of_exp_lift (g := w) (ψ := ψ) (D := A) hz ?_ ?_ ?_ ?_
    · exact hwsm z (le_of_lt ((hAmem z).mp hz).1) (le_of_lt ((hAmem z).mp hz).2)
    · exact ((continuousOn_iff_continuous_domRestrict).mpr hψon).continuousWithinAt hz
    · intro y hy
      exact hwunit y (le_of_lt ((hAmem y).mp hy).1) (le_of_lt ((hAmem y).mp hy).2)
    · intro y hy
      exact hψlift y hy
  -- the cutoff
  set χ : ℂ → ℝ := fun z => pStep rl ρ₁ ‖z‖ - pStep ρ₂ rh ‖z‖ with hχ
  have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    simp only [hχ]
    exact (contDiff_pStep_norm (a := rl) (b := ρ₁) (lt_trans hρ₀ hr₀) hr₁).sub
      (contDiff_pStep_norm (a := ρ₂) (b := rh) hρ₂ hr₂)
  have hχone : ∀ z : ℂ, ρ₁ ≤ ‖z‖ → ‖z‖ ≤ ρ₂ → χ z = 1 := by
    intro z h1 h2
    have h3 : ‖z‖ ≤ ρ₂ := h2
    simp only [hχ, pStep_eq_one hr₁ h1, pStep_eq_zero hr₂ h3, sub_zero]
  have hχzero_low : ∀ z : ℂ, ‖z‖ ≤ rl → χ z = 0 := by
    intro z h
    have h2 : ‖z‖ ≤ ρ₂ := by linarith
    simp only [hχ, pStep_eq_zero hr₁ h, pStep_eq_zero hr₂ h2, sub_self]
  have hχzero_high : ∀ z : ℂ, rh ≤ ‖z‖ → χ z = 0 := by
    intro z h
    have h1 : ρ₁ ≤ ‖z‖ := by linarith
    simp only [hχ, pStep_eq_one hr₁ h1, pStep_eq_one hr₂ h, sub_self]
  have hΨsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => χ z * ψ z) := by
    refine contDiff_of_contDiffOn_union_of_isOpen (s := A)
      (t := {z : ℂ | ‖z‖ < rl} ∪ {z : ℂ | rh < ‖z‖}) ?_ ?_ ?_ ?_ ?_
    · exact hχsm.contDiffOn.mul hψsm
    · refine ContDiffOn.congr (contDiffOn_const (c := (0 : ℝ))) (fun z hz => ?_)
      rcases hz with hz | hz
      · rw [hχzero_low z (le_of_lt hz), zero_mul]
      · rw [hχzero_high z (le_of_lt hz), zero_mul]
    · ext z
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      by_cases hz : ρ₀ < ‖z‖ ∧ ‖z‖ < ρ₃
      · exact Or.inl ((hAmem z).mpr hz)
      · rw [not_and_or] at hz
        rcases hz with hz | hz
        · exact Or.inr (Or.inl (lt_of_le_of_lt (not_lt.mp hz) hr₀))
        · exact Or.inr (Or.inr (lt_of_lt_of_le hr₃ (not_lt.mp hz)))
    · rw [hA, Set.ofPred_and]
      exact (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    · exact (isOpen_lt continuous_norm continuous_const).union
        (isOpen_lt continuous_const continuous_norm)
  refine ⟨fun z : ℂ => Complex.exp (((χ z * ψ z : ℝ) : ℂ) * Complex.I), ?_, ?_, ?_⟩
  · refine Complex.contDiff_exp.comp ?_
    exact (Complex.ofRealCLM.contDiff.comp hΨsm).mul contDiff_const
  · intro z
    exact norm_exp_mul_I (χ z * ψ z)
  · intro z h1 h2
    have hχz : χ z = 1 := hχone z h1 h2
    have hzA : z ∈ A :=
      (hAmem z).mpr ⟨lt_of_lt_of_le hr₀ (le_trans (le_of_lt hr₁) h1),
        lt_of_le_of_lt h2 (lt_trans hr₂ hr₃)⟩
    show Complex.exp (((χ z * ψ z : ℝ) : ℂ) * Complex.I) = w z
    rw [hχz, one_mul]
    exact hψlift z hzA

end

end Work.Drive
