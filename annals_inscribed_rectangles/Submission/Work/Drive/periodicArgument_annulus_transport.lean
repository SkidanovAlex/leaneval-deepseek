import Mathlib
import Submission.Work.Drive.periodic_argument_of_homotopy

/-!
# Transport of a periodic argument across an annulus

`Work.Drive.periodicArgument_annulus_transport`: let `w : ℂ → ℂ` be `C^∞` and of modulus one on the
closed annulus `A = {z | ρ ≤ ‖z‖ ≤ ρ₂}` (`0 < ρ < ρ₂`), and suppose that the *outer* radial loop
`σ ↦ w (ρ₂ · exp (σ I))` has a continuous `2π`-periodic argument `θ`.  Then the *inner* radial loop
`σ ↦ w (ρ · exp (σ I))` has one as well.

The two boundary loops of `A` are homotopic inside `A` by the linear radial motion

`F s σ = w ((ρ₂ + clamping s · (ρ - ρ₂)) · exp (σ I))`,

whose values are all in `A` (hence all of modulus one, by `hwunit`), so
`Work.Drive.periodic_argument_of_homotopy` — homotopy invariance of "has a continuous `2π`-periodic
argument", i.e. of the degree-zero condition of the winding number — transports `θ` from `s = 0` to
`s = 1`.  The clamping `s ↦ max 0 (min 1 s)` is what makes the radial motion a *map on all of `ℝ`*
(the family of `periodic_argument_of_homotopy` is indexed by all real `s`, while `w` is only known on
`A`); it agrees with the linear motion on `[0,1]`.

The content is that a periodic argument of `σ ↦ w (ρ₂ e^{iσ})` is *equivalent* to a periodic argument
of `σ ↦ w (ρ e^{iσ})`: both loops have the same winding number, since they are homotopic in the
annulus.  Equivalently, the inner loop is null-homotopic in `S¹` whenever the outer one is.
-/

namespace Work.Drive

open scoped ContDiff Topology

/-- **A continuous `2π`-periodic argument crosses the annulus.**

Let `w` be `C^∞` and of modulus one on the closed annulus `{z : ℂ | ρ ≤ ‖z‖ ≤ ρ₂}` with
`0 < ρ < ρ₂`.  If the loop `σ ↦ w (ρ₂ e^{iσ})` has a continuous `2π`-periodic argument `θ`, then the
loop `σ ↦ w (ρ e^{iσ})` has one too.

(The two loops are joined by the non-vanishing homotopy `σ ↦ w (r e^{iσ})`, `r ∈ [ρ, ρ₂]`, so this
is homotopy invariance of the winding number restricted to the annulus; no degree theory is used, only
`Work.Drive.periodic_argument_of_homotopy`.) -/
theorem periodicArgument_annulus_transport {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂)
    {w : ℂ → ℂ}
    (hwsm : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ ρ₂ → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w z)
    (hwunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ ρ₂ → ‖w z‖ = 1)
    {θ : ℝ → ℝ} (hθc : Continuous θ) (hθper : Function.Periodic θ (2 * Real.pi))
    (hθ : ∀ σ : ℝ, Complex.exp (((θ σ : ℝ) : ℂ) * Complex.I)
      = w ((ρ₂ : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I))) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ Function.Periodic ψ (2 * Real.pi) ∧
      ∀ σ : ℝ, Complex.exp (((ψ σ : ℝ) : ℂ) * Complex.I)
        = w ((ρ : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I)) := by
  -- The radial motion, clamped outside `[0,1]` so that it stays in the annulus for every `s : ℝ`.
  set f : ℝ → ℝ := fun s => max 0 (min 1 s) with hfdef
  set rad : ℝ → ℝ := fun s => ρ₂ + f s * (ρ - ρ₂) with hraddef
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hf1 : f 1 = 1 := by simp [hfdef]
  have hfcont : Continuous f := continuous_const.max (continuous_const.min continuous_id)
  have hfmem : ∀ s : ℝ, 0 ≤ f s ∧ f s ≤ 1 := by
    intro s
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hrad0 : rad 0 = ρ₂ := by
    rw [hraddef]; show ρ₂ + f 0 * (ρ - ρ₂) = ρ₂; rw [hf0]; ring
  have hrad1 : rad 1 = ρ := by
    rw [hraddef]; show ρ₂ + f 1 * (ρ - ρ₂) = ρ; rw [hf1]; ring
  have hradmem : ∀ s : ℝ, ρ ≤ rad s ∧ rad s ≤ ρ₂ := by
    intro s
    obtain ⟨h1, h2⟩ := hfmem s
    have heq : rad s = (1 - f s) * ρ₂ + f s * ρ := by
      rw [hraddef]; show ρ₂ + f s * (ρ - ρ₂) = (1 - f s) * ρ₂ + f s * ρ; ring
    rw [heq]
    constructor <;> nlinarith
  have hradcont : Continuous rad := by
    rw [hraddef]
    exact continuous_const.add (hfcont.mul continuous_const)
  -- The point of the annulus visited by the family at time `s` and parameter `σ`.
  set z : ℝ → ℝ → ℂ := fun s σ => ((rad s : ℝ) : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I)
    with hzdef
  have hznorm : ∀ s σ : ℝ, ‖z s σ‖ = rad s := by
    intro s σ
    have hpos : 0 < rad s := lt_of_lt_of_le hρ (hradmem s).1
    rw [hzdef]
    show ‖((rad s : ℝ) : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I)‖ = rad s
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hzcont : Continuous fun p : ℝ × ℝ => z p.1 p.2 := by
    rw [hzdef]
    show Continuous fun p : ℝ × ℝ =>
      ((rad p.1 : ℝ) : ℂ) * Complex.exp (((p.2 : ℝ) : ℂ) * Complex.I)
    exact ((Complex.ofRealCLM.continuous.comp (hradcont.comp continuous_fst)).mul
      (Complex.continuous_exp.comp ((Complex.ofRealCLM.continuous.comp continuous_snd).mul
        continuous_const)))
  -- The family: it is jointly continuous (only values in the annulus are used) and unit valued.
  have hFc : Continuous fun p : ℝ × ℝ => w (z p.1 p.2) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact ContinuousAt.comp (f := fun q : ℝ × ℝ => z q.1 q.2) (x := p)
      ((hwsm (z p.1 p.2) (by rw [hznorm]; exact (hradmem p.1).1)
        (by rw [hznorm]; exact (hradmem p.1).2)).continuousAt) hzcont.continuousAt
  have hFun : ∀ s σ : ℝ, ‖w (z s σ)‖ = 1 := by
    intro s σ
    exact hwunit (z s σ) (by rw [hznorm]; exact (hradmem s).1)
      (by rw [hznorm]; exact (hradmem s).2)
  -- Periodicity of every slice in `σ`.
  have hexp_shift : Complex.exp ((((2 * Real.pi : ℝ)) : ℂ) * Complex.I) = 1 := by
    rw [show ((((2 * Real.pi : ℝ)) : ℂ) * Complex.I)
      = ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
  have hzper : ∀ s σ : ℝ, z s (σ + 2 * Real.pi) = z s σ := by
    intro s σ
    rw [hzdef]
    show ((rad s : ℝ) : ℂ) * Complex.exp (((σ + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      = ((rad s : ℝ) : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I)
    rw [show (((σ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
        = ((σ : ℂ) * Complex.I) + ((((2 * Real.pi : ℝ)) : ℂ) * Complex.I) by
      push_cast; ring,
      Complex.exp_add, hexp_shift, mul_one]
  have hFper : ∀ s : ℝ, Function.Periodic (fun σ => w (z s σ)) (2 * Real.pi) := by
    intro s σ
    show w (z s (σ + 2 * Real.pi)) = w (z s σ)
    rw [hzper s σ]
  -- The starting slice is the outer loop, whose argument is `θ`.
  have hF0 : ∀ σ : ℝ, Complex.exp (((θ σ : ℝ) : ℂ) * Complex.I) = w (z 0 σ) := by
    intro σ
    rw [show z 0 σ = (ρ₂ : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I) from by
      rw [hzdef]
      show ((rad 0 : ℝ) : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I)
        = (ρ₂ : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I)
      rw [hrad0]]
    exact hθ σ
  obtain ⟨ψ, hψc, hψper, hψ⟩ :=
    periodic_argument_of_homotopy (fun s σ => w (z s σ)) hFc hFun hFper hθc hθper hF0
  refine ⟨ψ, hψc, hψper, ?_⟩
  intro σ
  rw [hψ σ]
  show w (z 1 σ) = w ((ρ : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I))
  rw [show z 1 σ = (ρ : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I) from by
    rw [hzdef]
    show ((rad 1 : ℝ) : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I)
      = (ρ : ℂ) * Complex.exp (((σ : ℝ) : ℂ) * Complex.I)
    rw [hrad1]]

end Work.Drive
