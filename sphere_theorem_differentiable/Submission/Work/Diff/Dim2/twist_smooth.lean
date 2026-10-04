import Mathlib
import Submission.Work.Diff.Dim2.Field

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set

/-!
# Smoothness of the "twist" map `x ↦ (cos A x, sin A x)`

`Complex.arg` is only continuous away from the branch cut `(-∞, 0]`, so the function

`x ↦ ((1 - β (σ x)) * (u x).arg + β (σ x) * ρ ((u x).arg))`

is *not* smooth in general.  However `ρ` is `2π`-periodic up to the translation `+ 2π`
(`ρ (θ + 2π) = ρ θ + 2π`), so the *angle* `A` is well defined modulo `2π` — and
`(cos, sin)` is `2π`-periodic, so `(cos (A x), sin (A x))` is a smooth function of `x`.

The proof is local on `M`: at a point `x₀` with `u x₀` off the branch cut we simply use
`Complex.arg` itself (smooth near `u x₀`, via `Complex.log`); at a point with `u x₀ = -1`
we use instead the locally smooth lift `Complex.arg (-(u x)) + π`, which differs from
`Complex.arg (u x)` by an integer multiple of `2π` everywhere, so that the resulting
`(cos, sin)` agrees pointwise.

This is the circle lemma isolated in `Plan2.lean` §4 (the twist `Az`).
-/

/-- The periodicity of `ρ` upgraded to all integer multiples of `2π`. -/
lemma rho_add_int_mul {ρ : ℝ → ℝ} (hρper : ∀ θ, ρ (θ + 2 * Real.pi) = ρ θ + 2 * Real.pi)
    (k : ℤ) (θ : ℝ) : ρ (θ + (k : ℝ) * (2 * Real.pi)) = ρ θ + (k : ℝ) * (2 * Real.pi) := by
  have hper : Function.Periodic (fun t : ℝ => ρ t - t) (2 * Real.pi) := by
    intro t
    show ρ (t + 2 * Real.pi) - (t + 2 * Real.pi) = ρ t - t
    rw [hρper t]
    ring
  have h := hper.int_mul k θ
  change ρ (θ + (k : ℝ) * (2 * Real.pi)) - (θ + (k : ℝ) * (2 * Real.pi)) = ρ θ - θ at h
  linarith

/-- `t ↦ (cos t, sin t)` is `2π`-periodic (integer multiples). -/
lemma ei_add_int_mul_two_pi (t : ℝ) (k : ℤ) :
    ((Real.cos (t + (k : ℝ) * (2 * Real.pi)), Real.sin (t + (k : ℝ) * (2 * Real.pi))) : ℝ × ℝ)
      = (Real.cos t, Real.sin t) := by
  rw [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- `Complex.arg` is smooth (`C^∞` as a real function) off its branch cut; equivalently,
`arg = im ∘ log` and `Complex.log` is complex-differentiable on the slit plane. -/
lemma contDiffAt_arg {z : ℂ} (hz : z ∈ Complex.slitPlane) : ContDiffAt ℝ ∞ Complex.arg z := by
  have hlog : ContDiffAt ℝ ∞ Complex.log z := (Complex.contDiffAt_log hz).restrict_scalars ℝ
  have h : ContDiffAt ℝ ∞ (fun w : ℂ => (Complex.log w).im) z :=
    ContDiffAt.comp z Complex.imCLM.contDiff.contDiffAt hlog
  simpa only [Complex.log_im] using h

/-- `arg (-z) + π` differs from `arg z` by an integer multiple of `2π`. -/
lemma arg_neg_add_pi (z : ℂ) (hz : z ≠ 0) :
    ∃ k : ℤ, Complex.arg (-z) + Real.pi = Complex.arg z + (k : ℝ) * (2 * Real.pi) := by
  have hπ : (((Real.pi : ℝ) : Real.Angle) + ((Real.pi : ℝ) : Real.Angle)) = 0 := by
    rw [← Real.Angle.coe_add, show Real.pi + Real.pi = 2 * Real.pi by ring, Real.Angle.coe_two_pi]
  have h1 : ((Complex.arg (-z) + Real.pi : ℝ) : Real.Angle) = (Complex.arg z : Real.Angle) := by
    rw [Real.Angle.coe_add, Complex.arg_neg_coe_angle hz, add_assoc, hπ, add_zero]
  obtain ⟨k, hk⟩ := (Real.Angle.angle_eq_iff_two_pi_dvd_sub (θ := Complex.arg (-z) + Real.pi)
      (ψ := Complex.arg z)).mp h1
  exact ⟨k, by linarith [hk]⟩

theorem twist_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {u : M → ℂ} (hu : ContMDiff I (modelWithCornersSelf ℝ ℂ) ∞ u) (hunit : ∀ x, ‖u x‖ = 1)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hper : ∀ θ, ρ (θ + 2 * Real.pi) = ρ θ + 2 * Real.pi)
    {σ : M → ℝ} (hσ : ContMDiff I 𝓘(ℝ,ℝ) ∞ σ) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ (fun x : M =>
        let A : ℝ := (1 - β (σ x)) * (u x).arg + β (σ x) * ρ ((u x).arg)
        (Real.cos A, Real.sin A)) ∧
      (∀ x : M, β (σ x) = 0 →
        ((Real.cos ((u x).arg), Real.sin ((u x).arg)) : ℝ × ℝ) = ((u x).re, (u x).im)) := by
  have hu_ne : ∀ x, u x ≠ 0 := fun x => norm_ne_zero_iff.mp (by rw [hunit x]; norm_num)
  refine ⟨?_, ?_⟩
  · intro x₀
    have hβσ : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun x => β (σ x)) x₀ :=
      hβ.contDiffAt.comp_contMDiffAt (hσ x₀)
    have h1 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun x => 1 - β (σ x)) x₀ := by
      simpa using (contMDiffAt_const (c := (1 : ℝ))).sub hβσ
    by_cases hmem : u x₀ ∈ Complex.slitPlane
    · -- `u x₀` is off the branch cut: `Complex.arg` is smooth near it.
      have harg : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun x => (u x).arg) x₀ :=
        (contDiffAt_arg hmem).comp_contMDiffAt (hu x₀)
      have h4 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun x => ρ ((u x).arg)) x₀ :=
        hρ.contDiffAt.comp_contMDiffAt harg
      have hA : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
          (fun x => (1 - β (σ x)) * (u x).arg + β (σ x) * ρ ((u x).arg)) x₀ :=
        (h1.mul harg).add (hβσ.mul h4)
      exact (Real.contDiff_cos.contDiffAt.prodMk Real.contDiff_sin.contDiffAt).comp_contMDiffAt hA
    · -- `u x₀` lies on the branch cut, hence `u x₀ = -1`: use the lift `arg (-u) + π`.
      have hargπ : (u x₀).arg = Real.pi := by
        by_contra hne
        exact hmem (Complex.mem_slitPlane_iff_arg.mpr ⟨hne, hu_ne x₀⟩)
      have hre : (u x₀).re < 0 := (Complex.arg_eq_pi_iff.mp hargπ).1
      have him : (u x₀).im = 0 := (Complex.arg_eq_pi_iff.mp hargπ).2
      have harg0 : Complex.arg (-(u x₀)) = 0 := by
        rw [Complex.arg_eq_zero_iff]
        exact ⟨by simp only [Complex.neg_re]; linarith,
               by simp only [Complex.neg_im, him, neg_zero]⟩
      have hslit : -(u x₀) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff_arg.mpr
          ⟨by rw [harg0]; exact Real.pi_ne_zero.symm, neg_ne_zero.mpr (hu_ne x₀)⟩
      have hneg : ContMDiffAt I 𝓘(ℝ,ℂ) ∞ (fun x => -u x) x₀ := (hu x₀).neg
      have hL : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun x => Complex.arg (-(u x)) + Real.pi) x₀ := by
        have houter : ContDiffAt ℝ ∞ (fun w : ℂ => Complex.arg w + Real.pi) (-(u x₀)) :=
          (contDiffAt_arg hslit).add (contDiffAt_const (c := Real.pi))
        exact ContDiffAt.comp_contMDiffAt (f := fun x => -u x) (x := x₀) houter hneg
      have h4 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun x => ρ (Complex.arg (-(u x)) + Real.pi)) x₀ :=
        hρ.contDiffAt.comp_contMDiffAt hL
      have hA' : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
          (fun x => (1 - β (σ x)) * (Complex.arg (-(u x)) + Real.pi)
                    + β (σ x) * ρ (Complex.arg (-(u x)) + Real.pi)) x₀ :=
        (h1.mul hL).add (hβσ.mul h4)
      have key : ContMDiffAt I 𝓘(ℝ, ℝ × ℝ) ∞
          (fun x => (Real.cos ((1 - β (σ x)) * (Complex.arg (-(u x)) + Real.pi)
                      + β (σ x) * ρ (Complex.arg (-(u x)) + Real.pi)),
                     Real.sin ((1 - β (σ x)) * (Complex.arg (-(u x)) + Real.pi)
                      + β (σ x) * ρ (Complex.arg (-(u x)) + Real.pi)))) x₀ :=
        (Real.contDiff_cos.contDiffAt.prodMk Real.contDiff_sin.contDiffAt).comp_contMDiffAt hA'
      -- the two functions agree pointwise, because the two angles differ by `2πℤ`
      refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      obtain ⟨k, hk⟩ := arg_neg_add_pi (u x) (hu_ne x)
      have hρk : ρ (Complex.arg (-(u x)) + Real.pi)
          = ρ ((u x).arg) + (k : ℝ) * (2 * Real.pi) := by
        rw [hk]
        exact rho_add_int_mul hper k ((u x).arg)
      have hAB : (1 - β (σ x)) * (Complex.arg (-(u x)) + Real.pi)
            + β (σ x) * ρ (Complex.arg (-(u x)) + Real.pi)
          = (1 - β (σ x)) * (u x).arg + β (σ x) * ρ ((u x).arg)
            + (k : ℝ) * (2 * Real.pi) := by
        rw [hρk, hk]
        ring
      rw [hAB]
      exact (ei_add_int_mul_two_pi ((1 - β (σ x)) * (u x).arg
        + β (σ x) * ρ ((u x).arg)) k).symm
  · -- on the unit circle, `(cos (arg z), sin (arg z)) = (z.re, z.im)`
    intro x _
    rw [Prod.mk.injEq]
    exact ⟨by rw [Complex.cos_arg (hu_ne x), hunit x, div_one],
           by rw [Complex.sin_arg, hunit x, div_one]⟩

end Work.Diff.Dim2
