import Submission.UnifDeps
import Submission.GreenData
import Submission.HolomorphicLog
import Submission.Conjugate

/-!
# The holomorphic modulus of a Green function with a logarithmic pole

The hyperbolic endgame (`Submission.uniformization_of_green_modulus`) needs, besides the Green
function `E`, a *holomorphic* `Φ` with `‖Φ x‖ = exp (-E x)`.  Classically `Φ = exp (-(E + iE*))`
where `E*` is the harmonic conjugate of `E`; the difficulty is that the conjugate is only
multivalued, with periods, and `Φ` is single-valued only because those periods lie in `2πℤ`.

The point of this module is that **this difficulty disappears if one already has a global
holomorphic function `g` with a single simple zero at the pole `z₀`**.  Indeed, `E + log ‖g‖` is
then harmonic on *all* of `X` (the two logarithmic poles cancel, and there is no other zero), so by
`Submission.exists_holomorphicOnX_re_of_harmonic` (which uses the cohomological hypothesis
`Hom (π₁ X, ℝ) = 0` of the uniformization theorem) there is `F` holomorphic on `X` with
`Re F = E + log ‖g‖`; then

`Φ := g * exp (-F)` satisfies `‖Φ‖ = ‖g‖ * exp (-(E + log ‖g‖)) = exp (-E)`.

So the construction of the *pair* `(E, Φ)` reduces to the construction of `g` alone, i.e. to a
single global holomorphic function with a single simple zero at `z₀`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The holomorphic modulus exists as soon as the logarithmic poles cancel.**  If `g` is
holomorphic on `X` with `g x ≠ 0` for `x ≠ z₀`, if `E + log ‖g‖` is harmonic on all of `X`, and if
`g` has a logarithmic pole at `z₀` (`Submission.HasLogPoleAt`), then there is a holomorphic `Φ` on
`X` with the same logarithmic pole and with `‖Φ x‖ = exp (-E x)` for `x ≠ z₀`.

The harmonicity of `E + log ‖g‖` is automatic when `E` and `log ‖g‖` have the same logarithmic
pole at `z₀` and `g` vanishes only at `z₀`; it is kept as an explicit hypothesis to avoid chart
computations. -/
theorem exists_holomorphic_modulus {x₀ z₀ : X} {E : X → ℝ} {g : X → ℂ}
    (hg : HolomorphicOnX g univ) (hg_ne : ∀ x, x ≠ z₀ → g x ≠ 0)
    (hK : HarmonicOnX (fun x => E x + Real.log ‖g x‖) univ)
    (hgpole : HasLogPoleAt z₀ g)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] :
    ∃ Φ : X → ℂ, HolomorphicOnX Φ univ ∧ HasLogPoleAt z₀ Φ ∧
      ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) := by
  obtain ⟨F, hFhol, hFre⟩ := exists_holomorphicOnX_re_of_harmonic x₀ hK
  have hFana : AnalyticAt ℂ (F ∘ (chartAt ℂ z₀).symm) ((chartAt ℂ z₀) z₀) := hFhol z₀ (mem_univ z₀)
  -- the logarithmic pole is inherited: multiply the local factor of `g` by `exp (-(F ·))`
  have hpole' : HasLogPoleAt z₀ (fun x => g x * Complex.exp (-(F x))) := by
    obtain ⟨H, hHana, hHne, hev⟩ := hgpole
    have hexpana : AnalyticAt ℂ
        (fun w : ℂ => Complex.exp (-(F ((chartAt ℂ z₀).symm w)))) ((chartAt ℂ z₀) z₀) := by
      have h1 : AnalyticAt ℂ (fun w : ℂ => -(F ((chartAt ℂ z₀).symm w))) ((chartAt ℂ z₀) z₀) :=
        hFana.neg
      exact h1.cexp
    refine ⟨fun w : ℂ => H w * Complex.exp (-(F ((chartAt ℂ z₀).symm w))), ?_, ?_, ?_⟩
    · exact hHana.mul hexpana
    · exact mul_ne_zero hHne (Complex.exp_ne_zero _)
    · filter_upwards [hev] with w hw
      have hw' : g ((chartAt ℂ z₀).symm w) = (w - (chartAt ℂ z₀) z₀) * H w := hw
      show g ((chartAt ℂ z₀).symm w) * Complex.exp (-(F ((chartAt ℂ z₀).symm w)))
        = (w - (chartAt ℂ z₀) z₀) *
          (H w * Complex.exp (-(F ((chartAt ℂ z₀).symm w))))
      rw [hw']
      ring
  refine ⟨fun x => g x * Complex.exp (-(F x)), ?_, hpole', ?_⟩
  · refine HolomorphicOnX.mul hg ?_
    intro x _
    exact HolomorphicOnXAt.cexp_neg (hFhol x (mem_univ x))
  · intro x hx
    have hgx : g x ≠ 0 := hg_ne x hx
    have hgp : 0 < ‖g x‖ := norm_pos_iff.mpr hgx
    have hnorm : ‖Complex.exp (-(F x))‖ = Real.exp (-(E x + Real.log ‖g x‖)) := by
      rw [Complex.norm_exp, Complex.neg_re, hFre x]
    have hexp : Real.exp (-(E x + Real.log ‖g x‖)) = Real.exp (-(E x)) / ‖g x‖ := by
      have h1 : -(E x + Real.log ‖g x‖) = -(E x) + -(Real.log ‖g x‖) := by ring
      rw [h1, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hgp, div_eq_mul_inv]
    rw [norm_mul, hnorm, hexp]
    field_simp

end Submission
