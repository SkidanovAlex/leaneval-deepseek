import Submission.UnifDeps
import Submission.ExtremalInj
import Submission.Holomorphic
import Submission.Commons.Analysis.Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero

/-!
# Uniformization from an injective map into a simply connected planar domain

Mathlib's `Analysis/Complex/RiemannMapping.lean` contains (at this revision) the first half of the
Riemann mapping theorem: *every open, simply connected, proper subset `U ⊆ ℂ` admits an injective
holmorphic map into the unit disc with non-vanishing derivative*.  At this revision those
declarations are **private to that module** (the module is a "private module", see
`set_option linter.privateModule false` in the file), so they cannot be imported; the statement has
been re-requested as the commons lemma
`Commons.Analysis.Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero` (fleet child, Session 18),
proved from the *public* `Complex.exists_continuousOn_pow_eq` of `BranchLogRoot.lean`.

Combined with Case A of uniformization (`Submission.uniformization_of_injective_into_disc`, which
upgrades "there is an injective holomorphic map `X → 𝔻`" into the target disjunction), that gives a
new input to the endgame of the challenge:

> if `X` admits an injective holomorphic map whose image lies in a proper simply connected planar
> domain `U`, then the uniformization conclusion holds for `X` (indeed `X ≅ 𝔻`).

This supersedes the special case "the image is bounded".  The commons lemma has landed (Session 18,
fleet child L118) and is used directly below.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Uniformization from an injective holomorphic map into a proper simply connected planar
domain.** -/
theorem uniformization_of_injective_to_simplyConnected {x₀ : X} [ConnectedSpace X]
    [SecondCountableTopology X] [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {φ : X → ℂ} (hφ : HolomorphicOnX φ univ) (hinj : Function.Injective φ)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hUne : U ≠ Set.univ)
    (hsub : Set.range φ ⊆ U) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  obtain ⟨f, hfmap, hfinj, hfderiv⟩ :=
    Commons.Analysis.Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero hUo hUc hUne
  have hmem : ∀ x : X, φ x ∈ U := fun x => hsub (Set.mem_range_self x)
  have hmt : ∀ x : X, f (φ x) ∈ Metric.ball (0 : ℂ) 1 := fun x => hfmap (hmem x)
  have hfbnd : ∀ x : X, ‖f (φ x)‖ ≤ 1 := fun x => by
    have h := hmt x
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
    exact le_of_lt h
  have ha : ‖f (φ x₀)‖ < 1 := by
    have h := hmt x₀
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at h
  -- the composite `x ↦ mobiusA (f (φ x₀)) (f (φ x))` is an injective holomorphic map into `𝔻`
  have hhol : HolomorphicOnX (fun x : X => mobiusA (f (φ x₀)) (f (φ x))) univ := by
    intro x _
    have h1 : AnalyticAt ℂ (φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hφ x (mem_univ x)
    have hev : ∀ᶠ z in 𝓝 (φ x), DifferentiableAt ℂ f z := by
      filter_upwards [hUo.mem_nhds (hmem x)] with z hz
      exact differentiableAt_of_deriv_ne_zero (hfderiv z hz)
    have hfana : AnalyticAt ℂ f (φ x) :=
      Complex.analyticAt_iff_eventually_differentiableAt.mpr hev
    have hmob : AnalyticAt ℂ (mobiusA (f (φ x₀))) (f (φ x)) :=
      analyticAt_mobiusA _ (mobiusA_denom_ne_zero ha (hfbnd x))
    have hφval : (φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = φ x := by
      simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    have hg : AnalyticAt ℂ (fun w : ℂ => mobiusA (f (φ x₀)) (f w))
        ((φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) := by
      rw [hφval]
      exact hmob.comp hfana
    exact hg.comp h1
  have hinj' : Function.Injective (fun x : X => mobiusA (f (φ x₀)) (f (φ x))) := by
    intro x y hxy
    refine hinj (hfinj (hmem x) (hmem y) ?_)
    exact mobiusA_injOn ha (hfbnd x) (hfbnd y) hxy
  have hbnd : ∀ x : X, ‖mobiusA (f (φ x₀)) (f (φ x))‖ ≤ 1 :=
    fun x => norm_mobiusA_le ha (hfbnd x)
  have h0 : (fun x : X => mobiusA (f (φ x₀)) (f (φ x))) x₀ = 0 :=
    mobiusA_self _
  exact uniformization_of_injective_into_disc (x₀ := x₀)
    ⟨_, ⟨⟨hhol, hbnd, h0⟩, hinj'⟩⟩

/-! ## The bounded-image case -/

/-- **Uniformization from a bounded injective holomorphic function.**  If `X` admits an injective
holomorphic map into a bounded subset of `ℂ`, then `X ≅ 𝔻` (second disjunct). -/
theorem uniformization_of_bounded_injective {x₀ : X} [ConnectedSpace X]
    [SecondCountableTopology X] [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {f : X → ℂ} (hf : HolomorphicOnX f univ) (hinj : Function.Injective f)
    {M : ℝ} (hM : ∀ x : X, ‖f x‖ ≤ M) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM x₀)
  set C : ℝ := 2 * M + 1 with hC
  have hCpos : 0 < C := by positivity
  have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hCpos.ne'
  set g : X → ℂ := fun x => (f x - f x₀) * (C : ℂ)⁻¹ with hgdef
  have hgval : ∀ x : X, g x = (f x - f x₀) * (C : ℂ)⁻¹ := fun x => rfl
  have hhol : HolomorphicOnX g univ := fun x _ => by
    have h1 : HolomorphicOnXAt (fun y : X => f y - f x₀) x :=
      (hf x (mem_univ x)).sub (by
        rw [HolomorphicOnXAt]
        have h2 : (fun _ : X => f x₀) ∘ (chartAt ℂ x).symm = fun _ : ℂ => f x₀ := rfl
        rw [h2]
        exact analyticAt_const)
    have h3 := HolomorphicOnXAt.mul_const h1 ((C : ℂ)⁻¹)
    exact h3
  have hnorm : ∀ x : X, ‖g x‖ ≤ 1 := by
    intro x
    have h1 : ‖f x - f x₀‖ ≤ C := by
      have h2 : ‖f x - f x₀‖ ≤ ‖f x‖ + ‖f x₀‖ := norm_sub_le _ _
      have h3 : ‖f x‖ + ‖f x₀‖ ≤ M + M := add_le_add (hM x) (hM x₀)
      have h4 : M + M ≤ C := by simp only [hC]; linarith
      linarith
    rw [hgval x, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hCpos]
    calc ‖f x - f x₀‖ * C⁻¹ ≤ C * C⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 := by rw [mul_inv_cancel₀ hCpos.ne']
  have hval : g x₀ = 0 := by rw [hgval x₀]; simp
  have hinjg : Function.Injective g := by
    intro x y hxy
    have h1 : (f x - f x₀) * (C : ℂ)⁻¹ = (f y - f x₀) * (C : ℂ)⁻¹ := hxy
    have h2 : f x - f x₀ = f y - f x₀ := mul_right_cancel₀ (inv_ne_zero hCne) h1
    have h3 : f x = f y := by
      have hh := congrArg (fun w : ℂ => w + f x₀) h2
      simpa using hh
    exact hinj h3
  exact uniformization_of_injective_into_disc (x₀ := x₀) ⟨g, ⟨⟨hhol, hnorm, hval⟩, hinjg⟩⟩

end Submission
