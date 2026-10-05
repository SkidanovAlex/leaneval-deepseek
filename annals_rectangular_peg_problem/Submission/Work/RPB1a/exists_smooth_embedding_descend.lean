import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB.B1.jordan_separation_C
import Submission.Work.RPB.Port.Drive.PolarTwist.isSmoothEmbedding_of_injective_deriv_ne_zero

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff

/-- **Descent of a smooth loop to the circle.**

A smooth loop `v : ℝ → ℂ` (`Work.RPB1a.IsSmoothLoop`) is `2π`-periodic, hence factors through the
covering map `Circle.exp : ℝ → Circle`; the descended map `γ : Circle → ℝ × ℝ` (the loop read in
`ℝ × ℝ` through `Complex.equivRealProdCLM`) is again a smooth embedding, and its range is the image
of the range of `v`.

The construction is the one of `Work.RPB.B1.jordan_separation_C`: `Circle.exp` is an open quotient
map, `v` is constant on its fibres (`Circle.exp_eq_exp` computes the fibre as `2πℤ` and `v` is
periodic by integer multiples of `2π`), so `Work.RPB.B1.exists_continuous_descend` produces a
continuous `γ` with `γ ∘ Circle.exp = e ∘ v`.  Injectivity of `γ` follows from injectivity of `v`
modulo `2π`, the derivative of the parametrisation of `γ` is `e (deriv v t) ≠ 0`, and
`Work.RPB.Port.Drive.PolarTwist.isSmoothEmbedding_of_injective_deriv_ne_zero` upgrades all this to
the smooth embedding. -/
theorem exists_smooth_embedding_descend (v : ℝ → ℂ) (hv : Work.RPB1a.IsSmoothLoop v) :
    ∃ γ : Circle → ℝ × ℝ,
      Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ ∧
      Continuous γ ∧ Function.Injective γ ∧
      (∀ t : ℝ, γ (Circle.exp t) = Complex.equivRealProdCLM (v t)) ∧
      Set.range γ = Complex.equivRealProdCLM '' Set.range v := by
  obtain ⟨hvd, hper, hinj, himm⟩ := hv
  -- The linear homeomorphism `ℂ ≃ ℝ × ℝ`.
  set e : ℂ ≃L[ℝ] ℝ × ℝ := Complex.equivRealProdCLM with he
  -- Periodicity by integer multiples of `2π`.
  have hper_z : ∀ (m : ℤ) (t : ℝ), v (t + ↑m * (2 * Real.pi)) = v t :=
    fun m t => (Function.Periodic.int_mul hper m) t
  -- `v` is constant on the fibres of `Circle.exp`.
  have hfac : (fun t : ℝ => e (v t)).FactorsThrough (⇑Circle.exp : ℝ → Circle) := by
    intro a b hab
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hab
    rw [hm]
    exact congrArg e (hper_z m b)
  have hf : Topology.IsQuotientMap (⇑Circle.exp : ℝ → Circle) :=
    IsOpenMap.isQuotientMap isLocalHomeomorph_circleExp.isOpenMap Circle.exp.continuous
      Circle.exp_surjective
  -- The descended map.
  obtain ⟨γ, hγcont, hγcomp⟩ :=
    Work.RPB.B1.exists_continuous_descend hf (e.continuous.comp hvd.continuous) hfac
  have hγ_exp : ∀ t : ℝ, γ (Circle.exp t) = e (v t) := fun t => by
    have := congrFun hγcomp t
    simpa [Function.comp_def] using this
  -- Injectivity of the descended map.
  have hγinj : Function.Injective γ := by
    intro z₁ z₂ h
    obtain ⟨t₁, rfl⟩ := Circle.exp_surjective z₁
    obtain ⟨t₂, rfl⟩ := Circle.exp_surjective z₂
    have h2 : e (v t₁) = e (v t₂) := by rw [← hγ_exp t₁, ← hγ_exp t₂]; exact h
    have h3 : v t₁ = v t₂ := e.injective h2
    obtain ⟨m, hm⟩ := hinj t₁ t₂ h3
    rw [hm]
    exact Circle.exp_eq_exp.mpr ⟨-m, by push_cast; ring⟩
  -- Smoothness of the `Circle.exp`-parametrisation.
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => γ (Circle.exp t)) := by
    have hfun : (fun t : ℝ => γ (Circle.exp t)) = fun t => e (v t) := funext hγ_exp
    rw [hfun]
    simpa [Function.comp_def] using e.contDiff.comp hvd
  -- Non-vanishing of the derivative of the parametrisation.
  have hderiv : ∀ t : ℝ, deriv (fun u : ℝ => γ (Circle.exp u)) t ≠ 0 := by
    intro t
    have hfun : (fun u : ℝ => γ (Circle.exp u)) = fun s => e (v s) := funext hγ_exp
    rw [hfun]
    have hU : HasDerivAt v (deriv v t) t :=
      (hvd.differentiable (by simp)).differentiableAt.hasDerivAt
    have hder : HasDerivAt (fun s : ℝ => e (v s)) (e (deriv v t)) t := by
      have h1 := (e : ℂ →L[ℝ] ℝ × ℝ).hasFDerivAt.comp_hasDerivAt t hU
      simpa [Function.comp_def] using h1
    rw [hder.deriv]
    intro h0
    exact himm t (e.injective (by simpa using h0))
  -- The descended curve is a smooth embedding.
  have hemb : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ :=
    Work.RPB.Port.Drive.PolarTwist.isSmoothEmbedding_of_injective_deriv_ne_zero
      γ hγcont hγinj hsmooth hderiv
  -- Its range is the image of the range of `v`.
  have hrange : Set.range γ = e '' Set.range v := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨t, rfl⟩ := Circle.exp_surjective z
      exact ⟨v t, ⟨t, rfl⟩, (hγ_exp t).symm⟩
    · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
      exact ⟨Circle.exp t, hγ_exp t⟩
  exact ⟨γ, hemb, hγcont, hγinj, hγ_exp, hrange⟩

end Work.RPB1a
