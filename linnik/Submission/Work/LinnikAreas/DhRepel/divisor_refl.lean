/-
# Reflection of the divisor of a completed `L`-function

For a non-principal primitive Dirichlet character `χ`, the completed `L`-function
`Λ = completedLFunction χ` is entire, and its zeros are symmetric under the reflection
`ρ ↦ 1 - conj ρ` of the critical strip.  This file records the precise statement needed for the
reindexing of the windowed divisor sums in `Work.LinnikAreas.DhRepel.l52Hyp_supply`, namely that
the *divisor* (i.e. the vanishing multiplicity) of `Λ` at `u` and at `1 - conj u` agree.

The mathematics: the functional equation
`Λ(χ, 1 - s) = N ^ (s - 1/2) · rootNumber χ · Λ(χ⁻¹, s)` together with the conjugation identity
`Λ(χ⁻¹, s) = conj (Λ(χ, conj s))` gives the reflection identity

`Λ(χ, 1 - w) = N ^ (w - 1/2) · rootNumber χ · conj (Λ(χ, conj w))`,

i.e. `Λ ∘ (1 - ·) = E · starComp Λ` with `E` an entire nowhere vanishing multiplier.  Since
multiplication by a nowhere vanishing holomorphic function does not change the order of vanishing,
and since `starComp` (i.e. `w ↦ conj (Λ (conj w))`) preserves the vanishing order across `conj`,
the multiplicities at `u` and at `1 - conj u` coincide.  The statements about the divisor are then
immediate from `MeromorphicOn.divisor_apply`, because `Λ` is entire.
-/
import Mathlib
import Submission.Work.LinnikAreas.DhRepel.l52Hyp_defs
import Submission.Work.A7.analyticOrderNatAt_star_symm
import Submission.Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_conj

namespace Work.LinnikAreas.DhRepel

open Complex DirichletCharacter Metric Filter
open scoped Real Topology BigOperators
open Commons.NumberTheory.DirichletCharacter (starComp)

/-- The completed `L`-function satisfies the reflection identity
`Λ(χ, 1 - w) = N ^ (w - 1/2) * rootNumber χ * conj (Λ(χ, conj w))`, i.e. the conjugated function
`starComp Λ` differs from `Λ ∘ (1 - ·)` by the nowhere vanishing entire factor
`w ↦ N ^ (w - 1/2) * rootNumber χ`. -/
lemma completedLFunction_comp_one_sub_eq_mul_starComp {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    DirichletCharacter.completedLFunction χ ∘ (fun w : ℂ => 1 - w)
      = fun w => (N : ℂ) ^ (w - 1/2) * χ.rootNumber *
          starComp (DirichletCharacter.completedLFunction χ) w := by
  funext w
  simp only [Function.comp_apply]
  rw [DirichletCharacter.IsPrimitive.completedLFunction_one_sub hχprim w]
  rw [← Commons.NumberTheory.DirichletCharacter.completedLFunction_conj_apply χ hχ w]
  rfl

/-- **Reflection of the vanishing multiplicity.**  For a non-principal primitive character `χ`
the meromorphic order of the completed `L`-function at `u` equals its order at `1 - conj u`. -/
lemma meromorphicOrderAt_completedLFunction_refl {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (u : ℂ) :
    meromorphicOrderAt (DirichletCharacter.completedLFunction χ) (1 - starRingEnd ℂ u)
      = meromorphicOrderAt (DirichletCharacter.completedLFunction χ) u := by
  set A : ℂ → ℂ := DirichletCharacter.completedLFunction χ with hA
  have hAdiff : Differentiable ℂ A := by rw [hA]; exact differentiable_completedLFunction hχ
  have hAstDiff : Differentiable ℂ (starComp A) :=
    Commons.NumberTheory.DirichletCharacter.differentiable_starComp hAdiff
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hroot : χ.rootNumber ≠ 0 := by
    intro h
    have h1 := Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one χ hχprim
    rw [h] at h1
    simp at h1
  have hEdiff : Differentiable ℂ (fun w : ℂ => (N : ℂ) ^ (w - 1/2) * χ.rootNumber) := by
    intro w
    exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hN)).mul_const _
  have hRel : A ∘ (fun w : ℂ => 1 - w)
      = fun w => (N : ℂ) ^ (w - 1/2) * χ.rootNumber * starComp A w := by
    rw [hA]
    exact completedLFunction_comp_one_sub_eq_mul_starComp χ hχ hχprim
  -- order at `1 - conj u` = order of `starComp A` at `conj u`
  have hstep1 : meromorphicOrderAt A (1 - starRingEnd ℂ u)
      = meromorphicOrderAt (starComp A) (starRingEnd ℂ u) := by
    have hc := meromorphicOrderAt_comp_of_deriv_ne_zero (𝕜 := ℂ) (E := ℂ)
      (f := A) (g := fun w : ℂ => 1 - w) (x := starRingEnd ℂ u) (by fun_prop) (by simp)
    rw [← hc, hRel]
    rw [show (fun w : ℂ => (N : ℂ) ^ (w - 1/2) * χ.rootNumber * starComp A w)
        = (fun w : ℂ => (N : ℂ) ^ (w - 1/2) * χ.rootNumber) * starComp A from rfl,
      meromorphicOrderAt_mul_of_ne_zero (hEdiff.analyticAt _) (by
        exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hN)) hroot)]
  -- order of `starComp A` at `conj u` = order of `A` at `u`
  have hstep2 : meromorphicOrderAt (starComp A) (starRingEnd ℂ u) = meromorphicOrderAt A u := by
    have hthis : analyticOrderAt (starComp A) (starRingEnd ℂ u) = analyticOrderAt A u := by
      rw [Work.A7.analyticOrderAt_starComp A (starRingEnd ℂ u), starRingEnd_self_apply]
    rw [AnalyticAt.meromorphicOrderAt_eq (hAstDiff.analyticAt _),
        AnalyticAt.meromorphicOrderAt_eq (hAdiff.analyticAt u), hthis]
  exact hstep1.trans hstep2

theorem divisor_refl {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {R₁ R₂ : ℝ} {u : ℂ} (hu : u ∈ Metric.closedBall (0 : ℂ) R₁)
    (hu' : 1 - starRingEnd ℂ u ∈ Metric.closedBall (0 : ℂ) R₂) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R₂)
        (1 - starRingEnd ℂ u) =
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R₁) u := by
  set A : ℂ → ℂ := DirichletCharacter.completedLFunction χ with hA
  have hAdiff : Differentiable ℂ A := by rw [hA]; exact differentiable_completedLFunction hχ
  have hOrder : meromorphicOrderAt A (1 - starRingEnd ℂ u) = meromorphicOrderAt A u := by
    rw [hA]
    exact meromorphicOrderAt_completedLFunction_refl χ hχ hχprim u
  have hM₂ : MeromorphicOn A (Metric.closedBall (0 : ℂ) R₂) :=
    fun z _ => (hAdiff.analyticAt z).meromorphicAt
  have hM₁ : MeromorphicOn A (Metric.closedBall (0 : ℂ) R₁) :=
    fun z _ => (hAdiff.analyticAt z).meromorphicAt
  rw [MeromorphicOn.divisor_apply hM₂ hu', MeromorphicOn.divisor_apply hM₁ hu, hOrder]

end Work.LinnikAreas.DhRepel
