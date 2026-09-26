import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_ne

noncomputable section

open UpperHalfPlane MeasureTheory Filter
open scoped Topology Manifold

namespace Work.Asymptotics

/-! ## The level sets of the `j`-invariant are null

The proof has three steps.

1. The lift `Φ z = j (ofComplex z)` of the `j`-invariant to a function on `ℂ` is holomorphic on
   the upper half plane: `j = E₄³/Δ` is holomorphic on `ℍ` and `ofComplex` is the inverse of the
   (injective, holomorphic) inclusion `ℍ → ℂ` there.
2. A fibre of a non-constant analytic function on a preconnected set is countable: by the
   principle of isolated zeros the fibre is discrete, and a discrete subset of the second
   countable space `ℂ` is countable.
3. `j` is not constant on the imaginary axis (`jInvariantFun_imagAxis_ne`, from the cusp
   asymptotics `j(it) ≥ c₀ e^{2πt}`), so step 2 applies; the map `t ↦ i t` is injective, so the
   set of `t > 0` with `j(i t) = j τ` is countable, hence Lebesgue-null.
-/

/-- The lift `z ↦ j (ofComplex z)` of the `j`-invariant is analytic on the upper half plane. -/
private lemma analyticOnNhd_jInvariantFun_comp_ofComplex :
    AnalyticOnNhd ℂ (fun z : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im} := by
  have hMD : MDiff Work.Kernels.jInvariantFun :=
    ((ModularFormClass.holo ModularForm.E₄).pow 3).div
      (CuspFormClass.holo CuspForm.discriminant)
      (fun z => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)
  exact (UpperHalfPlane.mdifferentiable_iff.mp hMD).analyticOnNhd
    UpperHalfPlane.isOpen_upperHalfPlaneSet

/-- **Fibres of a non-constant analytic function on a preconnected set are countable.**
The principle of isolated zeros (`AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`)
makes the fibre discrete, and a discrete subset of the second countable space `ℂ` is countable
(`IsLindelof.countable_of_isDiscrete`). -/
private lemma countable_of_analyticOnNhd_level {U : Set ℂ} (hU : IsPreconnected U) {Φ : ℂ → ℂ}
    (hΦ : AnalyticOnNhd ℂ Φ U) (hne : ∀ c : ℂ, ∃ z ∈ U, Φ z ≠ c) (c : ℂ) :
    (U ∩ {z : ℂ | Φ z = c}).Countable := by
  have hsub : AnalyticOnNhd ℂ (fun z : ℂ => Φ z - c) U := hΦ.sub analyticOnNhd_const
  rcases hsub.eqOn_zero_or_eventually_ne_zero_of_preconnected hU with h0 | hne'
  · obtain ⟨z, hz, hzc⟩ := hne c
    exact absurd (sub_eq_zero.mp (h0 hz)) hzc
  · have hs : ({z : ℂ | Φ z = c} : Set ℂ)ᶜ ∈ Filter.codiscreteWithin U := by
      refine Filter.mem_of_superset hne' ?_
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
      exact fun h => hz (sub_eq_zero.mpr h)
    have hdisc : IsDiscrete ({z : ℂ | Φ z = c} ∩ U) := isDiscrete_of_codiscreteWithin hs
    have hlint : IsLindelof ({z : ℂ | Φ z = c} ∩ U) := HereditarilyLindelofSpace.isLindelof _
    rw [Set.inter_comm]
    exact hlint.countable_of_isDiscrete hdisc

/-- The level set `{z ∈ ℍ : j z = c}` of the `j`-invariant, viewed inside `ℂ`, is countable. -/
private lemma countable_level_jInvariant (c : ℂ) :
    ({z : ℂ | 0 < z.im ∧ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) = c}).Countable := by
  have hU : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hne : ∀ c' : ℂ, ∃ z ∈ {z : ℂ | 0 < z.im},
      Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) ≠ c' := by
    intro c'
    obtain ⟨t, ht, hne⟩ := jInvariantFun_imagAxis_ne c'
    refine ⟨(t : ℂ) * Complex.I, ?_, hne⟩
    simp only [Set.mem_ofPred_eq]
    have him : ((t : ℂ) * Complex.I).im = t := by simp [Complex.mul_im]
    rw [him]
    exact ht
  have h := countable_of_analyticOnNhd_level hU analyticOnNhd_jInvariantFun_comp_ofComplex hne c
  simpa only [Set.ofPred_and] using h

/-- For every `τ : ℍ` the set of `t > 0` with `j(τ) = j(i t)` is Lebesgue-null: `t ↦ j(it)` is
real-analytic on `(0,∞)` and non-constant (it is the restriction of the non-constant holomorphic
function `z ↦ j(z)` to the imaginary axis), so its fibres are discrete, hence countable.  This
certifies that the "cleanliness" hypothesis `j τ ≠ j (i t)` of
`Work.Asymptotics.Kaxis_cusp_expansion` fails only on a null set. -/
theorem jInvariant_level_null (τ : UpperHalfPlane) :
    MeasureTheory.volume {t : ℝ | 0 < t ∧ Work.Kernels.jInvariantFun τ
      = Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I))} = 0 := by
  -- The fibre of `Φ z = j (ofComplex z)` over `j τ` is countable, and `t ↦ i t` is injective.
  have hcount : ({z : ℂ | 0 < z.im ∧
      Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)
        = Work.Kernels.jInvariantFun τ}).Countable :=
    countable_level_jInvariant _
  have hsub : {t : ℝ | 0 < t ∧ Work.Kernels.jInvariantFun τ
        = Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I))}
      ⊆ (fun t : ℝ => (t : ℂ) * Complex.I) ⁻¹'
        {z : ℂ | 0 < z.im ∧ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)
          = Work.Kernels.jInvariantFun τ} := by
    intro t ht
    obtain ⟨htpos, hteq⟩ := ht
    refine ⟨?_, hteq.symm⟩
    show 0 < ((t : ℂ) * Complex.I).im
    have him : ((t : ℂ) * Complex.I).im = t := by simp [Complex.mul_im]
    rw [him]
    exact htpos
  have hinj : Function.Injective (fun t : ℝ => (t : ℂ) * Complex.I) := by
    intro a b hab
    have h := congrArg Complex.im hab
    rw [Complex.mul_im, Complex.mul_im, Complex.I_im, Complex.I_re] at h
    simpa using h
  exact ((hcount.preimage hinj).mono hsub).measure_zero MeasureTheory.volume

end Work.Asymptotics
