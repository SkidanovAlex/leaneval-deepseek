import Mathlib

/-!
# Local injectivity of a `C^∞` map at a point where the Fréchet derivative is injective

This is a standalone analytic brick: if `f : ℝ × ℝ → F` is `C^∞` at `p` (with `F` a
finite-dimensional real normed space) and the Fréchet derivative `fderiv ℝ f p` is injective, then
`f` is injective on a ball around `p`.

## Proof outline

Since the domain `ℝ × ℝ` has dimension `2` and the derivative `A := fderiv ℝ f p` is injective,
`A` has a continuous linear left inverse `g : F →L[ℝ] ℝ × ℝ` (finite dimensionality of the codomain
`F` supplies continuity of the algebraic left inverse, see
`ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional`).

The map `h := g ∘ f` is then `C^∞` at `p` and its derivative there is `g ∘ A = 1`. By the
`C^n`-form of the inverse function theorem (`ContDiffAt.hasStrictFDerivAt'` +
`HasStrictFDerivAt.eventually_left_inverse`) `h` has a local left inverse `L` near `p`. Hence,
inside a small ball, `f x = f y` implies `h x = h y`, which implies
`x = L (h x) = L (h y) = y`.
-/

namespace Work.Drive

open Set Filter Metric
open scoped Topology

theorem local_injective_of_fderiv_injective
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : ℝ × ℝ → F} {p : ℝ × ℝ}
    (hs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f p)
    (hf : HasFDerivAt f (fderiv ℝ f p) p)
    (hinj : Function.Injective (fderiv ℝ f p)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Metric.ball p ρ, ∀ y ∈ Metric.ball p ρ, f x = f y → x = y := by
  classical
  set A : (ℝ × ℝ) →L[ℝ] F := fderiv ℝ f p with hAdef
  have hAinj : Function.Injective A := hinj
  -- A continuous linear left inverse of `A`, existing by finite dimensionality of `F`.
  have hAlin : A.HasLeftInverse :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hAinj
  set g : F →L[ℝ] (ℝ × ℝ) := hAlin.leftInverse with hgdef
  have hgA : g.comp A = 1 := by
    refine ContinuousLinearMap.ext fun x => ?_
    show g (A x) = x
    rw [hgdef]
    exact hAlin.leftInverse_leftInverse x
  -- `h := g ∘ f` is `C^∞` at `p` with derivative `1`.
  have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑g ∘ f) p :=
    ContDiffAt.continuousLinearMap_comp g hs
  have hfderiv : HasFDerivAt (⇑g ∘ f) (g.comp A) p := by
    have := HasFDerivAt.comp p (ContinuousLinearMap.hasFDerivAt g) hf
    simpa [hAdef, hgdef] using this
  have hfderiv' : HasFDerivAt (⇑g ∘ f) (1 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p :=
    hfderiv.congr_fderiv hgA
  have hstr : HasStrictFDerivAt (⇑g ∘ f) (1 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p :=
    hcd.hasStrictFDerivAt' hfderiv' (by simp)
  -- The inverse function theorem gives a local left inverse of `h` near `p`.
  have hleft := hstr.eventually_left_inverse (f' := ContinuousLinearEquiv.refl ℝ (ℝ × ℝ))
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.eventually_nhds_iff.mp hleft
  refine ⟨ρ, hρpos, ?_⟩
  intro x hx y hy hxy
  have hx' := hρ hx
  have hy' := hρ hy
  have hxy' : (⇑g ∘ f) x = (⇑g ∘ f) y := congrArg (⇑g) hxy
  exact hx'.symm.trans ((congrArg _ hxy').trans hy')

end Work.Drive
