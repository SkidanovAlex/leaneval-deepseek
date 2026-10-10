import Mathlib
import Submission.Work.SilvermanReduction.Basic

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SilvermanReduction

/-- **The reduction map is Galois-equivariant (Silverman, AEC, VII.2.1, `σ`-invariance).**
Let `W₀` be a Weierstrass curve over a field `𝕜`, `K/𝕜` a field extension which is simultaneously
the fraction field of a discrete valuation ring `R` (the local model of a place of `K`), and let
`σ : K ≃ₐ[𝕜] K` be an automorphism of `K` over `𝕜` which
(i) *preserves the valuation* (`PreservesValuation`, automatic when the place is the unique
extension of the valuation of `𝕜`, e.g. a totally ramified place) and
(ii) *acts trivially on the residue field* (`TrivialOnResidue`, i.e. `σ x - x` lies in the maximal
ideal for integral `x`).

Then the reduction map on the points of `W₀` over `K` is `σ`-invariant:
`redPoint (σ · P) = redPoint P`.

This is the property that makes the reduction map an obstruction to the twist being trivial:
at a place where `σ` acts trivially on the residue field, `red` kills every coboundary
`σ R - R`, while `red` does not kill a point with integral, nonsingular reduction.

Proof route: case on `P`; for `P = (x,y)` use `WeierstrassCurve.Affine.Point.map_some` and
`redPoint_some_mk` with the lifts `r, s` of `x, y`; the image point `(σ x, σ y)` is integral by
`PreservesValuation`, and its reductions agree with those of `x, y` by
`residue_eq_of_trivialOnResidue` (already proved in `Basic`).  For a point of negative valuation,
both sides are `0` (`PreservesValuation` shows `σx` is of negative valuation too). -/
theorem map_redPoint {𝕜 : Type*} [Field 𝕜] {K : Type*} [Field K] [Algebra 𝕜 K] [DecidableEq K]
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K]
    (W₀ : WeierstrassCurve.Affine 𝕜) (σ : K ≃ₐ[𝕜] K)
    [hW : (W₀.baseChange K).HasGoodReduction R]
    (hσ : Work.SilvermanReduction.PreservesValuation R (σ : K →+* K))
    (hτ : Work.SilvermanReduction.TrivialOnResidue R (σ : K →+* K))
    (P : WeierstrassCurve.Affine.Point (W₀.baseChange K)) :
    Work.SilvermanReduction.redPoint R (W₀.baseChange K)
        (WeierstrassCurve.Affine.Point.map (W' := W₀) (σ : K →ₐ[𝕜] K) P)
      = Work.SilvermanReduction.redPoint R (W₀.baseChange K) P := by
  have hσ' : ∀ x, Work.SilvermanReduction.val R K (σ x) = Work.SilvermanReduction.val R K x :=
    fun x => hσ x
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← WeierstrassCurve.Affine.Point.zero_def, WeierstrassCurve.Affine.Point.map_zero,
      Work.SilvermanReduction.redPoint_zero]
  · rw [WeierstrassCurve.Affine.Point.map_some]
    simp only [AlgEquiv.coe_toAlgHom]
    by_cases hx : ∃ r : R, algebraMap R K r = x
    · obtain ⟨r, hr⟩ := hx
      have hxI : Work.SilvermanReduction.IsIntegralK R K x :=
        (Work.SilvermanReduction.IsIntegralK.iff_exists x).mpr ⟨r, hr⟩
      obtain ⟨s, hs⟩ := Work.SilvermanReduction.exists_lift_of_y (W := W₀.baseChange K) h ⟨r, hr⟩
      have hyI : Work.SilvermanReduction.IsIntegralK R K y :=
        Work.SilvermanReduction.isIntegralK_of_equation (W := W₀.baseChange K) h.1 hxI
      have hσxI : Work.SilvermanReduction.IsIntegralK R K (σ x) := by
        show Work.SilvermanReduction.val R K (σ x) ≤ 1
        rw [hσ' x]
        exact hxI
      have hσyI : Work.SilvermanReduction.IsIntegralK R K (σ y) := by
        show Work.SilvermanReduction.val R K (σ y) ≤ 1
        rw [hσ' y]
        exact hyI
      obtain ⟨r', hr'⟩ := (Work.SilvermanReduction.IsIntegralK.iff_exists (σ x)).mp hσxI
      obtain ⟨s', hs'⟩ := (Work.SilvermanReduction.IsIntegralK.iff_exists (σ y)).mp hσyI
      rw [Work.SilvermanReduction.redPoint_some_mk (R := R) _ hr' hs',
        Work.SilvermanReduction.redPoint_some_mk (R := R) h hr hs,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨Work.SilvermanReduction.residue_eq_of_trivialOnResidue R hτ hxI hr hr',
        Work.SilvermanReduction.residue_eq_of_trivialOnResidue R hτ hyI hs hs'⟩
    · have hσx : ¬ ∃ r : R, algebraMap R K r = σ x := by
        rintro ⟨r', hr'⟩
        exact hx ((Work.SilvermanReduction.IsIntegralK.iff_exists x).mp (by
          rw [Work.SilvermanReduction.IsIntegralK, ← hσ' x]
          exact (Work.SilvermanReduction.IsIntegralK.iff_exists (σ x)).mpr ⟨r', hr'⟩))
      rw [Work.SilvermanReduction.redPoint_some_eq_zero (R := R) _ hσx,
        Work.SilvermanReduction.redPoint_some_eq_zero (R := R) h hx]

end Work.SilvermanReduction
