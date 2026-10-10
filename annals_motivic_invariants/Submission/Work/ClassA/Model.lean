/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.ClassA
-/
import Submission.Work.SilvermanReduction.All
import Submission.Work.PointlessTwist.All

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The class-(a) reduction model: the two properties of a place that the reduction map needs

`Work.SilvermanReduction.map_redPoint` proves that the reduction map on the points of a Weierstrass
curve at a discrete valuation ring `R` is compatible with an automorphism `σ` of the fraction field
provided `σ` *preserves the valuation* (`PreservesValuation`, phrased with the `ℤᵐ⁰`-valued
valuation `val R K`) and *acts trivially on the residue field* (`TrivialOnResidue`, phrased with
`val`).

For the concrete place of class (a) — the local ring `R = (𝒪_F)_𝔭` of the cyclotomic quintic field
`F ⊂ ℚ(ζ₂₅)` at the (unique) prime `𝔭` above `5` — the two properties are naturally proved in the
*ring-theoretic* form below, without any mention of the valuation map:

* `ModelPreserves R K σ` — the elements of `K` that lift to the model `R` are exactly those that
  stay liftable after applying `σ` (`σ(R) = R` as a subring of `K`);
* `ModelResidueTrivial R K σ` — `σ` acts trivially on the residue field of the model: a lift of
  `σ x` has the same residue as a lift of `x`, for integral `x`.

This file shows that these two properties suffice for the `σ`-invariance of the reduction map
(`redPoint_map_of_model`), and hence produce the place datum `Work.PointlessTwist.HasReductionPlace`
and the class-(a) obstruction `Work.PointlessTwist.PointlessOf` exactly as
`Work.SilvermanReduction.hasReductionPlace_of_localModelData` does from `LocalModelData`.

## Main results

* `redPoint_map_of_model` — the reduction map is `σ`-invariant under the two model properties.
* `hasReductionPlace_of_model` — the place datum `Work.PointlessTwist.HasReductionPlace D`.
* `pointlessOf_of_model` — `Work.PointlessTwist.PointlessOf C₅ L` at the paper's data.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.ClassA

noncomputable section

/-! ## 1. The two model properties -/

/-- **`σ` preserves the model.**  The elements of `K` that are integral at the discrete valuation
ring `R` (i.e. that lift to `R`) are exactly those that stay integral under `σ`.  This is the
ring-theoretic form of `σ(R) = R`. -/
def ModelPreserves {K : Type*} [Field K] (R : Type*) [CommRing R] [Algebra R K]
    (σ : K → K) : Prop :=
  ∀ x : K, (∃ r : R, algebraMap R K r = x) ↔ ∃ r : R, algebraMap R K r = σ x

/-- **`σ` acts trivially on the residue field of the model.**  If `r'` is a lift of `σ` applied to
the image of `r`, then `r` and `r'` have the same residue in `R ⧸ 𝔪`. -/
def ModelResidueTrivial {K : Type*} [Field K] (R : Type*) [CommRing R] [IsLocalRing R]
    [Algebra R K] (σ : K → K) : Prop :=
  ∀ r r' : R, algebraMap R K r' = σ (algebraMap R K r) → residue R r' = residue R r

/-! ## 2. The reduction map is `σ`-invariant -/

section Invariance

variable {𝕜 K : Type*} [Field 𝕜] [Field K] [Algebra 𝕜 K] [DecidableEq K]
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]
variable {W₀ : WeierstrassCurve.Affine 𝕜}

/-- **The reduction map is `σ`-invariant from the two model properties.**
This is `Work.SilvermanReduction.map_redPoint` with the valuation-theoretic hypotheses
`PreservesValuation`/`TrivialOnResidue` replaced by the ring-theoretic `ModelPreserves` and
`ModelResidueTrivial`, which is the form in which the concrete place of the cyclotomic quintic
field is verified. -/
theorem redPoint_map_of_model (σ : K →ₐ[𝕜] K) [hW : (W₀.baseChange K).HasGoodReduction R]
    (hpres : ModelPreserves R (⇑σ))
    (hres : ModelResidueTrivial R (⇑σ))
    (P : WeierstrassCurve.Affine.Point (W₀.baseChange K)) :
    Work.SilvermanReduction.redPoint R (W₀.baseChange K)
        (WeierstrassCurve.Affine.Point.map (W' := W₀) σ P)
      = Work.SilvermanReduction.redPoint R (W₀.baseChange K) P := by
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← WeierstrassCurve.Affine.Point.zero_def, WeierstrassCurve.Affine.Point.map_zero,
      Work.SilvermanReduction.redPoint_zero]
  · rw [WeierstrassCurve.Affine.Point.map_some]
    by_cases hx : ∃ r : R, algebraMap R K r = x
    · obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ :=
        Work.SilvermanReduction.exists_lift_of_y (W := W₀.baseChange K) h ⟨r, hr⟩
      obtain ⟨r', hr'⟩ := (hpres x).mp ⟨r, hr⟩
      obtain ⟨s', hs'⟩ := (hpres y).mp ⟨s, hs⟩
      rw [Work.SilvermanReduction.redPoint_some_mk (R := R) _ hr' hs',
        Work.SilvermanReduction.redPoint_some_mk (R := R) h hr hs,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hres r r' (by rw [hr]; exact hr'), hres s s' (by rw [hs]; exact hs')⟩
    · have hσx : ¬ ∃ r : R, algebraMap R K r = σ x := fun h' => hx ((hpres x).mpr h')
      rw [Work.SilvermanReduction.redPoint_some_eq_zero (R := R) _ hσx,
        Work.SilvermanReduction.redPoint_some_eq_zero (R := R) h hx]

end Invariance

/-! ## 3. The place datum and the class-(a) obstruction -/

section Datum

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

/-- **The place datum from the two model properties.**  A discrete valuation ring `R` inside the
top field of `D` with good reduction of `D.E`, on which `σ = D.ext.gen` acts by `ModelPreserves`
and `ModelResidueTrivial`, and at which the marker `D.PL` reduces non-trivially, gives
`Work.PointlessTwist.HasReductionPlace D`. -/
theorem hasReductionPlace_of_model (D : Work.PointlessTwist.QuinticTwist 𝕜)
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R D.ext.L] [IsFractionRing R D.ext.L] [DecidableEq (ResidueField R)]
    [hW : (D.E.baseChange D.ext.L).HasGoodReduction R]
    (hpres : ModelPreserves R ⇑(D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L))
    (hres : ModelResidueTrivial R ⇑(D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L))
    (hPL : Work.SilvermanReduction.redPoint R (D.E.baseChange D.ext.L) D.PL ≠ 0) :
    Work.PointlessTwist.HasReductionPlace D := by
  refine ⟨{ G := WeierstrassCurve.Affine.Point ((D.E.baseChange D.ext.L).reduction R)
            addCommGroup := inferInstance
            red := Work.SilvermanReduction.redPointAddMonoidHom R
            red_galMap := ?_
            red_PL_ne_zero := ?_ }⟩
  · intro P
    exact redPoint_map_of_model (𝕜 := 𝕜) (R := R) (W₀ := D.E)
      (D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L) hpres hres P
  · simpa using hPL

/-- **The class-(a) obstruction from the two model properties**, at the paper's data. -/
theorem pointlessOf_of_model (C₅ : Work.PointlessTwist.FiveTorsionCurve 𝕜)
    (L : Work.PointlessTwist.CyclicExtension 𝕜 5)
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R (Work.PointlessTwist.twistOf C₅ L).ext.L]
    [IsFractionRing R (Work.PointlessTwist.twistOf C₅ L).ext.L]
    [DecidableEq (ResidueField R)]
    [hW : ((Work.PointlessTwist.twistOf C₅ L).E.baseChange
      (Work.PointlessTwist.twistOf C₅ L).ext.L).HasGoodReduction R]
    (hpres : ModelPreserves R ⇑((Work.PointlessTwist.twistOf C₅ L).ext.gen :
      (Work.PointlessTwist.twistOf C₅ L).ext.L →ₐ[𝕜]
        (Work.PointlessTwist.twistOf C₅ L).ext.L))
    (hres : ModelResidueTrivial R ⇑((Work.PointlessTwist.twistOf C₅ L).ext.gen :
      (Work.PointlessTwist.twistOf C₅ L).ext.L →ₐ[𝕜]
        (Work.PointlessTwist.twistOf C₅ L).ext.L))
    (hPL : Work.SilvermanReduction.redPoint R ((Work.PointlessTwist.twistOf C₅ L).E.baseChange
      (Work.PointlessTwist.twistOf C₅ L).ext.L)
      (Work.PointlessTwist.twistOf C₅ L).PL ≠ 0) :
    Work.PointlessTwist.PointlessOf C₅ L :=
  Work.PointlessTwist.pointlessOf_of_hasReductionPlace C₅ L
    (hasReductionPlace_of_model (Work.PointlessTwist.twistOf C₅ L) R hpres hres hPL)

end Datum

end

end Work.ClassA
