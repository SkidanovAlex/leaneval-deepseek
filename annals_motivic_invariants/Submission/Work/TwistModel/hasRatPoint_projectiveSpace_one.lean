/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TwistModel
-/
import Mathlib
import Submission.Work.TwistModel.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℙ¹` has a rational point: `HasRatPoint 𝕜 (ℙ¹_𝕜)`

`Work.Arithmetic.HasRatPoint 𝕜 C` (`Submission/Work/Arithmetic/Defs.lean`) is the assertion that
the structure morphism `C ⟶ Spec 𝕜` has a section, i.e. that `C(𝕜) ≠ ∅` in the classical sense.

Here we discharge it for the projective line
`Work.PointlessIndexFive.projectiveSpace 𝕜 1 = Proj 𝕜[X₀,X₁]` (`Work.PointlessIndexFive.Model`):
the point `[1 : 0]` is a `𝕜`-rational point, because the chart `D₊(X₀)` is the affine line
`Spec 𝕜[X₁/X₀]` (`Work.Twist.chartPsi`, the chart isomorphism
`Work.Twist.away_chart_mvPolynomial`) and `Spec 𝕜[X₁/X₀] ⟶ Spec 𝕜` has the section
`X₁/X₀ ↦ 0`.

This is the *model-layer* complement of `C(𝕜) = ∅`: unlike the pointless quintic twists, `ℙ¹` does
carry a rational point, and the descent bridges of `Work.TwistModel.Defs` are therefore satisfied
trivially for it.  (It is also what tells us that the `C(𝕜) = ∅` configuration of the paper cannot
be met by the projective model itself.)

## What is proved

* `chartPsi_fromZeroRingHom` — on the *constants* `𝒜 0 ⊆ A⁰_{X₀}` (with `𝒜` the standard grading
  of `𝕜[X₀,…,X₁]`) the chart map `chartPsi` is the constant-coefficient map `C ∘ constantCoeff`;
* `hasRatPoint_projectiveSpace_one` — `HasRatPoint 𝕜 (ℙ¹_𝕜)`.

## Route of the main proof

Write `𝒜 = homogeneousSubmodule (Fin 2) 𝕜`, `f = X₀ ∈ 𝒜 1`, and let
`eco : ↥(𝒜 0) ≃+* 𝕜` be `Work.PointlessIndexFive.zeroComponentEquiv 𝕜 1`, so that
`C (eco c) = c` for `c ∈ ↥(𝒜 0)` (that is how `ℙ¹` is put over `Spec 𝕜`).

* The chart ring `Away 𝒜 f = A⁰_{X₀}` comes with the open immersion
  `Proj.awayι 𝒜 f hf hpos : Spec (Away 𝒜 f) ⟶ Proj 𝒜`, whose composite with the structure
  morphism is `Spec.map (ofHom (fromZeroRingHom 𝒜 (powers f)))` (`Proj.awayι_toSpecZero`).
* The dehomogenised evaluation `φ₀ = eco.symm ∘ constantCoeff ∘ chartPsi : Away 𝒜 f →+* ↥(𝒜 0)`
  is `(𝒜 0)`-linear: `φ₀.comp (fromZeroRingHom 𝒜 (powers f)) = RingHom.id ↥(𝒜 0)`
  (`chartPsi_fromZeroRingHom` computes `chartPsi` on the constants).  Hence
  `p' = Spec.map (ofHom φ₀) ≫ awayι` is a section of `Proj.toSpecZero 𝒜`.
* Pushing this section forward along the isomorphism `Spec.map eco.toCommRingCatIso.hom` and
  cancelling `Spec.map eco.toCommRingCatIso.inv` against it gives the section of
  `projectiveSpaceToSpec 𝕜 1`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

namespace Work.TwistModel

noncomputable section

/-- **The chart map on the constants.**  The degree-zero part `𝒜 0` of `𝕜[X₀,…,X₁]` consists of
constants, and the chart isomorphism `chartPsi` (`Work.Twist.away_chart_mvPolynomial`) of the
affine chart `D₊(X₀)` of `ℙ¹` carries the constant `a` to the constant polynomial
`C (constantCoeff a)`: the localised algebra map `Localization.awayLift (chartDhom) X₀` sends a
degree-zero fraction `a / 1` to `chartDhom a = C (constantCoeff a)`. -/
lemma chartPsi_fromZeroRingHom (𝕜 : Type) [Field 𝕜]
    (a : ↥(MvPolynomial.homogeneousSubmodule (Fin (1+1)) 𝕜 0)) :
    Work.Twist.chartPsi 𝕜 1 (fromZeroRingHom (MvPolynomial.homogeneousSubmodule (Fin (1+1)) 𝕜)
        (Submonoid.powers (MvPolynomial.X (0 : Fin (1+1)))) a)
      = MvPolynomial.C (MvPolynomial.constantCoeff (a : MvPolynomial (Fin (1+1)) 𝕜)) := by
  -- `fromZeroRingHom a` is the fraction `a / X₀ ^ 0`, on which `chartPsi` is `chartDhom`:
  have hfrom : fromZeroRingHom (MvPolynomial.homogeneousSubmodule (Fin (1+1)) 𝕜)
        (Submonoid.powers (MvPolynomial.X (0 : Fin (1+1)))) a
      = Away.mk (MvPolynomial.homogeneousSubmodule (Fin (1+1)) 𝕜)
          (Work.Twist.X0_mem_stdGrading 𝕜 1) 0 (a : MvPolynomial (Fin (1+1)) 𝕜)
          (by simpa using a.2) := rfl
  rw [hfrom, Work.Twist.chartPsi_awayMk]
  -- a degree-zero polynomial is a constant:
  have htd : (a : MvPolynomial (Fin (1+1)) 𝕜).totalDegree = 0 := by
    rw [MvPolynomial.totalDegree_zero_iff_isHomogeneous]
    exact a.2
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at htd
  rw [htd, MvPolynomial.constantCoeff_C]
  -- `chartDhom` is a `𝕜`-algebra map, so it fixes constants:
  simp [Work.Twist.chartDhom]

/-- **`ℙ¹_𝕜` has a `𝕜`-rational point** — the point `[1 : 0]`.

The structure morphism of `ℙ¹ = Proj 𝕜[X₀,X₁]` is `Proj.toSpecZero` followed by the spectrum of
the identification of the constants with `𝕜`; we exhibit a section, built from the affine chart
`D₊(X₀) ≅ Spec 𝕜[X₁/X₀]` and the point `X₁/X₀ = 0` of that affine line. -/
theorem hasRatPoint_projectiveSpace_one (𝕜 : Type) [Field 𝕜] :
    Work.Arithmetic.HasRatPoint 𝕜 (Work.PointlessIndexFive.projectiveSpace 𝕜 1) := by
  -- the standard grading of `𝕜[X₀,X₁]` and the chart variable `X₀ ∈ 𝒜 1`
  let 𝒜 : ℕ → Submodule 𝕜 (MvPolynomial (Fin (1+1)) 𝕜) :=
    MvPolynomial.homogeneousSubmodule (Fin (1+1)) 𝕜
  let f : MvPolynomial (Fin (1+1)) 𝕜 := MvPolynomial.X 0
  have hf : f ∈ 𝒜 1 := Work.Twist.X0_mem_stdGrading 𝕜 1
  have hpos : 0 < (1:ℕ) := one_pos
  -- the identification `↥(𝒜 0) ≃+* 𝕜` of the constants with `𝕜`, characterised by `C (eco c) = c`
  let eco : ↥(𝒜 0) ≃+* 𝕜 := Work.PointlessIndexFive.zeroComponentEquiv 𝕜 1
  have heco : ∀ p : ↥(𝒜 0), MvPolynomial.C (eco p) = (p : MvPolynomial (Fin (1+1)) 𝕜) :=
    (Work.PointlessIndexFive.exists_zeroComponentRingEquiv 𝕜 (Fin (1+1))).choose_spec
  -- the `↥(𝒜 0)`-linear dehomogenised evaluation `X₁/X₀ ↦ 0` on the chart ring
  let φ₀ : Away 𝒜 f →+* ↥(𝒜 0) := eco.symm.toRingHom.comp
      ((MvPolynomial.constantCoeff (σ := Fin 1) (R := 𝕜)).comp (Work.Twist.chartPsi 𝕜 1))
  -- `φ₀` is `↥(𝒜 0)`-linear, i.e. sends the constants `𝒜 0 ⊆ A⁰_{X₀}` to themselves
  have hφ₀ : φ₀.comp (fromZeroRingHom 𝒜 (Submonoid.powers f)) = RingHom.id ↥(𝒜 0) := by
    apply RingHom.ext
    intro a
    show eco.symm (MvPolynomial.constantCoeff (Work.Twist.chartPsi 𝕜 1
      (fromZeroRingHom 𝒜 (Submonoid.powers f) a))) = a
    rw [show Work.Twist.chartPsi 𝕜 1 (fromZeroRingHom 𝒜 (Submonoid.powers f) a)
        = MvPolynomial.C (MvPolynomial.constantCoeff (a : MvPolynomial (Fin (1+1)) 𝕜)) from
      chartPsi_fromZeroRingHom 𝕜 a]
    rw [MvPolynomial.constantCoeff_C]
    -- `eco a` is that same constant coefficient, because `C (eco a) = a`
    have h : eco a = MvPolynomial.constantCoeff (a : MvPolynomial (Fin (1+1)) 𝕜) := by
      have := congrArg MvPolynomial.constantCoeff (heco a); simpa using this
    rw [← h]
    exact eco.symm_apply_apply a
  -- the point of the chart, as a section of the structure morphism of `Proj 𝒜`
  let p' : Spec (CommRingCat.of ↥(𝒜 0)) ⟶ Proj 𝒜 :=
    Spec.map (CommRingCat.ofHom φ₀) ≫ Proj.awayι 𝒜 f hf hpos
  have hp' : p' ≫ Proj.toSpecZero 𝒜 = 𝟙 (Spec (CommRingCat.of ↥(𝒜 0))) := by
    show (Spec.map (CommRingCat.ofHom φ₀) ≫ Proj.awayι 𝒜 f hf hpos) ≫ Proj.toSpecZero 𝒜
      = 𝟙 (Spec (CommRingCat.of ↥(𝒜 0)))
    rw [Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      hφ₀, CommRingCat.ofHom_id, Spec.map_id]
  have hp1 : (Spec.map eco.toCommRingCatIso.hom ≫ p') ≫ Proj.toSpecZero 𝒜
      = Spec.map eco.toCommRingCatIso.hom := by
    rw [Category.assoc, hp', Category.comp_id]
  have hp2 : Spec.map eco.toCommRingCatIso.hom ≫ Spec.map eco.toCommRingCatIso.inv
      = 𝟙 (Spec (CommRingCat.of 𝕜)) := by
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  have hp : (Spec.map eco.toCommRingCatIso.hom ≫ p') ≫ Proj.toSpecZero 𝒜
      ≫ Spec.map eco.toCommRingCatIso.inv = 𝟙 (Spec (CommRingCat.of 𝕜)) := by
    rw [← Category.assoc, hp1, hp2]
  refine ⟨Spec.map eco.toCommRingCatIso.hom ≫ p', ?_⟩
  change (Spec.map eco.toCommRingCatIso.hom ≫ p') ≫ Proj.toSpecZero 𝒜
      ≫ Spec.map eco.toCommRingCatIso.inv = 𝟙 (Spec (CommRingCat.of 𝕜))
  exact hp

end

end Work.TwistModel
