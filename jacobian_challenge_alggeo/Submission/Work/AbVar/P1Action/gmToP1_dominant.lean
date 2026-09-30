/-
Area AV: the scaled `𝔾_m`-action on `ℙ¹` — dominance of the orbit map `𝔾_m ⟶ ℙ¹`, `T ↦ [T : 1]`.

The map `gmToP1 k` is the composite

  `𝔾_m = Spec k[T;T⁻¹] --Spec(chartEvalT)--> Spec (Away 𝒜 (X₁)) = D₊(X₁) --awayι--> Proj 𝒜 = ℙ¹`

where `chartEvalT k` is induced by `X₀/X₁ ↦ T` and `awayι` is the inclusion of the chart
`D₊(X₁)`.  Both factors are dominant:

* `Spec (chartEvalT k)` is dominant because `chartEvalT k` is injective (it is, up to the
  identification `Away 𝒜 (X₁) ≅ k[T₀]`, the localisation `k[T₀] → k[T₀][T₀⁻¹]`), and the
  range of `Spec` of a ring map has dense range as soon as its kernel lies in the nilradical.
* `awayι` is dominant because its range is the nonempty open chart `D₊(X₁)` of the irreducible
  scheme `ℙ¹`.

Dominance of a composite then follows from Mathlib's instance `IsDominant (f ≫ g)`.
-/
import Mathlib
import Submission.Work.AbVar.P1Action.Points
import Submission.Work.AbVar.ProjectiveLine.chart
import Submission.Work.AbVar.ProjectiveLine.isIntegral_P1
import Submission.Work.AbVar.ProjectiveLine.polyToAwaySurjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonObj MvPolynomial HomogeneousLocalization Limits
open scoped MonoidalCategory TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Work.AbVar.P1Action

section

variable (k : Type*) [Field k]

/-- The dehomogenisation `Away 𝒜 (X₁) → k[T₀]`, `X₀/X₁ ↦ T₀`, is injective: it is a left
inverse of the (surjective) map `k[T₀] → Away 𝒜 (X₁)`, `T₀ ↦ X₀/X₁`. -/
lemma gmToP1_awayToPoly_one_injective :
    Function.Injective (Work.AbVar.ProjectiveLine.awayToPoly (R := k) 1) := by
  have hsurj := Work.AbVar.ProjectiveLine.polyToAwaySurjective (R := k)
    (i := 1) (j := 0) (by decide)
  intro a b hab
  obtain ⟨p, rfl⟩ := hsurj a
  obtain ⟨q, rfl⟩ := hsurj b
  rw [Work.AbVar.ProjectiveLine.awayToPoly_polyToAway (R := k) (i := 1) (j := 0) (by decide),
      Work.AbVar.ProjectiveLine.awayToPoly_polyToAway (R := k) (i := 1) (j := 0) (by decide)] at hab
  rw [hab]

/-- `Polynomial.aeval T : k[T₀] → k[T;T⁻¹]` is injective, being the structure map of the
localisation `k[T₀][T₀⁻¹]`. -/
lemma gmToP1_aeval_T_injective : Function.Injective
    (Polynomial.aeval (R := k) (LaurentPolynomial.T 1 : Work.AbVar.P1Action.L k)) := by
  have h : Polynomial.aeval (R := k) (LaurentPolynomial.T 1 : Work.AbVar.P1Action.L k)
      = Polynomial.toLaurentAlg (R := k) := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X, Polynomial.coe_toLaurentAlg, Polynomial.toLaurent_X]
  rw [h]
  simpa using (Polynomial.toLaurent_injective (R := k))

/-- The chart evaluation `chartEvalT k : Away 𝒜 (X₁) → k[T;T⁻¹]`, `X₀/X₁ ↦ T`, is injective. -/
lemma gmToP1_chartEvalT_injective : Function.Injective (chartEvalT k) := by
  rw [show chartEvalT k
      = (Polynomial.aeval (R := k) (LaurentPolynomial.T 1 : Work.AbVar.P1Action.L k)).toRingHom.comp
        (Work.AbVar.ProjectiveLine.awayToPoly (R := k) 1) from rfl]
  rw [RingHom.coe_comp]
  exact (gmToP1_aeval_T_injective k).comp (gmToP1_awayToPoly_one_injective k)

/-- `Spec (chartEvalT k)` is dominant: its range is dense because the kernel of `chartEvalT k`
is trivial, hence contained in the nilradical of the chart ring. -/
lemma gmToP1_specMap_chartEvalT_dominant :
    IsDominant (Spec.map (CommRingCat.ofHom (chartEvalT k))) := by
  rw [isDominant_iff]
  show DenseRange (PrimeSpectrum.comap (chartEvalT k))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  rw [(RingHom.injective_iff_ker_eq_bot (chartEvalT k)).mp (gmToP1_chartEvalT_injective k)]
  exact bot_le

/-- The chart inclusion `awayι : D₊(X₁) ⟶ ℙ¹` is dominant: it is an open immersion and the
target `ℙ¹` is irreducible, so its nonempty open range is dense. -/
lemma gmToP1_chartObjHom_dominant : IsDominant (chartObjHom k 1) := by
  haveI : IrreducibleSpace (Proj (Work.AbVar.P1Grading k)) :=
    Work.AbVar.ProjectiveLine.irreducibleSpace_P1 k
  -- the generic point of `ℙ¹` lies in the chart `D₊(X₁)`, so this chart is nonempty
  have hmem : (Work.AbVar.ProjectiveLine.zeroPt k) ∈
      (↑(ProjectiveSpectrum.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1)) :
        Set (ProjectiveSpectrum (Work.AbVar.P1Grading k))) := by
    rw [ProjectiveSpectrum.mem_coe_basicOpen]
    intro h
    rw [Work.AbVar.ProjectiveLine.zeroPt_asHomogeneousIdeal] at h
    exact MvPolynomial.X_ne_zero 1 ((HomogeneousIdeal.mem_iff (I := ⊥)).mp h)
  have hdense : Dense ((Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1) :
      (Proj (Work.AbVar.P1Grading k)).Opens) : Set (Proj (Work.AbVar.P1Grading k))) :=
    IsOpen.dense (Proj.basicOpen _ _).isOpen
      ⟨(Work.AbVar.ProjectiveLine.zeroPt k : ↥(Proj (Work.AbVar.P1Grading k))), hmem⟩
  haveI : IsDominant ((Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1)).ι) :=
    Opens.isDominant_ι hdense
  -- `chartObjHom k 1` is `awayι`, which is the open chart inclusion up to an isomorphism
  change IsDominant (Proj.awayι (Work.AbVar.P1Grading k) (MvPolynomial.X 1)
    (Work.AbVar.ProjectiveLine.X_mem_stdG (R := k) 1) (by norm_num))
  rw [← Proj.basicOpenIsoSpec_inv_ι (𝒜 := Work.AbVar.P1Grading k) (f := MvPolynomial.X 1)
    (f_deg := Work.AbVar.ProjectiveLine.X_mem_stdG (R := k) 1) (hm := by norm_num)]
  infer_instance

end

theorem gmToP1_dominant (k : Type*) [Field k] :
    AlgebraicGeometry.IsDominant (Work.AbVar.P1Action.gmToP1 k).left := by
  haveI := gmToP1_specMap_chartEvalT_dominant k
  haveI := gmToP1_chartObjHom_dominant k
  show IsDominant (Spec.map (CommRingCat.ofHom (chartEvalT k)) ≫ chartObjHom k 1)
  infer_instance

end Work.AbVar.P1Action
