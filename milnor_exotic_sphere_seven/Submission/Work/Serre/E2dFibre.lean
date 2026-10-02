import Mathlib
import Submission.Work.Serre.E2dEngine
import Submission.Work.StemsB.SphLoopRelPair
import Submission.Work.Serre.nonempty_homology_iso_of_isZero_relChains

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibre of the pullback and the fibre of the map

This file contains the two facts about fibres that the E2(d) induction needs:

* `Work.Serre.isZero_relChains_fibre_of_contraction` — the pair `(X, q⁻¹{z₀})` has vanishing
  relative homology when the base is contracted onto `z₀` (the general form of
  `Work.Serre.isZero_relChains_preimage_singleton`, with the ambient space `X` itself rather than
  the subtype `↥(q⁻¹univ)`);
* `Work.Serre.pbFibreHomeo` — the fibre of the projection `τ^*E → I^m` over a point `z` is
  homeomorphic to the fibre of `p` over `τ z`;
* `Work.Serre.fibre_iso_pullback` — consequently the homology of the fibres of a Serre fibration
  over the points `τ d₀`, `τ d₁` of a cube agree.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Serre

noncomputable section

/-- **The pair of the total space with the fibre over a point has vanishing relative homology**,
for a contraction of the base onto that point fixing it: the form with the ambient space `X`
itself. -/
theorem isZero_relChains_fibre_of_contraction {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (q : C(X, Z)) (hq : Work.StemsB.IsSerreFibration q) (z₀ : Z)
    (c : C(Z × unitInterval, Z)) (hc0 : ∀ z, c (z, 0) = z) (hc1 : ∀ z, c (z, 1) = z₀)
    (hcz : ∀ t, c (z₀, t) = z₀) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of X) {x : X | q x = z₀}).homology m) := by
  have h := isZero_relChains_preimage_singleton q hq z₀ c hc0 hc1 hcz m
  -- transport along the canonical homeomorphism `↥(q ⁻¹' univ) ≃ₜ X`
  have hAB : ∀ x : ↥(q ⁻¹' (Set.univ : Set Z)),
      x ∈ {y : ↥(q ⁻¹' (Set.univ : Set Z)) | (y : X) ∈ q ⁻¹' ({z₀} : Set Z)} ↔
        (Homeomorph.Set.univ X) x ∈ {y : X | q y = z₀} := by
    intro x
    show q (x : X) ∈ ({z₀} : Set Z) ↔ q ((x : ↥(Set.univ : Set X)) : X) = z₀
    simp
  obtain ⟨e⟩ := Work.StemsB.nonempty_relChains_homology_iso_of_homeomorph
    (X := TopCat.of ↥(q ⁻¹' (Set.univ : Set Z))) (Y := TopCat.of X)
    (Homeomorph.Set.univ X)
    {y : ↥(q ⁻¹' (Set.univ : Set Z)) | (y : X) ∈ q ⁻¹' ({z₀} : Set Z)}
    {y : X | q y = z₀} hAB m
  exact IsZero.of_iso h e.symm

/-- **The fibre of the projection `τ^*E → I^m` over a point `z` is the fibre of `p` over `τ z`.** -/
def pbFibreHomeo {E B : Type} [TopologicalSpace E] [TopologicalSpace B] {m : ℕ} (p : C(E, B))
    (τ : C(Work.Stems.Cubical.IC m, B)) (z : Work.Stems.Cubical.IC m) :
    ↥{x : Work.StemsB.Pullback p τ | Work.StemsB.pullbackSnd p τ x = z} ≃ₜ
      Work.StemsB.fibre p (τ z) where
  toFun y := ⟨(y.1 : Work.StemsB.Pullback p τ).1.1, by
    have h1 : p ((y.1 : Work.StemsB.Pullback p τ).1.1)
        = τ ((y.1 : Work.StemsB.Pullback p τ).1.2) := (y.1 : Work.StemsB.Pullback p τ).2
    have h2 : (y.1 : Work.StemsB.Pullback p τ).1.2 = z := y.2
    rw [h2] at h1
    exact h1⟩
  invFun e := ⟨⟨(e.1, z), e.2⟩, rfl⟩
  left_inv y := by
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    refine Prod.ext rfl ?_
    exact (y.2).symm
  right_inv e := by
    refine Subtype.ext rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    fun_prop

/-- **The homology of the fibre of a Serre fibration over points of a cube is independent of the
point.** -/
theorem fibre_iso_pullback (m : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(Work.Stems.Cubical.IC m, B)) (d₀ d₁ : Work.Stems.Cubical.IC m) (k : ℕ) :
    Nonempty (((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p (τ d₁)))).homology k) ≅
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p (τ d₀)))).homology k)) := by
  -- the two vanishings, from the contraction of the cube onto each point
  have h₁ : ∀ j : ℕ, IsZero ((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
      {x : Work.StemsB.Pullback p τ | Work.StemsB.pullbackSnd p τ x = d₁}).homology j) := fun j =>
    isZero_relChains_fibre_of_contraction (Work.StemsB.pullbackSnd p τ)
      (fun i => Work.StemsB.hasHLP_pullback p τ (hp i)) d₁ (cubeContraction m d₁)
      (cubeContraction_zero m d₁) (cubeContraction_one m d₁) (cubeContraction_self m d₁) j
  have h₀ : ∀ j : ℕ, IsZero ((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
      {x : Work.StemsB.Pullback p τ | Work.StemsB.pullbackSnd p τ x = d₀}).homology j) := fun j =>
    isZero_relChains_fibre_of_contraction (Work.StemsB.pullbackSnd p τ)
      (fun i => Work.StemsB.hasHLP_pullback p τ (hp i)) d₀ (cubeContraction m d₀)
      (cubeContraction_zero m d₀) (cubeContraction_one m d₀) (cubeContraction_self m d₀) j
  -- the isomorphism of the two fibres of the projection
  obtain ⟨e⟩ := nonempty_homology_iso_of_isZero_relChains (Y := TopCat.of (Work.StemsB.Pullback p τ))
    {x : Work.StemsB.Pullback p τ | Work.StemsB.pullbackSnd p τ x = d₁}
    {x : Work.StemsB.Pullback p τ | Work.StemsB.pullbackSnd p τ x = d₀} h₁ h₀ k
  -- transport to the fibres of `p`
  have e₁ : Nonempty (((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥{x : Work.StemsB.Pullback p τ | Work.StemsB.pullbackSnd p τ x = d₁})).homology k) ≅
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p (τ d₁)))).homology k)) :=
    ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
        (TopCat.isoOfHomeo (pbFibreHomeo p τ d₁)))⟩
  have e₀ : Nonempty (((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥{x : Work.StemsB.Pullback p τ | Work.StemsB.pullbackSnd p τ x = d₀})).homology k) ≅
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p (τ d₀)))).homology k)) :=
    ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
        (TopCat.isoOfHomeo (pbFibreHomeo p τ d₀)))⟩
  obtain ⟨i₁⟩ := e₁
  obtain ⟨i₀⟩ := e₀
  exact ⟨i₁.symm ≪≫ e ≪≫ i₀⟩

end

end Work.Serre
