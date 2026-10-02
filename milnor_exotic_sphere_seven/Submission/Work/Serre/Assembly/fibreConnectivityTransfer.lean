import Mathlib
import Submission.Work.Serre.serreFibration_fibre_homology_iso
import Submission.Work.Cohomology.epsilonNaturality

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Transfer of the connectivity of the fibres of a Serre fibration along a path

For a Serre fibration `q : X → B`, a path `γ : I → B` from `b₀` to `b₁` and a natural number `f`,
the "connectivity data" of the fibre over `b₀` transfers to the fibre over `b₁`:

* the reduced homology `H_j(q⁻¹{b₀}; ℤ)` vanishes for `0 < j < f` (this is the
  `(f-1)`-connectivity of the fibre), and
* the augmentation `H₀(q⁻¹{b₀}; ℤ) ⟶ ℤ` is an isomorphism (`q⁻¹{b₀}` is path connected).

This is the statement that the connectivity of the fibre of a fibration is independent of the
chosen base point, which is what makes the Serre exact sequence of a fibration (and its
spectral-sequence consequences) well posed without choosing a base point.

## The route

The homology part is immediate from `Work.Serre.serreFibration_fibre_homology_iso`: the two fibres
have isomorphic homology in every degree, and `IsZero` is an isomorphism invariant.

For the degree-`0` augmentation the abstract isomorphism of `H₀` is not enough: the augmentation
is not determined by the isomorphism class of `H₀` alone.  We use instead the fact that the
augmentation is *natural* (`Work.Cohomology.epsilonNaturality`):

* if `f : X ⟶ Y` is a continuous map inducing an isomorphism on `H₀`, then `ε_X = H₀(f) ≫ ε_Y`,
  so `IsIso ε_X ↔ IsIso ε_Y` (`isIso_epsilon_iff_of_isIso_homologyMap`);
* a homeomorphism induces an isomorphism on `H₀` (`isIso_epsilon_iff_of_homeo`).

Now put the two fibres of `q` at the two ends of the pullback `P = I¹ ×_B X` of `q` along
`γ` (viewed through the standard identification `I¹ ≅ I`).  The fibres `F₀`, `F₁` of the pullback
over the two vertices are homeomorphic to `q⁻¹(γ 0)` and `q⁻¹(γ 1)` (`Work.Serre.pbFibreHomeo`),
and each inclusion `F_i ↪ P` induces an isomorphism on homology
(`Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains`, from the vanishing of the relative
homology of the pair `(P, F_i)`, which follows from the contractibility of the base `I¹`,
`Work.Serre.isZero_relChains_fibre_of_contraction`).  Chasing the four implications gives the
result.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.Serre.Assembly

noncomputable section

/-! ## Naturality of the augmentation -/

/-- **The degree-`0` augmentation is an isomorphism on one side of a homology isomorphism.**
If `f : X ⟶ Y` induces an isomorphism on `H₀(-;ℤ)`, then the augmentation of `X` is an isomorphism
if and only if the augmentation of `Y` is: `ε_X = H₀(f) ≫ ε_Y` by naturality of `ε`. -/
private theorem isIso_epsilon_iff_of_isIso_homologyMap {X Y : TopCat} (f : X ⟶ Y)
    (hf : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) 0)) :
    IsIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)) ↔
    IsIso (TopCat.singularHomology₀ε Y (ModuleCat.of ℤ ℤ)) := by
  have hnat := Work.Cohomology.epsilonNaturality X Y f
  constructor
  · intro hX
    haveI hc : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) 0
        ≫ TopCat.singularHomology₀ε Y (ModuleCat.of ℤ ℤ)) := by
      rw [hnat]; exact hX
    exact IsIso.of_isIso_comp_left
      (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) 0)
      (TopCat.singularHomology₀ε Y (ModuleCat.of ℤ ℤ))
  · intro hY
    have hcomp : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) 0
        ≫ TopCat.singularHomology₀ε Y (ModuleCat.of ℤ ℤ)) := IsIso.comp_isIso' hf hY
    exact hnat ▸ hcomp

/-- **The augmentation is invariant under homeomorphism.**  A homeomorphism `e : X ≃ₜ Y` induces
an isomorphism of `H₀` (it is an isomorphism of spaces), so the previous lemma applies. -/
private theorem isIso_epsilon_iff_of_homeo {X Y : TopCat} (e : ↑X ≃ₜ ↑Y) :
    IsIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)) ↔
    IsIso (TopCat.singularHomology₀ε Y (ModuleCat.of ℤ ℤ)) :=
  isIso_epsilon_iff_of_isIso_homologyMap (TopCat.isoOfHomeo e).hom inferInstance

/-! ## The interval as a cube -/

/-- The path `γ`, viewed as a map on the `1`-cube `I¹ ≅ I`. -/
private abbrev pathCube {B : Type} [TopologicalSpace B] (γ : C(unitInterval, B)) :
    C(Work.Stems.Cubical.IC 1, B) :=
  γ.comp Work.Stems.Cubical.icOneToUnit

/-- The point `0` of the `1`-cube. -/
private abbrev cubeZero : Work.Stems.Cubical.IC 1 := Work.Stems.Cubical.icOnePt 0

/-- The point `1` of the `1`-cube. -/
private abbrev cubeOne : Work.Stems.Cubical.IC 1 := Work.Stems.Cubical.icOnePt 1

private theorem pathCube_cubeZero {B : Type} [TopologicalSpace B] (γ : C(unitInterval, B)) :
    pathCube γ cubeZero = γ 0 := rfl

private theorem pathCube_cubeOne {B : Type} [TopologicalSpace B] (γ : C(unitInterval, B)) :
    pathCube γ cubeOne = γ 1 := rfl

/-! ## The transfer -/

/-- **The augmentation of the fibre is independent of the base point along a path.** -/
private theorem isIso_epsilon_fibre_of_path {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q) (γ : C(unitInterval, B))
    (h0 : IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q (γ 0)))
      (ModuleCat.of ℤ ℤ))) :
    IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q (γ 1)))
      (ModuleCat.of ℤ ℤ)) := by
  let τ := pathCube γ
  let d₀ := cubeZero
  let d₁ := cubeOne
  let P : TopCat := TopCat.of (Work.StemsB.Pullback q τ)
  let A₀ : Set P := {x : Work.StemsB.Pullback q τ | Work.StemsB.pullbackSnd q τ x = d₀}
  let A₁ : Set P := {x : Work.StemsB.Pullback q τ | Work.StemsB.pullbackSnd q τ x = d₁}
  haveI hqP : Work.StemsB.IsSerreFibration (Work.StemsB.pullbackSnd q τ) :=
    fun i => Work.StemsB.hasHLP_pullback q τ (hq i)
  -- the relative homology of the pair `(P, F_i)` vanishes, the base `I¹` being contracted on `dᵢ`
  have hv₀ : ∀ m, IsZero ((Work.Cohomology.relChains P A₀).homology m) := fun m =>
    Work.Serre.isZero_relChains_fibre_of_contraction (Work.StemsB.pullbackSnd q τ) hqP d₀
      (Work.Serre.cubeContraction 1 d₀) (fun u => Work.Serre.cubeContraction_zero 1 d₀ u)
      (fun u => Work.Serre.cubeContraction_one 1 d₀ u)
      (Work.Serre.cubeContraction_self 1 d₀) m
  have hv₁ : ∀ m, IsZero ((Work.Cohomology.relChains P A₁).homology m) := fun m =>
    Work.Serre.isZero_relChains_fibre_of_contraction (Work.StemsB.pullbackSnd q τ) hqP d₁
      (Work.Serre.cubeContraction 1 d₁) (fun u => Work.Serre.cubeContraction_zero 1 d₁ u)
      (fun u => Work.Serre.cubeContraction_one 1 d₁ u)
      (Work.Serre.cubeContraction_self 1 d₁) m
  -- hence both inclusions induce an isomorphism on `H₀`
  haveI hi₀ : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains P A₀) 0) :=
    Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains (Y := P) A₀ hv₀ 0
  haveI hi₁ : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains P A₁) 0) :=
    Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains (Y := P) A₁ hv₁ 0
  -- the four comparison steps
  have e₀ : IsIso (TopCat.singularHomology₀ε (TopCat.of ↥A₀) (ModuleCat.of ℤ ℤ)) ↔
      IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q (τ d₀)))
        (ModuleCat.of ℤ ℤ)) :=
    isIso_epsilon_iff_of_homeo (Work.Serre.pbFibreHomeo q τ d₀)
  have i₀ : IsIso (TopCat.singularHomology₀ε (TopCat.of ↥A₀) (ModuleCat.of ℤ ℤ)) ↔
      IsIso (TopCat.singularHomology₀ε P (ModuleCat.of ℤ ℤ)) :=
    isIso_epsilon_iff_of_isIso_homologyMap (Work.Cohomology.subtypeIncl P A₀) hi₀
  have i₁ : IsIso (TopCat.singularHomology₀ε (TopCat.of ↥A₁) (ModuleCat.of ℤ ℤ)) ↔
      IsIso (TopCat.singularHomology₀ε P (ModuleCat.of ℤ ℤ)) :=
    isIso_epsilon_iff_of_isIso_homologyMap (Work.Cohomology.subtypeIncl P A₁) hi₁
  have e₁ : IsIso (TopCat.singularHomology₀ε (TopCat.of ↥A₁) (ModuleCat.of ℤ ℤ)) ↔
      IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q (τ d₁)))
        (ModuleCat.of ℤ ℤ)) :=
    isIso_epsilon_iff_of_homeo (Work.Serre.pbFibreHomeo q τ d₁)
  exact e₁.mp (i₁.mpr (i₀.mp (e₀.mpr h0)))

/-! ## The target -/

theorem fibreConnectivityTransfer {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q) (f : ℕ) (b₀ b₁ : B)
    (γ : C(unitInterval, B)) (hγ0 : γ 0 = b₀) (hγ1 : γ 1 = b₁)
    (hfib : ∀ j : ℕ, 0 < j → j < f →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre q b₀))).homology j))
    (h0 : CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q b₀))
      (ModuleCat.of ℤ ℤ))) :
    (∀ j : ℕ, 0 < j → j < f →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre q b₁))).homology j)) ∧
    CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q b₁))
      (ModuleCat.of ℤ ℤ)) := by
  constructor
  · -- homology in intermediate degrees: transport the isomorphism of
    -- `Work.Serre.serreFibration_fibre_homology_iso` through `IsZero`
    intro j hj0 hjf
    obtain ⟨e⟩ := Work.Serre.serreFibration_fibre_homology_iso q hq γ j
    rw [← hγ1]
    refine IsZero.of_iso ?_ e.symm
    rw [hγ0]
    exact hfib j hj0 hjf
  · -- the degree-`0` augmentation
    have hε : IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q (γ 1)))
        (ModuleCat.of ℤ ℤ)) := by
      refine isIso_epsilon_fibre_of_path q hq γ ?_
      rw [hγ0]
      exact h0
    rw [← hγ1]
    exact hε

end

end Work.Serre.Assembly
