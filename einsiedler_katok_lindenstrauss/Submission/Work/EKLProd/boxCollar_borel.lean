import Mathlib
import Submission.Work.EKLProd.BoxFlowerDefs
import Submission.Work.EKLProd.box_measSection

/-!
# Borel measurability of a product-box collar

`Work.EKLProd.boxCollar_borel`: the collar
`boxCollar T U R A = (prodBox T U R) • A` — the union of the box plaques over the points of a
Borel set `A` of base points — is a Borel subset of `X₃`.

By definition (`BoxFlowerDefs`) the collar is the image of the Borel subset
`boxParam T U R A = (V R ∩ T) × (V R ∩ U) × A` of `SL₃(ℝ) × SL₃(ℝ) × X₃` under the continuous
parametrising map `boxParamMap (t,u,c) = (t * u) • c`:

* `measurableSet_boxParam` (from `EKLProd.box_measSection`): the parametrising set is Borel
  (`V R` is open, `T` and `U` are closed);
* `continuous_boxParamMap`: the parametrising map is continuous;
* `boxParamMap_injOn` instantiates the injectivity of `boxParamMap` on `boxParam T U R C` to the
  subset `A ⊆ C`: `hdisj` (`T ⊓ U = ⊥`) makes the decomposition `t * u` unique, while `hbound`
  together with `hcross` makes the base point unique — if `g • c = g' • c'` with `g, g'` in the
  product box and `c, c' ∈ A ⊆ C`, then `(g')⁻¹ * g ∈ Ucl H ρ` and `((g')⁻¹ * g) • c = c' ∈ C`,
  so `hcross` forces `(g')⁻¹ * g = 1`, i.e. `g = g'`, and then `c = c'` by invertibility of the
  action.

The image of a Borel set under a continuous injective map is Borel (Lusin–Suslin,
`MeasurableSet.image_of_continuousOn_injOn`), which gives the claim.  The freeness hypothesis
`hfreeH` is not needed for the measurability of the collar.
-/

open MeasureTheory Topology

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

theorem boxCollar_borel {H T U : Subgroup Work.EKLContract.SL3}
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {R ρ : ℝ} {C : Set Work.EKLContract.X3}
    (hbound : ∀ g ∈ Work.EKLProd.prodBox T U R, ∀ g' ∈ Work.EKLProd.prodBox T U R,
      g'⁻¹ * g ∈ Work.EKLComp.Ucl H ρ)
    (hfreeH : ∀ c ∈ C, ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ • c = h₂ • c → h₁ = h₂)
    (hcross : ∀ c ∈ C, ∀ v ∈ Work.EKLComp.Ucl H ρ, v • c ∈ C → v = 1)
    {A : Set Work.EKLContract.X3} (hAC : A ⊆ C) (hA : MeasurableSet A) :
    MeasurableSet (Work.EKLProd.boxCollar T U R A) := by
  haveI hpolSL : PolishSpace Work.EKLContract.SL3 :=
    Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  have hmeas : MeasurableSet (boxParam T U R A) :=
    measurableSet_boxParam T U hTc hUc R hA
  have hinj : Set.InjOn boxParamMap (boxParam T U R A) :=
    boxParamMap_injOn hdisj hbound (fun c hc v hv hvc => hcross c (hAC hc) v hv (hAC hvc))
  exact hmeas.image_of_continuousOn_injOn continuous_boxParamMap.continuousOn hinj

end Work.EKLProd
