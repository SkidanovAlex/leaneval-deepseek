/-
AREA TOOLKIT — coproduct interfaces exported for other areas (in particular RESOL).

This file collects the facts saying that the localization `Q : Cpx ⤒ D(LightCondAb)` preserves
small coproducts, and that quasi-isomorphisms are stable under colimits whose shape is exact in
`LightCondAb`:

* `quasiIso_colimMap` (C1): colimits (in particular coproducts) of quasi-isomorphisms are
  quasi-isomorphisms;
* `quasiIso_sigma` (C1, coproduct form);
* `hq_sigma_bijective` (C2): the homotopy category functor preserves small coproducts;
* `Qh_sigma_bijective` (C3): the localization `K(LightCondAb) ⤒ D(LightCondAb)` at the
  quasi-isomorphisms preserves small coproducts;
* `Q_sigma_bijective` (C3, in terms of `Q`): for every `W` in the derived category, the canonical
  map `Hom(Q (∐ K), W) → ∏ j, Hom(Q (K j), W)` is a bijection.

The coproduct instances of `Submission/Work/TOOLKIT/Instances.lean` are re-exported as well.
-/
import Submission.Work.TOOLKIT.Instances
import Submission.Work.TOOLKIT.Coprod.quasiIso_colimMap
import Submission.Work.TOOLKIT.Coprod.hq_sigma_bijective
import Submission.Work.TOOLKIT.Coprod.Qh_sigma_bijective
import Submission.Work.TOOLKIT.Sigma.quasiIso_sigma
import Submission.Work.TOOLKIT.Sigma.hom_coproduct_bijective

open CategoryTheory Limits

noncomputable section

namespace Work.TOOLKIT

/-- C1: colimits (of an exact shape) of quasi-isomorphisms are quasi-isomorphisms. -/
theorem quasiIso_colimMap {J : Type} [Category J]
    [HasColimitsOfShape J LightCondAb]
    [CategoryTheory.HasExactColimitsOfShape J LightCondAb]
    {F G : CategoryTheory.Functor J Cpx} (τ : F ⟶ G) (hτ : ∀ j, QuasiIso (τ.app j)) :
    QuasiIso (colimMap τ) :=
  Coprod.quasiIso_colimMap τ hτ

/-- C1, coproduct form: a coproduct of quasi-isomorphisms is a quasi-isomorphism. -/
theorem quasiIso_sigma (J : Type) (K L : J → Cpx)
    [HasCoproduct K] [HasCoproduct L] (f : ∀ j, K j ⟶ L j) (hf : ∀ j, QuasiIso (f j)) :
    QuasiIso (CategoryTheory.Limits.Sigma.map f) :=
  Work.TOOLKIT.Sigma.quasiIso_sigma J K L f hf

/-- C2: the homotopy category functor `hq` preserves small coproducts. -/
theorem hq_sigma_bijective (J : Type) (K : J → Cpx) [HasCoproduct K] (W : KCat) :
    Function.Bijective (fun (φ : (HomotopyCategory.quotient LightCondAb
        (ComplexShape.up ℤ)).obj (CategoryTheory.Limits.sigmaObj K) ⟶ W) (j : J) =>
      CategoryStruct.comp ((HomotopyCategory.quotient LightCondAb
        (ComplexShape.up ℤ)).map (CategoryTheory.Limits.Sigma.ι K j)) φ) :=
  Coprod.hq_sigma_bijective J K W

/-- C3: the localization `Qh` preserves small coproducts. -/
theorem Qh_sigma_bijective (J : Type) (K : J → Cpx) [HasCoproduct K] (Z : DCat) :
    Function.Bijective (fun (φ : DerivedCategory.Qh.obj ((HomotopyCategory.quotient
        LightCondAb (ComplexShape.up ℤ)).obj (CategoryTheory.Limits.sigmaObj K)) ⟶ Z) (j : J) =>
      CategoryStruct.comp (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).map (CategoryTheory.Limits.Sigma.ι K j))) φ) :=
  Coprod.Qh_sigma_bijective J K Z

/-- C3, in terms of `Q`: `Q` preserves small coproducts. -/
theorem Q_sigma_bijective (J : Type) (K : J → Cpx) [HasCoproduct K] (Z : DCat) :
    Function.Bijective (fun (g : DerivedCategory.Q.obj (CategoryTheory.Limits.sigmaObj K) ⟶ Z) (j : J) =>
      CategoryStruct.comp (DerivedCategory.Q.map (CategoryTheory.Limits.Sigma.ι K j)) g) :=
  Work.TOOLKIT.Sigma.hom_coproduct_bijective J K Z

end Work.TOOLKIT
