import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.HomologyIso

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- Elementwise description of the action on elements of the universe-lifting functor
`ModuleCat.{0,0} ℤ ⥤ ModuleCat.{u,0} ℤ`. -/
lemma uliftFunctor_map_hom_apply {M N : ModuleCat.{0,0} ℤ} (f : M ⟶ N) (x : ULift.{u,0} ↥M) :
    ((ModuleCat.uliftFunctor.{u,0} ℤ).map f).hom x =
      (ULift.moduleEquiv (R := ℤ)).symm (f.hom ((ULift.moduleEquiv (R := ℤ)) x)) := by
  rw [ModuleCat.uliftFunctor_map]
  rfl

set_option autoImplicit true in
theorem quasiIso_iff_of_conj {u : Universe} {C : ChainComplex (ModuleCat.{u, 0} ℤ) ℕ} {D : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ} (Φ : ∀ k : ℕ, (↥(C.X k) ≃ₗ[ℤ] ↥(D.X k))) (hΦ : ∀ (k : ℕ) (x : ↥(C.X (k + 1))), Φ k ((C.d (k + 1) k).hom x) = (D.d (k + 1) k).hom (Φ (k + 1) x)) {E : ChainComplex (ModuleCat.{u, 0} ℤ) ℕ} {F : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ} (Ψ : ∀ k : ℕ, (↥(E.X k) ≃ₗ[ℤ] ↥(F.X k))) (hΨ : ∀ (k : ℕ) (x : ↥(E.X (k + 1))), Ψ k ((E.d (k + 1) k).hom x) = (F.d (k + 1) k).hom (Ψ (k + 1) x)) (f : E ⟶ C) (g : F ⟶ D) (hfg : ∀ (k : ℕ) (x : ↥(E.X k)), Φ k ((f.f k) x) = (g.f k) (Ψ k x)) : QuasiIso f ↔ QuasiIso g := by
  -- lift the `D` and `F` sides into the universe of `C` and `E`
  let D' : ChainComplex (ModuleCat.{u, 0} ℤ) ℕ :=
    ((ModuleCat.uliftFunctor.{u, 0} ℤ).mapHomologicalComplex (ComplexShape.down ℕ)).obj D
  let F' : ChainComplex (ModuleCat.{u, 0} ℤ) ℕ :=
    ((ModuleCat.uliftFunctor.{u, 0} ℤ).mapHomologicalComplex (ComplexShape.down ℕ)).obj F
  let Φ' : ∀ k : ℕ, (↥(C.X k) ≃ₗ[ℤ] ↥(D'.X k)) :=
    fun k => Φ k ≪≫ₗ (ULift.moduleEquiv (R := ℤ)).symm
  let Ψ' : ∀ k : ℕ, (↥(E.X k) ≃ₗ[ℤ] ↥(F'.X k)) :=
    fun k => Ψ k ≪≫ₗ (ULift.moduleEquiv (R := ℤ)).symm
  have hΦ' : ∀ (k : ℕ) (x : ↥(C.X (k + 1))),
      Φ' k ((C.d (k + 1) k).hom x) = (D'.d (k + 1) k).hom (Φ' (k + 1) x) := by
    intro k x
    change (ULift.moduleEquiv (R := ℤ)).symm (Φ k ((C.d (k + 1) k).hom x))
        = (D'.d (k + 1) k).hom ((ULift.moduleEquiv (R := ℤ)).symm (Φ (k + 1) x))
    rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d,
      uliftFunctor_map_hom_apply (D.d (k + 1) k)
        ((ULift.moduleEquiv (R := ℤ)).symm (Φ (k + 1) x)),
      LinearEquiv.apply_symm_apply, hΦ k x]
  have hΨ' : ∀ (k : ℕ) (x : ↥(E.X (k + 1))),
      Ψ' k ((E.d (k + 1) k).hom x) = (F'.d (k + 1) k).hom (Ψ' (k + 1) x) := by
    intro k x
    change (ULift.moduleEquiv (R := ℤ)).symm (Ψ k ((E.d (k + 1) k).hom x))
        = (F'.d (k + 1) k).hom ((ULift.moduleEquiv (R := ℤ)).symm (Ψ (k + 1) x))
    rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d,
      uliftFunctor_map_hom_apply (F.d (k + 1) k)
        ((ULift.moduleEquiv (R := ℤ)).symm (Ψ (k + 1) x)),
      LinearEquiv.apply_symm_apply, hΨ k x]
  let φ : C ⟶ D' := HomologicalComplex.Hom.mk (fun k => (Φ' k).toModuleIso.hom)
    (fun i j hij => by
      rw [← hij]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      show (D'.d (j + 1) j).hom ((Φ' (j + 1)) x) = (Φ' j) ((C.d (j + 1) j).hom x)
      exact (hΦ' j x).symm)
  let ψ : E ⟶ F' := HomologicalComplex.Hom.mk (fun k => (Ψ' k).toModuleIso.hom)
    (fun i j hij => by
      rw [← hij]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      show (F'.d (j + 1) j).hom ((Ψ' (j + 1)) x) = (Ψ' j) ((E.d (j + 1) j).hom x)
      exact (hΨ' j x).symm)
  have hφiso : IsIso φ := HomologicalComplex.Hom.isIso_of_components φ
  have hψiso : IsIso ψ := HomologicalComplex.Hom.isIso_of_components ψ
  let g' : F' ⟶ D' :=
    ((ModuleCat.uliftFunctor.{u, 0} ℤ).mapHomologicalComplex (ComplexShape.down ℕ)).map g
  have hψf : ∀ k, ψ.f k = (Ψ' k).toModuleIso.hom := fun k => rfl
  have hφf : ∀ k, φ.f k = (Φ' k).toModuleIso.hom := fun k => rfl
  have hsqu : ψ ≫ g' = f ≫ φ := by
    apply HomologicalComplex.hom_ext
    intro k
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hψf k, hφf k]
    rw [show g'.f k = (ModuleCat.uliftFunctor.{u, 0} ℤ).map (g.f k) from
      CategoryTheory.Functor.mapHomologicalComplex_map_f (ModuleCat.uliftFunctor.{u, 0} ℤ)
        (ComplexShape.down ℕ) g k]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    show (ModuleCat.Hom.hom ((ModuleCat.uliftFunctor.{u, 0} ℤ).map (g.f k))) ((Ψ' k) x)
        = (Φ' k) ((f.f k) x)
    rw [show (Ψ' k) x = (ULift.moduleEquiv (R := ℤ)).symm (Ψ k x) from rfl,
      uliftFunctor_map_hom_apply (g.f k) ((ULift.moduleEquiv (R := ℤ)).symm (Ψ k x)),
      LinearEquiv.apply_symm_apply]
    rw [show (Φ' k) ((f.f k) x)
        = (ULift.moduleEquiv (R := ℤ)).symm (Φ k ((f.f k) x)) from rfl, hfg k x]
  have key1 : QuasiIso f ↔ QuasiIso g' := by
    haveI : IsIso φ := hφiso
    haveI : IsIso ψ := hψiso
    have h1 : QuasiIso f ↔ QuasiIso (f ≫ φ) := (quasiIso_iff_comp_right f φ).symm
    have h2 : QuasiIso (f ≫ φ) ↔ QuasiIso (ψ ≫ g') :=
      (iff_of_eq (congrArg (fun t => QuasiIso t) hsqu)).symm
    have h3 : QuasiIso (ψ ≫ g') ↔ QuasiIso g' := quasiIso_iff_comp_left ψ g'
    exact h1.trans (h2.trans h3)
  have key2 : QuasiIso g' ↔ QuasiIso g :=
    HomologicalComplex.quasiIso_map_iff_of_preservesHomology g (ModuleCat.uliftFunctor.{u, 0} ℤ)
  exact key1.trans key2

end

end Work.HomologyIso
