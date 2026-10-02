import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.hZeroOfPiZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A rationally acyclic space is path connected

`RatAcyclic X` says that the map `X → *` is a rational homology isomorphism, i.e. that the
*reduced* rational homology `H̃_*(X;ℚ)` vanishes.  In degree `0` this means that the map
`H₀(X;ℚ) → H₀(*;ℚ) = ℚ` is an isomorphism, and since `H₀(X;ℚ) = ℚ[π₀(X)]` is the free `ℚ`-module
on the set of path components, this is exactly the statement that `X` has a single path component
(and is nonempty).  Hence `RatAcyclic X → PathConnectedSpace X`.

## The formalisation

Mathlib computes `H₀(X;R) ≅ ∐_(fun _ : ZerothHomotopy X ↦ R)` (`TopCat.singularHomology₀Iso`), but
it does not record the *naturality* of this isomorphism in `X`.  The whole content of the proof is

* `h0Iso_natural` — the naturality square: the map `H₀(f;ℚ)` is carried by the two isomorphisms to
  the coproduct of copies of `ℚ` along the induced map `h0Pi0Map f` of path components
  (`(sigmaConst.obj ℚ).map`), the computation performed inside `Work.Serre.hZeroOfPiZero`
  (`hZeroOfPiZero_aux`); here it is extracted, and — this is the point — it needs *no* nonemptiness
  hypothesis, which is what lets us run the argument on a possibly empty `X`;
* `bijective_of_isIso_sigmaMap` — an abstract algebraic fact: for a map `F : S → T` of types, if the
  induced map `∐_S ℚ → ∐_T ℚ` (`Sigma.map'`) between the coproducts of copies of the nontrivial
  module `ℚ` is an isomorphism, then `F` is a bijection.  Proof: `Σ.ι s ≫ map' F = Σ.ι (F s)` gives
  injectivity (cancelling the isomorphism and then using `Σ.π s`), and composing `Σ.ι t ≫ map'⁻¹`
  with `map' ≫ Σ.π t` gives surjectivity.

Applying this to `F = h0Pi0Map (toPoint X)` yields that `ZerothHomotopy X` is a singleton, i.e.
that `X` is path connected (`pathConnectedSpace_iff_zerothHomotopy`).
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

set_option linter.style.haveILetI false

/-- **Naturality of the computation of `H₀(-;ℚ)` as the free `ℚ`-module on `π₀`.**

Conjugating the map `H₀(f;ℚ)` by the two isomorphisms `h0Iso` exhibits it as the coproduct of
copies of `ℚ` along the induced map `h0Pi0Map f` on path components.  (This is the computation
inside the proof of `Work.Serre.hZeroOfPiZero`/`hZeroOfPiZero_aux`; it is extracted here because we
need it without the `[Nonempty X]` hypothesis of that theorem.) -/
theorem h0Iso_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (h0Iso (TopCat.of X)).inv ≫
      HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0 ≫
      (h0Iso (TopCat.of Y)).hom = (sigmaConst.obj h0Coeff).map (TypeCat.ofHom (h0Pi0Map f)) := by
  apply Sigma.hom_ext
  intro i
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective i
  have hidx : ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map (TopCat.ofHom f)).app _
      (TopCat.toSSetObj₀Equiv.symm x))) = h0Pi0Map f (ZerothHomotopy.mk x) := by
    rw [h0_toSSetObj₀Equiv_natural, Equiv.apply_symm_apply, h0Pi0Map_mk]
  calc Sigma.ι (fun _ : ZerothHomotopy (TopCat.of X) ↦ h0Coeff) (ZerothHomotopy.mk x) ≫
        ((h0Iso (TopCat.of X)).inv ≫ HomologicalComplex.homologyMap
          (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0 ≫
          (h0Iso (TopCat.of Y)).hom)
      = (Sigma.ι (fun _ : ZerothHomotopy (TopCat.of X) ↦ h0Coeff) (ZerothHomotopy.mk x) ≫
          (h0Iso (TopCat.of X)).inv) ≫ (HomologicalComplex.homologyMap
          (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0 ≫
          (h0Iso (TopCat.of Y)).hom) := by simp only [Category.assoc]
    _ = h0Point (TopCat.of X) (TopCat.toSSetObj₀Equiv.symm x) ≫
          (HomologicalComplex.homologyMap
            (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0 ≫
            (h0Iso (TopCat.of Y)).hom) := by rw [h0Sigma_ι_inv_iso]
    _ = (h0Point (TopCat.of X) (TopCat.toSSetObj₀Equiv.symm x) ≫
          HomologicalComplex.homologyMap
            (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0) ≫
          (h0Iso (TopCat.of Y)).hom := by simp only [Category.assoc]
    _ = h0Point (TopCat.of Y) ((TopCat.toSSet.map (TopCat.ofHom f)).app _
          (TopCat.toSSetObj₀Equiv.symm x)) ≫ (h0Iso (TopCat.of Y)).hom := by
          rw [h0Point_natural]
    _ = Sigma.ι (fun _ : ZerothHomotopy (TopCat.of Y) ↦ h0Coeff) (ZerothHomotopy.mk
          (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map (TopCat.ofHom f)).app _
            (TopCat.toSSetObj₀Equiv.symm x)))) :=
          h0Point_iso (TopCat.of Y) _
    _ = Sigma.ι (fun _ : ZerothHomotopy (TopCat.of Y) ↦ h0Coeff)
          (h0Pi0Map f (ZerothHomotopy.mk x)) := by rw [hidx]
    _ = Sigma.ι (fun _ : ZerothHomotopy (TopCat.of X) ↦ h0Coeff) (ZerothHomotopy.mk x) ≫
          (sigmaConst.obj h0Coeff).map (TypeCat.ofHom (h0Pi0Map f)) := by
        rw [sigmaConst_obj_map, Sigma.ι_comp_map']
        simp

/-- If an endomorphism of a nontrivial module is equal to `0`, the module is a subsingleton — the
form in which the contradiction `𝟙 = 0` is consumed below. -/
theorem subsingleton_of_id_eq_zero {M : ModuleCat ℚ} (h : 𝟙 M = 0) : Subsingleton ↥M :=
  subsingleton_of_isZero ((IsZero.iff_id_eq_zero M).mpr h)

/-- **The free-module functor reflects bijectivity.**  If `F : S → T` induces an isomorphism
`∐_S ℚ → ∐_T ℚ` on the coproducts of copies of the nontrivial module `ℚ`, then `F` is a bijection.

Injectivity: `Σ.ι s ≫ Sigma.map' F = Σ.ι (F s)`, so `F s = F s'` gives `Σ.ι s = Σ.ι s'` after
cancelling the isomorphism, and applying `Σ.π s` turns this into `𝟙 = Σ.ι s' ≫ Σ.π s`, which is
`𝟙 = 0` unless `s = s'`.

Surjectivity: if `t ∉ range F` then `Sigma.map' F ≫ Σ.π t = 0` (both sides have the same
components `Σ.ι (F s) ≫ Σ.π t = 0`), whence
`𝟙 = Σ.ι t ≫ Σ.π t = (Σ.ι t ≫ (Sigma.map' F)⁻¹) ≫ Sigma.map' F ≫ Σ.π t = 0`. -/
theorem bijective_of_isIso_sigmaMap {S T : Type} (F : S → T)
    (h : IsIso (Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F
      (fun _ => 𝟙 h0Coeff))) :
    Function.Bijective F := by
  classical
  haveI := h
  refine ⟨?_, ?_⟩
  · intro s s' hss
    have h1 : Sigma.ι (fun _ : S => h0Coeff) s ≫
        Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F (fun _ => 𝟙 h0Coeff)
        = Sigma.ι (fun _ : T => h0Coeff) (F s) := by
      rw [Sigma.ι_comp_map']; simp
    have h2 : Sigma.ι (fun _ : S => h0Coeff) s' ≫
        Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F (fun _ => 𝟙 h0Coeff)
        = Sigma.ι (fun _ : T => h0Coeff) (F s') := by
      rw [Sigma.ι_comp_map']; simp
    have key : Sigma.ι (fun _ : S => h0Coeff) s = Sigma.ι (fun _ : S => h0Coeff) s' := by
      calc Sigma.ι (fun _ : S => h0Coeff) s
          = (Sigma.ι (fun _ : S => h0Coeff) s ≫
              Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F (fun _ => 𝟙 h0Coeff))
              ≫ inv (Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F
                (fun _ => 𝟙 h0Coeff)) := by
            rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        _ = (Sigma.ι (fun _ : S => h0Coeff) s' ≫
              Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F (fun _ => 𝟙 h0Coeff))
              ≫ inv (Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F
                (fun _ => 𝟙 h0Coeff)) := by
            rw [h1, h2, hss]
        _ = Sigma.ι (fun _ : S => h0Coeff) s' := by
            rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    by_contra hne
    have h3 := congrArg (fun g => g ≫ Sigma.π (fun _ : S => h0Coeff) s) key
    rw [Sigma.ι_π_eq_id] at h3
    have h4 : Sigma.ι (fun _ : S => h0Coeff) s' ≫ Sigma.π (fun _ : S => h0Coeff) s = 0 :=
      Sigma.ι_π_of_ne (f := fun _ : S => h0Coeff) (fun hh => hne hh.symm)
    rw [h4] at h3
    haveI : Subsingleton ↥h0Coeff := subsingleton_of_id_eq_zero h3
    exact one_ne_zero (Subsingleton.elim (1 : ℚ) 0)
  · intro t
    by_contra ht
    have ht' : ∀ s, F s ≠ t := fun s hh => ht ⟨s, hh⟩
    have hzero : Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F
        (fun _ => 𝟙 h0Coeff) ≫ Sigma.π (fun _ : T => h0Coeff) t = 0 := by
      apply Sigma.hom_ext
      intro s
      rw [← Category.assoc, Sigma.ι_comp_map']
      simp only [Category.id_comp]
      rw [Sigma.ι_π_of_ne (f := fun _ : T => h0Coeff) (ht' s)]
      simp
    have h1 : Sigma.ι (fun _ : T => h0Coeff) t
        = (Sigma.ι (fun _ : T => h0Coeff) t ≫
            inv (Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F
              (fun _ => 𝟙 h0Coeff)))
          ≫ Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F
              (fun _ => 𝟙 h0Coeff) := by
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hone : (𝟙 h0Coeff) = 0 := by
      calc (𝟙 h0Coeff)
          = Sigma.ι (fun _ : T => h0Coeff) t ≫ Sigma.π (fun _ : T => h0Coeff) t :=
            (Sigma.ι_π_eq_id (fun _ : T => h0Coeff) t).symm
        _ = ((Sigma.ι (fun _ : T => h0Coeff) t ≫
              inv (Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F
                (fun _ => 𝟙 h0Coeff)))
              ≫ Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F
                (fun _ => 𝟙 h0Coeff))
              ≫ Sigma.π (fun _ : T => h0Coeff) t := by rw [← h1]
        _ = (Sigma.ι (fun _ : T => h0Coeff) t ≫
              inv (Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F
                (fun _ => 𝟙 h0Coeff)))
              ≫ (Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F
                  (fun _ => 𝟙 h0Coeff) ≫ Sigma.π (fun _ : T => h0Coeff) t) := by rw [Category.assoc]
        _ = (Sigma.ι (fun _ : T => h0Coeff) t ≫
              inv (Sigma.map' (f := fun _ : T => h0Coeff) (g := fun _ : S => h0Coeff) F
                (fun _ => 𝟙 h0Coeff))) ≫ 0 := by rw [hzero]
        _ = 0 := by simp
    haveI : Subsingleton ↥h0Coeff := subsingleton_of_id_eq_zero hone
    exact one_ne_zero (Subsingleton.elim (1 : ℚ) 0)

/-- **A rationally acyclic space is path connected.**  `H₀(X;ℚ) ≅ ℚ` forces `π₀(X)` to be a
singleton: the map `H₀(X;ℚ) → H₀(*;ℚ)` is, under Mathlib's identification
`H₀(-;ℚ) ≅ ∐_(fun _ : ZerothHomotopy - ↦ ℚ)`, the free-module map along `ZerothHomotopy X →
ZerothHomotopy *`, which by `bijective_of_isIso_sigmaMap` must then be a bijection. -/
theorem pathConnectedSpace_of_ratAcyclic {X : Type} [TopologicalSpace X]
    (h : Work.Serre.RatAcyclic X) : PathConnectedSpace X := by
  haveI : IsIso (HomologicalComplex.homologyMap
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (toPoint X))) h0Coeff) 0) := h 0
  -- the naturality square exhibits `∐(h0Pi0Map (toPoint X))` as an isomorphism
  have hm : IsIso ((sigmaConst.obj h0Coeff).map (TypeCat.ofHom (h0Pi0Map (toPoint X)))) := by
    rw [← h0Iso_natural (toPoint X)]
    exact inferInstance
  -- hence the induced map on path components is a bijection
  have hbij : Function.Bijective (h0Pi0Map (toPoint X)) := by
    apply bijective_of_isIso_sigmaMap
    rw [sigmaConst_obj_map] at hm
    exact hm
  have hne : Nonempty (ZerothHomotopy X) := by
    obtain ⟨t⟩ := (inferInstance : Nonempty (ZerothHomotopy PUnit))
    obtain ⟨s, _⟩ := hbij.2 t
    exact ⟨s⟩
  have hsub : Subsingleton (ZerothHomotopy X) :=
    ⟨fun a b => hbij.1 (Subsingleton.elim (h0Pi0Map (toPoint X) a) _)⟩
  exact pathConnectedSpace_iff_zerothHomotopy.mpr ⟨hne, hsub⟩

end

end Work.Serre
