import Mathlib
import Submission.Work.Clifford.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.principalChar_mem_Irr`

The principal (trivial) character of a finite group is irreducible:
`Work.Clifford.principalChar G ∈ Work.Clifford.Irr G`.

`Work.Clifford.Irr G` is the set of characters of the *simple* finite dimensional complex
representations of `G`, so the statement asks for a simple object `V : FDRep ℂ G` whose character
is the constant function `1`.  We take for `V` the trivial representation of `G` on `ℂ`
(`FDRep.of (Representation.trivial ℂ G ℂ)`), whose character is `g ↦ trace (id : ℂ →ₗ ℂ) = 1`.

The mathematical content is therefore that this one-dimensional representation is simple.
Rather than reaching for the general dictionary between simple `FDRep`s and irreducible
representations, we prove simplicity directly from the definition of a simple object in an
abelian category, `CategoryTheory.simple_of_cosimple`: an object `X` is simple as soon as every
*epimorphism* out of `X` is either zero or an isomorphism.  Here the source of such an
epimorphism is one-dimensional over `ℂ`, so:

* an epimorphism is surjective on the underlying `ℂ`-vector spaces (the forgetful functors
  `FDRep ℂ G ⥤ FGModuleCat ℂ ⥤ ModuleCat ℂ` preserve epimorphisms);
* a *nonzero* linear map out of `ℂ` is injective (it sends the basis vector `1` to a nonzero
  vector, and `ℂ` is a field);
* hence a nonzero epimorphism is bijective, so an isomorphism; and conversely an isomorphism
  cannot be zero because `ℂ` is not the zero module.
-/

namespace Work.Clifford

noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- The trivial one-dimensional complex representation of a group is a simple object of
`FDRep ℂ G`. -/
theorem fdRep_trivial_simple (G : Type*) [Group G] :
    CategoryTheory.Simple (FDRep.of (Representation.trivial ℂ G ℂ)) := by
  refine simple_of_cosimple _ (fun {Z} f _ => ⟨?_, ?_⟩)
  · -- An isomorphism is nonzero: otherwise the one dimensional module `ℂ` would be a zero
    -- object.
    intro hiso hzero
    have h0 : IsIso (0 : FDRep.of (Representation.trivial ℂ G ℂ) ⟶ Z) := hzero ▸ hiso
    have hVz : IsZero (FDRep.of (Representation.trivial ℂ G ℂ)) :=
      (isIsoZero_iff_source_target_isZero _ _).mp h0 |>.1
    have h1 : 𝟙 (FDRep.of (Representation.trivial ℂ G ℂ)) = 0 := (IsZero.iff_id_eq_zero _).mp hVz
    have h2 : 𝟙 (FDRep.of (Representation.trivial ℂ G ℂ)).V = 0 := by
      have h := congrArg Action.Hom.hom h1
      simpa [Action.id_hom, Action.zero_hom] using h
    have h3 : 𝟙 ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).obj
        (FDRep.of (Representation.trivial ℂ G ℂ)).V) = 0 := by
      have h := congrArg ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).map) h2
      simpa using h
    have h4 : Subsingleton ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).obj
        (FDRep.of (Representation.trivial ℂ G ℂ)).V) := by
      constructor
      intro a b
      have ha : a = 0 := by
        simpa using congrArg (fun (m : ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).obj
          (FDRep.of (Representation.trivial ℂ G ℂ)).V) ⟶ ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).obj
          (FDRep.of (Representation.trivial ℂ G ℂ)).V)) => m a) h3
      have hb : b = 0 := by
        simpa using congrArg (fun (m : ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).obj
          (FDRep.of (Representation.trivial ℂ G ℂ)).V) ⟶ ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).obj
          (FDRep.of (Representation.trivial ℂ G ℂ)).V)) => m b) h3
      rw [ha, hb]
    have h5 : Subsingleton ℂ := h4
    exact one_ne_zero (Subsingleton.elim (1 : ℂ) 0)
  · -- A nonzero epimorphism is an isomorphism.
    intro hne
    have hne_hom : f.hom ≠ 0 := by
      intro h
      exact hne (Action.hom_ext f 0 (by rw [h, Action.zero_hom]))
    haveI hepi1 : Epi f.hom := by rw [← Action.forget_map]; exact Functor.map_epi _ f
    have hepi2 : Epi f.hom.hom := by
      haveI : Epi f.hom := hepi1
      exact Functor.map_epi (forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)) f.hom
    -- The underlying linear map is surjective.
    have hsurj : Function.Surjective (⇑(ConcreteCategory.hom f.hom.hom)) :=
      (ModuleCat.epi_iff_surjective _).mp hepi2
    -- It does not vanish at the basis vector `1`.
    have hφ1 : f.hom.hom (1 : (FDRep.of (Representation.trivial ℂ G ℂ)).V.obj) ≠ 0 := by
      intro h1
      apply hne_hom
      apply FGModuleCat.hom_ext
      have hlin : ModuleCat.Hom.hom f.hom.hom = 0 := by
        refine LinearMap.ext fun x => ?_
        have hx : x = x • (1 : (FDRep.of (Representation.trivial ℂ G ℂ)).V.obj) := by simp
        calc ModuleCat.Hom.hom f.hom.hom x
            = ModuleCat.Hom.hom f.hom.hom
                (x • (1 : (FDRep.of (Representation.trivial ℂ G ℂ)).V.obj)) := by
              conv_lhs => rw [hx]
          _ = x • ModuleCat.Hom.hom f.hom.hom
                (1 : (FDRep.of (Representation.trivial ℂ G ℂ)).V.obj) := by rw [map_smul]
          _ = 0 := by rw [h1, smul_zero]
      rw [hlin]
      simp
    -- Hence it is injective, by one-dimensionality of the source.
    have hinj : Function.Injective (⇑(ConcreteCategory.hom f.hom.hom)) := by
      intro x y hxy
      by_contra hxy'
      have hne' : x - y ≠ 0 := sub_ne_zero.mpr hxy'
      have hzero : (x - y) • f.hom.hom
          (1 : (FDRep.of (Representation.trivial ℂ G ℂ)).V.obj) = 0 := by
        have h2 : f.hom.hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
        rw [show x - y = (x - y) •
          (1 : (FDRep.of (Representation.trivial ℂ G ℂ)).V.obj) from by simp, map_smul] at h2
        exact h2
      rcases smul_eq_zero.mp hzero with h | h
      · exact hne' h
      · exact hφ1 h
    have hiso2 : IsIso f.hom.hom := by
      rw [isIso_iff_mono_and_epi]
      exact ⟨(ModuleCat.mono_iff_injective _).mpr hinj, (ModuleCat.epi_iff_surjective _).mpr hsurj⟩
    haveI : IsIso ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).map f.hom) := hiso2
    have hiso1 : IsIso f.hom :=
      isIso_of_reflects_iso f.hom (forget₂ (FGModuleCat ℂ) (ModuleCat ℂ))
    haveI : IsIso f.hom := hiso1
    exact Action.isIso_of_hom_isIso f

/-- The character of the trivial one-dimensional complex representation is the constant
function `1`: at every group element the representation acts by the identity, whose trace is
`finrank ℂ ℂ = 1`. -/
theorem fdRep_trivial_character (G : Type*) [Group G] (g : G) :
    (FDRep.of (Representation.trivial ℂ G ℂ)).character g = 1 := by
  show (LinearMap.trace ℂ (FDRep.of (Representation.trivial ℂ G ℂ)).V)
      ((FDRep.of (Representation.trivial ℂ G ℂ)).ρ g) = 1
  have h1 : (FDRep.of (Representation.trivial ℂ G ℂ)).ρ g = (1 : ℂ →ₗ[ℂ] ℂ) := rfl
  rw [h1, LinearMap.trace_one, Module.finrank_self]
  norm_num

theorem principalChar_mem_Irr {G : Type*} [Group G] [Fintype G] :
    Work.Clifford.principalChar G ∈ Work.Clifford.Irr G := by
  refine ⟨FDRep.of (Representation.trivial ℂ G ℂ), fdRep_trivial_simple G, ?_⟩
  ext g
  exact fdRep_trivial_character G g

end

end Work.Clifford
