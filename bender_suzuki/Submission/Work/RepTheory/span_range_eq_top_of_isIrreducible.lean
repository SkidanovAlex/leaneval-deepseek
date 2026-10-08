import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The image of an irreducible complex representation spans the endomorphism algebra

For a finite group `G`, a finite-dimensional complex representation `ρ` that is irreducible,
the `ℂ`-linear span of the operators `ρ g` (`g : G`) is the whole algebra `V →ₗ[ℂ] V` of
endomorphisms of the representation space.

This is the classical consequence of Schur's lemma and the Jacobson density theorem
(Burnside's theorem on the span of an irreducible matrix group).  The argument here is:

* `ℂ[G]` acts on `ρ.asModule` with a *simple* module structure, so the natural map
  `ℂ[G] → End_ℂ(V)` (which is `ρ.asAlgebraHom`) has image the span of `{ρ g}`;
* the centralizer `D = End_{ℂ[G]}(V)` is `ℂ` by Schur's lemma
  (`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`);
* Jacobson density (`Module.Finite.toModuleEnd_moduleEnd_surjective`) upgrades this to
  surjectivity of `ℂ[G] → End_D(V) = End_ℂ(V)`;
* hence the image of `ℂ[G]`, i.e. the span of `{ρ g}`, is everything.
-/

namespace Work.RepTheory

open scoped MonoidAlgebra

set_option linter.style.haveILetI false

theorem span_range_eq_top_of_isIrreducible {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Submodule.span ℂ (Set.range (fun g : G => (ρ g : V →ₗ[ℂ] V))) = ⊤ := by
  -- Schur's lemma: the centralizer of the (simple) `ℂ[G]`-module is `ℂ`.
  have hbij : Function.Bijective (algebraMap ℂ (Module.End ℂ[G] ρ.asModule)) :=
    IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ
  -- `ρ.asModule` is finite over its own endomorphism ring (which is `ℂ`).
  haveI hfinD : Module.Finite (Module.End ℂ[G] ρ.asModule) ρ.asModule := by
    obtain ⟨S, hS⟩ := (Module.Finite.fg_top (R := ℂ) (M := ρ.asModule))
    refine ⟨S, ?_⟩
    apply SetLike.coe_injective
    rw [Submodule.coe_span_eq_span_of_surjective (R := ℂ) (A := Module.End ℂ[G] ρ.asModule)
      hbij.surjective (↑S : Set ρ.asModule), hS]
    rfl
  -- Jacobson density: `ℂ[G]` surjects onto the `D`-linear endomorphisms of `ρ.asModule`.
  have hsurjMod : Function.Surjective
      (Module.toModuleEnd ℂ (S := ℂ[G]) ρ.asModule) := by
    have hsurjD : Function.Surjective
        (Module.toModuleEnd (Module.End ℂ[G] ρ.asModule) (S := ℂ[G]) ρ.asModule) :=
      Module.Finite.toModuleEnd_moduleEnd_surjective
    intro T
    -- every `ℂ`-linear map is `D`-linear, since `D = ℂ`.
    let f : Module.End (Module.End ℂ[G] ρ.asModule) ρ.asModule :=
      { toFun := ⇑T
        map_add' := T.map_add
        map_smul' := by
          intro d m
          obtain ⟨c, rfl⟩ := hbij.surjective d
          simp only [algebraMap_smul]
          exact T.map_smul c m }
    obtain ⟨r, hr⟩ := hsurjD f
    refine ⟨r, ?_⟩
    apply LinearMap.ext
    intro m
    have h1 : ((Module.toModuleEnd (Module.End ℂ[G] ρ.asModule) ρ.asModule) r) m = T m := by
      rw [hr]; rfl
    simpa [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply] using h1
  -- Transport along `ρ.asModuleEquiv` to obtain surjectivity of `ρ.asAlgebraHom`.
  have hsurj : Function.Surjective (ρ.asAlgebraHom) := by
    intro T
    let e := ρ.asModuleEquiv
    let S : Module.End ℂ ρ.asModule := e.symm.toLinearMap.comp (T.comp e.toLinearMap)
    obtain ⟨r, hr⟩ := hsurjMod S
    refine ⟨r, ?_⟩
    apply LinearMap.ext
    intro v
    have h1 : (r • (e.symm v) : ρ.asModule) = e.symm (T v) := by
      have h2 := congrArg (fun f : Module.End ℂ ρ.asModule => f (e.symm v)) hr
      simp only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply, S, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
      exact h2
    have h3 : e (r • e.symm v) = T v := by
      rw [h1, LinearEquiv.apply_symm_apply]
    have key : (ρ.asAlgebraHom r) v = e (r • e.symm v) := by
      rw [Representation.asModuleEquiv_map_smul ρ r (e.symm v), LinearEquiv.apply_symm_apply]
    rw [key, h3]
  -- The group elements span the group algebra.
  have hspan_of : Submodule.span ℂ (Set.range (fun g : G => MonoidAlgebra.of ℂ G g)) = ⊤ := by
    refine le_antisymm le_top ?_
    intro f _
    exact Submodule.span_mono (Set.image_subset_range _ _) (MonoidAlgebra.mem_span_support_coeff f)
  -- Conclude: the image of `ρ.asAlgebraHom` is the span of `{ρ g}`.
  refine le_antisymm le_top ?_
  intro T _
  obtain ⟨r, hr⟩ := hsurj T
  rw [← hr]
  have hr' : r ∈ Submodule.span ℂ (Set.range fun g : G => MonoidAlgebra.of ℂ G g) := by
    rw [hspan_of]; trivial
  have hQ : Set.range (fun g : G => MonoidAlgebra.of ℂ G g) ⊆
      Submodule.comap (ρ.asAlgebraHom).toLinearMap
        (Submodule.span ℂ (Set.range (fun g : G => ρ g))) := by
    rintro x ⟨g, rfl⟩
    exact Submodule.subset_span ⟨g, (Representation.asAlgebraHom_of ρ g).symm⟩
  exact (Submodule.span_le.mpr hQ) hr'

end Work.RepTheory
