import Mathlib
import Submission.Work.ATOM.Defs

namespace Work.ATOM

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

/-- Naturality of the comparison isomorphism `Hom(ℤ[S], A) ≅ A(S)` with respect to `zmap`:
precomposition with `ℤ[f]` corresponds to restriction of sections along `f`. -/
theorem homFreeEquiv_zmap {S T : LightProfinite.{0}} (f : S ⟶ T) (A : LightCondAb)
    (g : Work.ATOM.zfree T ⟶ A) :
    homFreeEquiv S A (zmap f ≫ g) = A.obj.map f.op (homFreeEquiv T A g) := by
  show (coherentTopology LightProfinite).yonedaEquiv
      ((freeForgetAdjunction ℤ).homEquiv (lightProfiniteToLightCondSet.obj S) A
        ((free ℤ).map (lightProfiniteToLightCondSet.map f) ≫ g)) =
    (ConcreteCategory.hom (A.obj.map f.op))
      ((coherentTopology LightProfinite).yonedaEquiv
        ((freeForgetAdjunction ℤ).homEquiv (lightProfiniteToLightCondSet.obj T) A g))
  rw [Adjunction.homEquiv_naturality_left]
  exact (GrothendieckTopology.yonedaEquiv_naturality (J := coherentTopology LightProfinite) _ f).symm

/-- A finite jointly surjective family of light profinite sets is an effective epimorphic family. -/
theorem effectiveEpiFamily_of_jointlySurjective {T : LightProfinite.{0}} {n : ℕ}
    (C : Fin n → LightProfinite.{0}) (ι : ∀ i, C i ⟶ T)
    (hcov : ∀ t : T, ∃ i, t ∈ Set.range (ι i)) : EffectiveEpiFamily C ι := by
  rw [← effectiveEpi_desc_iff_effectiveEpiFamily]
  rw [LightProfinite.effectiveEpi_iff_surjective]
  intro t
  obtain ⟨i, c, hc⟩ := hcov t
  exact ⟨(Sigma.ι C i) c, by rw [Sigma.ι_comp_desc_apply]; exact hc⟩

/-- Sections of a light condensed abelian group over `T` are determined by their restrictions
to a finite jointly surjective family of `T`. -/
theorem eq_of_forall_map_eq_of_jointlySurjective {T : LightProfinite.{0}} {n : ℕ}
    (C : Fin n → LightProfinite.{0}) (ι : ∀ i, C i ⟶ T)
    (hcov : ∀ t : T, ∃ i, t ∈ Set.range (ι i)) (M : LightCondAb)
    {x y : M.obj.obj (op T)}
    (h : ∀ i, M.obj.map (ι i).op x = M.obj.map (ι i).op y) : x = y := by
  have hS : Sieve.ofArrows C ι ∈ coherentTopology LightProfinite T := by
    rw [coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily]
    exact ⟨Fin n, inferInstance, C, ι, effectiveEpiFamily_of_jointlySurjective C ι hcov,
      fun i => Sieve.ofArrows_mk C ι i⟩
  have key := Presheaf.IsSheaf.hom_ext_ofArrows (J := coherentTopology LightProfinite) (P := M.obj)
      M.property ι hS (E := ModuleCat.of ℤ ℤ)
      (x := ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (M.obj.obj (op T)) x))
      (y := ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (M.obj.obj (op T)) y))
      ?_
  · have h2 : (LinearMap.toSpanSingleton ℤ (M.obj.obj (op T)) x) 1 =
        (LinearMap.toSpanSingleton ℤ (M.obj.obj (op T)) y) 1 :=
      congrArg (fun (f : ModuleCat.of ℤ ℤ ⟶ M.obj.obj (op T)) => (ModuleCat.Hom.hom f) 1) key
    exact LinearMap.toSpanSingleton_injective ℤ (M.obj.obj (op T)) (LinearMap.ext_ring h2)
  · intro i
    have hhom : (ModuleCat.Hom.hom (M.obj.map (ι i).op)) x =
        (ModuleCat.Hom.hom (M.obj.map (ι i).op)) y := h i
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply_one]
    exact hhom

/-- Two morphisms out of `ℤ[T]` agreeing after pullback along a finite closed cover of `T`
agree.  (Toolkit of `NOTES_LEAD_solid_gaps1.md` §3.4; the covers used by the `ATOM` area are
closed "equalizer sets" of continuous maps.) -/
theorem zmap_ext_of_closed_cover {T : LightProfinite.{0}} {M : LightCondAb}
    (a b : Work.ATOM.zfree T ⟶ M)
    (n : ℕ) (C : Fin n → LightProfinite.{0}) (ι : ∀ i, C i ⟶ T)
    (hcov : ∀ t : T, ∃ i, t ∈ Set.range (ι i))
    (h : ∀ i, Work.ATOM.zmap (ι i) ≫ a = Work.ATOM.zmap (ι i) ≫ b) : a = b := by
  apply (homFreeEquiv T M).injective
  exact eq_of_forall_map_eq_of_jointlySurjective C ι hcov M fun i => by
    rw [← homFreeEquiv_zmap (ι i) M a, ← homFreeEquiv_zmap (ι i) M b, h i]

end

end Work.ATOM
