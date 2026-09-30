import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
import Submission.Work.Pi6.SRANGE.HomQuot
import Submission.Work.Pi6.SRANGE.homQuot_bridge
import Submission.Work.Pi6.SRANGE.intR_map_ker_eq_range
import Submission.Work.Pi6.SRANGE.intR_presentation_bijective
import Submission.Work.Pi6.SRANGE.isIso_homologyMap_baseChangeMap
import Submission.Work.Pi6.SQ.intRPresentationSurjective
import Submission.Work.Pi6.SQ.h2OfHomologySurjective

/-!
# Base change along `ℤ → R` preserves surjectivity of the map on homology in the top degree

Let `f : C ⟶ D` be a chain map of chain complexes of torsion-free `ℤ`-modules which induces
isomorphisms on `Hᵢ` for `i < q` and a surjection on `H_q`.  Then for every commutative ring `R`
the base changed map (extension of scalars along `ℤ → R`) induces a surjection on `H_q`:
`Work.Pi6.SQ.baseChangeSurjective`.

This is the "surjectivity at the top degree" half of the general statement that a map of complexes
of torsion-free `ℤ`-modules which is an isomorphism below degree `q` and onto in degree `q` stays
an isomorphism below `q` (`Work.Pi6.SRANGE.isIso_homologyMap_baseChangeMap`) and stays onto in
degree `q` after extension of scalars.

The proof works with the presentation `Hᵢ = Zᵢ ⧸ Bᵢ` of the homology
(`Work.Pi6.SRANGE.homQuotMap`, `Work.Pi6.SRANGE.cycKer`, `Work.Pi6.SRANGE.cycBnd`), bridged to
the categorical `homologyMap` by `Work.Pi6.SQ.surjective_homologyMap_iff`:

* `Work.Pi6.SQ.h2OfHomologySurjective` converts the surjectivity of `H_q(f)` into the elementwise
  statement that every `q`-cycle of `D` is congruent modulo boundaries to the image of a cycle
  of `C`;
* in degree `q = j + 1`, the presentation in degree `j` — an isomorphism there, hence
  `Work.Pi6.SRANGE.intR_ker_map_bijective` — identifies the defect "cycle modulo boundaries" of
  the base-changed differentials with the failure of exactness of the base change of the degree-`j`
  presentation; surjectivity in degree `q` is then `Work.Pi6.SQ.intRPresentationSurjective`
  (right exactness of `- ⊗[ℤ] R`, no flatness needed) applied to the presentations in degree `q`;
* in degree `q = 0` no lower degree is needed: the `0`-cycles are everything
  (`Work.Pi6.SRANGE.Cyc A 0 = ⊤`) and `H₀` of the base change is `H₀ ⊗ R` by right exactness.

The two independent ingredients of the argument are delegated to
`Submission/Work/Pi6/SQ/intRPresentationSurjective.lean` and
`Submission/Work/Pi6/SQ/h2OfHomologySurjective.lean`.
-/

set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

attribute [local instance 10] AddCommGroup.toIntModule

namespace Work.Pi6.SQ.X2

noncomputable section

/-- **Surjectivity of `Hᵢ` is surjectivity on the concrete model `Zᵢ ⧸ Bᵢ`.** -/
theorem surjective_homologyMap_iff {R : Type} [CommRing R]
    {K L : ChainComplex (ModuleCat.{0} R) ℕ} (h : K ⟶ L) (i : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap h i).hom ↔
      Function.Surjective (Work.Pi6.SRANGE.homQuotMap R h i) := by
  have hkey : ⇑(HomologicalComplex.homologyMap h i) ∘ ⇑(Work.Pi6.SRANGE.homQuotEquiv K i)
      = ⇑(Work.Pi6.SRANGE.homQuotEquiv L i) ∘ ⇑(Work.Pi6.SRANGE.homQuotMap R h i) :=
    funext fun x => Work.Pi6.SRANGE.homQuotEquiv_naturality h i x
  constructor
  · intro hs
    have h1 : Function.Surjective
        (⇑(HomologicalComplex.homologyMap h i) ∘ ⇑(Work.Pi6.SRANGE.homQuotEquiv K i)) :=
      hs.comp (Work.Pi6.SRANGE.homQuotEquiv K i).surjective
    rw [hkey] at h1
    rwa [Function.Surjective.of_comp_iff' (Work.Pi6.SRANGE.homQuotEquiv L i).bijective
      (⇑(Work.Pi6.SRANGE.homQuotMap R h i))] at h1
  · intro hs
    have h1 : Function.Surjective
        (⇑(Work.Pi6.SRANGE.homQuotEquiv L i) ∘ ⇑(Work.Pi6.SRANGE.homQuotMap R h i)) :=
      (Work.Pi6.SRANGE.homQuotEquiv L i).surjective.comp hs
    rw [← hkey] at h1
    rwa [Function.Surjective.of_comp_iff (⇑(HomologicalComplex.homologyMap h i))
      (Work.Pi6.SRANGE.homQuotEquiv K i).surjective] at h1

/-- **Surjectivity on the concrete model.** If every cycle of `L` is congruent modulo
boundaries to the image of a cycle of `K`, then `Hᵢ(h)` is surjective. -/
theorem surjective_homQuotMap_of_forall {R : Type} [CommRing R]
    {K L : ChainComplex (ModuleCat.{0} R) ℕ} (h : K ⟶ L) (i : ℕ)
    (key : ∀ w : ↥(Work.Pi6.SRANGE.cycKer L i), ∃ z : ↥(Work.Pi6.SRANGE.cycKer K i),
      (h.f i).hom (z : ↥(K.X i)) - (w : ↥(L.X i))
        ∈ LinearMap.range ((L.d (i+1) i).hom)) :
    Function.Surjective (Work.Pi6.SRANGE.homQuotMap R h i) := by
  intro c
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective (Work.Pi6.SRANGE.cycBnd L i) c
  obtain ⟨z, hz⟩ := key w
  refine ⟨Submodule.Quotient.mk z, ?_⟩
  rw [Work.Pi6.SRANGE.homQuotMap_mk, Submodule.Quotient.eq]
  exact Submodule.mem_comap.mpr (by simpa [Work.Pi6.SRANGE.restrictMap_apply_val] using hz)

theorem baseChangeSurjective (R : Type) [CommRing R]
    {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : C ⟶ D) (q : ℕ)
    (hC : ∀ i : ℕ, Module.IsTorsionFree ℤ (C.X i))
    (hD : ∀ i : ℕ, Module.IsTorsionFree ℤ (D.X i))
    (hiso : ∀ i : ℕ, i < q → CategoryTheory.IsIso (HomologicalComplex.homologyMap f i))
    (hsurj : Function.Surjective (HomologicalComplex.homologyMap f q).hom) :
    Function.Surjective
      (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.baseChangeMap R f) q).hom := by
  rw [surjective_homologyMap_iff (Work.Pi6.SRANGE.baseChangeMap R f) q]
  have h2q : ∀ w : ↥(Work.Pi6.SRANGE.Cyc D q),
      ∃ w' : ↥(Work.Pi6.SRANGE.Cyc C q), ∃ v : ↥(Work.Pi6.SRANGE.Bdry D q),
        Work.Pi6.SRANGE.cycMap f q w' + Work.Pi6.SRANGE.mum D q v = w :=
    h2OfHomologySurjective f q hsurj
  refine surjective_homQuotMap_of_forall (Work.Pi6.SRANGE.baseChangeMap R f) q ?_
  intro w
  have key : ∃ z : ↥(Work.Pi6.SRANGE.CycR R C q),
      ((Work.Pi6.SRANGE.baseChangeMap R f).f q).hom
          (z : ↥((Work.Pi6.SRANGE.baseChange R C).X q))
        - (w : ↥((Work.Pi6.SRANGE.baseChange R D).X q))
        ∈ LinearMap.range (((Work.Pi6.SRANGE.baseChange R D).d (q+1) q).hom) := by
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · subst hq0
      have htop : ∀ (A : ChainComplex (ModuleCat.{0} ℤ) ℕ), Work.Pi6.SRANGE.Cyc A 0 = ⊤ := by
        intro A
        rw [Work.Pi6.SRANGE.Cyc, show A.d 0 (0-1) = 0 from
          HomologicalComplex.shape A 0 0 (by simp [ComplexShape.down])]
        rw [ModuleCat.hom_zero, LinearMap.ker_zero]
      have hsurjC : Function.Surjective
          (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
            (ModuleCat.ofHom (Work.Pi6.SRANGE.Cyc D 0).subtype))) := by
        haveI : Epi (ModuleCat.ofHom (Work.Pi6.SRANGE.Cyc D 0).subtype) :=
          (ModuleCat.epi_iff_surjective _).mpr fun x =>
            ⟨⟨x, by rw [htop D]; exact Submodule.mem_top⟩, rfl⟩
        exact (ModuleCat.epi_iff_surjective _).mp
          (Functor.map_epi (Work.Pi6.SRANGE.IntR R)
            (ModuleCat.ofHom (Work.Pi6.SRANGE.Cyc D 0).subtype))
      obtain ⟨w₁, hw₁⟩ := hsurjC (w : ↥((Work.Pi6.SRANGE.baseChange R D).X 0))
      have hL4 := intRPresentationSurjective R
        (Work.Pi6.SRANGE.mum C 0) (Work.Pi6.SRANGE.mum D 0)
        (Work.Pi6.SRANGE.bndMapOf f 0) (Work.Pi6.SRANGE.cycMap f 0)
        (Work.Pi6.SRANGE.cycMap_mum f 0) h2q
      obtain ⟨x₁, hx₁⟩ := hL4 w₁
      have hnat := Work.Pi6.SRANGE.cycMap_naturality_apply R f 0 x₁
      refine ⟨⟨ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
          (ModuleCat.ofHom (Work.Pi6.SRANGE.Cyc C 0).subtype)) x₁, ?_⟩, ?_⟩
      · rw [Work.Pi6.SRANGE.CycR, LinearMap.mem_ker]
        rw [show (Work.Pi6.SRANGE.baseChange R C).d 0 (0-1) = 0 from by
          rw [show (Work.Pi6.SRANGE.baseChange R C).d 0 (0-1)
              = (Work.Pi6.SRANGE.IntR R).map (C.d 0 (0-1)) from rfl]
          rw [show C.d 0 (0-1) = 0 from
            HomologicalComplex.shape C 0 0 (by simp [ComplexShape.down])]
          rw [Functor.map_zero]]
        rw [ModuleCat.hom_zero, LinearMap.zero_apply]
      · rw [show (Work.Pi6.SRANGE.baseChangeMap R f).f 0
            = (Work.Pi6.SRANGE.IntR R).map (f.f 0) from rfl]
        rw [hnat]
        rw [← hw₁]
        rw [show (Work.Pi6.SRANGE.baseChange R D).d (0+1) 0
            = (Work.Pi6.SRANGE.IntR R).map (D.d (0+1) 0) from rfl]
        rw [Work.Pi6.SRANGE.intR_d_range R D 0]
        exact Submodule.mem_map.mpr ⟨ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
          (ModuleCat.ofHom (Work.Pi6.SRANGE.cycMap f 0))) x₁ - w₁, hx₁, by rw [map_sub]⟩
    · obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hqpos).symm⟩
      obtain ⟨h1j, h2j⟩ := Work.Pi6.SRANGE.h12_of_bijective f j
        ((Work.Pi6.SRANGE.homQuot_bridge ℤ f j).mp (hiso j (by omega)))
      have hL4 := intRPresentationSurjective R
        (Work.Pi6.SRANGE.mum C (j+1)) (Work.Pi6.SRANGE.mum D (j+1))
        (Work.Pi6.SRANGE.bndMapOf f (j+1)) (Work.Pi6.SRANGE.cycMap f (j+1))
        (Work.Pi6.SRANGE.cycMap_mum f (j+1)) h2q
      have hw1 : ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
            (ModuleCat.ofHom (Work.Pi6.SRANGE.qm D j)))
            (w : ↥((Work.Pi6.SRANGE.baseChange R D).X (j+1)))
          ∈ LinearMap.ker (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
            (ModuleCat.ofHom (Work.Pi6.SRANGE.b2c D j)))) :=
        (Work.Pi6.SRANGE.intR_d_ker_iff R D j hD
          (w : ↥((Work.Pi6.SRANGE.baseChange R D).X (j+1)))).mp w.2
      haveI := hC j
      haveI : Module.IsTorsionFree ℤ ↥(Work.Pi6.SRANGE.Cyc C j) := inferInstance
      haveI := hD j
      haveI : Module.IsTorsionFree ℤ ↥(Work.Pi6.SRANGE.Cyc D j) := inferInstance
      have hL3 := Work.Pi6.SRANGE.intR_ker_map_bijective R
        (Work.Pi6.SRANGE.b2c C j) (Work.Pi6.SRANGE.mum_injective C j)
        (inferInstance : Module.IsTorsionFree ℤ ↥(Work.Pi6.SRANGE.Cyc C j))
        (Work.Pi6.SRANGE.b2c D j) (Work.Pi6.SRANGE.mum_injective D j)
        (inferInstance : Module.IsTorsionFree ℤ ↥(Work.Pi6.SRANGE.Cyc D j))
        (Work.Pi6.SRANGE.bndMapOf f j) (Work.Pi6.SRANGE.cycMap f j)
        (Work.Pi6.SRANGE.cycMap_mum f j) h1j h2j
      obtain ⟨y', hy'1, hy'2⟩ := hL3.2 _ hw1
      haveI : Epi (ModuleCat.ofHom (Work.Pi6.SRANGE.qm C j)) :=
        (ModuleCat.epi_iff_surjective _).mpr (Work.Pi6.SRANGE.qm_surjective C j)
      obtain ⟨x₀, hx₀⟩ := (ModuleCat.epi_iff_surjective _).mp
        (Functor.map_epi (Work.Pi6.SRANGE.IntR R)
          (ModuleCat.ofHom (Work.Pi6.SRANGE.qm C j))) y'
      have hfacC : ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map (C.d (j+1) j))
          = (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
                (ModuleCat.ofHom (Work.Pi6.SRANGE.Cyc C j).subtype))).comp
            ((ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
                (ModuleCat.ofHom (Work.Pi6.SRANGE.b2c C j)))).comp
              (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
                (ModuleCat.ofHom (Work.Pi6.SRANGE.qm C j))))) := by
        rw [Work.Pi6.SRANGE.d_eq_comp' C j, Functor.map_comp, Functor.map_comp,
          ModuleCat.hom_comp, ModuleCat.hom_comp]
        ext x
        rfl
      have hcyc : ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map (C.d (j+1) j)) x₀ = 0 := by
        rw [hfacC, LinearMap.comp_apply, LinearMap.comp_apply, hx₀, hy'1, map_zero]
      have hnatD := Work.Pi6.SRANGE.qm_naturality_apply R f j x₀
      have hstep : ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
            (ModuleCat.ofHom (Work.Pi6.SRANGE.qm D j)))
            (((Work.Pi6.SRANGE.baseChangeMap R f).f (j+1)).hom x₀
              - (w : ↥((Work.Pi6.SRANGE.baseChange R D).X (j+1)))) = 0 := by
        rw [show (Work.Pi6.SRANGE.baseChangeMap R f).f (j+1)
            = (Work.Pi6.SRANGE.IntR R).map (f.f (j+1)) from rfl]
        rw [map_sub, hnatD, hx₀, hy'2, sub_self]
      obtain ⟨w₁, hw₁⟩ := LinearMap.mem_range.mp (by
        rw [← Work.Pi6.SRANGE.intR_qm_ker R D j, LinearMap.mem_ker]
        exact hstep)
      obtain ⟨x₁, hx₁⟩ := hL4 w₁
      have hcyc2 : ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map (C.d (j+1) j))
            (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
              (ModuleCat.ofHom (Work.Pi6.SRANGE.Cyc C (j+1)).subtype)) x₁) = 0 := by
        have hF : (Work.Pi6.SRANGE.IntR R).map (ModuleCat.ofHom
            (Work.Pi6.SRANGE.Cyc C (j+1)).subtype ≫ C.d (j+1) j) = 0 := by
          rw [Work.Pi6.SRANGE.d_comp_cyc C j, Functor.map_zero]
        have h := congrArg (fun (g : (Work.Pi6.SRANGE.IntR R).obj
            (ModuleCat.of ℤ ↥(Work.Pi6.SRANGE.Cyc C (j+1))) ⟶
            (Work.Pi6.SRANGE.IntR R).obj (C.X j)) => ModuleCat.Hom.hom g x₁) hF
        rw [Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_zero,
          LinearMap.zero_apply, LinearMap.comp_apply] at h
        exact h
      have hnat2 := Work.Pi6.SRANGE.cycMap_naturality_apply R f (j+1) x₁
      refine ⟨⟨(x₀ : ↥((Work.Pi6.SRANGE.baseChange R C).X (j+1)))
          - ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
              (ModuleCat.ofHom (Work.Pi6.SRANGE.Cyc C (j+1)).subtype)) x₁, ?_⟩, ?_⟩
      · rw [Work.Pi6.SRANGE.CycR, LinearMap.mem_ker]
        rw [map_sub]
        rw [show ModuleCat.Hom.hom ((Work.Pi6.SRANGE.baseChange R C).d (j+1) (j+1-1)) x₀
            = 0 from hcyc]
        rw [show ModuleCat.Hom.hom ((Work.Pi6.SRANGE.baseChange R C).d (j+1) (j+1-1))
              (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
                (ModuleCat.ofHom (Work.Pi6.SRANGE.Cyc C (j+1)).subtype)) x₁)
            = 0 from hcyc2]
        rw [sub_zero]
      · rw [map_sub]
        rw [show ((Work.Pi6.SRANGE.baseChangeMap R f).f (j+1)).hom
              (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
                (ModuleCat.ofHom (Work.Pi6.SRANGE.Cyc C (j+1)).subtype)) x₁)
            = ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map (f.f (j+1)))
              (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
                (ModuleCat.ofHom (Work.Pi6.SRANGE.Cyc C (j+1)).subtype)) x₁) from rfl]
        rw [hnat2]
        rw [show (Work.Pi6.SRANGE.baseChange R D).d (j+1+1) (j+1)
            = (Work.Pi6.SRANGE.IntR R).map (D.d (j+1+1) (j+1)) from rfl]
        rw [Work.Pi6.SRANGE.intR_d_range R D (j+1)]
        refine Submodule.mem_map.mpr ⟨-(ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR R).map
            (ModuleCat.ofHom (Work.Pi6.SRANGE.cycMap f (j+1)))) x₁ - w₁),
          Submodule.neg_mem _ hx₁, ?_⟩
        rw [map_neg, map_sub, hw₁, neg_sub, sub_right_comm]
  obtain ⟨z, hz⟩ := key
  exact ⟨z, hz⟩

end

end Work.Pi6.SQ.X2
