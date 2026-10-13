import Mathlib
import Submission.Work.DSMap.Mix

/-!
# DSMX0U — the finite free model of `RΓ(X, 𝒪)` for a given finite affine cover: definitions

Subproject **DSMX0U** of the `direct_summand` project: it supplies the node `MX0U` of the
MIX2 design, i.e. the statement `DSMap.Mix2.IsFinFreeModelU` for *every* finite affine cover
of a projective scheme over a Noetherian ring.

The content of `MX0U` (design `direct_summand_mix2.md`) is `F1` (the Čech complex of a finite
affine cover computes `RΓ(X, 𝒪_X)`) together with `COH` (its cohomology is finitely generated
and bounded) plus the **pseudo-coherence step**, which is what this area builds:

> a cochain complex `C` of `A`-modules, bounded below and above, with finitely generated
> cohomology, admits a bounded-above complex `P` of finitely generated free `A`-modules with a
> quasi-isomorphism `P ⟶ C`, compatible with a prescribed coaugmentation `A ⟶ C⁰`.

## The construction

Let `C` be a cochain complex of `A`-modules indexed by `ℤ`, and `N : ℤ`.

* A `Spine C j` is the data of a *two-term free presentation of `H^j(C)`*: finitely generated
  free modules `K`, `F`, an injective `ι : K ⟶ F`, a surjection `ρ : F ⟶ H^j(C)` with kernel
  the image of `ι`, and a lift `σ : F ⟶ Z^j(C)` of `ρ` to the cycles of `C`.
* The spine in degree `j` occupies degrees `(j-1, j)` of the model complex: the model is the
  direct sum of the two-term complexes `K j →(ι) F j` placed in degrees `(j-1, j)`, that is

    `(modelComplex d).X i = F i × K (i + 1)`,  `d i (i+1) (x, g) = (ι (i+1) g, 0)`.
* The missing datum is how the relations `K (i+1)` of level `i + 1` sit in the chains of `C` of
  degree `i`: `ModelData.β i : K (i+1) ⟶ C.X i`, with
  `β i ≫ d_C i (i+1) = ι (i+1) ≫ σ (i+1) ≫ iCycles (i+1)`.
* The model chain map is `(x, g) ↦ σ i x + β i g` in degree `i`.  Its cohomology in degree `i`
  is `F i ⧸ im (ι i) ≅ H^i(C)`, so it is a quasi-isomorphism.

`ModelData A C N` additionally requires the spines outside the window `[0, N]` to be zero, which
makes the model bounded above (and is compatible with `H^i(C) = 0` outside the window).

## Proof strategy (for the lemmas of the area)

* **Spines exist** (using `A` Noetherian and `H^j(C)` finitely generated): pick a finitely
  generated free `F₀` with a surjection `p : F₀ ↠ H^j(C)`, let `K₀ = ker p`, pick a finitely
  generated free `K` with a surjection `q : K ↠ K₀`, set `F = K ⊕ F₀` and
  `ι : K ↪ F`, `g ↦ (g, q g)`.  Then `coker ι ≅ H^j(C)`, and one takes `ρ` to be the composite
  `F ↠ coker ι ≅ H^j(C)` — so that `ker ρ = range ι` *exactly*, which is the content of the
  fields `ρ_ι` and `ρ_ker`.  The lift `σ` of `ρ` to the cycles exists because `F` is free and
  `C.cycles j ↠ C.homology j` is surjective; `β i` exists because `K` is free and
  `C.X i ↠ B^{i+1}(C)` is surjective, the target lying in `B^{i+1}(C)` by `ρ_ι` of level `i+1`.
  Outside the window `[0, N]` one takes the zero spine, using `IsZero (C.X j) → IsZero (C.homology j)`.
* **The model is bounded above**: for `i > N` (and `i < -1`) both components of `modelX` are
  `zmod`, and a pair of zero modules is a zero module (`isZero_pairMod`).
* **The model map is a quasi-isomorphism**: compute both sides as concrete modules.  For the
  model, `ker (d i (i+1)) = F i × 0` (using `ι (i+1)` injective) and
  `range (d (i-1) i) = range (ι i) × 0`, so `H^i(P) ≅ F i ⧸ range (ι i)`; the induced map to
  `H^i(C)` is `x ↦ [σ i x]`, which is surjective because `ρ i` is surjective and injective
  because `ker (ρ i) = range (ι i)`.  The relevant API is `ShortComplex.moduleCatLeftHomologyData`
  (`K = LinearMap.ker g`, `H = K ⧸ range (moduleCatToCycles)`), `moduleCatHomologyIso`,
  `ShortComplex.LeftHomologyMapData` with `LeftHomologyMapData.quasiIso_iff`, together with
  `quasiIsoAt_iff` and `quasiIso_iff`.
* **The coaugmentation**: if `a : A ⟶ C⁰` is a cocycle, use `C.homologyπ 0` and the surjectivity
  of `ρ 0` to find `x : F 0` with `ρ 0 x = [a]`; then `σ 0 x - a 1 ∈ B⁰(C) = 0` because
  `C.X (-1) = 0`.  Hence `ε : A ⟶ F 0 × K 1`, `1 ↦ (x, 0)` has `ε ≫ modelMap.f 0 = a` and is a
  cycle.
-/

namespace Work.DSMX0U

open CategoryTheory Limits

set_option linter.style.haveILetI false

universe a

variable (A : Type a) [CommRing A]

/-! ## The zero module and the pair of modules -/

/-- The zero `A`-module, as a concrete object of `ModuleCat`.  Using a concrete representative
makes the instances `IsZero`, `Module.Free`, `Module.Finite` available. -/
abbrev zmod : ModuleCat.{a} A := ModuleCat.of A PUnit

instance : Subsingleton (zmod A) := inferInstance

lemma isZero_zmod : IsZero (zmod A) := ModuleCat.isZero_of_subsingleton _

instance free_zmod : Module.Free A (zmod A) := Module.Free.of_subsingleton A _

instance finite_zmod : Module.Finite A (zmod A) :=
  Module.Finite.of_surjective (0 : (Fin 0 → A) →ₗ[A] ↥(zmod A))
    (fun _ => ⟨0, Subsingleton.elim _ _⟩)

/-- The product `M × N` of two `A`-modules, as an object of `ModuleCat`.  This is a *concrete*
model for the biproduct, chosen so that differentials and chain maps are explicit
`LinearMap`s. -/
abbrev pairMod (M N : ModuleCat.{a} A) : ModuleCat.{a} A := ModuleCat.of A (↥M × ↥N)

instance (M N : ModuleCat.{a} A) [Module.Free A M] [Module.Free A N] :
    Module.Free A (pairMod A M N) := Module.Free.prod A ↥M ↥N

instance (M N : ModuleCat.{a} A) [Module.Finite A M] [Module.Finite A N] :
    Module.Finite A (pairMod A M N) := Module.Finite.prod

instance (M N : ModuleCat.{a} A) [Subsingleton ↥M] [Subsingleton ↥N] :
    Subsingleton (pairMod A M N) := inferInstance

/-- The pair of two zero modules is a zero module. -/
lemma isZero_pairMod (M N : ModuleCat.{a} A) (hM : M = zmod A) (hN : N = zmod A) :
    IsZero (pairMod A M N) := by
  subst hM; subst hN
  exact ModuleCat.isZero_of_subsingleton _

/-! ## Spines and model data -/

/-- **The spine of `C` in degree `j`**: a two-term free presentation `K →(ι) F` of `H^j(C)`,
together with a lift of the presentation to the cycles of `C` in degree `j`. -/
structure Spine (C : CochainComplex (ModuleCat.{a} A) ℤ) (j : ℤ) where
  /-- the module of relations of the presentation of `H^j(C)` (it sits in degree `j - 1` of
  the model) -/
  K : ModuleCat.{a} A
  /-- the module of generators of the presentation of `H^j(C)` (it sits in degree `j` of the
  model) -/
  F : ModuleCat.{a} A
  freeK : Module.Free A K
  finiteK : Module.Finite A K
  freeF : Module.Free A F
  finiteF : Module.Finite A F
  /-- the relations, as a submodule of the generators -/
  ι : K ⟶ F
  ι_injective : Function.Injective ι.hom
  /-- the presentation of the cohomology -/
  ρ : F ⟶ C.homology j
  ρ_surjective : Function.Surjective ρ.hom
  /-- the relations are killed by the presentation -/
  ρ_ι : ∀ k : K, ρ.hom (ι.hom k) = 0
  /-- every element of the kernel of the presentation comes from the relations: the kernel of
  `ρ` is exactly the image of `ι` -/
  ρ_ker : ∀ f : F, ρ.hom f = 0 → ∃ k : K, ι.hom k = f
  /-- a lift of the presentation to the cycles of `C` -/
  σ : F ⟶ C.cycles j
  σ_π : σ ≫ C.homologyπ j = ρ

variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {N : ℤ}

/-- **The model data**: a spine in every degree, a lift `β i : K (i+1) ⟶ C.X i` of the
relations of level `i + 1` to the chains of degree `i`, and the requirement that the spines
outside the window `[0, N]` are zero. -/
structure ModelData (C : CochainComplex (ModuleCat.{a} A) ℤ) (N : ℤ) where
  sp : ∀ j : ℤ, Spine A C j
  /-- the relations of level `i + 1` in the chains of degree `i` -/
  β : ∀ i : ℤ, (sp (i + 1)).K ⟶ C.X i
  β_d : ∀ i : ℤ,
    β i ≫ C.d i (i + 1) = (sp (i + 1)).ι ≫ (sp (i + 1)).σ ≫ C.iCycles (i + 1)
  zeroF : ∀ j : ℤ, (j < 0 ∨ N < j) → (sp j).F = zmod A
  zeroK : ∀ j : ℤ, (j < 0 ∨ N < j) → (sp j).K = zmod A

/-! ## The model complex and the model chain map -/

/-- The degree `i` term of the model: the generators of degree `i` together with the relations
of level `i + 1`. -/
noncomputable abbrev modelX (d : ModelData A C N) (i : ℤ) : ModuleCat.{a} A :=
  pairMod A (d.sp i).F (d.sp (i + 1)).K

lemma modelX_free (d : ModelData A C N) (i : ℤ) : Module.Free A (modelX A d i) := by
  haveI := (d.sp i).freeF
  haveI := (d.sp (i + 1)).freeK
  exact inferInstance

lemma modelX_finite (d : ModelData A C N) (i : ℤ) : Module.Finite A (modelX A d i) := by
  haveI := (d.sp i).finiteF
  haveI := (d.sp (i + 1)).finiteK
  exact inferInstance

lemma modelX_isZero_of_gt (d : ModelData A C N) {i : ℤ} (hi : N < i) : IsZero (modelX A d i) :=
  isZero_pairMod A _ _ (d.zeroF i (Or.inr hi)) (d.zeroK (i + 1) (Or.inr (by omega)))

/-- The differential of the model: `(x, g) ↦ (ι (i+1) g, 0)`. -/
noncomputable def modelD (d : ModelData A C N) (i : ℤ) :
    modelX A d i ⟶ modelX A d (i + 1) :=
  ModuleCat.ofHom
    (LinearMap.prod (M := ↥(d.sp i).F × ↥(d.sp (i + 1)).K) (M₂ := ↥(d.sp (i + 1)).F)
      (M₃ := ↥(d.sp (i + 1 + 1)).K)
      ((d.sp (i + 1)).ι.hom.comp (LinearMap.snd A ↥(d.sp i).F ↥(d.sp (i + 1)).K))
      (0 : ↥(d.sp i).F × ↥(d.sp (i + 1)).K →ₗ[A] ↥(d.sp (i + 1 + 1)).K))

lemma modelD_comp (d : ModelData A C N) (i : ℤ) :
    modelD A d i ≫ modelD A d (i + 1) = 0 := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_comp, modelD, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
  apply LinearMap.ext
  intro p
  obtain ⟨x, g⟩ := p
  simp [LinearMap.prod_apply, Function.prod_apply]

/-- **The model complex**: the direct sum of the two-term complexes `K j → F j` placed in
degrees `(j-1, j)`. -/
noncomputable def modelComplex (d : ModelData A C N) : CochainComplex (ModuleCat.{a} A) ℤ :=
  CochainComplex.of (modelX A d) (modelD A d) (modelD_comp A d)

/-- The degree `i` component of the model chain map: `(x, g) ↦ σ i x + β i g`. -/
noncomputable def modelMapHom (d : ModelData A C N) (i : ℤ) :
    ↥(modelX A d i) →ₗ[A] ↥(C.X i) :=
  LinearMap.coprod (M := ↥(d.sp i).F) (M₂ := ↥(d.sp (i + 1)).K) (M₃ := ↥(C.X i))
    ((d.sp i).σ ≫ C.iCycles i).hom (d.β i).hom

/-- An element of the cycles has zero differential. -/
lemma iCycles_d_apply (i j : ℤ) (x : ↥(C.cycles i)) :
    (C.d i j).hom ((C.iCycles i).hom x) = 0 := by
  have h : (C.iCycles i ≫ C.d i j).hom = (0 : ↥(C.cycles i) →ₗ[A] ↥(C.X j)) := by
    rw [HomologicalComplex.iCycles_d, ModuleCat.hom_zero]
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.zero_apply] using
    congrArg (fun (f : ↥(C.cycles i) →ₗ[A] ↥(C.X j)) => f x) h

/-- The defining property of `β`, evaluated on an element. -/
lemma beta_apply (d : ModelData A C N) (i : ℤ) (g : ↥(d.sp (i + 1)).K) :
    (C.d i (i + 1)).hom ((d.β i).hom g) =
      (C.iCycles (i + 1)).hom ((d.sp (i + 1)).σ.hom ((d.sp (i + 1)).ι.hom g)) := by
  have h : (d.β i ≫ C.d i (i + 1)).hom =
      ((d.sp (i + 1)).ι ≫ (d.sp (i + 1)).σ ≫ C.iCycles (i + 1)).hom := by
    rw [d.β_d i]
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_comp] at h
  simpa only [LinearMap.comp_apply] using
    congrArg (fun (f : ↥(d.sp (i + 1)).K →ₗ[A] ↥(C.X (i + 1))) => f g) h

/-- The model chain map commutes with the differentials: the composite of `σ i` with the
differential of `C` is zero (cycles), and `β i` is a lift of the relations (the `β_d` field). -/
lemma modelMap_comm (d : ModelData A C N) (i : ℤ) :
    ModuleCat.ofHom (modelMapHom A d i) ≫ C.d i (i + 1) =
      modelD A d i ≫ ModuleCat.ofHom (modelMapHom A d (i + 1)) := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_comp, modelD, modelMapHom, ModuleCat.hom_ofHom]
  apply LinearMap.ext
  intro p
  obtain ⟨x, g⟩ := p
  simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply,
    Function.prod_apply, map_add, LinearMap.map_zero]
  rw [iCycles_d_apply, beta_apply]
  simp

/-- **The model chain map** `modelComplex d ⟶ C`. -/
lemma modelComplex_d (d : ModelData A C N) (i : ℤ) :
    (modelComplex A d).d i (i + 1) = modelD A d i :=
  CochainComplex.of_d (modelX A d) (modelD A d) i

noncomputable def modelMap (d : ModelData A C N) : modelComplex A d ⟶ C :=
  CochainComplex.ofHom (fun i => ModuleCat.ofHom (modelMapHom A d i))
    (fun i => by rw [modelComplex_d]; exact modelMap_comm A d i)

end Work.DSMX0U
