import Mathlib
import Submission.Work.Serre.CellStep.Sigma
import Submission.Work.Serre.sigmaToSSetHom_isIso
import Submission.Work.Serre.chainComplexFunctor_preserves_coproduct
import Submission.Work.Serre.cokernel_coproduct_iso
import Submission.Work.Serre.serreC0SigmaHomology
import Submission.Work.Serre.sigmaRelChainsIso
import Submission.Work.StemsB.CellStep.SigmaNat

set_option synthInstance.maxHeartbeats 400000


/-!
# Additivity of relative homology over a disjoint union

The target is `Work.Serre.CellStep.sigmaAdditivity`: the relative singular chain complex of a
disjoint union of pairs is the direct sum of the relative chain complexes of the pieces, and the
map induced by a *family* of maps of pairs is the coproduct of the individual maps, so it is an
isomorphism on `H_m` as soon as every piece map is.

The proof has three parts.

* **Additivity of homology over a coproduct of chain complexes.**  For a family of chain maps
  `f i : K i ⟶ L i`, the canonical map `∐ᵢ Hₙ(Kᵢ) ⟶ Hₙ(∐ᵢ Kᵢ)` induced by the coproduct inclusions
  is an isomorphism (`Work.Serre.sigma_desc_sigmaι_isIso`) and is natural
  (`Work.Serre.CellStep.sigma_desc_homologyMap_natural`); hence `Hₙ(∐ᵢ fᵢ)` is an isomorphism
  whenever the `Hₙ(fᵢ)` are (`Work.Serre.CellStep.isIso_homologyMap_sigma`).
* **Naturality of the decomposition of the relative chains of a disjoint union**
  (`Work.Serre.CellStep.relChainsCoproductSquare`): the canonical identifications of
  `C_*(Σᵢ Xᵢ, Σᵢ Aᵢ)` with `∐ᵢ C_*(Xᵢ, Aᵢ)` can be chosen so that the map of pairs induced by a
  family `gᵢ : (Xᵢ,Aᵢ) → (Yᵢ,Bᵢ)` corresponds to the coproduct of the `gᵢ`.  This uses the
  naturality of `chainSigmaMap` for a general family of maps (`chainSigmaMap_natural_gen`) and the
  fact that cokernels commute with coproducts, with the canonical projection
  (`Work.Serre.CellStep.cokernelSigmaIso`).
* **Assembly** (`Work.Serre.CellStep.sigmaAdditivity`).
-/

set_option backward.isDefEq.respectTransparency false

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.CellStep

noncomputable section

/-! ## Coproduct naturality in the category of `ℤ`-modules -/

/-- Coproduct naturality: `Sigma.map` followed by `Sigma.desc`. -/
theorem sigma_map_desc {ι : Type} {A B : ι → ModuleCat ℤ} {P : ModuleCat ℤ}
    (f : ∀ i, A i ⟶ B i) (g : ∀ i, B i ⟶ P) :
    Limits.Sigma.map f ≫ Limits.Sigma.desc g = Limits.Sigma.desc (fun i => f i ≫ g i) := by
  apply Limits.Sigma.hom_ext
  intro i
  rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_desc,
    Limits.Sigma.ι_desc]

/-- **Cokernels commute with coproducts**, with the canonical projection: there is an isomorphism
`cokernel (∐ᵢ fᵢ) ≅ ∐ᵢ cokernel (fᵢ)` whose composite with `cokernel.π (∐ᵢ fᵢ)` is the coproduct of
the `cokernel.π (fᵢ)`. -/
theorem cokernelSigmaIso {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*}
    [HasCoproductsOfShape ι C] [HasCokernels C] {A B : ι → C} (f : ∀ i, A i ⟶ B i) :
    ∃ (e : cokernel (Limits.Sigma.map f) ≅ ∐ fun i => cokernel (f i)),
      cokernel.π (Limits.Sigma.map f) ≫ e.hom
        = Limits.Sigma.map (fun i => cokernel.π (f i)) := by
  classical
  let F : ι → C := fun i => cokernel (f i)
  have hm (i : ι) : f i ≫ Sigma.ι B i ≫ cokernel.π (Limits.Sigma.map f) = 0 := by
    rw [← Limits.Sigma.ι_map_assoc (p := f) i, cokernel.condition, comp_zero]
  let d : (∐ B) ⟶ (∐ F) := Sigma.desc (fun i => cokernel.π (f i) ≫ Sigma.ι F i)
  have hd : Limits.Sigma.map f ≫ d = 0 := by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_map (p := f) i, Category.assoc, Sigma.ι_desc]
    simp
  let v : cokernel (Limits.Sigma.map f) ⟶ (∐ F) := cokernel.desc (Limits.Sigma.map f) d hd
  let u : (∐ F) ⟶ cokernel (Limits.Sigma.map f) :=
    Sigma.desc (fun i =>
      cokernel.desc (f i) (Sigma.ι B i ≫ cokernel.π (Limits.Sigma.map f)) (hm i))
  have huv : u ≫ v = 𝟙 (∐ F) := by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_desc _ i, Category.comp_id]
    apply (cancel_epi (cokernel.π (f i))).mp
    rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc, Sigma.ι_desc _ i]
  have hvu : v ≫ u = 𝟙 (cokernel (Limits.Sigma.map f)) := by
    apply (cancel_epi (cokernel.π (Limits.Sigma.map f))).mp
    rw [← Category.assoc, cokernel.π_desc, Category.comp_id]
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_desc _ i, Category.assoc, Sigma.ι_desc _ i, cokernel.π_desc]
  refine ⟨{ hom := v, inv := u, hom_inv_id := hvu, inv_hom_id := huv }, ?_⟩
  rw [cokernel.π_desc]
  apply Sigma.hom_ext
  intro i
  rw [Limits.Sigma.ι_map, Sigma.ι_desc]

/-! ## Additivity of homology over a coproduct -/

/-- **Naturality of the comparison map `∐ Hₙ(Kᵢ) ⟶ Hₙ(∐ Kᵢ)`** (the map whose being an
isomorphism is `Work.Serre.sigma_desc_sigmaι_isIso`). -/
theorem sigma_desc_homologyMap_natural {ι : Type} {K L : ι → ChainComplex (ModuleCat ℤ) ℕ}
    (f : ∀ i, K i ⟶ L i) (n : ℕ) :
    Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι K i) n)
        ≫ HomologicalComplex.homologyMap (Limits.Sigma.map f) n
      = Limits.Sigma.map (fun i => HomologicalComplex.homologyMap (f i) n)
        ≫ Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι L i) n) := by
  rw [Work.Serre.sigma_desc_comp, sigma_map_desc]
  congr 1
  funext i
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    Limits.Sigma.ι_map]

/-- **Additivity of homology over a coproduct of chain complexes**: if a family of chain maps
induces isomorphisms on `Hₙ`, then so does the coproduct of the maps. -/
theorem isIso_homologyMap_sigma {ι : Type} {K L : ι → ChainComplex (ModuleCat ℤ) ℕ}
    (f : ∀ i, K i ⟶ L i) (n : ℕ)
    (h : ∀ i, IsIso (HomologicalComplex.homologyMap (f i) n)) :
    IsIso (HomologicalComplex.homologyMap (Limits.Sigma.map f) n) := by
  haveI hK : IsIso (Limits.Sigma.desc
      (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι K i) n)) :=
    Work.Serre.sigma_desc_sigmaι_isIso K n
  haveI hL : IsIso (Limits.Sigma.desc
      (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι L i) n)) :=
    Work.Serre.sigma_desc_sigmaι_isIso L n
  haveI hf : ∀ i, IsIso (HomologicalComplex.homologyMap (f i) n) := h
  haveI hG : IsIso (Limits.Sigma.map (fun i => HomologicalComplex.homologyMap (f i) n)) :=
    Limits.Sigma.map_isIso (fun i => HomologicalComplex.homologyMap (f i) n)
  have hsq := sigma_desc_homologyMap_natural f n
  have hX : HomologicalComplex.homologyMap (Limits.Sigma.map f) n
      = (asIso (Limits.Sigma.desc
            (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι K i) n))).inv
        ≫ (Limits.Sigma.map (fun i => HomologicalComplex.homologyMap (f i) n)
            ≫ Limits.Sigma.desc
                (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι L i) n)) := by
    rw [← hsq]
    exact (Iso.inv_hom_id_assoc (asIso (Limits.Sigma.desc
        (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι K i) n))) _).symm
  rw [hX]
  infer_instance

/-! ## Naturality of `chainSigmaMap` for a general family of maps -/

/-- Naturality of `sigmaToSSetHom` for a general family of maps, in inverse form. -/
theorem sigmaToSSetHom_natural_gen_inv {ι : Type} {X Y : ι → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (f : ∀ i, C(X i, Y i)) :
    (asIso (Work.Serre.sigmaToSSetHom ι X)).inv
        ≫ Limits.Sigma.map (fun i => TopCat.toSSet.map (TopCat.ofHom (f i)))
      = TopCat.toSSet.map (Work.Serre.sigmaMapTop ι X Y f)
        ≫ (asIso (Work.Serre.sigmaToSSetHom ι Y)).inv := by
  rw [Iso.inv_comp_eq, asIso_hom, ← Category.assoc,
    Work.StemsB.CellStep.sigmaToSSetHom_natural_gen ι X Y f, Category.assoc]
  simp [asIso]

/-- **Naturality of `chainSigmaMap` with respect to a family of continuous maps**, in the unfolded
form (mirroring `Work.Serre.chainSigmaMap_natural_core`). -/
theorem chainSigmaMap_natural_gen_core {ι : Type} {X Y : ι → Type}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)] (f : ∀ i, C(X i, Y i)) :
    (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (asIso (Work.Serre.sigmaToSSetHom ι X)).inv ≫
      (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (X i))))).inv) ≫
      Limits.Sigma.map (fun i => ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.toSSet.map (TopCat.ofHom (f i))))
    = ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.toSSet.map (Work.Serre.sigmaMapTop ι X Y f)) ≫
      (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (asIso (Work.Serre.sigmaToSSetHom ι Y)).inv ≫
      (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (Y i))))).inv) := by
  rw [Category.assoc, chainCoprodComp_natural_inv, ← Category.assoc, ← Functor.map_comp,
    sigmaToSSetHom_natural_gen_inv, Functor.map_comp, Category.assoc]

/-- **Naturality of `chainSigmaMap` with respect to a family of continuous maps.** -/
theorem chainSigmaMap_natural_gen {ι : Type} {X Y : ι → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (f : ∀ i, C(X i, Y i)) :
    Work.Serre.chainSigmaMap ℤ ι X ≫ Limits.Sigma.map
        (fun i => Work.Cohomology.chainMap ℤ (TopCat.of (X i)) (TopCat.of (Y i))
          (TopCat.ofHom (f i)))
      = Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, X i)) (TopCat.of (Σ i, Y i))
          (Work.Serre.sigmaMapTop ι X Y f)
        ≫ Work.Serre.chainSigmaMap ℤ ι Y := by
  rw [Work.Serre.chainSigmaMap_eq, Work.Serre.chainSigmaMap_eq]
  change (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (asIso (Work.Serre.sigmaToSSetHom ι X)).inv ≫
      (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (X i))))).inv) ≫
      Limits.Sigma.map (fun i => ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.toSSet.map (TopCat.ofHom (f i))))
    = ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.toSSet.map (Work.Serre.sigmaMapTop ι X Y f)) ≫
      (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (asIso (Work.Serre.sigmaToSSetHom ι Y)).inv ≫
      (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (Y i))))).inv)
  exact chainSigmaMap_natural_gen_core f

/-! ## Naturality of the coproduct decomposition of the relative chains -/

/-- **The relative chain complex of a disjoint union, decomposed compatibly with a family of maps of
pairs.**  There are isomorphisms `C_*(ΣᵢXᵢ, ΣᵢAᵢ) ≅ ∐ᵢ C_*(Xᵢ,Aᵢ)` and
`C_*(ΣᵢYᵢ, ΣᵢBᵢ) ≅ ∐ᵢ C_*(Yᵢ,Bᵢ)` under which the map of pairs induced by a family
`gᵢ : (Xᵢ,Aᵢ) → (Yᵢ,Bᵢ)` corresponds to the coproduct of the `gᵢ`. -/
theorem relChainsCoproductSquare {ι : Type} {X Y : ι → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (A : ∀ i, Set (X i)) (B : ∀ i, Set (Y i))
    (g : ∀ i, C(X i, Y i)) (hg : ∀ i, Set.MapsTo (g i) (A i) (B i)) :
    ∃ (eX : Work.Cohomology.relChains (TopCat.of (Σ i, X i)) {x | x.2 ∈ A x.1} ≅
          ∐ fun i => Work.Cohomology.relChains (TopCat.of (X i)) (A i))
      (eY : Work.Cohomology.relChains (TopCat.of (Σ i, Y i)) {y | y.2 ∈ B y.1} ≅
          ∐ fun i => Work.Cohomology.relChains (TopCat.of (Y i)) (B i)),
      eX.hom ≫ Limits.Sigma.map (fun i => Work.Serre.pairMap (A i) (B i) (g i) (hg i))
        = Work.Serre.sigmaPairMap X Y A B g hg ≫ eY.hom := by
  classical
  haveI hqXi : IsIso (Work.Serre.chainSigmaMap ℤ ι X) :=
    Work.Serre.chainSigmaMap_isIso ℤ ι X
  haveI hqYi : IsIso (Work.Serre.chainSigmaMap ℤ ι Y) :=
    Work.Serre.chainSigmaMap_isIso ℤ ι Y
  let qX : Work.Cohomology.singularChains ℤ (TopCat.of (Σ i, X i)) ≅
      (∐ fun i => Work.Cohomology.singularChains ℤ (TopCat.of (X i))) :=
    asIso (Work.Serre.chainSigmaMap ℤ ι X)
  let qY : Work.Cohomology.singularChains ℤ (TopCat.of (Σ i, Y i)) ≅
      (∐ fun i => Work.Cohomology.singularChains ℤ (TopCat.of (Y i))) :=
    asIso (Work.Serre.chainSigmaMap ℤ ι Y)
  let pX : Work.Cohomology.singularChains ℤ (TopCat.of {x : Σ i, X i | x.2 ∈ A x.1}) ≅
      (∐ fun i => Work.Cohomology.singularChains ℤ (TopCat.of (↥(A i)))) :=
    asIso (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.toSSet.map (Work.Serre.sigmaASHomeo ι X A).inv) ≫
      (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
          (asIso (Work.Serre.sigmaToSSetHom ι (fun i => ↥(A i)))).inv ≫
        (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (↥(A i)))))).inv))
  let pY : Work.Cohomology.singularChains ℤ (TopCat.of {y : Σ i, Y i | y.2 ∈ B y.1}) ≅
      (∐ fun i => Work.Cohomology.singularChains ℤ (TopCat.of (↥(B i)))) :=
    asIso (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.toSSet.map (Work.Serre.sigmaASHomeo ι Y B).inv) ≫
      (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
          (asIso (Work.Serre.sigmaToSSetHom ι (fun i => ↥(B i)))).inv ≫
        (asIso (chainCoprodComp ℤ ι (fun i => TopCat.toSSet.obj (TopCat.of (↥(B i)))))).inv))
  let fA : ∀ i, Work.Cohomology.singularChains ℤ (TopCat.of (↥(A i))) ⟶
      Work.Cohomology.singularChains ℤ (TopCat.of (X i)) :=
    fun i => Work.Cohomology.inclChains (TopCat.of (X i)) (A i)
  let fB : ∀ i, Work.Cohomology.singularChains ℤ (TopCat.of (↥(B i))) ⟶
      Work.Cohomology.singularChains ℤ (TopCat.of (Y i)) :=
    fun i => Work.Cohomology.inclChains (TopCat.of (Y i)) (B i)
  have hsqX : pX.hom ≫ Limits.Sigma.map fA
      = Work.Cohomology.inclChains (TopCat.of (Σ i, X i)) {x | x.2 ∈ A x.1} ≫ qX.hom :=
    Work.Serre.chainSigmaMap_natural ι X A
  have hsqY : pY.hom ≫ Limits.Sigma.map fB
      = Work.Cohomology.inclChains (TopCat.of (Σ i, Y i)) {y | y.2 ∈ B y.1} ≫ qY.hom :=
    Work.Serre.chainSigmaMap_natural ι Y B
  let e1X := cokernel.mapIso (Work.Cohomology.inclChains (TopCat.of (Σ i, X i))
        {x | x.2 ∈ A x.1}) (Limits.Sigma.map fA) pX qX (hsqX.symm)
  let e1Y := cokernel.mapIso (Work.Cohomology.inclChains (TopCat.of (Σ i, Y i))
        {y | y.2 ∈ B y.1}) (Limits.Sigma.map fB) pY qY (hsqY.symm)
  obtain ⟨e2X, he2X⟩ := cokernelSigmaIso
    (A := fun i => Work.Cohomology.singularChains ℤ (TopCat.of (↥(A i))))
    (B := fun i => Work.Cohomology.singularChains ℤ (TopCat.of (X i))) fA
  obtain ⟨e2Y, he2Y⟩ := cokernelSigmaIso
    (A := fun i => Work.Cohomology.singularChains ℤ (TopCat.of (↥(B i))))
    (B := fun i => Work.Cohomology.singularChains ℤ (TopCat.of (Y i))) fB
  let eX := e1X ≪≫ e2X
  let eY := e1Y ≪≫ e2Y
  have he1X : cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, X i))
        {x | x.2 ∈ A x.1}) ≫ e1X.hom
      = qX.hom ≫ cokernel.π (Limits.Sigma.map fA) := by
    dsimp only [e1X]
    rw [cokernel.mapIso_hom, Work.Cohomology.cokernel_π_map]
  have he1Y : cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, Y i))
        {y | y.2 ∈ B y.1}) ≫ e1Y.hom
      = qY.hom ≫ cokernel.π (Limits.Sigma.map fB) := by
    dsimp only [e1Y]
    rw [cokernel.mapIso_hom, Work.Cohomology.cokernel_π_map]
  have hcharX : cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, X i))
        {x | x.2 ∈ A x.1}) ≫ eX.hom
      = qX.hom ≫ Limits.Sigma.map (fun i => cokernel.π (fA i)) := by
    rw [show eX = e1X ≪≫ e2X from rfl, Iso.trans_hom, ← Category.assoc, he1X, Category.assoc, he2X]
  have hcharY : cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, Y i))
        {y | y.2 ∈ B y.1}) ≫ eY.hom
      = qY.hom ≫ Limits.Sigma.map (fun i => cokernel.π (fB i)) := by
    rw [show eY = e1Y ≪≫ e2Y from rfl, Iso.trans_hom, ← Category.assoc, he1Y, Category.assoc, he2Y]
  have hpair (i : ι) : cokernel.π (fA i) ≫ Work.Serre.pairMap (A i) (B i) (g i) (hg i)
      = Work.Cohomology.chainMap ℤ (TopCat.of (X i)) (TopCat.of (Y i)) (TopCat.ofHom (g i))
        ≫ cokernel.π (fB i) := by
    dsimp only [fA, fB]
    unfold Work.Serre.pairMap Work.Cohomology.relChainsMapOf
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  have hsig : cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, X i))
        {x | x.2 ∈ A x.1}) ≫ Work.Serre.sigmaPairMap X Y A B g hg
      = Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, X i)) (TopCat.of (Σ i, Y i))
          (Work.Serre.sigmaMapTop ι X Y g)
        ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, Y i))
            {y | y.2 ∈ B y.1}) := by
    unfold Work.Serre.sigmaPairMap Work.Cohomology.relChainsMapOf
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  have hnat : qX.hom ≫ Limits.Sigma.map
        (fun i => Work.Cohomology.chainMap ℤ (TopCat.of (X i)) (TopCat.of (Y i))
          (TopCat.ofHom (g i)))
      = Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, X i)) (TopCat.of (Σ i, Y i))
          (Work.Serre.sigmaMapTop ι X Y g) ≫ qY.hom := by
    rw [show qX.hom = Work.Serre.chainSigmaMap ℤ ι X from rfl,
      show qY.hom = Work.Serre.chainSigmaMap ℤ ι Y from rfl]
    exact chainSigmaMap_natural_gen g
  have hL : cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, X i)) {x | x.2 ∈ A x.1})
        ≫ (eX.hom ≫ Limits.Sigma.map (fun i => Work.Serre.pairMap (A i) (B i) (g i) (hg i)))
      = Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, X i)) (TopCat.of (Σ i, Y i))
          (Work.Serre.sigmaMapTop ι X Y g)
        ≫ (qY.hom ≫ Limits.Sigma.map (fun i => cokernel.π (fB i))) := by
    calc cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, X i)) {x | x.2 ∈ A x.1})
          ≫ (eX.hom ≫ Limits.Sigma.map (fun i => Work.Serre.pairMap (A i) (B i) (g i) (hg i)))
        = (cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, X i)) {x | x.2 ∈ A x.1})
            ≫ eX.hom)
          ≫ Limits.Sigma.map (fun i => Work.Serre.pairMap (A i) (B i) (g i) (hg i)) :=
          (Category.assoc _ _ _).symm
      _ = (qX.hom ≫ Limits.Sigma.map (fun i => cokernel.π (fA i)))
          ≫ Limits.Sigma.map (fun i => Work.Serre.pairMap (A i) (B i) (g i) (hg i)) := by
          rw [hcharX]
      _ = qX.hom ≫ (Limits.Sigma.map (fun i => cokernel.π (fA i))
          ≫ Limits.Sigma.map (fun i => Work.Serre.pairMap (A i) (B i) (g i) (hg i))) :=
          Category.assoc _ _ _
      _ = qX.hom ≫ Limits.Sigma.map (fun i =>
            cokernel.π (fA i) ≫ Work.Serre.pairMap (A i) (B i) (g i) (hg i)) := by
          rw [Limits.Sigma.map_comp_map]
      _ = qX.hom ≫ Limits.Sigma.map (fun i =>
            Work.Cohomology.chainMap ℤ (TopCat.of (X i)) (TopCat.of (Y i)) (TopCat.ofHom (g i))
              ≫ cokernel.π (fB i)) := by
          rw [show (fun i => cokernel.π (fA i) ≫ Work.Serre.pairMap (A i) (B i) (g i) (hg i))
              = (fun i => Work.Cohomology.chainMap ℤ (TopCat.of (X i)) (TopCat.of (Y i))
                  (TopCat.ofHom (g i)) ≫ cokernel.π (fB i))
              from funext (fun i => hpair i)]
      _ = qX.hom ≫ (Limits.Sigma.map (fun i =>
            Work.Cohomology.chainMap ℤ (TopCat.of (X i)) (TopCat.of (Y i)) (TopCat.ofHom (g i)))
          ≫ Limits.Sigma.map (fun i => cokernel.π (fB i))) := by
          rw [Limits.Sigma.map_comp_map]
      _ = (qX.hom ≫ Limits.Sigma.map (fun i =>
            Work.Cohomology.chainMap ℤ (TopCat.of (X i)) (TopCat.of (Y i)) (TopCat.ofHom (g i))))
          ≫ Limits.Sigma.map (fun i => cokernel.π (fB i)) :=
          (Category.assoc _ _ _).symm
      _ = (Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, X i)) (TopCat.of (Σ i, Y i))
            (Work.Serre.sigmaMapTop ι X Y g) ≫ qY.hom)
          ≫ Limits.Sigma.map (fun i => cokernel.π (fB i)) := by
          rw [hnat]
      _ = Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, X i)) (TopCat.of (Σ i, Y i))
            (Work.Serre.sigmaMapTop ι X Y g)
          ≫ (qY.hom ≫ Limits.Sigma.map (fun i => cokernel.π (fB i))) :=
          Category.assoc _ _ _
  have hR : cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, X i)) {x | x.2 ∈ A x.1})
        ≫ (Work.Serre.sigmaPairMap X Y A B g hg ≫ eY.hom)
      = Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, X i)) (TopCat.of (Σ i, Y i))
          (Work.Serre.sigmaMapTop ι X Y g)
        ≫ (qY.hom ≫ Limits.Sigma.map (fun i => cokernel.π (fB i))) := by
    calc cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, X i)) {x | x.2 ∈ A x.1})
          ≫ (Work.Serre.sigmaPairMap X Y A B g hg ≫ eY.hom)
        = (cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, X i)) {x | x.2 ∈ A x.1})
            ≫ Work.Serre.sigmaPairMap X Y A B g hg) ≫ eY.hom := (Category.assoc _ _ _).symm
      _ = (Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, X i)) (TopCat.of (Σ i, Y i))
            (Work.Serre.sigmaMapTop ι X Y g)
          ≫ cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, Y i))
              {y | y.2 ∈ B y.1})) ≫ eY.hom := by rw [hsig]
      _ = Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, X i)) (TopCat.of (Σ i, Y i))
            (Work.Serre.sigmaMapTop ι X Y g)
          ≫ (cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, Y i))
              {y | y.2 ∈ B y.1}) ≫ eY.hom) := Category.assoc _ _ _
      _ = Work.Cohomology.chainMap ℤ (TopCat.of (Σ i, X i)) (TopCat.of (Σ i, Y i))
            (Work.Serre.sigmaMapTop ι X Y g)
          ≫ (qY.hom ≫ Limits.Sigma.map (fun i => cokernel.π (fB i))) := by
          rw [hcharY]
  refine ⟨eX, eY, ?_⟩
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains (TopCat.of (Σ i, X i))
    {x | x.2 ∈ A x.1}))).mp
  exact hL.trans hR.symm

/-! ## Additivity of relative homology over a disjoint union -/

theorem sigmaAdditivity {ι : Type} {X Y : ι → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (A : ∀ i, Set (X i)) (B : ∀ i, Set (Y i))
    (g : ∀ i, C(X i, Y i)) (hg : ∀ i, Set.MapsTo (g i) (A i) (B i)) (m : ℕ)
    (h : ∀ i, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.pairMap (A i) (B i) (g i) (hg i)) m)) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.sigmaPairMap X Y A B g hg) m) := by
  obtain ⟨eX, eY, hsq⟩ := relChainsCoproductSquare A B g hg
  let pm : ∀ i, Work.Cohomology.relChains (TopCat.of (X i)) (A i) ⟶
      Work.Cohomology.relChains (TopCat.of (Y i)) (B i) :=
    fun i => Work.Serre.pairMap (A i) (B i) (g i) (hg i)
  haveI hadd : IsIso (HomologicalComplex.homologyMap (Limits.Sigma.map pm) m) :=
    isIso_homologyMap_sigma pm m h
  haveI heX : IsIso (HomologicalComplex.homologyMap eX.hom m) :=
    Iso.isIso_hom (HomologicalComplex.homologyMapIso eX m)
  haveI heY : IsIso (HomologicalComplex.homologyMap eY.hom m) :=
    Iso.isIso_hom (HomologicalComplex.homologyMapIso eY m)
  have hsq' : HomologicalComplex.homologyMap eX.hom m
        ≫ HomologicalComplex.homologyMap (Limits.Sigma.map pm) m
      = HomologicalComplex.homologyMap (Work.Serre.sigmaPairMap X Y A B g hg) m
        ≫ HomologicalComplex.homologyMap eY.hom m := by
    calc HomologicalComplex.homologyMap eX.hom m
          ≫ HomologicalComplex.homologyMap (Limits.Sigma.map pm) m
        = HomologicalComplex.homologyMap (eX.hom ≫ Limits.Sigma.map pm) m :=
          (HomologicalComplex.homologyMap_comp eX.hom (Limits.Sigma.map pm) m).symm
      _ = HomologicalComplex.homologyMap
            (Work.Serre.sigmaPairMap X Y A B g hg ≫ eY.hom) m := by rw [hsq]
      _ = HomologicalComplex.homologyMap (Work.Serre.sigmaPairMap X Y A B g hg) m
          ≫ HomologicalComplex.homologyMap eY.hom m :=
          HomologicalComplex.homologyMap_comp (Work.Serre.sigmaPairMap X Y A B g hg) eY.hom m
  haveI hFB : IsIso (HomologicalComplex.homologyMap (Work.Serre.sigmaPairMap X Y A B g hg) m
      ≫ HomologicalComplex.homologyMap eY.hom m) := by
    rw [← hsq']
    infer_instance
  exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap
    (Work.Serre.sigmaPairMap X Y A B g hg) m) (HomologicalComplex.homologyMap eY.hom m)

end

end Work.Serre.CellStep
