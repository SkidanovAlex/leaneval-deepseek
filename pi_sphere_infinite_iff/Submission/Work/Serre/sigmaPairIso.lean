import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.sigmaChainsIso
import Submission.Work.Serre.sigmaRelChainsIso
import Submission.Work.Serre.coprodChainAux
import Submission.Work.Serre.sigmaHomologyRat
import Submission.Work.Cohomology.localHomology

/-!
# The relative chain complex of a disjoint union of pairs

The relative singular chain complex (over `ℚ`) of a disjoint union `(Σ i, X i, Σ i, A i)` is the
direct sum of the relative singular chain complexes of the pieces `(X i, A i)`, and the map induced
by a family of maps of pairs corresponds to the coproduct of the individual maps.  This is the
bookkeeping needed to reduce the additivity of relative homology over `ℚ` to the corresponding
statement for the coproduct of chain complexes (`Work.Serre.isIso_homologyMap_sigma`).
-/

set_option maxHeartbeats 1000000

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

variable {ι : Type}

/-! ## Naturality of the coproduct comparison for singular chains -/

theorem csrSigmaIota_map_comm {X Y : ι → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (g : ∀ i, C(X i, Y i)) (j : ι) :
    TopCat.sigmaι (fun i => TopCat.of (X i)) j ≫ sigmaMapTop ι X Y g
      = TopCat.ofHom (g j) ≫ TopCat.sigmaι (fun i => TopCat.of (Y i)) j := by
  ext x
  · rfl
  · exact HEq.rfl

theorem csrSigmaToSSetHom_natural_map {X Y : ι → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (g : ∀ i, C(X i, Y i)) :
    sigmaToSSetHom ι X ≫ TopCat.toSSet.map (sigmaMapTop ι X Y g)
      = Limits.Sigma.map (fun i => TopCat.toSSet.map (TopCat.ofHom (g i))) ≫ sigmaToSSetHom ι Y := by
  apply Limits.Sigma.hom_ext
  intro j
  have hL : Limits.Sigma.ι (fun i => TopCat.toSSet.obj (TopCat.of (X i))) j
        ≫ (sigmaToSSetHom ι X ≫ TopCat.toSSet.map (sigmaMapTop ι X Y g))
      = TopCat.toSSet.map (TopCat.sigmaι (fun i => TopCat.of (X i)) j ≫ sigmaMapTop ι X Y g) := by
    rw [← Category.assoc, sigmaToSSetHom, Limits.Sigma.ι_desc, ← Functor.map_comp]
  have hR : Limits.Sigma.ι (fun i => TopCat.toSSet.obj (TopCat.of (X i))) j
        ≫ (Limits.Sigma.map (fun i => TopCat.toSSet.map (TopCat.ofHom (g i))) ≫ sigmaToSSetHom ι Y)
      = TopCat.toSSet.map (TopCat.ofHom (g j) ≫ TopCat.sigmaι (fun i => TopCat.of (Y i)) j) := by
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, sigmaToSSetHom, Limits.Sigma.ι_desc,
      ← Functor.map_comp]
  rw [hL, hR]
  exact congrArg (fun φ => TopCat.toSSet.map φ) (csrSigmaIota_map_comm g j)

/-- The inverse form of `csrSigmaToSSetHom_natural_map`. -/
theorem csrSigmaToSSetHom_natural_map_inv {X Y : ι → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (g : ∀ i, C(X i, Y i)) :
    (asIso (sigmaToSSetHom ι X)).inv ≫
        Limits.Sigma.map (fun i => TopCat.toSSet.map (TopCat.ofHom (g i)))
      = TopCat.toSSet.map (sigmaMapTop ι X Y g) ≫ (asIso (sigmaToSSetHom ι Y)).inv := by
  rw [Iso.inv_comp_eq, asIso_hom, ← Category.assoc, csrSigmaToSSetHom_natural_map, Category.assoc]
  simp [asIso]

/-- **The core naturality identity** of the comparison map `∐ i, C_*(X i) ← C_*(Σ i, X i)` with
respect to a family of continuous maps, stated purely in terms of the simplicial chain functor. -/
theorem chainSigmaMap_natural_map_core (R : Type) [CommRing R] {X Y : ι → Type}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)] (g : ∀ i, C(X i, Y i)) :
    ((((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
          (asIso (sigmaToSSetHom ι X)).inv ≫
        (asIso (chainCoprodComp R ι (fun i => TopCat.toSSet.obj (TopCat.of (X i))))).inv) ≫
      Limits.Sigma.map (fun i => ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
        (TopCat.toSSet.map (TopCat.ofHom (g i)))))
    = ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
        (TopCat.toSSet.map (sigmaMapTop ι X Y g)) ≫
      (((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
          (asIso (sigmaToSSetHom ι Y)).inv ≫
        (asIso (chainCoprodComp R ι (fun i => TopCat.toSSet.obj (TopCat.of (Y i))))).inv) := by
  rw [Category.assoc, chainCoprodComp_natural_inv, ← Category.assoc, ← Functor.map_comp,
    csrSigmaToSSetHom_natural_map_inv, Functor.map_comp, Category.assoc]

end

end Work.Serre

namespace Work.Serre

noncomputable section

variable {ι : Type}

/-! ## The comparison for a family of subspaces -/

/-- The comparison `C_*(Σ i, A i) ≅ ∐ i, C_*(A i)` transported along the canonical
homeomorphism `Σ i, ↥(A i) ≅ {x : Σ i, X i | x.2 ∈ A x.1}`. -/
noncomputable def csrABaseIso (R : Type) [CommRing R] (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    (A : ∀ i, Set (X i)) :
    Work.Cohomology.singularChains R (TopCat.of {x : Σ i, X i | x.2 ∈ A x.1}) ≅
      ∐ fun i => Work.Cohomology.singularChains R (TopCat.of (↥(A i))) :=
  (((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).mapIso
      (TopCat.toSSet.mapIso (sigmaASHomeo ι X A).symm)) ≪≫
    chainSigmaIso R ι (fun i => ↥(A i))

/-- **The core identity** underlying `csrABaseIso_hom_natural`. -/
theorem csrABaseIso_hom_core (R : Type) [CommRing R] (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    (A : ∀ i, Set (X i)) :
    ((((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
          (asIso (sigmaToSSetHom ι (fun i => ↥(A i)))).inv ≫
        (asIso (chainCoprodComp R ι (fun i => TopCat.toSSet.obj (TopCat.of (↥(A i)))))).inv) ≫
      Limits.Sigma.map (fun i => ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
        (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of (X i)) (A i)))))
    = ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
        (TopCat.toSSet.map (sigmaSubtypeMap ι X A)) ≫
      (((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
        (asIso (sigmaToSSetHom ι X)).inv ≫
      (asIso (chainCoprodComp R ι (fun i => TopCat.toSSet.obj (TopCat.of (X i))))).inv) := by
  rw [Category.assoc, chainCoprodComp_natural_inv, ← Category.assoc, ← Functor.map_comp,
    sigmaToSSetHom_natural_inv, Functor.map_comp, Category.assoc]

/-- **Naturality of `csrABaseIso`** with respect to the inclusions of the subspaces. -/
theorem csrABaseIso_hom_natural (R : Type) [CommRing R] (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (A : ∀ i, Set (X i)) :
    (csrABaseIso R X A).hom ≫
        Limits.Sigma.map (fun i => Work.StemsB.relChainsRIncl R (TopCat.of (X i)) (A i))
      = Work.StemsB.relChainsRIncl R (TopCat.of (Σ i, X i)) {x | x.2 ∈ A x.1}
        ≫ chainSigmaMap R ι X := by
  change ((((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
          (TopCat.toSSet.map (sigmaASHomeo ι X A).inv) ≫
        (((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
            (asIso (sigmaToSSetHom ι (fun i => ↥(A i)))).inv ≫
          (asIso (chainCoprodComp R ι (fun i => TopCat.toSSet.obj (TopCat.of (↥(A i)))))).inv)) ≫
        Limits.Sigma.map (fun i => ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
          (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of (X i)) (A i)))))
    = ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
        (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of (Σ i, X i))
          {x | x.2 ∈ A x.1})) ≫
      (((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
        (asIso (sigmaToSSetHom ι X)).inv ≫
      (asIso (chainCoprodComp R ι (fun i => TopCat.toSSet.obj (TopCat.of (X i))))).inv)
  rw [Category.assoc, csrABaseIso_hom_core, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, sigmaASHomeo_inv_comp]

end

end Work.Serre

namespace Work.Serre

noncomputable section

variable {ι : Type}

/-! ## Cokernels commute with coproducts: a canonical form -/

/-- The canonical isomorphism `cokernel (∐ i, f i) ≅ ∐ i, cokernel (f i)`. -/
def csrCokernelSigmaIso {K L : ι → ChainComplex (ModuleCat ℚ) ℕ} (f : ∀ i, K i ⟶ L i) :
    cokernel (Limits.Sigma.map f) ≅ ∐ fun i => cokernel (f i) where
  hom := cokernel.desc (Limits.Sigma.map f)
    (Limits.Sigma.desc (fun i => cokernel.π (f i) ≫ Limits.Sigma.ι (fun i => cokernel (f i)) i))
    (by
      apply Limits.Sigma.hom_ext
      intro i
      rw [← Category.assoc, Limits.Sigma.ι_map (p := f) i, Category.assoc, Limits.Sigma.ι_desc _ i,
        ← Category.assoc, cokernel.condition, zero_comp, comp_zero])
  inv := Limits.Sigma.desc (fun i => cokernel.desc (f i)
    (Limits.Sigma.ι L i ≫ cokernel.π (Limits.Sigma.map f))
    (by rw [← Limits.Sigma.ι_map_assoc (p := f) i, cokernel.condition, comp_zero]))
  hom_inv_id := by
    apply (cancel_epi (cokernel.π (Limits.Sigma.map f))).mp
    rw [← Category.assoc, cokernel.π_desc, Category.comp_id]
    apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_desc _ i, Category.assoc, Limits.Sigma.ι_desc _ i,
      cokernel.π_desc]
  inv_hom_id := by
    apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_desc _ i, Category.comp_id]
    apply (cancel_epi (cokernel.π (f i))).mp
    rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc,
      Limits.Sigma.ι_desc _ i]

theorem csrCokernelSigmaIso_hom {K L : ι → ChainComplex (ModuleCat ℚ) ℕ} (f : ∀ i, K i ⟶ L i) :
    cokernel.π (Limits.Sigma.map f) ≫ (csrCokernelSigmaIso f).hom
      = Limits.Sigma.desc (fun i => cokernel.π (f i) ≫ Limits.Sigma.ι (fun i => cokernel (f i)) i) :=
  cokernel.π_desc _ _ _

theorem csrCokernelSigmaIso_inv_ι {K L : ι → ChainComplex (ModuleCat ℚ) ℕ} (f : ∀ i, K i ⟶ L i)
    (i : ι) :
    Limits.Sigma.ι (fun i => cokernel (f i)) i ≫ (csrCokernelSigmaIso f).inv
      = cokernel.desc (f i) (Limits.Sigma.ι L i ≫ cokernel.π (Limits.Sigma.map f))
          (by rw [← Limits.Sigma.ι_map_assoc (p := f) i, cokernel.condition, comp_zero]) :=
  Limits.Sigma.ι_desc _ _

end

end Work.Serre

namespace Work.Serre

noncomputable section

variable {ι : Type}

/-- The `by fun_prop`-free form of the map `Sigma.map id g`. -/
theorem csrOfHom_sigmaMapTop_gen {X Y : ι → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (g : ∀ i, C(X i, Y i)) (G : C(Σ i, X i, Σ i, Y i))
    (hG : ∀ x, G x = Sigma.map id (fun i => g i) x) :
    TopCat.ofHom G = sigmaMapTop ι X Y g := by
  apply TopCat.ext
  intro x
  show G x = Sigma.map id (fun i => g i) x
  rw [hG x]

end

end Work.Serre

namespace Work.Serre

noncomputable section

variable {ι : Type}

/-! ## The projection formula for the map induced by a map of pairs -/

/-- **The projection formula** for the map of relative chain complexes induced by a map of pairs. -/
theorem csrRelMapOf_π {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) :
    cokernel.π (Work.StemsB.relChainsRIncl ℚ X A) ≫ csrRelMapOf X Y A B f g w
      = Work.Cohomology.chainMap ℚ X Y f ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ Y B) := by
  rw [Work.Serre.csrRelMapOf]
  exact Work.Cohomology.cokernel_π_map (Work.StemsB.relChainsRIncl ℚ X A)
    (Work.StemsB.relChainsRIncl ℚ Y B)
    (Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) g) _ _

/-- **The projection formula** for `relChainsRPairMap`. -/
theorem csrRelChainsRPairMap_π {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (g : C(X, Y)) (hg : Set.MapsTo g A B) :
    cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) ≫ relChainsRPairMap A B g hg
      = Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom g)
        ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Y) B) := by
  show cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A)
      ≫ Work.Serre.csrRelMapOf (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom g)
          (TopCat.ofHom ⟨fun x => ⟨g x.1, hg x.2⟩, by fun_prop⟩) (by ext x; rfl)
      = Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom g)
        ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Y) B)
  exact csrRelMapOf_π (X := TopCat.of X) (Y := TopCat.of Y) A B (TopCat.ofHom g)
    (TopCat.ofHom ⟨fun x => ⟨g x.1, hg x.2⟩, by fun_prop⟩) (by ext x; rfl)

/-! ## The main square -/

/-- **The relative chain complex of a disjoint union of pairs is the coproduct of the relative chain
complexes of the pieces**, naturally in a family of maps of pairs. -/
theorem relChainsCoproductSquareRat {X Y : ι → Type}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (A : ∀ i, Set (X i)) (B : ∀ i, Set (Y i)) (g : ∀ i, C(X i, Y i))
    (hg : ∀ i, Set.MapsTo (g i) (A i) (B i)) :
    ∃ (eX : Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, X i)) {x | x.2 ∈ A x.1} ≅
          ∐ fun i => Work.StemsB.relChainsR ℚ (TopCat.of (X i)) (A i))
      (eY : Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, Y i)) {y | y.2 ∈ B y.1} ≅
          ∐ fun i => Work.StemsB.relChainsR ℚ (TopCat.of (Y i)) (B i)),
      eX.hom ≫ Limits.Sigma.map (fun i => relChainsRPairMap (A i) (B i) (g i) (hg i))
        = relChainsRPairMap {x : (Σ i, X i) | x.2 ∈ A x.1}
            {y : (Σ i, Y i) | y.2 ∈ B y.1}
            ⟨Sigma.map id (fun i => g i), by fun_prop⟩
            (by rintro ⟨i, x⟩ hx; exact hg i hx) ≫ eY.hom := by
  set hfFam : ∀ i, Work.Cohomology.singularChains ℚ (TopCat.of (↥(A i))) ⟶
      Work.Cohomology.singularChains ℚ (TopCat.of (X i)) :=
    fun i => Work.StemsB.relChainsRIncl ℚ (TopCat.of (X i)) (A i) with hfFam_def
  set hgFam : ∀ i, Work.Cohomology.singularChains ℚ (TopCat.of (↥(B i))) ⟶
      Work.Cohomology.singularChains ℚ (TopCat.of (Y i)) :=
    fun i => Work.StemsB.relChainsRIncl ℚ (TopCat.of (Y i)) (B i) with hgFam_def
  set fX : Work.Cohomology.singularChains ℚ (TopCat.of {x : Σ i, X i | x.2 ∈ A x.1}) ⟶
      Work.Cohomology.singularChains ℚ (TopCat.of (Σ i, X i)) :=
    Work.StemsB.relChainsRIncl ℚ (TopCat.of (Σ i, X i)) {x | x.2 ∈ A x.1} with hfX_def
  set fY : Work.Cohomology.singularChains ℚ (TopCat.of {y : Σ i, Y i | y.2 ∈ B y.1}) ⟶
      Work.Cohomology.singularChains ℚ (TopCat.of (Σ i, Y i)) :=
    Work.StemsB.relChainsRIncl ℚ (TopCat.of (Σ i, Y i)) {y | y.2 ∈ B y.1} with hfY_def
  set sX : Work.Cohomology.singularChains ℚ (TopCat.of (Σ i, X i)) ≅
      ∐ fun i => Work.Cohomology.singularChains ℚ (TopCat.of (X i)) :=
    chainSigmaIso ℚ ι X with hsX
  set sY : Work.Cohomology.singularChains ℚ (TopCat.of (Σ i, Y i)) ≅
      ∐ fun i => Work.Cohomology.singularChains ℚ (TopCat.of (Y i)) :=
    chainSigmaIso ℚ ι Y with hsY
  set sA : Work.Cohomology.singularChains ℚ (TopCat.of {x : Σ i, X i | x.2 ∈ A x.1}) ≅
      ∐ fun i => Work.Cohomology.singularChains ℚ (TopCat.of (↥(A i))) :=
    csrABaseIso ℚ X A with hsA
  set sB : Work.Cohomology.singularChains ℚ (TopCat.of {y : Σ i, Y i | y.2 ∈ B y.1}) ≅
      ∐ fun i => Work.Cohomology.singularChains ℚ (TopCat.of (↥(B i))) :=
    csrABaseIso ℚ Y B with hsB
  have hA : fX ≫ sX.hom = sA.hom ≫ Limits.Sigma.map hfFam := by
    rw [hfX_def, hsX, hsA, hfFam_def]
    exact (csrABaseIso_hom_natural ℚ X A).symm
  have hB : fY ≫ sY.hom = sB.hom ≫ Limits.Sigma.map hgFam := by
    rw [hfY_def, hsY, hsB, hgFam_def]
    exact (csrABaseIso_hom_natural ℚ Y B).symm
  set eX : cokernel fX ≅ ∐ fun i => cokernel (hfFam i) :=
    cokernel.mapIso (f := fX) (f' := Limits.Sigma.map hfFam) (p := sA) (q := sX) (w := hA)
      ≪≫ csrCokernelSigmaIso hfFam with heX
  set eY : cokernel fY ≅ ∐ fun i => cokernel (hgFam i) :=
    cokernel.mapIso (f := fY) (f' := Limits.Sigma.map hgFam) (p := sB) (q := sY) (w := hB)
      ≪≫ csrCokernelSigmaIso hgFam with heY
  set DfX : (∐ fun i => Work.Cohomology.singularChains ℚ (TopCat.of (X i))) ⟶
      ∐ fun i => cokernel (hfFam i) :=
    Limits.Sigma.desc (fun i => cokernel.π (hfFam i) ≫
      Limits.Sigma.ι (fun i => cokernel (hfFam i)) i) with hDfX
  set DfY : (∐ fun i => Work.Cohomology.singularChains ℚ (TopCat.of (Y i))) ⟶
      ∐ fun i => cokernel (hgFam i) :=
    Limits.Sigma.desc (fun i => cokernel.π (hgFam i) ≫
      Limits.Sigma.ι (fun i => cokernel (hgFam i)) i) with hDfY
  have hπX : cokernel.π fX ≫ eX.hom = sX.hom ≫ DfX := by
    rw [heX, Iso.trans_hom, ← Category.assoc, cokernel.mapIso_hom fX (Limits.Sigma.map hfFam)
        sA sX hA,
      Work.Cohomology.cokernel_π_map fX (Limits.Sigma.map hfFam) sA.hom sX.hom hA,
      Category.assoc, csrCokernelSigmaIso_hom, hDfX]
  have hπY : cokernel.π fY ≫ eY.hom = sY.hom ≫ DfY := by
    rw [heY, Iso.trans_hom, ← Category.assoc, cokernel.mapIso_hom fY (Limits.Sigma.map hgFam)
        sB sY hB,
      Work.Cohomology.cokernel_π_map fY (Limits.Sigma.map hgFam) sB.hom sY.hom hB,
      Category.assoc, csrCokernelSigmaIso_hom, hDfY]
  have hpiece : ∀ i, cokernel.π (hfFam i) ≫ relChainsRPairMap (A i) (B i) (g i) (hg i)
      = Work.Cohomology.chainMap ℚ (TopCat.of (X i)) (TopCat.of (Y i)) (TopCat.ofHom (g i))
        ≫ cokernel.π (hgFam i) := by
    intro i
    exact csrRelChainsRPairMap_π (A i) (B i) (g i) (hg i)
  have hPairMap : cokernel.π fX ≫ relChainsRPairMap {x : (Σ i, X i) | x.2 ∈ A x.1}
        {y : (Σ i, Y i) | y.2 ∈ B y.1} ⟨Sigma.map id (fun i => g i), by fun_prop⟩
        (by rintro ⟨i, x⟩ hx; exact hg i hx)
      = Work.Cohomology.chainMap ℚ (TopCat.of (Σ i, X i)) (TopCat.of (Σ i, Y i))
          (TopCat.ofHom ⟨Sigma.map id (fun i => g i), by fun_prop⟩) ≫ cokernel.π fY := by
    exact csrRelChainsRPairMap_π {x : (Σ i, X i) | x.2 ∈ A x.1}
      {y : (Σ i, Y i) | y.2 ∈ B y.1}
      ⟨Sigma.map id (fun i => g i), by fun_prop⟩ (by rintro ⟨i, x⟩ hx; exact hg i hx)
  have hXnat : Work.Cohomology.chainMap ℚ (TopCat.of (Σ i, X i)) (TopCat.of (Σ i, Y i))
        (TopCat.ofHom ⟨Sigma.map id (fun i => g i), by fun_prop⟩) ≫ sY.hom
      = sX.hom ≫ Limits.Sigma.map (fun i => Work.Cohomology.chainMap ℚ (TopCat.of (X i))
          (TopCat.of (Y i)) (TopCat.ofHom (g i))) := by
    rw [hsX, hsY]
    conv_lhs => rw [csrOfHom_sigmaMapTop_gen (X := X) (Y := Y) g _ (fun x => rfl)]
    change (((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map
        (TopCat.toSSet.map (sigmaMapTop ι X Y g)) ≫
      (((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map
          (asIso (sigmaToSSetHom ι Y)).inv ≫
        (asIso (chainCoprodComp ℚ ι (fun i => TopCat.toSSet.obj (TopCat.of (Y i))))).inv))
    = ((((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map
          (asIso (sigmaToSSetHom ι X)).inv ≫
        (asIso (chainCoprodComp ℚ ι (fun i => TopCat.toSSet.obj (TopCat.of (X i))))).inv) ≫
      Limits.Sigma.map (fun i => ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map
        (TopCat.toSSet.map (TopCat.ofHom (g i)))))
    exact (chainSigmaMap_natural_map_core ℚ (X := X) (Y := Y) g).symm
  have key : DfX ≫ Limits.Sigma.map (fun i => relChainsRPairMap (A i) (B i) (g i) (hg i))
      = Limits.Sigma.map (fun i => Work.Cohomology.chainMap ℚ (TopCat.of (X i))
          (TopCat.of (Y i)) (TopCat.ofHom (g i))) ≫ DfY := by
    rw [hDfX, hDfY]
    apply Limits.Sigma.hom_ext
    intro j
    have hL : Limits.Sigma.ι (fun i => Work.Cohomology.singularChains ℚ (TopCat.of (X i))) j
          ≫ (Limits.Sigma.desc (fun i => cokernel.π (hfFam i) ≫
              Limits.Sigma.ι (fun i => cokernel (hfFam i)) i)
            ≫ Limits.Sigma.map (fun i => relChainsRPairMap (A i) (B i) (g i) (hg i)))
        = cokernel.π (hfFam j) ≫ (relChainsRPairMap (A j) (B j) (g j) (hg j)
            ≫ Limits.Sigma.ι (fun i => cokernel (hgFam i)) j) := by
      rw [← Category.assoc, Limits.Sigma.ι_desc, Category.assoc,
        Limits.Sigma.ι_map (p := fun i => relChainsRPairMap (A i) (B i) (g i) (hg i)) j]
    have hR : Limits.Sigma.ι (fun i => Work.Cohomology.singularChains ℚ (TopCat.of (X i))) j
          ≫ (Limits.Sigma.map (fun i => Work.Cohomology.chainMap ℚ (TopCat.of (X i))
              (TopCat.of (Y i)) (TopCat.ofHom (g i)))
            ≫ Limits.Sigma.desc (fun i => cokernel.π (hgFam i) ≫
              Limits.Sigma.ι (fun i => cokernel (hgFam i)) i))
        = Work.Cohomology.chainMap ℚ (TopCat.of (X j)) (TopCat.of (Y j)) (TopCat.ofHom (g j))
            ≫ (cokernel.π (hgFam j) ≫ Limits.Sigma.ι (fun i => cokernel (hgFam i)) j) := by
      rw [← Category.assoc,
        Limits.Sigma.ι_map (p := fun i => Work.Cohomology.chainMap ℚ (TopCat.of (X i))
          (TopCat.of (Y i)) (TopCat.ofHom (g i))) j,
        Category.assoc, Limits.Sigma.ι_desc]
    rw [hL, hR]
    calc cokernel.π (hfFam j) ≫ (relChainsRPairMap (A j) (B j) (g j) (hg j)
            ≫ Limits.Sigma.ι (fun i => cokernel (hgFam i)) j)
        = (cokernel.π (hfFam j) ≫ relChainsRPairMap (A j) (B j) (g j) (hg j))
            ≫ Limits.Sigma.ι (fun i => cokernel (hgFam i)) j := (Category.assoc _ _ _).symm
      _ = (Work.Cohomology.chainMap ℚ (TopCat.of (X j)) (TopCat.of (Y j)) (TopCat.ofHom (g j))
            ≫ cokernel.π (hgFam j)) ≫ Limits.Sigma.ι (fun i => cokernel (hgFam i)) j := by
          rw [hpiece j]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of (X j)) (TopCat.of (Y j)) (TopCat.ofHom (g j))
            ≫ (cokernel.π (hgFam j) ≫ Limits.Sigma.ι (fun i => cokernel (hgFam i)) j) :=
          Category.assoc _ _ _
  refine ⟨eX, eY, ?_⟩
  apply (cancel_epi (cokernel.π fX)).mp
  conv_lhs => rw [← Category.assoc, hπX]
  conv_rhs => rw [← Category.assoc, hPairMap, Category.assoc, hπY]
  rw [Category.assoc]
  conv_rhs => rw [← Category.assoc, hXnat, Category.assoc]
  rw [key]

end

end Work.Serre
