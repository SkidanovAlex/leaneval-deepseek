import Mathlib
import Submission.Work.Serre.CellStep.Defs
import Submission.Work.Serre.CellStep.Tools
import Submission.Work.Serre.CellStep.Model
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.StemsB.SphLoopRelPair
import Submission.Work.Serre.E2dEngine

set_option synthInstance.maxHeartbeats 400000


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.CellStep

noncomputable section

open Work.Cohomology Work.RatHurewicz Work.Serre

/-! ## 1. Infrastructure: maps of relative chain complexes

The whole reduction is a chain of commuting squares of maps of relative chain complexes.  The maps
are induced by maps of pairs; here are the two facts about them that the assembly uses:
composition (`Work.Cohomology.relChainsMapOf_comp` is for the presentation with an explicit map on
the relative parts, `relChainsMapOfStems_comp` for `Work.StemsB.relChainsMapOf`), and uniqueness
(two such maps with the same underlying map of total spaces agree).
-/

theorem chainMap_id_self (X : TopCat) :
    chainMap ℤ X X (𝟙 X) = 𝟙 (singularChains ℤ X) :=
  show ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      (𝟙 X) = 𝟙 _ from CategoryTheory.Functor.map_id _ X

/-- **Composition of maps of relative chain complexes** in the `Work.StemsB.relChainsMapOf`
presentation. -/
theorem relChainsMapOfStems_comp {X Y Z : TopCat} {A : Set X} {B : Set Y} {C : Set Z}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : ∀ x, x ∈ A → f x ∈ B) (hg : ∀ y, y ∈ B → g y ∈ C) :
    Work.StemsB.relChainsMapOf f A B hf ≫ Work.StemsB.relChainsMapOf g B C hg
      = Work.StemsB.relChainsMapOf (f ≫ g) A C (fun x hx => hg (f x) (hf x hx)) := by
  apply (cancel_epi (cokernel.π (inclChains X A))).1
  calc cokernel.π (inclChains X A)
        ≫ (Work.StemsB.relChainsMapOf f A B hf ≫ Work.StemsB.relChainsMapOf g B C hg)
      = (cokernel.π (inclChains X A) ≫ Work.StemsB.relChainsMapOf f A B hf)
          ≫ Work.StemsB.relChainsMapOf g B C hg := (Category.assoc _ _ _).symm
    _ = (chainMap ℤ X Y f ≫ cokernel.π (inclChains Y B))
          ≫ Work.StemsB.relChainsMapOf g B C hg := by
          rw [Work.StemsB.π_comp_relChainsMapOf]
    _ = chainMap ℤ X Y f
          ≫ (cokernel.π (inclChains Y B) ≫ Work.StemsB.relChainsMapOf g B C hg) :=
          Category.assoc _ _ _
    _ = chainMap ℤ X Y f ≫ (chainMap ℤ Y Z g ≫ cokernel.π (inclChains Z C)) := by
          rw [Work.StemsB.π_comp_relChainsMapOf]
    _ = (chainMap ℤ X Y f ≫ chainMap ℤ Y Z g) ≫ cokernel.π (inclChains Z C) :=
          (Category.assoc _ _ _).symm
    _ = chainMap ℤ X Z (f ≫ g) ≫ cokernel.π (inclChains Z C) := by
          rw [Work.StemsB.chainMap_comp]
    _ = cokernel.π (inclChains X A)
          ≫ Work.StemsB.relChainsMapOf (f ≫ g) A C (fun x hx => hg (f x) (hf x hx)) :=
          (Work.StemsB.π_comp_relChainsMapOf (f ≫ g) A C _).symm

/-- The defining equation of `Work.Cohomology.relChainsMapOf` on the cokernel projections. -/
theorem pi_comp_relChainsMapOfCo {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B) (w : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B) :
    cokernel.π (inclChains X A) ≫ Work.Cohomology.relChainsMapOf X Y A B f g w
      = chainMap ℤ X Y f ≫ cokernel.π (inclChains Y B) := by
  rw [Work.Cohomology.relChainsMapOf]
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- Two `Work.Cohomology.relChainsMapOf`s with the same underlying map of total spaces agree. -/
theorem relChainsMapOf_congrStems {X Y : TopCat} (A : Set X) (B : Set Y) {f : X ⟶ Y}
    {g₁ g₂ : TopCat.of A ⟶ TopCat.of B}
    (w₁ : subtypeIncl X A ≫ f = g₁ ≫ subtypeIncl Y B)
    (w₂ : subtypeIncl X A ≫ f = g₂ ≫ subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f g₁ w₁
      = Work.Cohomology.relChainsMapOf X Y A B f g₂ w₂ := by
  apply (cancel_epi (cokernel.π (inclChains X A))).1
  rw [pi_comp_relChainsMapOfCo, pi_comp_relChainsMapOfCo]

/-- Two `Work.Cohomology.relChainsMapOf`s with the same underlying data agree. -/
theorem relChainsMapOf_congrAll {X Y : TopCat} (A : Set X) (B : Set Y) {f₁ f₂ : X ⟶ Y}
    (hf : f₁ = f₂) {g₁ g₂ : TopCat.of A ⟶ TopCat.of B}
    (w₁ : subtypeIncl X A ≫ f₁ = g₁ ≫ subtypeIncl Y B)
    (w₂ : subtypeIncl X A ≫ f₂ = g₂ ≫ subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f₁ g₁ w₁
      = Work.Cohomology.relChainsMapOf X Y A B f₂ g₂ w₂ := by
  subst hf
  exact relChainsMapOf_congrStems A B w₁ w₂

/-- **Uniqueness**: a map of relative chain complexes which behaves like `relChainsMapOf f` on the
cokernel projections is `Work.StemsB.relChainsMapOf f`. -/
theorem relChainsMapOf_unique {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (hf : ∀ x, x ∈ A → f x ∈ B) {φ : relChains X A ⟶ relChains Y B}
    (hφ : cokernel.π (inclChains X A) ≫ φ = chainMap ℤ X Y f ≫ cokernel.π (inclChains Y B)) :
    φ = Work.StemsB.relChainsMapOf f A B hf := by
  symm
  apply (cancel_epi (cokernel.π (inclChains X A))).1
  rw [Work.StemsB.π_comp_relChainsMapOf]
  exact hφ.symm

/-- `relCokerMap` is `Work.StemsB.relChainsMapOf` of the identity. -/
theorem relCokerMap_eq_idMap (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    relCokerMap X A B hAB = Work.StemsB.relChainsMapOf (𝟙 X) A B (fun x hx => hAB hx) := by
  apply (cancel_epi (cokernel.π (inclChains X A))).1
  rw [relCokerMap_comp_π, Work.StemsB.π_comp_relChainsMapOf, chainMap_id_self, Category.id_comp]

/-- **Transfer along a commuting square of chain complexes.**  If the horizontal maps of
`h ≫ v = u ≫ g` are quasi-isomorphisms in degree `k`, then `u` and `v` are isomorphisms on `H_k` at
the same time. -/
theorem isIso_homologyMap_of_square {C₁ C₂ B₁ B₂ : ChainComplex (ModuleCat ℤ) ℕ}
    (h : C₁ ⟶ C₂) (g : B₁ ⟶ B₂) (u : C₁ ⟶ B₁) (v : C₂ ⟶ B₂)
    (hsq : h ≫ v = u ≫ g) (k : ℕ)
    (hh : IsIso (HomologicalComplex.homologyMap h k))
    (hg : IsIso (HomologicalComplex.homologyMap g k))
    (hu : IsIso (HomologicalComplex.homologyMap u k)) :
    IsIso (HomologicalComplex.homologyMap v k) := by
  haveI := hh
  haveI := hg
  haveI := hu
  have hw : HomologicalComplex.homologyMap h k ≫ HomologicalComplex.homologyMap v k
      = HomologicalComplex.homologyMap u k ≫ HomologicalComplex.homologyMap g k := by
    rw [← HomologicalComplex.homologyMap_comp, hsq, HomologicalComplex.homologyMap_comp]
  have hα : HomologicalComplex.homologyMap v k
      = inv (HomologicalComplex.homologyMap h k)
        ≫ (HomologicalComplex.homologyMap u k ≫ HomologicalComplex.homologyMap g k) := by
    calc HomologicalComplex.homologyMap v k
        = 𝟙 _ ≫ HomologicalComplex.homologyMap v k := (Category.id_comp _).symm
      _ = (inv (HomologicalComplex.homologyMap h k) ≫ HomologicalComplex.homologyMap h k)
            ≫ HomologicalComplex.homologyMap v k := by
          rw [IsIso.inv_hom_id, Category.id_comp]
      _ = inv (HomologicalComplex.homologyMap h k)
            ≫ (HomologicalComplex.homologyMap h k ≫ HomologicalComplex.homologyMap v k) :=
          Category.assoc _ _ _
      _ = inv (HomologicalComplex.homologyMap h k)
            ≫ (HomologicalComplex.homologyMap u k ≫ HomologicalComplex.homologyMap g k) := by
          rw [hw]
  rw [hα]
  infer_instance

/-! ## 2. The nodes of the reduction

The reduction compares the model per-cell map `csModelMap n p τ` (over the open ball `csB`, relative
part the shell `csSh`) with the disc pair map `discPairMap n p τ` (over the closed cell, relative
part the boundary sphere).  The intermediate nodes are the maps of pairs induced by the projection
`τ^*E → D^{n+2}` over the same total space, with the relative parts
`csSh ⊇ csS ⊆ csQ ⊇ cellSphereSet`.
-/

variable {n : ℕ} {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The total space of the pullback `τ^*E`. -/
abbrev Pb (p : C(E, B)) (τ : C(cellDisk n, B)) : TopCat := TopCat.of (Work.StemsB.Pullback p τ)

/-- The model cell, as a space. -/
abbrev Dc (n : ℕ) : TopCat := TopCat.of (Work.RatHurewicz.cellDisk n)

/-- The preimage in the pullback of a subset of the model cell. -/
abbrev Tp (p : C(E, B)) (τ : C(cellDisk n, B)) (S : Set (cellDisk n)) :
    Set (Work.StemsB.Pullback p τ) := Work.Serre.discPre n p τ S

/-- The projection `τ^*E → D^{n+2}`, restricted to `↥(Tp S)`. -/
def projD (p : C(E, B)) (τ : C(cellDisk n, B)) (S : Set (cellDisk n)) :
    TopCat.of ↥(Tp p τ S) ⟶ Dc n :=
  TopCat.ofHom ⟨fun x => Work.StemsB.pullbackSnd p τ x.1,
    (Work.StemsB.pullbackSnd p τ).continuous.comp continuous_subtype_val⟩

/-- The relative part `csSh` inside the model pair, as a subset of `↥(Tp (csB))`. -/
abbrev SrcRel (p : C(E, B)) (τ : C(cellDisk n, B)) :
    Set ↥(Tp p τ (csB (n := n))) :=
  {x : ↥(Tp p τ (csB (n := n))) | (x : Work.StemsB.Pullback p τ) ∈ Tp p τ (csSh (n := n))}

/-- `Pa₀'`: the model pair map with the base enlarged to the closed cell. -/
def Pa0' (p : C(E, B)) (τ : C(cellDisk n, B)) :
    relChains (TopCat.of ↥(Tp p τ (csB (n := n)))) (SrcRel p τ)
      ⟶ relChains (Dc n) (csSh (n := n)) :=
  Work.StemsB.relChainsMapOf (projD p τ (csB (n := n))) (SrcRel p τ) (csSh (n := n))
    (fun _ hx => hx)

/-- `Pa₁`: the map of pairs `(P, T csSh) → (D, csSh)`. -/
def Pa1 (p : C(E, B)) (τ : C(cellDisk n, B)) :
    relChains (Pb p τ) (Tp p τ (csSh (n := n))) ⟶ relChains (Dc n) (csSh (n := n)) :=
  Work.StemsB.relChainsMapOf (TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
    (Tp p τ (csSh (n := n))) (csSh (n := n)) (fun _ hx => hx)

/-- `Pa₂`: the map of pairs `(P, T csS) → (D, csS)`. -/
def Pa2 (p : C(E, B)) (τ : C(cellDisk n, B)) :
    relChains (Pb p τ) (Tp p τ (csS (n := n))) ⟶ relChains (Dc n) (csS (n := n)) :=
  Work.StemsB.relChainsMapOf (TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
    (Tp p τ (csS (n := n))) (csS (n := n)) (fun _ hx => hx)

/-- `Pa₃`: the map of pairs `(P, T csQ) → (D, csQ)`. -/
def Pa3 (p : C(E, B)) (τ : C(cellDisk n, B)) :
    relChains (Pb p τ) (Tp p τ (csQ (n := n))) ⟶ relChains (Dc n) (csQ (n := n)) :=
  Work.StemsB.relChainsMapOf (TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
    (Tp p τ (csQ (n := n))) (csQ (n := n)) (fun _ hx => hx)

/-- `Pa₄`: the disc pair map `(P, T S^{n+1}) → (D^{n+2}, S^{n+1})`. -/
abbrev Pa4 (p : C(E, B)) (τ : C(cellDisk n, B)) :
    relChains (Pb p τ) (Tp p τ (cellSphereSet n)) ⟶ relChains (Dc n) (cellSphereSet n) :=
  Work.Serre.discPairMap n p τ

/-! ## 3. The two presentations of a map of pairs -/

/-- Two `Work.StemsB.relChainsMapOf`s with equal underlying maps agree. -/
theorem relChainsMapOfStems_congr {X Y : TopCat} {A : Set X} {B : Set Y} {f₁ f₂ : X ⟶ Y}
    (hf : f₁ = f₂) (h₁ : ∀ x, x ∈ A → f₁ x ∈ B) (h₂ : ∀ x, x ∈ A → f₂ x ∈ B) :
    Work.StemsB.relChainsMapOf f₁ A B h₁ = Work.StemsB.relChainsMapOf f₂ A B h₂ := by
  subst hf
  rfl

/-- As `relChainsMapOfStems_congr`, with the two membership proofs left implicit. -/
theorem relChainsMapOfStems_congr' {X Y : TopCat} {A : Set X} {B : Set Y} {f₁ f₂ : X ⟶ Y}
    (hf : f₁ = f₂)
    {h₁ : ∀ x, x ∈ A → f₁ x ∈ B} {h₂ : ∀ x, x ∈ A → f₂ x ∈ B} :
    Work.StemsB.relChainsMapOf f₁ A B h₁ = Work.StemsB.relChainsMapOf f₂ A B h₂ := by
  subst hf
  rfl

/-- The `Work.StemsB.relChainsMapOf` presentation unfolds to the `Work.Cohomology.relChainsMapOf`
one with the canonical maps on the relative parts. -/
theorem stems_eq_cohom {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (hf : ∀ x, x ∈ A → f x ∈ B) :
    Work.StemsB.relChainsMapOf f A B hf
      = Work.Cohomology.relChainsMapOf X Y A B f (Work.StemsB.pairRestrict f A B hf)
          (Work.StemsB.pairRestrict_comp_subtypeIncl f A B hf).symm := by
  apply (cancel_epi (cokernel.π (inclChains X A))).1
  rw [Work.StemsB.π_comp_relChainsMapOf, pi_comp_relChainsMapOfCo]

/-- The base relative part: the shell `csSh` inside the open ball `csB`. -/
abbrev TrSh (n : ℕ) : Set ↥(csB (n := n)) :=
  {x : ↥(csB (n := n)) | (x : cellDisk n) ∈ csSh (n := n)}

/-- The restricted projection `↥(Tp (csB)) → ↥csB`. -/
def projB (p : C(E, B)) (τ : C(cellDisk n, B)) :
    TopCat.of ↥(Tp p τ (csB (n := n))) ⟶ TopCat.of ↥(csB (n := n)) :=
  TopCat.ofHom ⟨fun x => ⟨Work.StemsB.pullbackSnd p τ x.1, x.2⟩,
    Continuous.subtype_mk ((Work.StemsB.pullbackSnd p τ).continuous.comp continuous_subtype_val)
      (fun x => x.2)⟩

/-- **The model map in the `Work.StemsB.relChainsMapOf` presentation.** -/
theorem csModelMap_eq_stems (p : C(E, B)) (τ : C(cellDisk n, B)) :
    Work.Serre.csModelMap n p τ
      = Work.StemsB.relChainsMapOf (projB p τ) (SrcRel p τ) (TrSh n) (fun _ hx => hx) := by
  rw [Work.Serre.csModelMap, stems_eq_cohom]
  exact relChainsMapOf_congrStems _ _ _ _

/-- **The disc pair map in the `Work.StemsB.relChainsMapOf` presentation.** -/
theorem discPairMap_eq_stems (p : C(E, B)) (τ : C(cellDisk n, B)) :
    Work.Serre.discPairMap n p τ
      = Work.StemsB.relChainsMapOf (TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
          (Tp p τ (cellSphereSet n)) (cellSphereSet n) (fun _ hx => hx) := by
  rw [Work.Serre.discPairMap, stems_eq_cohom]
  exact relChainsMapOf_congrStems _ _ _ _

/-- **The honest inclusion of pairs in the `Work.StemsB.relChainsMapOf` presentation.** -/
theorem relChainsMap_eq_stems {X : TopCat} (U A : Set X) :
    relChainsMap X U A
      = Work.StemsB.relChainsMapOf (subtypeIncl X U) {y : U | (y : X) ∈ A} A (fun _ hx => hx) := by
  rw [relChainsMap, stems_eq_cohom]
  exact relChainsMapOf_congrStems _ _ _ _

/-! ## 4. The five commuting squares -/

variable (p : C(E, B)) (τ : C(cellDisk n, B))

/-- **Square 1** (enlarging the base from the open ball to the closed cell). -/
theorem square1 :
    Pa0' p τ = Work.Serre.csModelMap n p τ ≫ relChainsMap (Dc n) (csB (n := n)) (csSh (n := n)) := by
  rw [Pa0', csModelMap_eq_stems, relChainsMap_eq_stems, relChainsMapOfStems_comp]
  exact relChainsMapOfStems_congr' (f₁ := projD p τ (csB (n := n)))
    (f₂ := projB p τ ≫ subtypeIncl (Dc n) (csB (n := n))) (by ext x; rfl)

/-- **Square 2** (enlarging the total space from the tube over the open ball to the pullback). -/
theorem square2 :
    relChainsMap (Pb p τ) (Tp p τ (csB (n := n))) (Tp p τ (csSh (n := n))) ≫ Pa1 p τ
      = Pa0' p τ ≫ 𝟙 (relChains (Dc n) (csSh (n := n))) := by
  rw [Category.comp_id, Pa0', Pa1, relChainsMap_eq_stems, relChainsMapOfStems_comp]
  exact relChainsMapOfStems_congr'
    (f₁ := subtypeIncl (Pb p τ) (Tp p τ (csB (n := n))) ≫ TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
    (f₂ := projD p τ (csB (n := n))) (by ext x; rfl)

/-- **Square 3** (shrinking the relative part from the shell to the middle sphere). -/
theorem square3 :
    relCokerMap (Pb p τ) (Tp p τ (csS (n := n))) (Tp p τ (csSh (n := n)))
        (fun x hx => csS_subset_csSh (n := n) hx) ≫ Pa1 p τ
      = Pa2 p τ ≫ relCokerMap (Dc n) (csS (n := n)) (csSh (n := n))
          (csS_subset_csSh (n := n)) := by
  rw [relCokerMap_eq_idMap, relCokerMap_eq_idMap, Pa1, Pa2, relChainsMapOfStems_comp,
    relChainsMapOfStems_comp]
  exact relChainsMapOfStems_congr'
    (f₁ := 𝟙 (Pb p τ) ≫ TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
    (f₂ := TopCat.ofHom (Work.StemsB.pullbackSnd p τ) ≫ 𝟙 (Dc n))
    (by rw [Category.id_comp, Category.comp_id])

/-- **Square 4** (enlarging the relative part from the middle sphere to the closed shell). -/
theorem square4 :
    relCokerMap (Pb p τ) (Tp p τ (csS (n := n))) (Tp p τ (csQ (n := n)))
        (fun x hx => csS_subset_csQ (n := n) hx) ≫ Pa3 p τ
      = Pa2 p τ ≫ relCokerMap (Dc n) (csS (n := n)) (csQ (n := n))
          (csS_subset_csQ (n := n)) := by
  rw [relCokerMap_eq_idMap, relCokerMap_eq_idMap, Pa2, Pa3, relChainsMapOfStems_comp,
    relChainsMapOfStems_comp]
  exact relChainsMapOfStems_congr'
    (f₁ := 𝟙 (Pb p τ) ≫ TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
    (f₂ := TopCat.ofHom (Work.StemsB.pullbackSnd p τ) ≫ 𝟙 (Dc n))
    (by rw [Category.id_comp, Category.comp_id])

/-- **Square 5** (shrinking the relative part from the closed shell to the boundary sphere). -/
theorem square5 :
    relCokerMap (Pb p τ) (Tp p τ (cellSphereSet n)) (Tp p τ (csQ (n := n)))
        (fun x hx => cellSphereSet_subset_csQ (n := n) hx) ≫ Pa3 p τ
      = Work.Serre.discPairMap n p τ ≫ relCokerMap (Dc n) (cellSphereSet n) (csQ (n := n))
          (cellSphereSet_subset_csQ (n := n)) := by
  rw [relCokerMap_eq_idMap, relCokerMap_eq_idMap, Pa3, discPairMap_eq_stems,
    relChainsMapOfStems_comp, relChainsMapOfStems_comp]
  exact relChainsMapOfStems_congr'
    (f₁ := 𝟙 (Pb p τ) ≫ TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
    (f₂ := TopCat.ofHom (Work.StemsB.pullbackSnd p τ) ≫ 𝟙 (Dc n))
    (by rw [Category.id_comp, Category.comp_id])

/-! ## 5. Acyclicity and the quasi-isomorphisms of the horizontal maps -/

/-- The total-side relative chains of the preimage of a pair of base subsets. -/
abbrev TotRel (p : C(E, B)) (τ : C(cellDisk n, B)) (W₀ W : Set (cellDisk n)) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  relChains (TopCat.of ↥(Tp p τ W))
    {x : ↥(Tp p τ W) | (x : Work.StemsB.Pullback p τ) ∈ Tp p τ W₀}

/-- The base-side relative chains of a pair of subsets. -/
abbrev BsRel (W₀ W : Set (cellDisk n)) : ChainComplex (ModuleCat ℤ) ℕ :=
  relChains (TopCat.of ↥W) {x : ↥W | (x : cellDisk n) ∈ W₀}

/-- **The vanishing of the relative homology of a lifted pair** from the compression of the base
pair (the E2(b) engine). -/
theorem isZero_TotRel (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(cellDisk n, B)) {W₀ W : Set (cellDisk n)} (hW : W₀ ⊆ W)
    (hc : ∀ d, Work.RatHurewicz.CompressRel ↥W {x : ↥W | (x : cellDisk n) ∈ W₀} d) (k : ℕ) :
    IsZero ((TotRel p τ W₀ W).homology k) :=
  Work.Serre.isZero_relChains_preimage_of_base_compress (Work.StemsB.pullbackSnd p τ)
    (fun m => Work.StemsB.hasHLP_pullback p τ (hp m)) W₀ W hW hc k

/-- **The vanishing of the relative homology of a pair of subsets** from its compression. -/
theorem isZero_BsRel {W₀ W : Set (cellDisk n)}
    (hc : ∀ d, Work.RatHurewicz.CompressRel ↥W {x : ↥W | (x : cellDisk n) ∈ W₀} d) (k : ℕ) :
    IsZero ((BsRel W₀ W).homology k) :=
  Work.Serre.isZero_relChains_of_compress hc k

/-- The canonical homeomorphism `↥A ≃ₜ ↥{y : ↥B | (y : X) ∈ A}` for `A ⊆ B ⊆ X`. -/
def subSetHomeo' {X : TopCat} {A B : Set X} (h : A ⊆ B) :
    ↥A ≃ₜ ↥{y : ↥B | (y : X) ∈ A} where
  toFun a := ⟨⟨(a : X), h a.2⟩, a.2⟩
  invFun b := ⟨(b.1 : X), b.2⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv b := by apply Subtype.ext; apply Subtype.ext; rfl
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val (fun a => h a.2)) (fun a => a.2)
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun b => b.2)

/-- The square of `inclChainsSub` with the canonical homeomorphism of the relative parts, in the
form consumed by `cokernel.mapIso`. -/
theorem inclChainsSub_eq_mapIso_comp' {X : TopCat} {A B : Set X} (h : A ⊆ B) :
    inclChainsSub X A B h ≫ (Iso.refl (singularChains ℤ (TopCat.of ↥B))).hom
      = (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo (subSetHomeo' h))).hom
        ≫ inclChains (TopCat.of ↥B) {y : ↥B | (y : X) ∈ A} := by
  rw [Iso.refl_hom, Category.comp_id]
  have hmap : (TopCat.isoOfHomeo (subSetHomeo' h)).hom ≫
        subtypeIncl (TopCat.of ↥B) {y : ↥B | (y : X) ∈ A}
      = (TopCat.ofHom ⟨fun z : ↥A => ⟨(z : X), h z.2⟩,
          Continuous.subtype_mk (f := fun z : ↥A => (z : X)) continuous_subtype_val
            (fun z => h z.2)⟩ : TopCat.of ↥A ⟶ TopCat.of ↥B) := by
    ext z; rfl
  rw [show inclChainsSub X A B h
      = chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥B)
        (TopCat.ofHom ⟨fun z : ↥A => ⟨(z : X), h z.2⟩,
          Continuous.subtype_mk (f := fun z : ↥A => (z : X)) continuous_subtype_val
            (fun z => h z.2)⟩) from rfl]
  rw [show (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo (subSetHomeo' h))).hom
      = chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥{y : ↥B | (y : X) ∈ A})
        (TopCat.isoOfHomeo (subSetHomeo' h)).hom from rfl]
  rw [show inclChains (TopCat.of ↥B) {y : ↥B | (y : X) ∈ A}
      = chainMap ℤ (TopCat.of ↥{y : ↥B | (y : X) ∈ A}) (TopCat.of ↥B)
        (subtypeIncl (TopCat.of ↥B) {y : ↥B | (y : X) ∈ A}) from rfl]
  rw [← Functor.map_comp, hmap]

/-- **Two models of the relative chains of a pair `(B,A)`** (`A ⊆ B ⊆ X`): the cokernel model
`coker (inclChainsSub X A B h)` and the subspace model `relChains (↥B) (A∩)`. -/
noncomputable def cokerInclChainsSub_iso {X : TopCat} {A B : Set X} (hAB : A ⊆ B) :
    cokernel (inclChainsSub X A B hAB) ≅
      relChains (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A} :=
  cokernel.mapIso (f := inclChainsSub X A B hAB)
    (inclChains (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A})
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo (subSetHomeo' hAB)))
    (Iso.refl _) (inclChainsSub_eq_mapIso_comp' hAB)

theorem cokerInclChainsSub_isZero (X : TopCat) {A B : Set X} (hAB : A ⊆ B)
    (h : ∀ k, IsZero ((relChains (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A}).homology k)) (k : ℕ) :
    IsZero ((CategoryTheory.Limits.cokernel (inclChainsSub X A B hAB)).homology k) :=
  IsZero.of_iso (h k)
    (asIso (HomologicalComplex.homologyMap (cokerInclChainsSub_iso hAB).hom k))

/-- **"Shrink the relative part" is a quasi-isomorphism** when the pair is acyclic. -/
theorem isIso_relCokerMap_of_acyclic (X : TopCat) {A B : Set X} (hAB : A ⊆ B)
    (h : ∀ k, IsZero ((relChains (TopCat.of ↥B) {x : ↥B | (x : X) ∈ A}).homology k)) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (relCokerMap X A B hAB) k) :=
  Work.Serre.isIso_relCokerMap_of_acyclic X hAB (fun k => cokerInclChainsSub_isZero X hAB h k) k

/-! ### 5.1 The compressions -/

/-- The straight-line contraction of the closed unit ball onto its centre. -/
def cellBallContr (n : ℕ) (z : cellDisk n × unitInterval) : cellDisk n :=
  ⟨(1 - ((z.2 : unitInterval) : ℝ)) • ((z.1 : cellDisk n) : CellVec n), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
    have h1 : |1 - ((z.2 : unitInterval) : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (z.2 : unitInterval).2.2)]
      linarith [(z.2 : unitInterval).2.1]
    have h2 : ‖((z.1 : cellDisk n) : CellVec n)‖ ≤ 1 := norm_coe_le_one z.1
    calc |1 - ((z.2 : unitInterval) : ℝ)| * ‖((z.1 : cellDisk n) : CellVec n)‖
        ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num⟩

theorem continuous_cellBallContr (n : ℕ) : Continuous (cellBallContr n) := by
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous fun z : cellDisk n × unitInterval => (1 - ((z.2 : unitInterval) : ℝ)) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_snd)
  have h2 : Continuous fun z : cellDisk n × unitInterval => (z.1 : CellVec n) :=
    continuous_subtype_val.comp continuous_fst
  exact h1.smul h2

theorem cellBallContr_norm (n : ℕ) (z : cellDisk n × unitInterval) :
    ‖(cellBallContr n z : CellVec n)‖
      = |1 - ((z.2 : unitInterval) : ℝ)| * ‖((z.1 : cellDisk n) : CellVec n)‖ := by
  show ‖(1 - ((z.2 : unitInterval) : ℝ)) • ((z.1 : cellDisk n) : CellVec n)‖ = _
  rw [norm_smul, Real.norm_eq_abs]

theorem cellBallContr_zero (n : ℕ) (x : cellDisk n) : cellBallContr n (x, 0) = x := by
  apply Subtype.ext
  simp [cellBallContr]

theorem cellBallContr_one (n : ℕ) (x : cellDisk n) :
    ((cellBallContr n (x, 1) : cellDisk n) : CellVec n) = 0 := by
  simp [cellBallContr]

theorem cellBallContr_of_eq_zero (n : ℕ) {x : cellDisk n} (hx : (x : CellVec n) = 0)
    (t : unitInterval) : cellBallContr n (x, t) = x := by
  apply Subtype.ext
  simp [cellBallContr, hx]

theorem cellBallContr_norm_lt_one (n : ℕ) {x : cellDisk n} (hx : ‖(x : CellVec n)‖ < 1)
    (t : unitInterval) : ‖(cellBallContr n (x, t) : CellVec n)‖ < 1 := by
  rw [cellBallContr_norm]
  have h1 : |1 - ((t : unitInterval) : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (t : unitInterval).2.2)]
    linarith [(t : unitInterval).2.1]
  have h3 : |1 - ((t : unitInterval) : ℝ)| * ‖(x : CellVec n)‖ ≤ ‖(x : CellVec n)‖ := by
    calc |1 - ((t : unitInterval) : ℝ)| * ‖(x : CellVec n)‖ ≤ 1 * ‖(x : CellVec n)‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖(x : CellVec n)‖ := one_mul _
  exact lt_of_le_of_lt h3 hx

/-- The radial rescaling of a punctured cell towards the sphere of radius `r`. -/
def cellShellRescale (n : ℕ) (r : ℝ) (x : cellDisk n) (t : unitInterval) : CellVec n :=
  (((1 - ((t : unitInterval) : ℝ)) * ‖(x : CellVec n)‖ + ((t : unitInterval) : ℝ) * r)
    * (‖(x : CellVec n)‖)⁻¹) • (x : CellVec n)

theorem cellShellRescale_norm (n : ℕ) (r : ℝ) (x : cellDisk n) (t : unitInterval)
    (hx : 0 < ‖(x : CellVec n)‖) (hr : 0 < r) :
    ‖cellShellRescale n r x t‖
      = (1 - ((t : unitInterval) : ℝ)) * ‖(x : CellVec n)‖
        + ((t : unitInterval) : ℝ) * r := by
  have hne : ‖(x : CellVec n)‖ ≠ 0 := ne_of_gt hx
  have hnn : 0 ≤ ((1 - ((t : unitInterval) : ℝ)) * ‖(x : CellVec n)‖
      + ((t : unitInterval) : ℝ) * r) * (‖(x : CellVec n)‖)⁻¹ := by
    have h1 : 0 ≤ (1 - ((t : unitInterval) : ℝ)) * ‖(x : CellVec n)‖ :=
      mul_nonneg (sub_nonneg.mpr (t : unitInterval).2.2) (norm_nonneg _)
    have h2 : 0 ≤ ((t : unitInterval) : ℝ) * r := mul_nonneg (t : unitInterval).2.1 (le_of_lt hr)
    exact mul_nonneg (by linarith) (inv_nonneg.mpr (norm_nonneg _))
  rw [cellShellRescale, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn, mul_assoc,
    inv_mul_cancel₀ hne, mul_one]

theorem cellShellRescale_smul_eq_self (n : ℕ) (r : ℝ) {x : cellDisk n}
    {t : unitInterval} (hcoef : ((1 - ((t : unitInterval) : ℝ)) * ‖(x : CellVec n)‖
      + ((t : unitInterval) : ℝ) * r) * (‖(x : CellVec n)‖)⁻¹ = 1) :
    cellShellRescale n r x t = (x : CellVec n) := by
  rw [cellShellRescale, hcoef, one_smul]

theorem cellShellRescale_zero (n : ℕ) (r : ℝ) (x : cellDisk n)
    (hx : 0 < ‖(x : CellVec n)‖) : cellShellRescale n r x 0 = (x : CellVec n) := by
  refine cellShellRescale_smul_eq_self n r ?_
  rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, one_mul, zero_mul, add_zero,
    mul_inv_cancel₀ (ne_of_gt hx)]

theorem cellShellRescale_of_norm_eq (n : ℕ) (r : ℝ) (x : cellDisk n) (t : unitInterval)
    (hr : 0 < r) (hx : ‖(x : CellVec n)‖ = r) : cellShellRescale n r x t = (x : CellVec n) := by
  refine cellShellRescale_smul_eq_self n r ?_
  rw [hx]
  have h1 : (1 - ((t : unitInterval) : ℝ)) * r + ((t : unitInterval) : ℝ) * r = r := by ring
  rw [h1, mul_inv_cancel₀ (ne_of_gt hr)]

/-- The convexity estimates for the radial rescaling. -/
theorem convex_lt_right {a r y t : ℝ} (hy : a < y) (hr : a < r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a < (1 - t) * y + t * r := by
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · rw [h1]; ring_nf; exact hr
  · have h2 : 0 < 1 - t := sub_pos.mpr h1
    have h3 : (1 - t) * a < (1 - t) * y := mul_lt_mul_of_pos_left hy h2
    have h4 : t * a ≤ t * r := mul_le_mul_of_nonneg_left hr.le ht0
    nlinarith [h3, h4]

theorem convex_lt_left {b r y t : ℝ} (hy : y < b) (hr : r < b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * y + t * r < b := by
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · rw [h1]; ring_nf; exact hr
  · have h2 : 0 < 1 - t := sub_pos.mpr h1
    have h3 : (1 - t) * y < (1 - t) * b := mul_lt_mul_of_pos_left hy h2
    have h4 : t * r ≤ t * b := mul_le_mul_of_nonneg_left hr.le ht0
    nlinarith [h3, h4]

theorem convex_le_one {r y t : ℝ} (hy : y ≤ 1) (hr : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * y + t * r ≤ 1 := by
  have h3 : (1 - t) * y ≤ (1 - t) * 1 := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr ht1)
  have h4 : t * r ≤ t * 1 := mul_le_mul_of_nonneg_left hr ht0
  linarith [h3, h4]

theorem convex_le_right {a r y t : ℝ} (hy : a ≤ y) (hr : a ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a ≤ (1 - t) * y + t * r := by
  have h3 : (1 - t) * a ≤ (1 - t) * y := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr ht1)
  have h4 : t * a ≤ t * r := mul_le_mul_of_nonneg_left hr ht0
  linarith [h3, h4]

theorem convex_le_left {b r y t : ℝ} (hy : y ≤ b) (hr : r ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * y + t * r ≤ b := by
  have h3 : (1 - t) * y ≤ (1 - t) * b := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr ht1)
  have h4 : t * r ≤ t * b := mul_le_mul_of_nonneg_left hr ht0
  linarith [h3, h4]

/-- The radial rescaling is continuous on a shell that avoids the centre. -/
theorem continuous_cellShellRescale (n : ℕ) (r : ℝ) {S : Set (cellDisk n)}
    (hS : ∀ x : ↥S, 0 < ‖((x : ↥S) : CellVec n)‖) :
    Continuous fun z : ↥S × unitInterval => cellShellRescale n r ((z.1 : ↥S) : cellDisk n) z.2 := by
  have hnorm : Continuous fun z : ↥S × unitInterval => ‖((z.1 : ↥S) : CellVec n)‖ :=
    continuous_norm.comp ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst)
  have hcoef : Continuous fun z : ↥S × unitInterval =>
      ((1 - ((z.2 : unitInterval) : ℝ)) * ‖((z.1 : ↥S) : CellVec n)‖
        + ((z.2 : unitInterval) : ℝ) * r) * (‖((z.1 : ↥S) : CellVec n)‖)⁻¹ := by
    refine Continuous.mul (Continuous.add (Continuous.mul ?_ hnorm)
      (Continuous.mul ?_ continuous_const)) ?_
    · exact continuous_const.sub (continuous_subtype_val.comp continuous_snd)
    · exact continuous_subtype_val.comp continuous_snd
    · exact Continuous.inv₀ hnorm (fun z => ne_of_gt (hS z.1))
  exact hcoef.smul ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst)

/-- **The ball `csB` compresses onto its centre.** -/
theorem compressRel_csB_csPt (n : ℕ) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(csB (n := n))
      {x : ↥(csB (n := n)) | (x : cellDisk n) ∈ csPt (n := n)} d := by
  intro d
  refine Work.Serre.compressRel_of_deformation (Y := ↥(csB (n := n)))
    (A := {x : ↥(csB (n := n)) | (x : cellDisk n) ∈ csPt (n := n)})
    ⟨fun z : ↥(csB (n := n)) × unitInterval =>
      ⟨cellBallContr n (z.1, z.2), cellBallContr_norm_lt_one n z.1.2 z.2⟩, ?_⟩ ?_ ?_ ?_ d
  · refine Continuous.subtype_mk ?_ (fun z => cellBallContr_norm_lt_one n z.1.2 z.2)
    exact (continuous_cellBallContr n).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  · intro y
    apply Subtype.ext
    exact cellBallContr_zero n (y : cellDisk n)
  · intro y
    exact cellBallContr_one n (y : cellDisk n)
  · intro y hy t
    apply Subtype.ext
    exact cellBallContr_of_eq_zero n hy t

/-- **The model cell compresses onto its centre.** -/
theorem compressRel_cellDisk_csPt (n : ℕ) :
    ∀ d, Work.RatHurewicz.CompressRel (cellDisk n)
      {x : cellDisk n | (x : cellDisk n) ∈ csPt (n := n)} d := by
  intro d
  refine Work.Serre.compressRel_of_deformation (Y := cellDisk n)
    (A := {x : cellDisk n | (x : cellDisk n) ∈ csPt (n := n)})
    ⟨cellBallContr n, continuous_cellBallContr n⟩ ?_ ?_ ?_ d
  · intro y; exact cellBallContr_zero n y
  · intro y; exact cellBallContr_one n y
  · intro y hy t; exact cellBallContr_of_eq_zero n hy t

/-- **The model cell, as `↥univ`, compresses onto its centre.** -/
theorem compressRel_cellDiskUniv_csPt (n : ℕ) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(Set.univ : Set (cellDisk n))
      {x : ↥(Set.univ : Set (cellDisk n)) | (x : cellDisk n) ∈ csPt (n := n)} d := by
  intro d
  refine Work.Serre.compressRel_of_deformation
    (Y := ↥(Set.univ : Set (cellDisk n)))
    (A := {x : ↥(Set.univ : Set (cellDisk n)) | (x : cellDisk n) ∈ csPt (n := n)})
    ⟨fun z : ↥(Set.univ : Set (cellDisk n)) × unitInterval =>
      ⟨cellBallContr n (z.1, z.2), trivial⟩, ?_⟩ ?_ ?_ ?_ d
  · refine Continuous.subtype_mk ?_ (fun _ => trivial)
    exact (continuous_cellBallContr n).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  · intro y; apply Subtype.ext; exact cellBallContr_zero n (y : cellDisk n)
  · intro y; exact cellBallContr_one n (y : cellDisk n)
  · intro y hy t; apply Subtype.ext; exact cellBallContr_of_eq_zero n hy t

/-- **The radial compression of an open shell onto a middle sphere.** -/
theorem compressRel_cellShell (n : ℕ) (a b r : ℝ) (ha : 0 < a) (har : a < r) (hrb : r < b)
    (hb : b ≤ 1) :
    ∀ d, Work.RatHurewicz.CompressRel
      ↥{x : cellDisk n | a < ‖(x : CellVec n)‖ ∧ ‖(x : CellVec n)‖ < b}
      {x : ↥{x : cellDisk n | a < ‖(x : CellVec n)‖ ∧ ‖(x : CellVec n)‖ < b} |
        ‖((x : cellDisk n) : CellVec n)‖ = r} d := by
  intro d
  set S : Set (cellDisk n) := {x : cellDisk n | a < ‖(x : CellVec n)‖ ∧ ‖(x : CellVec n)‖ < b}
  set A : Set ↥S := {x : ↥S | ‖((x : ↥S) : CellVec n)‖ = r}
  have hlt : ∀ y : ↥S, a < ‖((y : ↥S) : CellVec n)‖ := fun y => y.2.1
  have hr : 0 < r := lt_trans ha har
  have hr1 : r ≤ 1 := le_of_lt (lt_of_lt_of_le hrb hb)
  refine Work.Serre.compressRel_of_deformation (Y := ↥S) (A := A)
    ⟨fun z : ↥S × unitInterval =>
      ⟨⟨cellShellRescale n r (z.1 : cellDisk n) z.2, ?_⟩, ?_⟩, ?_⟩ ?_ ?_ ?_ d
  · rw [Metric.mem_closedBall, dist_zero_right,
      cellShellRescale_norm n r (z.1 : cellDisk n) z.2 (lt_trans ha (hlt z.1)) hr]
    exact convex_le_one (norm_coe_le_one (z.1 : cellDisk n)) hr1
      (z.2 : unitInterval).2.1 (z.2 : unitInterval).2.2
  · refine ⟨?_, ?_⟩
    · rw [cellShellRescale_norm n r (z.1 : cellDisk n) z.2 (lt_trans ha (hlt z.1)) hr]
      exact convex_lt_right (hlt z.1) har (z.2 : unitInterval).2.1 (z.2 : unitInterval).2.2
    · rw [cellShellRescale_norm n r (z.1 : cellDisk n) z.2 (lt_trans ha (hlt z.1)) hr]
      exact convex_lt_left z.1.2.2 hrb (z.2 : unitInterval).2.1 (z.2 : unitInterval).2.2
  · refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact continuous_cellShellRescale (S := S) n r (fun y => lt_trans ha (hlt y))
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    exact cellShellRescale_zero n r (y : cellDisk n) (lt_trans ha (hlt y))
  · intro y
    change ‖cellShellRescale n r (y : cellDisk n) (1 : unitInterval)‖ = r
    rw [cellShellRescale_norm n r (y : cellDisk n) 1 (lt_trans ha (hlt y)) hr]
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
    ring
  · intro y hy t
    apply Subtype.ext
    apply Subtype.ext
    exact cellShellRescale_of_norm_eq n r (y : cellDisk n) t hr hy

/-- **The radial compression of a closed annulus onto its middle sphere.** -/
theorem compressRel_cellAnnulus (n : ℕ) (a b r : ℝ) (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b)
    (hr1 : r ≤ 1) :
    ∀ d, Work.RatHurewicz.CompressRel
      ↥{x : cellDisk n | a ≤ ‖(x : CellVec n)‖ ∧ ‖(x : CellVec n)‖ ≤ b}
      {x : ↥{x : cellDisk n | a ≤ ‖(x : CellVec n)‖ ∧ ‖(x : CellVec n)‖ ≤ b} |
        ‖((x : cellDisk n) : CellVec n)‖ = r} d := by
  intro d
  set S : Set (cellDisk n) := {x : cellDisk n | a ≤ ‖(x : CellVec n)‖ ∧ ‖(x : CellVec n)‖ ≤ b}
  set A : Set ↥S := {x : ↥S | ‖((x : ↥S) : CellVec n)‖ = r}
  have hle : ∀ y : ↥S, a ≤ ‖((y : ↥S) : CellVec n)‖ := fun y => y.2.1
  have hr : 0 < r := lt_of_lt_of_le ha har
  refine Work.Serre.compressRel_of_deformation (Y := ↥S) (A := A)
    ⟨fun z : ↥S × unitInterval =>
      ⟨⟨cellShellRescale n r (z.1 : cellDisk n) z.2, ?_⟩, ?_⟩, ?_⟩ ?_ ?_ ?_ d
  · rw [Metric.mem_closedBall, dist_zero_right,
      cellShellRescale_norm n r (z.1 : cellDisk n) z.2 (lt_of_lt_of_le ha (hle z.1)) hr]
    exact convex_le_one (norm_coe_le_one (z.1 : cellDisk n)) hr1
      (z.2 : unitInterval).2.1 (z.2 : unitInterval).2.2
  · refine ⟨?_, ?_⟩
    · rw [cellShellRescale_norm n r (z.1 : cellDisk n) z.2 (lt_of_lt_of_le ha (hle z.1)) hr]
      exact convex_le_right (hle z.1) har (z.2 : unitInterval).2.1 (z.2 : unitInterval).2.2
    · rw [cellShellRescale_norm n r (z.1 : cellDisk n) z.2 (lt_of_lt_of_le ha (hle z.1)) hr]
      exact convex_le_left z.1.2.2 hrb (z.2 : unitInterval).2.1 (z.2 : unitInterval).2.2
  · refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact continuous_cellShellRescale (S := S) n r (fun y => lt_of_lt_of_le ha (hle y))
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    exact cellShellRescale_zero n r (y : cellDisk n) (lt_of_lt_of_le ha (hle y))
  · intro y
    change ‖cellShellRescale n r (y : cellDisk n) (1 : unitInterval)‖ = r
    rw [cellShellRescale_norm n r (y : cellDisk n) 1 (lt_of_lt_of_le ha (hle y)) hr]
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
    ring
  · intro y hy t
    apply Subtype.ext
    apply Subtype.ext
    exact cellShellRescale_of_norm_eq n r (y : cellDisk n) t hr hy

/-- The compression of the shell `csSh` onto the sphere `csS`. -/
theorem compressRel_csSh_csS (n : ℕ) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(csSh (n := n))
      {x : ↥(csSh (n := n)) | (x : cellDisk n) ∈ csS (n := n)} d :=
  compressRel_cellShell n (3/4) 1 (7/8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The compression of the closed shell `csQ` onto the sphere `csS`. -/
theorem compressRel_csQ_csS (n : ℕ) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(csQ (n := n))
      {x : ↥(csQ (n := n)) | (x : cellDisk n) ∈ csS (n := n)} d :=
  compressRel_cellAnnulus n (7/8) 1 (7/8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The compression of the closed shell `csQ` onto the boundary sphere. -/
theorem compressRel_csQ_cellSphereSet (n : ℕ) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(csQ (n := n))
      {x : ↥(csQ (n := n)) | (x : cellDisk n) ∈ cellSphereSet n} d :=
  compressRel_cellAnnulus n (7/8) 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### 5.2 Acyclicity of the two "whole space" pairs -/

/-- The triple `csPt ⊆ csB ⊆ cellDisk` computes `C_*(cellDisk, csB)`. -/
theorem isZero_relChains_Dc_csB (n : ℕ) (k : ℕ) :
    IsZero ((relChains (Dc n) (csB (n := n))).homology k) := by
  have hsub : csPt (n := n) ⊆ csB (n := n) := by
    intro x hx
    change ‖(x : CellVec n)‖ < 1
    rw [show (x : CellVec n) = 0 from hx, norm_zero]
    norm_num
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    Work.Cohomology.tripleShort (Dc n) (csPt (n := n)) (csB (n := n)) hsub
  have h1 : ∀ j, IsZero (S.X₁.homology j) := fun j => by
    have hS : S.X₁ = CategoryTheory.Limits.cokernel
        (inclChainsSub (Dc n) (csPt (n := n)) (csB (n := n)) hsub) :=
      Work.Cohomology.tripleShort_X1 (Dc n) (csPt (n := n)) (csB (n := n)) hsub
    rw [hS]
    exact cokerInclChainsSub_isZero (Dc n) hsub
      (fun j => isZero_BsRel (compressRel_csB_csPt n) j) j
  have h2 : ∀ j, IsZero (S.X₂.homology j) := fun j => by
    have hS : S.X₂ = relChains (Dc n) (csPt (n := n)) := rfl
    rw [hS]
    exact Work.Serre.isZero_relChains_of_compress (compressRel_cellDisk_csPt n) j
  have hS : S.X₃ = relChains (Dc n) (csB (n := n)) := rfl
  rw [← hS]
  haveI hiso := Work.Serre.isIso_homologyMap_g_of_acyclic_X1
    (Work.Cohomology.relChains_triple_shortExact (Dc n) (csPt (n := n)) (csB (n := n)) hsub) h1 k
  exact IsZero.of_iso (h2 k) (asIso (HomologicalComplex.homologyMap S.g k)).symm

/-! ### 5.3 The "whole space" transport -/

/-- The canonical homeomorphism `↥(q ⁻¹' univ) ≃ₜ X`. -/
def univPreHomeo {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (q : C(X, Z)) :
    ↥(q ⁻¹' (Set.univ : Set Z)) ≃ₜ X where
  toFun x := x.1
  invFun y := ⟨y, by rw [Set.mem_preimage]; trivial⟩
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk continuous_id
    (fun y => by rw [Set.mem_preimage]; trivial)

/-- Vanishing of relative homology is unchanged by the canonical homeomorphism
`↥(q ⁻¹' univ) ≃ₜ X`. -/
theorem isZero_relChains_univPre_iff {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (q : C(X, Z)) (A : Set X) (k : ℕ) :
    IsZero ((relChains (TopCat.of ↥(q ⁻¹' (Set.univ : Set Z)))
      {x : ↥(q ⁻¹' (Set.univ : Set Z)) | (x : X) ∈ A}).homology k) ↔
      IsZero ((relChains (TopCat.of X) A).homology k) := by
  obtain ⟨iso⟩ := Work.StemsB.nonempty_relChains_homology_iso_of_homeomorph
    (X := TopCat.of ↥(q ⁻¹' (Set.univ : Set Z))) (Y := TopCat.of X) (univPreHomeo q)
    {x : ↥(q ⁻¹' (Set.univ : Set Z)) | (x : X) ∈ A} A
    (fun x => by
      rw [show (univPreHomeo q) x = (x : X) from rfl]
      exact Iff.rfl)
    k
  exact Iso.isZero_iff iso

/-- **The pair `(P, T csB)` is acyclic.** -/
theorem isZero_relChains_Pb_csB (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(cellDisk n, B)) (k : ℕ) :
    IsZero ((relChains (Pb p τ) (Tp p τ (csB (n := n)))).homology k) := by
  have hq : Work.StemsB.IsSerreFibration (Work.StemsB.pullbackSnd p τ) :=
    fun m => Work.StemsB.hasHLP_pullback p τ (hp m)
  have hsub : csPt (n := n) ⊆ csB (n := n) := by
    intro x hx
    change ‖(x : CellVec n)‖ < 1
    rw [show (x : CellVec n) = 0 from hx, norm_zero]
    norm_num
  have hAB : Tp p τ (csPt (n := n)) ⊆ Tp p τ (csB (n := n)) := fun x hx => hsub hx
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    Work.Cohomology.tripleShort (Pb p τ) (Tp p τ (csPt (n := n))) (Tp p τ (csB (n := n))) hAB
  have h1 : ∀ j, IsZero (S.X₁.homology j) := fun j => by
    have hS : S.X₁ = CategoryTheory.Limits.cokernel
        (inclChainsSub (Pb p τ) (Tp p τ (csPt (n := n))) (Tp p τ (csB (n := n))) hAB) :=
      Work.Cohomology.tripleShort_X1 (Pb p τ) (Tp p τ (csPt (n := n)))
        (Tp p τ (csB (n := n))) hAB
    rw [hS]
    exact cokerInclChainsSub_isZero (Pb p τ) hAB
      (fun j => Work.Serre.isZero_relChains_preimage_of_base_compress (Work.StemsB.pullbackSnd p τ)
        hq (csPt (n := n)) (csB (n := n)) hsub (compressRel_csB_csPt n) j) j
  have h2 : ∀ j, IsZero (S.X₂.homology j) := fun j => by
    have hS : S.X₂ = relChains (Pb p τ) (Tp p τ (csPt (n := n))) := rfl
    rw [hS]
    exact (isZero_relChains_univPre_iff (q := Work.StemsB.pullbackSnd p τ)
      (Tp p τ (csPt (n := n))) j).mp
      (Work.Serre.isZero_relChains_preimage_of_base_compress (Work.StemsB.pullbackSnd p τ) hq
        (csPt (n := n)) (Set.univ) (Set.subset_univ _) (compressRel_cellDiskUniv_csPt n) j)
  have hS : S.X₃ = relChains (Pb p τ) (Tp p τ (csB (n := n))) := rfl
  rw [← hS]
  haveI hiso := Work.Serre.isIso_homologyMap_g_of_acyclic_X1
    (Work.Cohomology.relChains_triple_shortExact (Pb p τ) (Tp p τ (csPt (n := n)))
      (Tp p τ (csB (n := n))) hAB) h1 k
  exact IsZero.of_iso (h2 k) (asIso (HomologicalComplex.homologyMap S.g k)).symm

/-! ### 5.4 The two enlargements are quasi-isomorphisms -/

/-- The homeomorphism `↥{y : ↥U | (y : X) ∈ A} ≃ₜ ↥A` for `A ⊆ U` (the map `inclInterA`). -/
def inclInterHomeo {X : TopCat} {U A : Set X} (hAU : A ⊆ U) :
    ↥{y : ↥U | (y : X) ∈ A} ≃ₜ ↥A where
  toFun z := ⟨(z.1 : X), z.2⟩
  invFun a := ⟨⟨(a : X), hAU a.2⟩, a.2⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun z => z.2)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val (fun a => hAU a.2)) (fun a => a.2)

/-- The five-lemma form of `relChainsMapOf` for the `Work.StemsB` presentation. -/
theorem relChainsMapOfStems_isIso {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (hf : ∀ x, x ∈ A → f x ∈ B) (k : ℕ)
    (h1 : ∀ j, IsIso (HomologicalComplex.homologyMap (chainMap ℤ X Y f) j))
    (h2 : ∀ j, IsIso (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of A) (TopCat.of B) (Work.StemsB.pairRestrict f A B hf)) j)) :
    IsIso (HomologicalComplex.homologyMap (Work.StemsB.relChainsMapOf f A B hf) k) := by
  rw [stems_eq_cohom A B f hf]
  exact Work.Cohomology.relChainsMapOf_isIso A B f (Work.StemsB.pairRestrict f A B hf)
    (Work.StemsB.pairRestrict_comp_subtypeIncl f A B hf).symm k h1 h2

/-- **Enlarging the ambient space is a quasi-isomorphism.** -/
theorem relChainsMap_isIso (X : TopCat) (U A : Set X) (hAU : A ⊆ U)
    (h : ∀ k, IsZero ((relChains X U).homology k)) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (relChainsMap X U A) k) := by
  rw [relChainsMap_eq_stems]
  refine relChainsMapOfStems_isIso _ _ _ _ k ?_ ?_
  · intro j
    exact Work.Serre.isIso_homologyMap_f_of_acyclic_X3 (Work.Cohomology.hPairShort_shortExact X U)
      h j
  · intro j
    rw [show Work.StemsB.pairRestrict (subtypeIncl X U) {y : ↥U | (y : X) ∈ A} A (fun _ hx => hx)
        = Work.StemsB.sphHomeoHom (inclInterHomeo hAU) from by ext z; rfl]
    haveI : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of ↥{y : ↥U | (y : X) ∈ A}) (TopCat.of ↥A)
        (Work.StemsB.sphHomeoHom (inclInterHomeo hAU))) :=
      Work.StemsB.isIso_chainMap_sphHomeoHom (X := TopCat.of ↥{y : ↥U | (y : X) ∈ A})
        (Y := TopCat.of ↥A) (inclInterHomeo hAU)
    exact Functor.map_isIso
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) j)
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥{y : ↥U | (y : X) ∈ A}) (TopCat.of ↥A)
        (Work.StemsB.sphHomeoHom (inclInterHomeo hAU)))

/-- The identity of a chain complex is a quasi-isomorphism. -/
theorem isIso_homologyMap_id (C : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (𝟙 C) k) := by
  rw [HomologicalComplex.homologyMap_id]
  infer_instance

/-- **The transfer along a commuting square**, as an equivalence. -/
theorem isIso_homologyMap_iff_of_square {C₁ C₂ B₁ B₂ : ChainComplex (ModuleCat ℤ) ℕ}
    (h : C₁ ⟶ C₂) (g : B₁ ⟶ B₂) (u : C₁ ⟶ B₁) (v : C₂ ⟶ B₂)
    (hsq : h ≫ v = u ≫ g) (k : ℕ)
    (hh : IsIso (HomologicalComplex.homologyMap h k))
    (hg : IsIso (HomologicalComplex.homologyMap g k)) :
    IsIso (HomologicalComplex.homologyMap u k) ↔ IsIso (HomologicalComplex.homologyMap v k) := by
  haveI := hh
  haveI := hg
  have hw : HomologicalComplex.homologyMap h k ≫ HomologicalComplex.homologyMap v k
      = HomologicalComplex.homologyMap u k ≫ HomologicalComplex.homologyMap g k := by
    rw [← HomologicalComplex.homologyMap_comp, hsq, HomologicalComplex.homologyMap_comp]
  constructor
  · intro hu
    haveI := hu
    have hα : HomologicalComplex.homologyMap v k
        = inv (HomologicalComplex.homologyMap h k)
          ≫ (HomologicalComplex.homologyMap u k ≫ HomologicalComplex.homologyMap g k) := by
      calc HomologicalComplex.homologyMap v k
          = 𝟙 _ ≫ HomologicalComplex.homologyMap v k := (Category.id_comp _).symm
        _ = (inv (HomologicalComplex.homologyMap h k) ≫ HomologicalComplex.homologyMap h k)
              ≫ HomologicalComplex.homologyMap v k := by
            rw [IsIso.inv_hom_id, Category.id_comp]
        _ = inv (HomologicalComplex.homologyMap h k)
              ≫ (HomologicalComplex.homologyMap h k ≫ HomologicalComplex.homologyMap v k) :=
            Category.assoc _ _ _
        _ = inv (HomologicalComplex.homologyMap h k)
              ≫ (HomologicalComplex.homologyMap u k ≫ HomologicalComplex.homologyMap g k) := by
            rw [hw]
    rw [hα]
    infer_instance
  · intro hv
    haveI := hv
    have hα : HomologicalComplex.homologyMap u k
        = HomologicalComplex.homologyMap h k
          ≫ (HomologicalComplex.homologyMap v k ≫ inv (HomologicalComplex.homologyMap g k)) := by
      calc HomologicalComplex.homologyMap u k
          = HomologicalComplex.homologyMap u k ≫ 𝟙 _ := (Category.comp_id _).symm
        _ = HomologicalComplex.homologyMap u k
              ≫ (HomologicalComplex.homologyMap g k ≫ inv (HomologicalComplex.homologyMap g k)) := by
            rw [IsIso.hom_inv_id]
        _ = (HomologicalComplex.homologyMap u k ≫ HomologicalComplex.homologyMap g k)
              ≫ inv (HomologicalComplex.homologyMap g k) := (Category.assoc _ _ _).symm
        _ = (HomologicalComplex.homologyMap h k ≫ HomologicalComplex.homologyMap v k)
              ≫ inv (HomologicalComplex.homologyMap g k) := by rw [← hw]
        _ = HomologicalComplex.homologyMap h k
              ≫ (HomologicalComplex.homologyMap v k ≫ inv (HomologicalComplex.homologyMap g k)) :=
            Category.assoc _ _ _
    rw [hα]
    infer_instance

/-! ## 6. The reduction -/

/-- **The model per-cell statement follows from the disc statement.** -/
theorem csModelIso_of_discIso (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(cellDisk n, B)) (i : ℕ)
    (hDisc : CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.discPairMap n p τ) i)) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.csModelMap n p τ) i) := by
  have hsub1 : Tp p τ (csS (n := n)) ⊆ Tp p τ (csSh (n := n)) :=
    fun x hx => csS_subset_csSh (n := n) hx
  have hsub2 : Tp p τ (csS (n := n)) ⊆ Tp p τ (csQ (n := n)) :=
    fun x hx => csS_subset_csQ (n := n) hx
  have hsub3 : Tp p τ (cellSphereSet n) ⊆ Tp p τ (csQ (n := n)) :=
    fun x hx => cellSphereSet_subset_csQ (n := n) hx
  have hsub4 : Tp p τ (csSh (n := n)) ⊆ Tp p τ (csB (n := n)) :=
    fun x hx => csSh_subset_csB (n := n) hx
  have h3 : CategoryTheory.IsIso (HomologicalComplex.homologyMap (Pa3 p τ) i) :=
    (isIso_homologyMap_iff_of_square
      (h := relCokerMap (Pb p τ) (Tp p τ (cellSphereSet n)) (Tp p τ (csQ (n := n))) hsub3)
      (g := relCokerMap (Dc n) (cellSphereSet n) (csQ (n := n))
        (cellSphereSet_subset_csQ (n := n)))
      (u := Pa4 p τ) (v := Pa3 p τ) (square5 p τ) i
      (isIso_relCokerMap_of_acyclic (X := Pb p τ) hsub3
        (fun j => isZero_TotRel (W₀ := cellSphereSet n) (W := csQ (n := n)) p hp τ (cellSphereSet_subset_csQ (n := n))
        (compressRel_csQ_cellSphereSet n) j) i)
      (isIso_relCokerMap_of_acyclic (X := Dc n) (cellSphereSet_subset_csQ (n := n))
        (fun j => Work.Serre.isZero_relChains_of_compress (compressRel_csQ_cellSphereSet n) j) i)).mp hDisc
  have h2 : CategoryTheory.IsIso (HomologicalComplex.homologyMap (Pa2 p τ) i) :=
    (isIso_homologyMap_iff_of_square
      (h := relCokerMap (Pb p τ) (Tp p τ (csS (n := n))) (Tp p τ (csQ (n := n))) hsub2)
      (g := relCokerMap (Dc n) (csS (n := n)) (csQ (n := n)) (csS_subset_csQ (n := n)))
      (u := Pa2 p τ) (v := Pa3 p τ) (square4 p τ) i
      (isIso_relCokerMap_of_acyclic (X := Pb p τ) hsub2
        (fun j => isZero_TotRel (W₀ := csS (n := n)) (W := csQ (n := n)) p hp τ (csS_subset_csQ (n := n))
        (compressRel_csQ_csS n) j) i)
      (isIso_relCokerMap_of_acyclic (X := Dc n) (csS_subset_csQ (n := n))
        (fun j => Work.Serre.isZero_relChains_of_compress (compressRel_csQ_csS n) j) i)).mpr h3
  have h1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap (Pa1 p τ) i) :=
    (isIso_homologyMap_iff_of_square
      (h := relCokerMap (Pb p τ) (Tp p τ (csS (n := n))) (Tp p τ (csSh (n := n))) hsub1)
      (g := relCokerMap (Dc n) (csS (n := n)) (csSh (n := n)) (csS_subset_csSh (n := n)))
      (u := Pa2 p τ) (v := Pa1 p τ) (square3 p τ) i
      (isIso_relCokerMap_of_acyclic (X := Pb p τ) hsub1
        (fun j => isZero_TotRel (W₀ := csS (n := n)) (W := csSh (n := n)) p hp τ (csS_subset_csSh (n := n))
        (compressRel_csSh_csS n) j) i)
      (isIso_relCokerMap_of_acyclic (X := Dc n) (csS_subset_csSh (n := n))
        (fun j => Work.Serre.isZero_relChains_of_compress (compressRel_csSh_csS n) j) i)).mp h2
  have h0' : CategoryTheory.IsIso (HomologicalComplex.homologyMap (Pa0' p τ) i) :=
    (isIso_homologyMap_iff_of_square
      (h := relChainsMap (Pb p τ) (Tp p τ (csB (n := n))) (Tp p τ (csSh (n := n))))
      (g := 𝟙 (relChains (Dc n) (csSh (n := n))))
      (u := Pa0' p τ) (v := Pa1 p τ) (square2 p τ) i
      (relChainsMap_isIso (Pb p τ) (Tp p τ (csB (n := n))) (Tp p τ (csSh (n := n))) hsub4
        (isZero_relChains_Pb_csB p hp τ) i)
      (isIso_homologyMap_id (relChains (Dc n) (csSh (n := n))) i)).mpr h1
  exact (isIso_homologyMap_iff_of_square
    (h := 𝟙 _)
    (g := relChainsMap (Dc n) (csB (n := n)) (csSh (n := n)))
    (u := Work.Serre.csModelMap n p τ) (v := Pa0' p τ)
    (by rw [Category.id_comp]; exact square1 p τ) i
    (isIso_homologyMap_id _ i)
    (relChainsMap_isIso (Dc n) (csB (n := n)) (csSh (n := n)) (csSh_subset_csB (n := n))
      (isZero_relChains_Dc_csB n) i)).mpr h0'

end

end Work.Serre.CellStep
