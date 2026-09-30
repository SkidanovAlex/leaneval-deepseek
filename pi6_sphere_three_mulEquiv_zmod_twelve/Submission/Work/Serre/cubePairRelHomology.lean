import Mathlib
import Submission.Work.StemsB.CubePairHomology
import Submission.Work.StemsB.CubePairAcyclic
import Submission.Work.StemsB.CubeMidIso
import Submission.Work.StemsB.SphLoopRelPair
import Submission.Work.Cohomology.Endgame.relCohMV_elim
import Submission.Work.ThreeConnected.Excision.relMV_iso_of_acyclic
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Cohomology.homologyContractible

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

namespace Work.Serre

noncomputable section

/-! ## The `0`-cube

The pair `(I⁰ × S, I⁰ × R)` is the pair `(S,R)`: `I⁰` is a point, so the projection onto the second
factor is a homeomorphism of pairs. -/

/-- The projection `I⁰ × S → S` is a homeomorphism. -/
def cubeZeroHomeo (S : Type) [TopologicalSpace S] : (Work.StemsB.CubeP S 0) ≃ₜ S where
  toFun := Prod.snd
  invFun := fun p => (fun _ => 0, p)
  left_inv := fun x => by
    refine Prod.ext ?_ rfl
    exact Subsingleton.elim _ _
  right_inv := fun p => rfl
  continuous_toFun := continuous_snd
  continuous_invFun := by fun_prop

/-- **Base case `k = 0`** of the pair form of the relative homology of the cube pair. -/
theorem cubePairRelHomology_zero (S : Type) [TopologicalSpace S] (R : Set S) (j : ℕ) :
    Nonempty (((Work.Cohomology.relChains (Work.StemsB.CubeSpace S 0)
        (Work.StemsB.cubeBdryK S 0 ∪ {p : Work.StemsB.CubeP S 0 | p.2 ∈ R})).homology j) ≅
      ((Work.Cohomology.relChains (TopCat.of S) R).homology j)) := by
  have hset : Work.StemsB.cubeBdryK S 0 ∪ {p : Work.StemsB.CubeP S 0 | p.2 ∈ R}
      = {p : Work.StemsB.CubeP S 0 | p.2 ∈ R} := by
    rw [Work.StemsB.cubeBdryK_zero]
    exact Set.empty_union _
  have h2 : Work.Cohomology.relChains (Work.StemsB.CubeSpace S 0)
        (Work.StemsB.cubeBdryK S 0 ∪ {p : Work.StemsB.CubeP S 0 | p.2 ∈ R})
      ≅ Work.Cohomology.relChains (Work.StemsB.CubeSpace S 0)
        {p : Work.StemsB.CubeP S 0 | p.2 ∈ R} :=
    eqToIso (congrArg (fun s => Work.Cohomology.relChains (Work.StemsB.CubeSpace S 0) s) hset)
  obtain ⟨e⟩ := Work.StemsB.nonempty_relChains_homology_iso_of_homeomorph
    (X := TopCat.of (Work.StemsB.CubeP S 0)) (Y := TopCat.of S) (cubeZeroHomeo S)
    {p : Work.StemsB.CubeP S 0 | p.2 ∈ R} R (fun x => Iff.rfl) j
  exact ⟨HomologicalComplex.homologyMapIso h2 j ≪≫ e⟩

/-! ## Removing a contractible factor -/

/-- `TopCat.Homotopy f g` from a homotopy of the underlying continuous maps. -/
def topCatHomotopy_of_homotopic {X Y : TopCat} {f g : X ⟶ Y}
    (h : (TopCat.Hom.hom f).Homotopic (TopCat.Hom.hom g)) : TopCat.Homotopy f g := h.some

/-- **The projection `C × W → W` is a quasi-isomorphism when `C` is contractible.** -/
theorem isIso_chainMap_snd_prod_contractible (C W : Type) [TopologicalSpace C]
    [TopologicalSpace W] [ContractibleSpace C] (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (C × W)) (TopCat.of W)
        (TopCat.ofHom (ContinuousMap.snd : C(C × W, W)))) k) := by
  obtain ⟨c₀, hc₀⟩ := id_nullhomotopic C
  let F : C(C × W, W) := ContinuousMap.snd
  let G : C(W, C × W) :=
    ContinuousMap.prodMk (ContinuousMap.const W c₀) (ContinuousMap.id W)
  let f : TopCat.of (C × W) ⟶ TopCat.of W := TopCat.ofHom F
  let g : TopCat.of W ⟶ TopCat.of (C × W) := TopCat.ofHom G
  have hid : (ContinuousMap.id C).prodMap (ContinuousMap.id W) = ContinuousMap.id (C × W) := by
    ext p <;> rfl
  have hFG : G.comp F = (ContinuousMap.const C c₀).prodMap (ContinuousMap.id W) := by
    ext p <;> rfl
  have hmain : ((ContinuousMap.id C).prodMap (ContinuousMap.id W)).Homotopic
      ((ContinuousMap.const C c₀).prodMap (ContinuousMap.id W)) :=
    hc₀.prodMap (ContinuousMap.Homotopic.refl (ContinuousMap.id W))
  have h1' : (G.comp F).Homotopic (ContinuousMap.id (C × W)) := hmain.symm
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of (C × W))) := topCatHomotopy_of_homotopic h1'
  have hGF : F.comp G = ContinuousMap.id W := by
    ext z
    rfl
  have h2' : (F.comp G).Homotopic (ContinuousMap.id W) :=
    ContinuousMap.Homotopic.refl (ContinuousMap.id W)
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of W)) := topCatHomotopy_of_homotopic h2'
  exact Work.Cohomology.homologyEquiv ℤ (TopCat.of (C × W)) (TopCat.of W) f g h1 h2 k

/-- **The relative homology of `(C × Z, C × R)` is that of `(Z,R)`** for a contractible `C`: the
projection is a homotopy equivalence of pairs. -/
theorem relChains_prod_contractible (C Z : Type) [TopologicalSpace C] [TopologicalSpace Z]
    [ContractibleSpace C] (R : Set Z) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of (C × Z)) {x : C × Z | x.2 ∈ R}).homology m) ≅
      ((Work.Cohomology.relChains (TopCat.of Z) R).homology m)) := by
  let A : Set (C × Z) := {x : C × Z | x.2 ∈ R}
  let B : Set Z := R
  let f : TopCat.of (C × Z) ⟶ TopCat.of Z := TopCat.ofHom (ContinuousMap.snd : C(C × Z, Z))
  let g' : TopCat.of A ⟶ TopCat.of B := Work.StemsB.pairRestrict f A B (fun x hx => hx)
  -- the homeomorphism `A ≅ C × ↥R` and the second projection `C × ↥R → ↥R`
  let eHom : TopCat.of A ≃ₜ TopCat.of (C × ↥R) :=
    { toFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
      invFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
      left_inv := fun x => by ext <;> rfl
      right_inv := fun y => by ext <;> rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let s : TopCat.of A ⟶ TopCat.of (C × ↥R) := Work.StemsB.sphHomeoHom eHom
  let sndR : TopCat.of (C × ↥R) ⟶ TopCat.of ↥R :=
    TopCat.ofHom (ContinuousMap.snd : C(C × ↥R, ↥R))
  have hg_eq : g' = s ≫ sndR := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hg : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g') k) := by
    intro k
    have hchain : Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g'
        = Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of (C × ↥R)) s
          ≫ Work.Cohomology.chainMap ℤ (TopCat.of (C × ↥R)) (TopCat.of ↥R) sndR := by
      rw [hg_eq, ← Work.StemsB.chainMap_comp]
    rw [hchain, HomologicalComplex.homologyMap_comp]
    haveI hch : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of (C × ↥R)) s) :=
      Work.StemsB.isIso_chainMap_sphHomeoHom eHom
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of (C × ↥R)) s) k) :=
      Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k)
        (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of (C × ↥R)) s)
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (C × ↥R)) (TopCat.of ↥R) sndR) k) :=
      isIso_chainMap_snd_prod_contractible C ↥R k
    infer_instance
  have hw : CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.subtypeIncl (TopCat.of (C × Z)) A) f
      = CategoryTheory.CategoryStruct.comp g' (Work.Cohomology.subtypeIncl (TopCat.of Z) B) :=
    Work.StemsB.pairRestrict_comp_subtypeIncl f A B (fun x hx => hx)
  haveI : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf (TopCat.of (C × Z)) (TopCat.of Z) A B f g' hw) m) :=
    Work.Cohomology.relChainsMapOf_isIso (X := TopCat.of (C × Z)) (Y := TopCat.of Z)
      A B f g' hw m
      (fun k => isIso_chainMap_snd_prod_contractible C Z k) hg
  exact ⟨asIso (HomologicalComplex.homologyMap
    (Work.Cohomology.relChainsMapOf (TopCat.of (C × Z)) (TopCat.of Z) A B f g' hw) m)⟩


/-! ## The middle slab of the cover, with the parameter pair adjoined -/

/-- **The relative chains of the middle slab compute those of the `k`-cube pair** over the
parameter `midParam S = (1/4,3/4) × S`, with the relative set of the slab being the boundary part
together with the preimage of `R`.  This is the relativised form of `Work.StemsB.midRelIso`: the
last coordinate of a point of the middle slab is never `0` or `1`, so the boundary condition is
carried by the first `k` coordinates, and the `R`-condition is carried by the parameter. -/
theorem midRelChains_iso (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of ↥(Work.StemsB.slabMid (Y := S) k))
        ((Subtype.val) ⁻¹' (Work.StemsB.slabMid (Y := S) k ∩ (Work.StemsB.cubeBdry (Y := S) k ∪
          {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R})))).homology m) ≅
      ((Work.Cohomology.relChains (Work.StemsB.CubeSpace (Work.StemsB.midParam S) k)
        (Work.StemsB.cubeBdryK (Work.StemsB.midParam S) k ∪
          {p : Work.StemsB.CubeP (Work.StemsB.midParam S) k |
            p.2 ∈ {x : Work.StemsB.midParam S | x.2 ∈ R}})).homology m)) := by
  have key : ∀ z : ↥(Work.StemsB.slabMid (Y := S) k),
      z ∈ ((Subtype.val) ⁻¹' (Work.StemsB.slabMid (Y := S) k ∩
        (Work.StemsB.cubeBdry (Y := S) k ∪ {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R})))
      ↔ (Work.StemsB.midHomeo (Y := S) k) z ∈
        (Work.StemsB.cubeBdryK (Work.StemsB.midParam S) k ∪
          {p : Work.StemsB.CubeP (Work.StemsB.midParam S) k |
            p.2 ∈ {x : Work.StemsB.midParam S | x.2 ∈ R}}) := by
    intro z
    constructor
    · intro hz
      obtain ⟨-, hb | hq⟩ := hz
      · exact Or.inl (Work.StemsB.midTo_mem_bdry (Y := S) k ⟨z.2, hb⟩)
      · exact Or.inr hq
    · intro hz
      refine ⟨z.2, ?_⟩
      rcases hz with hb | hq
      · left
        have h := Work.StemsB.midFrom_mem_bdry (Y := S) k hb
        rw [show (Work.StemsB.midHomeo (Y := S) k) z = Work.StemsB.midTo (Y := S) k z from rfl]
          at h
        rw [Work.StemsB.midFrom_midTo] at h
        exact h.2
      · exact Or.inr hq
  exact Work.StemsB.nonempty_relChains_homology_iso_of_homeomorph
    (X := TopCat.of ↥(Work.StemsB.slabMid (Y := S) k))
    (Y := Work.StemsB.CubeSpace (Work.StemsB.midParam S) k)
    (Work.StemsB.midHomeo (Y := S) k) _ _ key m


/-! ## The slabs are acyclic relative to the boundary together with the parameter pair -/

/-- The relative set of the first slab with the parameter pair adjoined. -/
def slabBigA (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) :
    Set ↥(Work.StemsB.slabA (Y := S) k) :=
  (Subtype.val) ⁻¹' (Work.StemsB.slabA (Y := S) k ∩
    (Work.StemsB.cubeBdry (Y := S) k ∪ {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R}))

/-- The relative set of the second slab with the parameter pair adjoined. -/
def slabBigB (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) :
    Set ↥(Work.StemsB.slabB (Y := S) k) :=
  (Subtype.val) ⁻¹' (Work.StemsB.slabB (Y := S) k ∩
    (Work.StemsB.cubeBdry (Y := S) k ∪ {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R}))

/-- The homotopy `homA` preserves the boundary modulo the parameter pair. -/
theorem homA_mem_bdry_or (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S)
    (z : unitInterval × Work.StemsB.CubeP S (k+1)) (hzA : z.2 ∈ Work.StemsB.slabA (Y := S) k)
    (hz : z.2 ∈ Work.StemsB.cubeBdry (Y := S) k ∪
      {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R}) :
    Work.StemsB.homA (Y := S) k z ∈ Work.StemsB.cubeBdry (Y := S) k ∪
      {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R} := by
  rcases hz with hb | hq
  · exact Or.inl (Work.StemsB.homA_mem_bdry (Y := S) k hzA hb)
  · exact Or.inr (by simpa [Work.StemsB.homA_snd] using hq)

/-- The homotopy `homB` preserves the boundary modulo the parameter pair. -/
theorem homB_mem_bdry_or (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S)
    (z : unitInterval × Work.StemsB.CubeP S (k+1)) (hzB : z.2 ∈ Work.StemsB.slabB (Y := S) k)
    (hz : z.2 ∈ Work.StemsB.cubeBdry (Y := S) k ∪
      {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R}) :
    Work.StemsB.homB (Y := S) k z ∈ Work.StemsB.cubeBdry (Y := S) k ∪
      {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R} := by
  rcases hz with hb | hq
  · exact Or.inl (Work.StemsB.homB_mem_bdry (Y := S) k hzB hb)
  · exact Or.inr (by simpa [Work.StemsB.homB_snd] using hq)

/-- The push map of the first slab, restricted to the enlarged relative set. -/
def pushBigA (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) :
    TopCat.of (slabBigA k S R) ⟶ TopCat.of ↥(Work.StemsB.slabAi (Y := S) k) :=
  TopCat.ofHom
    ⟨fun x => ⟨⟨Work.StemsB.pushLast (Y := S) k x.1.1,
        Work.StemsB.pushLast_mem_slabA (Y := S) k x.1.1⟩,
      ⟨Work.StemsB.pushLast_mem_slabA (Y := S) k x.1.1,
        Work.StemsB.pushLast_mem_bdry (Y := S) k x.1.1⟩⟩,
      Continuous.subtype_mk (Continuous.subtype_mk
        ((Work.StemsB.continuous_pushLast (Y := S) k).comp
          (continuous_subtype_val.comp continuous_subtype_val)) _) _⟩

/-- The push map of the second slab, restricted to the enlarged relative set. -/
def pushBigB (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) :
    TopCat.of (slabBigB k S R) ⟶ TopCat.of ↥(Work.StemsB.slabBi (Y := S) k) :=
  TopCat.ofHom
    ⟨fun x => ⟨⟨Work.StemsB.pushToOne (Y := S) k x.1.1,
        Work.StemsB.pushToOne_mem_slabB (Y := S) k x.1.1⟩,
      ⟨Work.StemsB.pushToOne_mem_slabB (Y := S) k x.1.1,
        Work.StemsB.pushToOne_mem_bdry (Y := S) k x.1.1⟩⟩,
      Continuous.subtype_mk (Continuous.subtype_mk
        ((Work.StemsB.continuous_pushToOne (Y := S) k).comp
          (continuous_subtype_val.comp continuous_subtype_val)) _) _⟩

/-- The inclusion of the boundary part of the first slab into the enlarged relative set. -/
def inclBigA (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) :
    TopCat.of ↥(Work.StemsB.slabAi (Y := S) k) ⟶ TopCat.of (slabBigA k S R) :=
  Work.StemsB.pairRestrict (𝟙 (TopCat.of ↥(Work.StemsB.slabA (Y := S) k)))
    (Work.StemsB.slabAi (Y := S) k) (slabBigA k S R) (fun _ hx => ⟨hx.1, Or.inl hx.2⟩)

/-- The inclusion of the boundary part of the second slab into the enlarged relative set. -/
def inclBigB (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) :
    TopCat.of ↥(Work.StemsB.slabBi (Y := S) k) ⟶ TopCat.of (slabBigB k S R) :=
  Work.StemsB.pairRestrict (𝟙 (TopCat.of ↥(Work.StemsB.slabB (Y := S) k)))
    (Work.StemsB.slabBi (Y := S) k) (slabBigB k S R) (fun _ hx => ⟨hx.1, Or.inl hx.2⟩)

/-- The underlying continuous map of the homotopy on the enlarged relative set of the first
slab. -/
def homABigA (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) :
    C(unitInterval × ↥(slabBigA k S R), Work.StemsB.CubeP S (k+1)) :=
  ⟨fun z => Work.StemsB.homA (Y := S) k (z.1, z.2.1.1),
    (Work.StemsB.continuous_homA (Y := S) k).comp
      (Continuous.prodMk continuous_fst
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))⟩

/-- The underlying continuous map of the homotopy on the enlarged relative set of the second
slab. -/
def homABigB (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) :
    C(unitInterval × ↥(slabBigB k S R), Work.StemsB.CubeP S (k+1)) :=
  ⟨fun z => Work.StemsB.homB (Y := S) k (z.1, z.2.1.1),
    (Work.StemsB.continuous_homB (Y := S) k).comp
      (Continuous.prodMk continuous_fst
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))⟩

/-- The deformation of the enlarged relative set of the first slab onto its boundary part. -/
def homBigA (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) :
    TopCat.Homotopy (pushBigA k S R ≫ inclBigA k S R)
      (𝟙 (TopCat.of ↥(slabBigA k S R))) :=
  ContinuousMap.Homotopy.mk
    ⟨fun z => ⟨⟨homABigA k S R z, Work.StemsB.homA_mem_slabA (Y := S) k z.2.2.1⟩,
        ⟨Work.StemsB.homA_mem_slabA (Y := S) k z.2.2.1,
          homA_mem_bdry_or k S R (z.1, z.2.1.1) z.2.2.1 z.2.2.2⟩⟩,
      ((homABigA k S R).continuous.subtype_mk _).subtype_mk _⟩
    (fun p => by
      apply Subtype.ext
      apply Subtype.ext
      change Work.StemsB.homA (Y := S) k ((0 : unitInterval), p.1.1)
        = Work.StemsB.pushLast (Y := S) k p.1.1
      rw [Work.StemsB.homA_zero])
    (fun p => by
      apply Subtype.ext
      apply Subtype.ext
      change Work.StemsB.homA (Y := S) k ((1 : unitInterval), p.1.1) = p.1.1
      rw [Work.StemsB.homA_one])

/-- The deformation of the enlarged relative set of the second slab onto its boundary part. -/
def homBigB (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) :
    TopCat.Homotopy (pushBigB k S R ≫ inclBigB k S R)
      (𝟙 (TopCat.of ↥(slabBigB k S R))) :=
  ContinuousMap.Homotopy.mk
    ⟨fun z => ⟨⟨homABigB k S R z, Work.StemsB.homB_mem_slabB (Y := S) k z.2.2.1⟩,
        ⟨Work.StemsB.homB_mem_slabB (Y := S) k z.2.2.1,
          homB_mem_bdry_or k S R (z.1, z.2.1.1) z.2.2.1 z.2.2.2⟩⟩,
      ((homABigB k S R).continuous.subtype_mk _).subtype_mk _⟩
    (fun p => by
      apply Subtype.ext
      apply Subtype.ext
      change Work.StemsB.homB (Y := S) k ((0 : unitInterval), p.1.1)
        = Work.StemsB.pushToOne (Y := S) k p.1.1
      rw [Work.StemsB.homB_zero])
    (fun p => by
      apply Subtype.ext
      apply Subtype.ext
      change Work.StemsB.homB (Y := S) k ((1 : unitInterval), p.1.1) = p.1.1
      rw [Work.StemsB.homB_one])

/-- The homotopy inverse composite for the enlarged relative set of the first slab. -/
def homBigA_inv (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) :
    TopCat.Homotopy (inclBigA k S R ≫ pushBigA k S R)
      (𝟙 (TopCat.of ↥(Work.StemsB.slabAi (Y := S) k))) := by
  have h : inclBigA k S R ≫ pushBigA k S R
      = Work.StemsB.inclSlabA (Y := S) k ≫ Work.StemsB.pushSlabA (Y := S) k := by
    apply TopCat.hom_ext
    ext x <;> rfl
  rw [h]
  exact Work.StemsB.homSlabAi (Y := S) k

/-- The homotopy inverse composite for the enlarged relative set of the second slab. -/
def homBigB_inv (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) :
    TopCat.Homotopy (inclBigB k S R ≫ pushBigB k S R)
      (𝟙 (TopCat.of ↥(Work.StemsB.slabBi (Y := S) k))) := by
  have h : inclBigB k S R ≫ pushBigB k S R
      = Work.StemsB.inclSlabB (Y := S) k ≫ Work.StemsB.pushSlabB (Y := S) k := by
    apply TopCat.hom_ext
    ext x <;> rfl
  rw [h]
  exact Work.StemsB.homSlabBi (Y := S) k

/-- **The first slab is acyclic relative to the boundary together with the parameter pair.** -/
theorem isZero_relChains_slabBigA (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(Work.StemsB.slabA (Y := S) k))
      (slabBigA k S R)).homology m) := by
  let X : TopCat := TopCat.of ↥(Work.StemsB.slabA (Y := S) k)
  let Y : TopCat := TopCat.of ↥(slabBigA k S R)
  let push' : X ⟶ Y := Work.StemsB.pushSlabA (Y := S) k ≫ inclBigA k S R
  have h1 : TopCat.Homotopy (Work.Cohomology.subtypeIncl X (slabBigA k S R) ≫ push')
      (𝟙 Y) := by
    have heq : Work.Cohomology.subtypeIncl X (slabBigA k S R) ≫ push'
        = pushBigA k S R ≫ inclBigA k S R := by
      apply TopCat.hom_ext
      ext x <;> rfl
    rw [heq]
    exact homBigA k S R
  have h2 : TopCat.Homotopy (push' ≫ Work.Cohomology.subtypeIncl X (slabBigA k S R))
      (𝟙 X) := by
    have heq : push' ≫ Work.Cohomology.subtypeIncl X (slabBigA k S R)
        = Work.StemsB.pushSlabA (Y := S) k ≫ Work.StemsB.inclSlabA (Y := S) k := by
      apply TopCat.hom_ext
      ext x <;> rfl
    rw [heq]
    exact Work.StemsB.homSlabA (Y := S) k
  have hiso : ∀ n, IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl ℤ X (slabBigA k S R)) n) :=
    fun n => Work.Cohomology.homologyEquiv ℤ Y X
      (Work.Cohomology.subtypeIncl X (slabBigA k S R)) push' h1 h2 n
  cases m with
  | zero =>
      exact Work.ThreeConnected.Excision.isZero_homology_zero_of_cokernel_pi_eq_zero
        (Work.Cohomology.inclChains X (slabBigA k S R))
        (Work.ThreeConnected.Excision.homologyMap_cokernel_pi_eq_zero
          (Work.Cohomology.subtypeIncl X (slabBigA k S R)) push' ⟨h2⟩ 0)
  | succ j =>
      exact Work.StemsB.isZero_relChainsR_homology_succ_of_isIso ℤ X (slabBigA k S R) j
        (hiso (j + 1)) (hiso j)

/-- **The second slab is acyclic relative to the boundary together with the parameter pair.** -/
theorem isZero_relChains_slabBigB (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(Work.StemsB.slabB (Y := S) k))
      (slabBigB k S R)).homology m) := by
  let X : TopCat := TopCat.of ↥(Work.StemsB.slabB (Y := S) k)
  let Y : TopCat := TopCat.of ↥(slabBigB k S R)
  let push' : X ⟶ Y := Work.StemsB.pushSlabB (Y := S) k ≫ inclBigB k S R
  have h1 : TopCat.Homotopy (Work.Cohomology.subtypeIncl X (slabBigB k S R) ≫ push')
      (𝟙 Y) := by
    have heq : Work.Cohomology.subtypeIncl X (slabBigB k S R) ≫ push'
        = pushBigB k S R ≫ inclBigB k S R := by
      apply TopCat.hom_ext
      ext x <;> rfl
    rw [heq]
    exact homBigB k S R
  have h2 : TopCat.Homotopy (push' ≫ Work.Cohomology.subtypeIncl X (slabBigB k S R))
      (𝟙 X) := by
    have heq : push' ≫ Work.Cohomology.subtypeIncl X (slabBigB k S R)
        = Work.StemsB.pushSlabB (Y := S) k ≫ Work.StemsB.inclSlabB (Y := S) k := by
      apply TopCat.hom_ext
      ext x <;> rfl
    rw [heq]
    exact Work.StemsB.homSlabB (Y := S) k
  have hiso : ∀ n, IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl ℤ X (slabBigB k S R)) n) :=
    fun n => Work.Cohomology.homologyEquiv ℤ Y X
      (Work.Cohomology.subtypeIncl X (slabBigB k S R)) push' h1 h2 n
  cases m with
  | zero =>
      exact Work.ThreeConnected.Excision.isZero_homology_zero_of_cokernel_pi_eq_zero
        (Work.Cohomology.inclChains X (slabBigB k S R))
        (Work.ThreeConnected.Excision.homologyMap_cokernel_pi_eq_zero
          (Work.Cohomology.subtypeIncl X (slabBigB k S R)) push' ⟨h2⟩ 0)
  | succ j =>
      exact Work.StemsB.isZero_relChainsR_homology_succ_of_isIso ℤ X (slabBigB k S R) j
        (hiso (j + 1)) (hiso j)

/-- **The first small-chains term of the relative Mayer–Vietoris sequence vanishes in every
degree**, for the cube pair with the parameter pair adjoined. -/
theorem isZero_relSmallChains_slabBigA (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S)
    (m : ℕ) :
    IsZero ((Work.Cohomology.relSmallChains (X := Work.StemsB.CubeSpace S (k+1))
      (Work.StemsB.slabA (Y := S) k) (Work.StemsB.slabB (Y := S) k)
      (Work.StemsB.slabA (Y := S) k)
      (Work.StemsB.slabA (Y := S) k ∩ (Work.StemsB.cubeBdry (Y := S) k ∪
        {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R}))
      (Set.inter_subset_left : Work.StemsB.slabA (Y := S) k ∩
        (Work.StemsB.cubeBdry (Y := S) k ∪ {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R})
        ⊆ Work.StemsB.slabA (Y := S) k)).homology m) := by
  obtain ⟨e⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains
    (X := Work.StemsB.CubeSpace S (k+1)) (Work.StemsB.slabA (Y := S) k)
    (Work.StemsB.slabB (Y := S) k) (Work.StemsB.slabA (Y := S) k)
    (Work.StemsB.slabA (Y := S) k ∩ (Work.StemsB.cubeBdry (Y := S) k ∪
      {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R}))
    (Set.inter_subset_left : Work.StemsB.slabA (Y := S) k ∩
      (Work.StemsB.cubeBdry (Y := S) k ∪ {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R})
      ⊆ Work.StemsB.slabA (Y := S) k)
    (Or.inl subset_rfl)
  exact IsZero.of_iso (isZero_relChains_slabBigA k S R m)
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso e)

/-- **The second small-chains term of the relative Mayer–Vietoris sequence vanishes in every
degree**, for the cube pair with the parameter pair adjoined. -/
theorem isZero_relSmallChains_slabBigB (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S)
    (m : ℕ) :
    IsZero ((Work.Cohomology.relSmallChains (X := Work.StemsB.CubeSpace S (k+1))
      (Work.StemsB.slabA (Y := S) k) (Work.StemsB.slabB (Y := S) k)
      (Work.StemsB.slabB (Y := S) k)
      (Work.StemsB.slabB (Y := S) k ∩ (Work.StemsB.cubeBdry (Y := S) k ∪
        {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R}))
      (Set.inter_subset_left : Work.StemsB.slabB (Y := S) k ∩
        (Work.StemsB.cubeBdry (Y := S) k ∪ {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R})
        ⊆ Work.StemsB.slabB (Y := S) k)).homology m) := by
  obtain ⟨e⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains
    (X := Work.StemsB.CubeSpace S (k+1)) (Work.StemsB.slabA (Y := S) k)
    (Work.StemsB.slabB (Y := S) k) (Work.StemsB.slabB (Y := S) k)
    (Work.StemsB.slabB (Y := S) k ∩ (Work.StemsB.cubeBdry (Y := S) k ∪
      {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R}))
    (Set.inter_subset_left : Work.StemsB.slabB (Y := S) k ∩
      (Work.StemsB.cubeBdry (Y := S) k ∪ {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R})
      ⊆ Work.StemsB.slabB (Y := S) k)
    (Or.inr subset_rfl)
  exact IsZero.of_iso (isZero_relChains_slabBigB k S R m)
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso e)

/-- **The homology of a biproduct of chain complexes vanishes in a degree when both factors
do.** -/
theorem isZero_homology_biprod' {C D : ChainComplex (ModuleCat ℤ) ℕ} {n : ℕ}
    (hC : IsZero (C.homology n)) (hD : IsZero (D.homology n)) :
    IsZero ((C ⊞ D).homology n) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n
  have h : IsZero (F.obj (C ⊞ D)) := by
    rw [IsZero.iff_id_eq_zero]
    have hfst : F.map (biprod.fst : C ⊞ D ⟶ C) = 0 := hC.eq_of_tgt _ 0
    have hsnd : F.map (biprod.snd : C ⊞ D ⟶ D) = 0 := hD.eq_of_tgt _ 0
    calc 𝟙 (F.obj (C ⊞ D)) = F.map (𝟙 (C ⊞ D)) := (F.map_id _).symm
      _ = F.map (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) := by rw [biprod.total]
      _ = F.map (biprod.fst ≫ biprod.inl) + F.map (biprod.snd ≫ biprod.inr) := F.map_add
      _ = F.map biprod.fst ≫ F.map biprod.inl + F.map biprod.snd ≫ F.map biprod.inr := by
            rw [F.map_comp, F.map_comp]
      _ = 0 := by rw [hfst, hsnd, zero_comp, zero_comp, add_zero]
  simpa [F] using h

/-- **The middle term of the relative Mayer–Vietoris sequence of the cube cover vanishes in every
degree**, for the cube pair with the parameter pair adjoined. -/
theorem isZero_relMVH2_cubeRel (k : ℕ) (S : Type) [TopologicalSpace S] (R : Set S) (m : ℕ) :
    IsZero (Work.Cohomology.relMVH₂ (Work.StemsB.CubeSpace S (k+1))
      (Work.StemsB.cubeBdry (Y := S) k ∪ {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R})
      (Work.StemsB.slabA (Y := S) k) (Work.StemsB.slabB (Y := S) k) m) :=
  isZero_homology_biprod' (isZero_relSmallChains_slabBigA k S R m)
    (isZero_relSmallChains_slabBigB k S R m)

/-! ## The induction -/

/-- **The pair form of the relative homology of the cube pair.**  For every `k`, every space `S`
and every subset `R ⊆ S`, the `(j+k)`-th relative homology of `(Iᵏ × S, ∂Iᵏ × S ∪ Iᵏ × R)` is the
`j`-th relative homology of `(S,R)`. -/
theorem cubePairRelHomology_aux (k : ℕ) :
    ∀ (S : Type) [TopologicalSpace S] (R : Set S) (j : ℕ),
      Nonempty (((Work.Cohomology.relChains (Work.StemsB.CubeSpace S k)
        (Work.StemsB.cubeBdryK S k ∪ {p : Work.StemsB.CubeP S k | p.2 ∈ R})).homology (j + k)) ≅
      ((Work.Cohomology.relChains (TopCat.of S) R).homology j)) := by
  induction k with
  | zero =>
      intro S _ R j
      obtain ⟨e⟩ := cubePairRelHomology_zero S R j
      exact ⟨(eqToIso (congrArg (fun n => (Work.Cohomology.relChains (Work.StemsB.CubeSpace S 0)
        (Work.StemsB.cubeBdryK S 0 ∪ {p : Work.StemsB.CubeP S 0 | p.2 ∈ R})).homology n)
        (Nat.add_zero j))).trans e⟩
  | succ k ih =>
      intro S _ R j
      -- the cube pair, and the cover by the two slabs
      let X : TopCat := Work.StemsB.CubeSpace S (k+1)
      let A : Set X := Work.StemsB.cubeBdry (Y := S) k ∪
        {p : Work.StemsB.CubeP S (k+1) | p.2 ∈ R}
      let U : Set X := Work.StemsB.slabA (Y := S) k
      let V : Set X := Work.StemsB.slabB (Y := S) k
      haveI hδ : IsIso (Work.Cohomology.relMVδ X A U V (j + k)) :=
        Work.ThreeConnected.Excision.relMV_iso_of_acyclic (X := X) A U V
          (isZero_relMVH2_cubeRel k S R) (j + k)
      -- the identification of the first Mayer–Vietoris term with the middle slab
      obtain ⟨e₁₀⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains
        (X := X) U V (Work.StemsB.slabMid (Y := S) k) (Work.StemsB.slabMid (Y := S) k ∩ A)
        (Set.inter_subset_left : Work.StemsB.slabMid (Y := S) k ∩ A
          ⊆ Work.StemsB.slabMid (Y := S) k)
        (Or.inl (by intro x hx; exact hx.1))
      let e₁ := (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ)
        (j + k)).mapIso e₁₀
      -- the middle slab is the `k`-cube pair over `midParam S`
      obtain ⟨e₂⟩ := midRelChains_iso k S R (j + k)
      -- the induction hypothesis, over the parameter space `midParam S`
      obtain ⟨e₃⟩ := ih (Work.StemsB.midParam S)
        {x : Work.StemsB.midParam S | x.2 ∈ R} j
      -- removing the contractible factor `(1/4,3/4)`
      haveI : ContractibleSpace ↥(Set.Ioo (1/4:ℝ) (3/4)) :=
        Convex.contractibleSpace (convex_Ioo (1/4:ℝ) (3/4)) ⟨1/2, by norm_num⟩
      obtain ⟨e₄⟩ := relChains_prod_contractible ↥(Set.Ioo (1/4:ℝ) (3/4)) S R j
      refine ⟨(Work.Cohomology.relMVSmallIso X A U V (Work.StemsB.isOpen_slabA (Y := S) k)
          (Work.StemsB.isOpen_slabB (Y := S) k) (Work.StemsB.slabA_union_slabB (Y := S) k)
          ((j + k) + 1)).symm
        ≪≫ asIso (Work.Cohomology.relMVδ X A U V (j + k)) ≪≫ e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄⟩

/-- **The pair form of the relative homology of the cube pair.**  For the cube pair
`(Iᵏ × P, ∂Iᵏ × P ∪ Iᵏ × Q)` the `(j+k)`-th relative homology is the `j`-th relative homology of
`(P,Q)`.

The proof is by induction on `k`.  The induction step is the Mayer–Vietoris sequence of the cover
of the cube by the two slabs `{last < 3/4}` and `{last > 1/4}`: the middle term vanishes (each slab
deformation-retracts onto its boundary face, which lies in the relative set —
`isZero_relMVH2_cubeRel`), so the connecting map is an isomorphism, and the first term of the
sequence is the middle slab, which is the `k`-cube pair over `(1/4,3/4) × P`
(`midRelChains_iso`); splitting off the contractible factor `(1/4,3/4)`
(`relChains_prod_contractible`) leaves the induction hypothesis.  The base case `k = 0` is the
homeomorphism `I⁰ × P ≅ P`. -/
theorem cubePairRelHomology (k : ℕ) (P : Type) [TopologicalSpace P] (Q : Set P) (j : ℕ) :
    Nonempty (((Work.Cohomology.relChains (Work.StemsB.CubeSpace P k)
        (Work.StemsB.cubeBdryK P k ∪ {p : Work.StemsB.CubeP P k | p.2 ∈ Q})).homology (j + k)) ≅
      ((Work.Cohomology.relChains (TopCat.of P) Q).homology j)) :=
  cubePairRelHomology_aux k P Q j

end

end Work.Serre
