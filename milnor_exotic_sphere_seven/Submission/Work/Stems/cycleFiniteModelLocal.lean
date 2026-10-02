import Mathlib
import Submission.Work.Stems.cycleLiftOfIso
import Submission.Work.StemsB.compactSupportChain
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.StemsB.killToFgModel
import Submission.Work.StemsB.descentCells
import Submission.Work.StemsB.attachSubmodel
import Submission.Work.StemsB.wedgePiKfinite
import Submission.Work.Serre.serreK2
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.Stems.subsingleton_of_contractible
import Submission.Work.StemsB.PiMap
import Submission.Work.StemsB.injective_chainMap
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.Serre.Models
import Submission.Work.Cohomology.Pullback
import Submission.Work.Serre.CWModel.Defs
import Submission.Work.Serre.surjective_pimap_setIncl_of_compressRel
import Submission.Work.AttachPush.exists_homotopy_avoids_cellOrigins
import Submission.Work.RatHurewicz.compressRel_attachCells_range

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A rational cycle of a range model comes from a finite model (area STEMS)

This file proves `Work.Stems.CycleFiniteModelLocal`, the first geometric input of the reduction of
`Work.RatHurewicz.RangeModelRatAcyclic` to its finitely generated case; the statement is the one
introduced in `Submission/Work/Stems/cycleLiftOfIso.lean`, and the proof below is the
`Submission/Work/StemsB/cycleFiniteModel.lean` development, carried over to area STEMS (that module
does not build at present because the interface of `Work.StemsB.cycleLift` changed; here the
cycle-lifting step uses the already available `Work.Stems.cycleLift_of_isIso`, which is exactly the
"up to a boundary" form the argument needs, and the bookkeeping lemmas
`Work.Stems.chainMap_comp_eq` / `Work.Stems.chainMap_d_apply` are imported from
`Submission/Work/Stems/cycleLiftOfIso.lean` instead of being restated).

The helper lemmas are kept in namespace `Work.Stems`; the final statement
`Work.Stems.cycleFiniteModelLocal` is the requested one, and the full-strength explicit-argument
form is `Work.Stems.cycleFiniteModelLocal_aux`.

The route is the "CW model" route: take the cell model `Γ → Z` of `Z` in the homotopy range
(`Work.Serre.CWModel.exists_model`, π-bijective through degree `2k`), lift the cycle along the
induced isomorphism on rational homology (`Work.Serre.serreK2` + `Work.Stems.cycleLift_of_isIso`),
and replace `Γ` by a *finite submodel* `W ⊆ Γ` containing the (compact) support of the lifted
cycle.  The finite submodel is produced by the tower induction `Work.Stems.towerA_submodel`: a
compact subset of an iterated cell attachment meets only finitely many cells, so a finite family of
cells of the tower can be chosen whose restricted attachment contains the compact set; the existence
of that family, together with the restricted attachment and its embedding into the tower, is
`Work.StemsB.descentCells` + `Work.StemsB.attachSubmodel`.
-/

open scoped Topology Topology.Homotopy unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Stems

noncomputable section

open Work.RatHurewicz Work.Serre.CWModel

set_option maxHeartbeats 8000000

/-- `π_k` of a subsingleton additive group is finitely generated. -/
theorem moduleFinite_of_subsingleton {M : Type} [AddCommGroup M] [Module ℤ M]
    (h : Subsingleton M) : Module.Finite ℤ M :=
  Module.Finite.of_fg_top (by
    rw [Subsingleton.elim (⊤ : Submodule ℤ M) ⊥]
    exact Submodule.fg_bot)

/-- Surjectivity transfers triviality. -/
theorem subsingleton_of_surjective' {α β : Type*} (f : α → β)
    (hf : Function.Surjective f) (hα : Subsingleton α) : Subsingleton β := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hf a
  obtain ⟨b', rfl⟩ := hf b
  rw [Subsingleton.elim a' b']

/-- Triviality of a group transfers along a surjective homomorphism. -/
theorem subsingleton_of_surjective_mulHom {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (hG : Subsingleton G) : Subsingleton H :=
  subsingleton_of_surjective' (⇑f) hf hG

/-- Finite generation of `π_k` transfers along a surjective homomorphism. -/
theorem moduleFinite_of_surjective_mulHom {G H : Type} [CommGroup G] [CommGroup H] (f : G →* H)
    (hf : Function.Surjective f) [Module.Finite ℤ (Additive G)] : Module.Finite ℤ (Additive H) := by
  let L : Additive G →ₗ[ℤ] Additive H :=
    { toFun := fun z => Additive.ofMul (f (Additive.toMul z))
      map_add' := fun z z' => by
        change Additive.ofMul (f (Additive.toMul z * Additive.toMul z'))
          = Additive.ofMul (f (Additive.toMul z)) + Additive.ofMul (f (Additive.toMul z'))
        rw [map_mul]; rfl
      map_smul' := fun n z => by
        change Additive.ofMul (f (Additive.toMul z ^ n))
          = n • Additive.ofMul (f (Additive.toMul z))
        rw [map_zpow]; rfl }
  have hfgG : (⊤ : Submodule ℤ (Additive G)).FG := Module.Finite.fg_top
  have h1 := hfgG.map L
  rw [Module.finite_def]
  rwa [Submodule.map_top, LinearMap.range_eq_top.mpr (fun y => ?_)] at h1
  obtain ⟨z, hz⟩ := hf (Additive.toMul y)
  exact ⟨Additive.ofMul z, by
    change Additive.ofMul (f z) = y
    rw [hz]
    simp⟩

/-- **A submodel of a space**: an embedded subspace which is `(k-1)`-connected with finitely
generated `π_k`. -/
structure SubModel (k : ℕ) (hk : 2 ≤ k) (Y : Type) [TopologicalSpace Y] where
  W : Type
  inst : TopologicalSpace W
  w₀ : W
  ψ : @ContinuousMap W Y inst _
  emb : Topology.IsEmbedding (ψ : W → Y)
  conn : ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) W w₀)
  fgk : letI : k.AtLeastTwo := ⟨hk⟩
    Module.Finite ℤ (Additive (HomotopyGroup (Fin k) W w₀))

attribute [instance] SubModel.inst

/-- The trivial submodel of a point. -/
def subModelPUnit (k : ℕ) (hk : 2 ≤ k) : SubModel k hk PUnit where
  W := PUnit
  inst := inferInstance
  w₀ := ⟨⟩
  ψ := ContinuousMap.id PUnit
  emb := Topology.IsEmbedding.id
  conn := by
    intro i hi
    haveI : Subsingleton (HomotopyGroup (Fin i) PUnit (⟨⟩ : PUnit)) :=
      Work.Stems.subsingleton_of_contractible (⟨⟩ : PUnit)
    infer_instance
  fgk := by
    haveI : k.AtLeastTwo := ⟨hk⟩
    haveI : Subsingleton (HomotopyGroup (Fin k) PUnit (⟨⟩ : PUnit)) :=
      Work.Stems.subsingleton_of_contractible (⟨⟩ : PUnit)
    haveI : Subsingleton (Additive (HomotopyGroup (Fin k) PUnit (⟨⟩ : PUnit))) :=
      ⟨fun a b => Subsingleton.elim _ _⟩
    exact moduleFinite_of_subsingleton inferInstance

/-- Triviality of `π_i` transports to the range of an embedding. -/
theorem subsingleton_range_of_isEmbedding {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : Topology.IsEmbedding (f : X → Y)) (x₀ : X) (i : ℕ) [Nonempty (Fin i)]
    (h : Subsingleton (HomotopyGroup (Fin i) X x₀)) :
    Subsingleton (HomotopyGroup (Fin i) (Set.range (f : X → Y)) ⟨f x₀, x₀, rfl⟩) := by
  obtain ⟨e⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin i) hf.toHomeomorph.toHomotopyEquiv x₀
  have h1 : Subsingleton (HomotopyGroup (Fin i) (Set.range (f : X → Y))
      (hf.toHomeomorph.toHomotopyEquiv.toFun x₀)) :=
    ⟨fun a b => e.symm.injective (h.elim _ _)⟩
  exact (show hf.toHomeomorph.toHomotopyEquiv.toFun x₀ = ⟨f x₀, x₀, rfl⟩ from rfl) ▸ h1

/-- Finite generation of `π_k` transports to the range of an embedding. -/
theorem moduleFinite_range_of_isEmbedding {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : Topology.IsEmbedding (f : X → Y)) (x₀ : X) (k : ℕ) [Nontrivial (Fin k)]
    [Module.Finite ℤ (Additive (HomotopyGroup (Fin k) X x₀))] :
    Module.Finite ℤ (Additive (HomotopyGroup (Fin k) (Set.range (f : X → Y))
      ⟨f x₀, x₀, rfl⟩)) := by
  obtain ⟨e⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin k) hf.toHomeomorph.toHomotopyEquiv x₀
  have h1 : Module.Finite ℤ (Additive (HomotopyGroup (Fin k) (Set.range (f : X → Y))
      (hf.toHomeomorph.toHomotopyEquiv.toFun x₀))) :=
    Module.Finite.equiv (e.toAdditive.toIntLinearEquiv)
  exact (show hf.toHomeomorph.toHomotopyEquiv.toFun x₀ = ⟨f x₀, x₀, rfl⟩ from rfl) ▸ h1

open scoped Topology Topology.Homotopy unitInterval
open CategoryTheory CategoryTheory.Limits

open Work.RatHurewicz Work.Serre.CWModel

/-- The inclusion `attachIncl` is an embedding. -/
theorem isEmbedding_attachIncl (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) : Topology.IsEmbedding (attachIncl n Y ι f) :=
  ⟨Work.RatHurewicz.isInducing_attachIncl n Y ι f,
    Work.RatHurewicz.AttachRange.attachIncl_injective n Y ι f⟩

/-- **The high step**: attaching cells of dimension `≥ k+1` to a submodel extends it. -/
theorem attachStep_submodel {k : ℕ} (hk : 2 ≤ k) (n' : ℕ) {Y : Type} [TopologicalSpace Y]
    {ι : Type} (f : ι → C(cellSphere n', Y)) (hdeg : k + 1 ≤ n' + 2)
    {K : Set (attachCells n' Y ι f)} (hK : IsCompact K)
    (J : Finset ι) (K₀ : Set Y) (hK₀ : IsCompact K₀)
    (himg : ∀ i ∈ J, Set.range (f i) ⊆ K₀)
    (hcov : ∀ x ∈ K, x ∈ Set.range (attachIncl n' Y ι f)
      ∪ ⋃ i ∈ (J : Set ι), Set.range (cellMap n' Y ι f i))
    (hdesc : ∀ x ∈ K, x ∈ Set.range (attachIncl n' Y ι f) →
      ∃ y ∈ K₀, attachIncl n' Y ι f y = x)
    (S : SubModel k hk Y) (hS : K₀ ⊆ Set.range (S.ψ : S.W → Y)) :
    ∃ (S' : SubModel k hk (attachCells n' Y ι f)), K ⊆ Set.range (S'.ψ : S'.W → _) := by
  classical
  have himg' : ∀ j : {i // i ∈ J}, Set.range (f (j.1)) ⊆ Set.range (S.ψ : S.W → Y) :=
    fun j x hx => hS (himg j.1 j.2 hx)
  obtain ⟨h, hcompat, ψ', q, hemb, hcomp, hrange⟩ :=
    Work.StemsB.attachSubmodel n' Y ι f S.W S.ψ S.emb (fun j : {i // i ∈ J} => j.1)
      Subtype.val_injective himg'
  let W' : Type := attachCells n' S.W {i // i ∈ J} h
  letI : TopologicalSpace W' := inferInstance
  let w₀' : W' := attachIncl n' S.W _ h S.w₀
  haveI : k.AtLeastTwo := ⟨hk⟩
  have hembAtt : Topology.IsEmbedding (attachIncl n' S.W {i // i ∈ J} h) :=
    isEmbedding_attachIncl n' S.W {i // i ∈ J} h
  have hconn : ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) W' w₀') := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have hZ : Subsingleton (ZerothHomotopy S.W) := by
        refine ⟨fun a b => ?_⟩
        have h0 : Subsingleton (HomotopyGroup (Fin 0) S.W S.w₀) := S.conn 0 (by omega)
        exact (HomotopyGroup.pi0EquivZerothHomotopy (X := S.W) (x := S.w₀)).symm.injective
          (h0.elim _ _)
      haveI : PathConnectedSpace S.W :=
        pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk S.w₀⟩, hZ⟩
      haveI : PathConnectedSpace W' := pathConnectedSpace_attachCells n' S.W _ h
      exact (HomotopyGroup.pi0EquivZerothHomotopy (X := W') (x := w₀')).injective.subsingleton
    · have hsi : i - 1 + 1 = i := Nat.sub_add_cancel hpos
      haveI : NeZero (i - 1 + 1) := ⟨by omega⟩
      have hsurj := Work.Serre.surjective_pimap_setIncl_of_compressRel
        (A := Set.range (attachIncl n' S.W {i // i ∈ J} h))
        (⟨w₀', ⟨S.w₀, by simp [w₀']⟩⟩ : Set.range (attachIncl n' S.W {i // i ∈ J} h))
        i (fun d hd => compressRel_attachCells_range n' S.W {i // i ∈ J} h d (by omega))
        (i - 1) (by omega)
      have htriv : Subsingleton (HomotopyGroup (Fin (i - 1 + 1))
          (Set.range (attachIncl n' S.W {i // i ∈ J} h))
          (⟨w₀', ⟨S.w₀, by simp [w₀']⟩⟩ : Set.range (attachIncl n' S.W {i // i ∈ J} h))) := by
        have hbase : (⟨w₀', ⟨S.w₀, by simp [w₀']⟩⟩ :
            Set.range (attachIncl n' S.W {i // i ∈ J} h)) =
            (⟨attachIncl n' S.W {i // i ∈ J} h S.w₀, S.w₀, rfl⟩ :
              Set.range (attachIncl n' S.W {i // i ∈ J} h)) := Subtype.ext rfl
        rw [hbase]
        haveI : Nonempty (Fin i) := ⟨⟨0, hpos⟩⟩
        have h := subsingleton_range_of_isEmbedding (attachIncl n' S.W {i // i ∈ J} h) hembAtt
          S.w₀ i (S.conn i hi)
        simpa only [hsi] using h
      have hpt : (Work.RatHurewicz.setIncl (Set.range (attachIncl n' S.W {i // i ∈ J} h)))
          (⟨w₀', ⟨S.w₀, by simp [w₀']⟩⟩ : Set.range (attachIncl n' S.W {i // i ∈ J} h))
          = w₀' := rfl
      have key := subsingleton_of_surjective_mulHom
        (Work.StemsB.πmap (Work.RatHurewicz.setIncl (Set.range (attachIncl n' S.W {i // i ∈ J} h)))
          (i - 1) (⟨w₀', ⟨S.w₀, by simp [w₀']⟩⟩ :
            Set.range (attachIncl n' S.W {i // i ∈ J} h))) hsurj htriv
      simpa only [hsi, hpt] using key
  have hfgk : (letI : k.AtLeastTwo := ⟨hk⟩
      Module.Finite ℤ (Additive (HomotopyGroup (Fin k) W' w₀'))) := by
    haveI : k.AtLeastTwo := ⟨hk⟩
    have hsk : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    haveI : (k - 1 + 1).AtLeastTwo := ⟨by omega⟩
    have hsurj := Work.Serre.surjective_pimap_setIncl_of_compressRel
      (A := Set.range (attachIncl n' S.W {i // i ∈ J} h))
      (⟨w₀', ⟨S.w₀, by simp [w₀']⟩⟩ : Set.range (attachIncl n' S.W {i // i ∈ J} h))
      k (fun d hd => compressRel_attachCells_range n' S.W {i // i ∈ J} h d (by omega))
      (k - 1) (by omega)
    have hfgA : Module.Finite ℤ (Additive (HomotopyGroup (Fin (k - 1 + 1))
        (Set.range (attachIncl n' S.W {i // i ∈ J} h))
        (⟨attachIncl n' S.W {i // i ∈ J} h S.w₀, S.w₀, rfl⟩ : Set.range _))) := by
      haveI : Module.Finite ℤ (Additive (HomotopyGroup (Fin k) S.W S.w₀)) := by
        simpa [SubModel.fgk] using S.fgk
      haveI := moduleFinite_range_of_isEmbedding (attachIncl n' S.W {i // i ∈ J} h) hembAtt S.w₀ k
      exact Module.Finite.equiv ((Work.StemsB.indexCastMulEquiv
        (⟨attachIncl n' S.W {i // i ∈ J} h S.w₀, S.w₀, rfl⟩ : Set.range _) hsk).symm.toAdditive
          |>.toIntLinearEquiv)
    haveI := hfgA
    have key0 := moduleFinite_of_surjective_mulHom
      (Work.StemsB.πmap (Work.RatHurewicz.setIncl (Set.range (attachIncl n' S.W {i // i ∈ J} h)))
        (k - 1) (⟨w₀', ⟨S.w₀, by simp [w₀']⟩⟩ :
          Set.range (attachIncl n' S.W {i // i ∈ J} h))) hsurj
    have key : Module.Finite ℤ (Additive (HomotopyGroup (Fin (k - 1 + 1)) W' w₀')) := key0
    exact Module.Finite.equiv ((Work.StemsB.indexCastMulEquiv w₀' hsk).toAdditive.toIntLinearEquiv)
  refine ⟨(⟨W', inferInstance, w₀', ψ', hemb, hconn, hfgk⟩ :
    SubModel k hk (attachCells n' Y ι f)), ?_⟩
  intro x hx
  rw [hrange]
  rcases hcov x hx with hx1 | hx2
  · left
    obtain ⟨y, hyK₀, hy⟩ := hdesc x hx hx1
    obtain ⟨w, hw⟩ := hS hyK₀
    exact ⟨w, by rw [ContinuousMap.comp_apply, hw, hy]⟩
  · right
    simp only [Set.mem_iUnion, Set.mem_range] at hx2 ⊢
    obtain ⟨i, hiJ, u, hu⟩ := hx2
    exact ⟨⟨i, hiJ⟩, u, hu⟩


open Work.RatHurewicz Work.Serre.CWModel

/-- **The low step**: attaching `k`-cells to a point (the wedge). -/
theorem attachStepLow_submodel {k : ℕ} (hk : 2 ≤ k) {ι : Type}
    (f : ι → C(cellSphere (k - 2), PUnit))
    {K : Set (attachCells (k - 2) PUnit ι f)} (hK : IsCompact K)
    (J : Finset ι) (K₀ : Set PUnit) (hK₀ : IsCompact K₀)
    (himg : ∀ i ∈ J, Set.range (f i) ⊆ K₀)
    (hcov : ∀ x ∈ K, x ∈ Set.range (attachIncl (k - 2) PUnit ι f)
      ∪ ⋃ i ∈ (J : Set ι), Set.range (cellMap (k - 2) PUnit ι f i))
    (hdesc : ∀ x ∈ K, x ∈ Set.range (attachIncl (k - 2) PUnit ι f) →
      ∃ y ∈ K₀, attachIncl (k - 2) PUnit ι f y = x) :
    ∃ (S' : SubModel k hk (attachCells (k - 2) PUnit ι f)), K ⊆ Set.range (S'.ψ : S'.W → _) := by
  classical
  have hembId : Topology.IsEmbedding (ContinuousMap.id PUnit) := Topology.IsEmbedding.id
  have himg' : ∀ j : {i // i ∈ J}, Set.range (f (j.1)) ⊆
      Set.range ((ContinuousMap.id PUnit : C(PUnit, PUnit)) : PUnit → PUnit) := by
    intro j z hz
    exact ⟨PUnit.unit, Subsingleton.elim _ _⟩
  obtain ⟨h, hcompat, ψ', q, hemb, hcomp, hrange⟩ :=
    Work.StemsB.attachSubmodel (k - 2) PUnit ι f PUnit (ContinuousMap.id PUnit) hembId
      (fun j : {i // i ∈ J} => j.1) Subtype.val_injective himg'
  -- the lifted family is the constant family
  have hcongr : h = Work.Serre.Wedge.wF (k - 2) {i // i ∈ J} := by
    funext j
    ext z
  let W' : Type := attachCells (k - 2) PUnit {i // i ∈ J} h
  letI : TopologicalSpace W' := inferInstance
  let w₀' : W' := attachIncl (k - 2) PUnit _ h PUnit.unit
  haveI : k.AtLeastTwo := ⟨hk⟩
  have hwk := Work.StemsB.wedgePiKfinite k hk {i // i ∈ J}
  refine ⟨(⟨W', inferInstance, w₀', ψ', hemb, ?_, ?_⟩ :
    SubModel k hk (attachCells (k - 2) PUnit ι f)), ?_⟩
  · intro i hi
    show Subsingleton (HomotopyGroup (Fin i) (attachCells (k - 2) PUnit {i // i ∈ J} h) w₀')
    rw [hcongr]
    exact hwk.1 i hi
  · show (letI : k.AtLeastTwo := ⟨hk⟩
      Module.Finite ℤ (Additive (HomotopyGroup (Fin k)
        (attachCells (k - 2) PUnit {i // i ∈ J} h) w₀')))
    rw [hcongr]
    exact hwk.2
  · intro x hx
    rw [hrange]
    rcases hcov x hx with hx1 | hx2
    · left
      obtain ⟨y, hyK₀, hy⟩ := hdesc x hx hx1
      exact ⟨y, by rw [ContinuousMap.comp_apply, hy]⟩
    · right
      simp only [Set.mem_iUnion, Set.mem_range] at hx2 ⊢
      obtain ⟨i, hiJ, u, hu⟩ := hx2
      exact ⟨⟨i, hiJ⟩, u, hu⟩


open Work.RatHurewicz Work.Serre.CWModel

/-- The step data of `genStep`. -/
abbrev genI {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StA B b₀ n) : Type :=
  HomotopyGroup (Fin (n + 2)) B (s.g s.y₀)

abbrev genF {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StA B b₀ n) : genI s → C(cellSphere n, s.Y) :=
  fun _ => ContinuousMap.const (cellSphere n) s.y₀

theorem genStep_Y {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StA B b₀ n) :
    (genStep s).Y = attachCells n s.Y (genI s) (genF s) := rfl

/-- The step data of `killStep`. -/
abbrev killI {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StG B b₀ n) : Type :=
  {α : HomotopyGroup (Fin (n + 2)) s.Y s.y₀ // Work.Serre.piMapN s.g (n + 2) s.y₀ α = 1}

abbrev killF {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StG B b₀ n) : killI s → C(cellSphere (n + 1), s.Y) :=
  fun k => killFamily (n + 1) s.Y s.y₀ k.1

theorem killStep_Y {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StG B b₀ n) :
    (killStep s).Y = attachCells (n + 1) s.Y (killI s) (killF s) := rfl

theorem towerA_zero {B : Type} [TopologicalSpace B] (b₀ : B) (b : ℕ) (hb : 2 ≤ b)
    (hB : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) B b₀)) :
    (towerA B b₀ b hb hB 0).Y = PUnit := rfl

theorem towerA_succ {B : Type} [TopologicalSpace B] (b₀ : B) (b : ℕ) (hb : 2 ≤ b)
    (hB : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) B b₀)) (n : ℕ) :
    towerA B b₀ b hb hB (n + 1) = killStep (genStep (towerA B b₀ b hb hB n)) := rfl

/-- **The tower induction**: every compact set of a stage is contained in a submodel. -/
theorem towerA_submodel (k : ℕ) (hk : 2 ≤ k) (B : Type) [TopologicalSpace B] (b₀ : B)
    (hB : ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) B b₀)) :
    ∀ (n : ℕ) (K : Set (towerA B b₀ k hk hB n).Y), IsCompact K →
      ∃ (S : SubModel k hk (towerA B b₀ k hk hB n).Y),
        K ⊆ Set.range (S.ψ : S.W → (towerA B b₀ k hk hB n).Y) := by
  intro n
  induction n with
  | zero =>
    intro K hK
    haveI hsub : Subsingleton ((towerA B b₀ k hk hB 0).Y) := inferInstanceAs (Subsingleton PUnit)
    refine ⟨subModelPUnit k hk, fun x _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩⟩
  | succ n ih =>
    intro K hK
    obtain ⟨J₂, K₀₂, hK₀₂, himg₂, hcov₂, hdesc₂⟩ :=
      Work.StemsB.descentCells (k - 2 + n + 1) (genStep (towerA B b₀ k hk hB n)).Y
        (killI (genStep (towerA B b₀ k hk hB n)) : Type)
        (killF (genStep (towerA B b₀ k hk hB n))) hK
    obtain ⟨J₁, K₀₁, hK₀₁, himg₁, hcov₁, hdesc₁⟩ :=
      Work.StemsB.descentCells (k - 2 + n) (towerA B b₀ k hk hB n).Y
        (genI (towerA B b₀ k hk hB n) : Type) (genF (towerA B b₀ k hk hB n)) hK₀₂
    rcases Nat.eq_zero_or_pos n with hn0 | hpos
    · -- the case `n = 0`: the generator step attaches `k`-cells (the wedge case)
      subst hn0
      obtain ⟨S₁, hS₁⟩ := attachStepLow_submodel (k := k) hk
        (genF (towerA B b₀ k hk hB 0)) hK₀₂ J₁ K₀₁ hK₀₁ himg₁ hcov₁ hdesc₁
      obtain ⟨S₂, hS₂⟩ := attachStep_submodel (k := k) hk (n' := k - 2 + 1)
        (killF (genStep (towerA B b₀ k hk hB 0))) (by omega) hK J₂ K₀₂ hK₀₂ himg₂ hcov₂ hdesc₂
        S₁ hS₁
      exact ⟨S₂, hS₂⟩
    · -- the case `n ≥ 1`: both steps are high
      obtain ⟨S₀, hS₀⟩ := ih K₀₁ hK₀₁
      obtain ⟨S₁, hS₁⟩ := attachStep_submodel (k := k) hk (n' := k - 2 + n)
        (genF (towerA B b₀ k hk hB n)) (by omega) hK₀₂ J₁ K₀₁ hK₀₁ himg₁ hcov₁ hdesc₁ S₀ hS₀
      obtain ⟨S₂, hS₂⟩ := attachStep_submodel (k := k) hk (n' := k - 2 + n + 1)
        (killF (genStep (towerA B b₀ k hk hB n))) (by omega) hK J₂ K₀₂ hK₀₂ himg₂ hcov₂ hdesc₂
        S₁ hS₁
      exact ⟨S₂, hS₂⟩



/-! ## The bookkeeping lemmas `chainMap_comp_eq`, `chainMap_d_apply` are provided upstream
by `Submission.Work.Stems.cycleLiftOfIso`. -/

/-- **A rational cycle of a range model is (up to a boundary) the pushforward of a cycle of a finite model.**

Let `k ≥ 2`, let `Z` be a range model of `K(A,k)` in degrees `≤ 2k-1` (`π_i(Z) = 0` for
`i ≤ 2k-1`, `i ≠ k`; `A = π_k(Z)` is arbitrary), and let `z` be a rational `j`-cycle of `Z` with
`k < j ≤ 2k-1`.  Then there are a space `W` which is `(k-1)`-connected with `π_k(W)` finitely
generated, a map `φ : W → Z`, a rational `j`-cycle `w` of `W` and a `(j+1)`-chain `b` of `Z` with
`φ_* w = z + ∂b`.

Two routes work.

(1) CW model.  Take the CW model `Γ → Z` of `Z` in the homotopy range
(`Work.Serre.CWModel.exists_model` with `N = 2k`: a bijection on `π_i` for `i ≤ 2k`, all cells of
dimension `≥ k`), and use `Work.Serre.serreK2` (an `N`-connected map induces an isomorphism on
rational homology in degrees `< N`) to write the class of `z` as `g_*[w]` for a cycle `w` of `Γ`.
A cycle of `Γ` is a cycle of a finite submodel `Γ₀ ⊆ Γ`: it has compact support, and a compact
subset of an iterated cell attachment lies in a finite subcomplex — an induction over the tower
`Work.Serre.CWModel.towerA`, using `Work.AttachPush.finite_meets_cellInterior` for a single
attachment.  The finite submodel `Γ₀` is `(k-1)`-connected (its cells have dimension `≥ k`) and
`π_k(Γ₀)` is finitely generated: the `k`-cells of the model are attached along *constant* maps, so
the `k`-skeleton of `Γ₀` is a wedge of `k`-spheres and `π_k` of it is free on the `k`-cells, while
the compression property `Work.RatHurewicz.compressRel_attachCells_range` at dimension `k` shows
that `π_k(Γ₀)` is generated by them.

(2) Direct.  Realize the cycle directly on a finite complex built from its simplices (glue the
standard simplices along the faces that cancel in `∂z`), then attach cells to make the result
`(k-1)`-connected with finitely generated `π_k` (possible because `π_i(Z) = 0` for `i < k`).

Weakening the conclusion to "`φ_* w` is homologous to `z`" (as stated) is exactly what the final
assembly consumes; the exact chain-level statement is not needed. -/
theorem cycleFiniteModelLocal_aux
    (k j : ℕ) (hk : 2 ≤ k) (hj₁ : k < j) (hj₂ : j ≤ 2 * k - 1)
    (Z : Type) [TopologicalSpace Z] (z₀ : Z)
    (hZ : ∀ i : ℕ, i ≤ 2 * k - 1 → i ≠ k → Subsingleton (HomotopyGroup (Fin i) Z z₀))
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of Z)).X j)
    (hz : (Work.Cohomology.singularChains ℚ (TopCat.of Z)).d j (j - 1) z = 0) :
    ∃ (W : Type) (_ : TopologicalSpace W) (w₀ : W) (φ : C(W, Z))
      (w : (Work.Cohomology.singularChains ℚ (TopCat.of W)).X j)
      (b : (Work.Cohomology.singularChains ℚ (TopCat.of Z)).X (j + 1)),
      (Work.Cohomology.singularChains ℚ (TopCat.of W)).d j (j - 1) w = 0 ∧
      (Work.Cohomology.chainMap ℚ (TopCat.of W) (TopCat.of Z) (TopCat.ofHom φ)).f j w
        = z + (Work.Cohomology.singularChains ℚ (TopCat.of Z)).d (j + 1) j b ∧
      (∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) W w₀)) ∧
      (letI : k.AtLeastTwo := ⟨hk⟩
       Module.Finite ℤ (Additive (HomotopyGroup (Fin k) W w₀))) := by
  classical
  -- ## Step 1: the cell model of `Z` in the homotopy range
  have hZk : ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) Z z₀) :=
    fun i hi => hZ i (by omega) (by omega)
  -- we run the model tower up to stage `2k + 2`, so that `π_i(g)` is bijective for `i ≤ 2k`
  let st := towerA Z z₀ k hk hZk (2 * k + 2)
  letI : TopologicalSpace st.Y := st.inst
  have hgbase : st.g st.y₀ = z₀ := st.gbase
  haveI hconn : PathConnectedSpace st.Y := st.conn
  haveI hconnZ : PathConnectedSpace Z := by
    have hZ0 : Subsingleton (HomotopyGroup (Fin 0) Z z₀) := hZk 0 (by omega)
    haveI := hZ0
    have hz0 : Subsingleton (ZerothHomotopy Z) :=
      ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := Z) (x := z₀)).symm.injective
        (Subsingleton.elim _ _)⟩
    exact pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk z₀⟩, hz0⟩
  have hbij : ∀ i : ℕ, i ≤ 2 * k → ∀ x : st.Y,
      Function.Bijective (Work.Serre.piMapN st.g i x) := by
    intro i hi x
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have h1 : Subsingleton (HomotopyGroup (Fin 0) st.Y x) :=
        (HomotopyGroup.pi0EquivZerothHomotopy (X := st.Y) (x := x)).injective.subsingleton
      have h2 : Subsingleton (HomotopyGroup (Fin 0) Z (st.g x)) :=
        (HomotopyGroup.pi0EquivZerothHomotopy (X := Z) (x := st.g x)).injective.subsingleton
      exact ⟨fun a b _ => h1.elim a b, fun y => ⟨default, h2.elim _ _⟩⟩
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact Work.Serre.bijective_piMapN_of_joined st.g (PathConnectedSpace.joined st.y₀ x) (m + 1)
        (st.bij m (by omega))
  -- ## Step 2: the induced isomorphism on rational homology below degree `2k`
  have hiso : CategoryTheory.IsIso (Work.Serre.ratHomologyMap st.g j) :=
    Work.Serre.serreK2 st.Y Z st.g (2 * k) (fun i hi x => hbij i (by omega) x) j (by omega)
  -- ## Step 3: lift the cycle to the model
  obtain ⟨v, b, hvcyc, hvmap⟩ := Work.Stems.cycleLift_of_isIso st.g j hiso z hz
  -- ## Step 4: the lifted cycle lies in a compact subspace
  obtain ⟨K, hK, w, hw⟩ := Work.StemsB.compactSupportChain (X := st.Y) j v
  -- ## Step 5: the finite submodel of the model containing that compact set
  obtain ⟨S, hS⟩ := towerA_submodel k hk Z z₀ hZk (2 * k + 2) K hK
  have hSK : K ⊆ Set.range (S.ψ : S.W → st.Y) := hS
  -- ## Step 6: corestrict the chain along the submodel embedding
  let ζ : C(↥K, S.W) :=
    (S.emb.toHomeomorph.symm : C(Set.range (S.ψ : S.W → st.Y), S.W)).comp
      ⟨fun x => ⟨x.1, hS x.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩
  have hζ : (S.ψ).comp ζ = Work.RatHurewicz.setIncl K := by
    ext x
    exact congrArg Subtype.val (S.emb.toHomeomorph.apply_symm_apply ⟨x.1, hS x.2⟩)
  let w'' : (Work.Cohomology.singularChains ℚ (TopCat.of S.W)).X j :=
    (Work.Cohomology.chainMap ℚ (TopCat.of ↥K) (TopCat.of S.W) (TopCat.ofHom ζ)).f j w
  have hψw'' : (Work.Cohomology.chainMap ℚ (TopCat.of S.W) (TopCat.of st.Y)
      (TopCat.ofHom S.ψ)).f j w'' = v := by
    have h1 : Work.Cohomology.chainMap ℚ (TopCat.of ↥K) (TopCat.of st.Y)
        (TopCat.ofHom (S.ψ.comp ζ))
        = Work.Cohomology.chainMap ℚ (TopCat.of ↥K) (TopCat.of S.W) (TopCat.ofHom ζ)
          ≫ Work.Cohomology.chainMap ℚ (TopCat.of S.W) (TopCat.of st.Y) (TopCat.ofHom S.ψ) :=
      chainMap_comp_eq ζ S.ψ
    rw [hζ] at h1
    have h2 := congrArg (fun m => ModuleCat.Hom.hom (HomologicalComplex.Hom.f m j) w) h1
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [hw] at h2
    exact h2.symm
  have hw''cyc : (Work.Cohomology.singularChains ℚ (TopCat.of S.W)).d j (j - 1) w'' = 0 := by
    have h1 : (Work.Cohomology.chainMap ℚ (TopCat.of S.W) (TopCat.of st.Y)
        (TopCat.ofHom S.ψ)).f (j - 1)
        ((Work.Cohomology.singularChains ℚ (TopCat.of S.W)).d j (j - 1) w'') = 0 := by
      rw [chainMap_d_apply S.ψ j (j - 1) w'', hψw'', hvcyc]
    exact Work.StemsB.injective_chainMap (f := S.ψ) S.emb.injective (j - 1) (by
      rw [h1]
      exact (map_zero _).symm)
  -- ## Step 7: assembly
  refine ⟨S.W, S.inst, S.w₀, st.g.comp S.ψ, w'', b, hw''cyc, ?_, S.conn, S.fgk⟩
  have hcomp : Work.Cohomology.chainMap ℚ (TopCat.of S.W) (TopCat.of Z)
      (TopCat.ofHom (st.g.comp S.ψ))
      = Work.Cohomology.chainMap ℚ (TopCat.of S.W) (TopCat.of st.Y) (TopCat.ofHom S.ψ)
        ≫ Work.Cohomology.chainMap ℚ (TopCat.of st.Y) (TopCat.of Z) (TopCat.ofHom st.g) :=
    chainMap_comp_eq S.ψ st.g
  have h2 := congrArg (fun m => ModuleCat.Hom.hom (HomologicalComplex.Hom.f m j) w'') hcomp
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [h2, hψw'', hvmap]

end

end Work.Stems

namespace Work.Stems

theorem cycleFiniteModelLocal : Work.Stems.CycleFiniteModelLocal := cycleFiniteModelLocal_aux

end Work.Stems
