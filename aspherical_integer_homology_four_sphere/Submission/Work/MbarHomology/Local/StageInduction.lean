/-
# The cell-by-cell induction over the localized (star) filtration

This file assembles the stage steps (`StageCx.lean`) into the statement that the subdivision is a
quasi-isomorphism on every "stage" of a lower set of cells: the stages are
`(S.filter (·.dim < k)) ∪ E` for `E` a set of `k`-cells of `S`, and the induction is over `k` and
then over `E`, adjoining one cell at a time.  The individual steps are the five lemma
(`quasiIso_of_sub_quot`) with the piece of the new cell, whose quasi-isomorphism is the local
condition at that cell (`stageQuotMap_eq_locMap`).
-/
import Mathlib
import Submission.Work.MbarHomology.Local.StageCx
import Submission.Work.Subdivision.SubDataQuasiIso
import Submission.Work.Subdivision.SubDataEq
import Submission.Work.Subdivision.ComapChainIso
import Submission.Work.MbarHomology.Local.stageQuotMap_eq_locMap
import Submission.Work.Subdivision.SkelInduction
import Submission.Work.Subdivision.PieceInduction

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

namespace PolyCW

variable (P : PolyCW.{u})

set_option allowUnsafeReducibility true
attribute [local reducible] cellChain sdChain cellS sdS cellSMod sdSMod leSub ltSub
  SubData.chain SubData.quot SubData.quotOf PolyCW.icF PolyCW.ioF

/-- The subdivision restricted to the support filtration of a lower finset of cells. -/
noncomputable def stageMap (hdd : P.HasDdZero) (haug : P.HasAugZero) (S : Finset P.Cell)
    (hS : IsLowerFinset P S) :
    (cellS P hdd S hS).chain ⟶ (sdS P S).chain :=
  (cellS P hdd S hS).restrictMap (sdS P S) (subdiv P hdd haug) (subdivCpt_mem_S P hdd haug hS)

/-- The map on the stage `insert a T` is the level map of `StageCx.lean`. -/
theorem stageMap_insert_eq (hdd : P.HasDdZero) (haug : P.HasAugZero) {T : Finset P.Cell}
    (a : P.Cell) (h : IsStage P a T) :
    stageMap P hdd haug (insert a T) h.insert_lower = levelMapS P hdd haug a h := rfl

end PolyCW

/-! ### The five lemma in the third-term direction -/

variable {C C' : ChainComplex (ModuleCat ℤ) ℕ}

/-- **Five lemma for a compatible subcomplex, third term.**  If a chain map `f` is a
quasi-isomorphism and its restriction to a compatible subcomplex is one, then the induced map on
the quotients is one. -/
theorem quasiIso_quotMap_of_sub (S : SubData C) (S' : SubData C') (f : C ⟶ C')
    (hf : ∀ k, S.sub k ≤ (S'.sub k).comap (f.f k).hom)
    (w : S.incl ≫ S.proj = 0) (w' : S'.incl ≫ S'.proj = 0)
    (h₁ : QuasiIso (S.restrictMap S' f hf)) (h₂ : QuasiIso f) :
    QuasiIso (S.quotMap S' f hf) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (S.shortComplexHom S' f hf w w')
    (shortComplexOf_shortExact S w) (shortComplexOf_shortExact S' w')
    (by rw [SubData.shortComplexHom_τ₁]; exact h₁) (by rw [SubData.shortComplexHom_τ₂]; exact h₂)

namespace PolyCW

variable (P : PolyCW.{u})

/-! ### The stages of the induction -/

/-- The finset of the `k`-cells of a lower set. -/
abbrev stageCells (S : Finset P.Cell) (k : ℕ) : Finset P.Cell :=
  S.filter (fun f => P.dim f = k)

/-- The cells of `S` of dimension `< k`. -/
abbrev stageBelow (S : Finset P.Cell) (k : ℕ) : Finset P.Cell :=
  S.filter (fun f => P.dim f < k)

theorem isLowerFinset_stageBelow {S : Finset P.Cell} (hS : IsLowerFinset P S) (k : ℕ) :
    IsLowerFinset P (stageBelow P S k) := by
  intro f hf g hg
  rw [stageBelow, Finset.mem_filter] at hf ⊢
  exact ⟨hS f hf.1 g hg, lt_of_le_of_lt (P.dim_le hg) hf.2⟩

theorem isLowerFinset_stage {S : Finset P.Cell} (hS : IsLowerFinset P S) {k : ℕ}
    {E : Finset P.Cell} (hE : E ⊆ stageCells P S k) :
    IsLowerFinset P (stageBelow P S k ∪ E) := by
  intro f hf g hg
  rw [Finset.mem_union] at hf ⊢
  rcases hf with hf | hf
  · exact Or.inl ((isLowerFinset_stageBelow P hS k) f hf g hg)
  · have hE' := hE hf
    rw [stageCells, Finset.mem_filter] at hE'
    by_cases hdim : P.dim g = k
    · refine Or.inr ?_
      have hgf : g = f := by
        by_contra hne
        have hlt := P.dim_lt hg hne
        omega
      rw [hgf]; exact hf
    · refine Or.inl ?_
      rw [stageBelow, Finset.mem_filter]
      exact ⟨hS f hE'.1 g hg, lt_of_le_of_ne (le_trans (P.dim_le hg) (le_of_eq hE'.2)) hdim⟩

theorem isStage_stage {S : Finset P.Cell} (hS : IsLowerFinset P S) {k : ℕ} {E : Finset P.Cell}
    (hE : E ⊆ stageCells P S k) {a : P.Cell} (ha : a ∈ stageCells P S k) (haE : a ∉ E) :
    IsStage P a (stageBelow P S k ∪ E) := by
  have ha' := ha
  rw [stageCells, Finset.mem_filter] at ha'
  refine ⟨isLowerFinset_stage P hS hE, ?_, ?_, ?_⟩
  · intro hmem
    rw [Finset.mem_union] at hmem
    rcases hmem with hmem | hmem
    · rw [stageBelow, Finset.mem_filter] at hmem
      omega
    · exact haE hmem
  · intro f hf
    rw [Finset.mem_union] at hf
    rcases hf with hf | hf
    · rw [stageBelow, Finset.mem_filter] at hf
      omega
    · have hE' := hE hf
      rw [stageCells, Finset.mem_filter] at hE'
      exact le_of_eq (hE'.2.trans ha'.2.symm)
  · intro f hf
    refine Finset.mem_union_left _ ?_
    rw [stageBelow, Finset.mem_filter]
    exact ⟨hS a ha'.1 f hf.le, lt_of_lt_of_le (P.dim_lt hf.le (ne_of_lt hf)) (le_of_eq ha'.2)⟩

theorem stage_insert_eq (S : Finset P.Cell) (k : ℕ) (E : Finset P.Cell) (a : P.Cell) :
    insert a (stageBelow P S k ∪ E) = stageBelow P S k ∪ insert a E := by
  ext f
  rw [Finset.mem_insert, Finset.mem_union, Finset.mem_union, Finset.mem_insert]
  tauto

/-- `PolyCW.stageMap` does not depend on the proof that the finset is lower. -/
theorem stageMap_congr (hdd : P.HasDdZero) (haug : P.HasAugZero) {S : Finset P.Cell}
    (h₁ h₂ : IsLowerFinset P S) :
    stageMap P hdd haug S h₁ = stageMap P hdd haug S h₂ := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The quasi-isomorphism property of `PolyCW.stageMap` is invariant under replacing the stage by
an equal finset. -/
theorem quasiIso_stageMap_congr (hdd : P.HasDdZero) (haug : P.HasAugZero) {S S' : Finset P.Cell}
    (h : S = S') (h₁ : IsLowerFinset P S) (h₂ : IsLowerFinset P S') :
    (QuasiIso (stageMap P hdd haug S h₁) ↔ QuasiIso (stageMap P hdd haug S' h₂)) := by
  subst h
  rw [stageMap_congr P hdd haug h₁ h₂]

theorem insert_subset_stageCells {S : Finset P.Cell} {k : ℕ} {E : Finset P.Cell}
    (hE : E ⊆ stageCells P S k) {a : P.Cell} (ha : a ∈ stageCells P S k) :
    insert a E ⊆ stageCells P S k := by
  intro f hf
  rcases Finset.mem_insert.mp hf with rfl | hf
  exacts [ha, hE hf]

/-! ### The stage step -/

/-- **The stage step**: adjoining an unadded `k`-cell to a stage, the map on the larger stage is a
quasi-isomorphism as soon as it is one on the smaller stage and the local condition holds at the new
cell. -/
theorem stage_step (hdd : P.HasDdZero) (haug : P.HasAugZero) (S : Finset P.Cell)
    (hS : IsLowerFinset P S) {k : ℕ} {E : Finset P.Cell} (hE : E ⊆ stageCells P S k)
    {a : P.Cell} (ha : a ∈ stageCells P S k) (haE : a ∉ E)
    (ih : QuasiIso (stageMap P hdd haug (stageBelow P S k ∪ E)
      (isLowerFinset_stage P hS hE)))
    (hsp : QuasiIso (locMap P hdd haug a)) :
    QuasiIso (stageMap P hdd haug (stageBelow P S k ∪ insert a E)
      (isLowerFinset_stage P hS (insert_subset_stageCells P hE ha))) := by
  have hst : IsStage P a (stageBelow P S k ∪ E) := isStage_stage P hS hE ha haE
  have hpieceSub : ∀ m, (cellPieceS P hdd a hst).sub m ≤
      ((sdPieceS P a hst).sub m).comap ((levelMapS P hdd haug a hst).f m).hom :=
    cellPieceS_hf P hdd haug a hst
  have hlevel : QuasiIso (stageMap P hdd haug (stageBelow P S k ∪ E)
      (isLowerFinset_stage P hS hE)) := ih
  have h₁ : QuasiIso ((cellPieceS P hdd a hst).restrictMap (sdPieceS P a hst)
      (levelMapS P hdd haug a hst) hpieceSub) :=
    quasiIso_of_iso_square
      (SubData.comapChainIso (cellS P hdd (insert a (stageBelow P S k ∪ E)) hst.insert_lower)
        (cellSMod P hdd (stageBelow P S k ∪ E))
        (fun m => cellSMod_mono P hdd (Finset.subset_insert a _) m)
        (cellS P hdd (stageBelow P S k ∪ E) hst.lower).d_mem)
      (SubData.comapChainIso (sdS P (insert a (stageBelow P S k ∪ E)))
        (sdSMod P (stageBelow P S k ∪ E))
        (fun m => sdSMod_mono P (Finset.subset_insert a _) m)
        (sdS P (stageBelow P S k ∪ E)).d_mem)
      ((cellS P hdd (stageBelow P S k ∪ E) hst.lower).restrictMap (sdS P (stageBelow P S k ∪ E))
        (subdiv P hdd haug) (subdivCpt_mem_S P hdd haug hst.lower))
      ((cellPieceS P hdd a hst).restrictMap (sdPieceS P a hst) (levelMapS P hdd haug a hst)
        hpieceSub)
      (comapChainIso_restrictMap_comm (cellS P hdd (insert a (stageBelow P S k ∪ E)) hst.insert_lower)
        (cellSMod P hdd (stageBelow P S k ∪ E))
        (fun m => cellSMod_mono P hdd (Finset.subset_insert a _) m)
        (cellS P hdd (stageBelow P S k ∪ E) hst.lower).d_mem
        (sdS P (insert a (stageBelow P S k ∪ E))) (sdSMod P (stageBelow P S k ∪ E))
        (fun m => sdSMod_mono P (Finset.subset_insert a _) m)
        (sdS P (stageBelow P S k ∪ E)).d_mem
        (subdiv P hdd haug) (subdivCpt_mem_S P hdd haug hst.insert_lower)
        (subdivCpt_mem_S P hdd haug hst.lower))
      hlevel
  have h₃ : QuasiIso ((cellPieceS P hdd a hst).quotMap (sdPieceS P a hst)
      (levelMapS P hdd haug a hst) hpieceSub) := by
    obtain ⟨Φ, Ψ, hsq⟩ := MbarHomology.Local.stageQuotMap_eq_locMap P hdd haug a hst
    exact quasiIso_of_iso_square Φ Ψ (locMap P hdd haug a)
      (stageQuotMap P hdd haug a hst) hsq.symm hsp
  have hmid : QuasiIso (levelMapS P hdd haug a hst) :=
    quasiIso_of_sub_quot (cellPieceS P hdd a hst) (sdPieceS P a hst)
      (levelMapS P hdd haug a hst) hpieceSub (incl_proj _) (incl_proj _) h₁ h₃
  have hins : QuasiIso (stageMap P hdd haug (insert a (stageBelow P S k ∪ E))
      hst.insert_lower) := by
    rw [stageMap_insert_eq]
    exact hmid
  exact (quasiIso_stageMap_congr P hdd haug (stage_insert_eq P S k E a).symm _ _).mpr hins

/-! ### The base cases -/

theorem isLowerFinset_empty : IsLowerFinset P (∅ : Finset P.Cell) := by
  intro f hf
  exact absurd hf (Finset.notMem_empty f)

theorem stageBelow_zero (S : Finset P.Cell) : stageBelow P S 0 = ∅ :=
  Finset.filter_eq_empty_iff.mpr fun f _ => by simp

theorem stageBelow_succ_union (S : Finset P.Cell) (k : ℕ) :
    stageBelow P S k ∪ stageCells P S k = stageBelow P S (k + 1) := by
  ext f
  simp only [Finset.mem_union, stageBelow, stageCells, Finset.mem_filter]
  constructor
  · rintro (⟨hf, h1⟩ | ⟨hf, h2⟩)
    · exact ⟨hf, by omega⟩
    · exact ⟨hf, by omega⟩
  · rintro ⟨hf, h⟩
    rcases lt_or_eq_of_le (by omega : P.dim f ≤ k) with h' | h'
    · exact Or.inl ⟨hf, h'⟩
    · exact Or.inr ⟨hf, h'⟩

theorem cellSMod_empty (hdd : P.HasDdZero) (k : ℕ) :
    cellSMod P hdd (∅ : Finset P.Cell) k = ⊥ := by
  have hset : {y : (cellChain P hdd).X k |
      ∃ e : {e : P.Cell // P.dim e = k}, e.1 ∈ (∅ : Finset P.Cell) ∧ y = cellElem P hdd k e}
      = (∅ : Set _) := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨e, he, -⟩
    exact Finset.notMem_empty _ he
  rw [cellSMod, hset, Submodule.span_empty]

theorem sdSMod_empty (k : ℕ) : sdSMod P (∅ : Finset P.Cell) k = ⊥ := by
  have hset : {y : (sdChain P).X k |
      ∃ σ : Simplex P.Cell k, (∀ i, σ i ∈ (∅ : Finset P.Cell)) ∧ y = sdElem P σ}
      = (∅ : Set _) := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨σ, hσ, -⟩
    exact Finset.notMem_empty _ (hσ 0)
  rw [sdSMod, hset, Submodule.span_empty]

/-- The map on the empty stage is an isomorphism, hence a quasi-isomorphism. -/
theorem stageMap_empty_quasiIso (hdd : P.HasDdZero) (haug : P.HasAugZero) :
    QuasiIso (stageMap P hdd haug (∅ : Finset P.Cell) (isLowerFinset_empty P)) := by
  have hsub : ∀ k, Subsingleton ((cellS P hdd (∅ : Finset P.Cell)
      (isLowerFinset_empty P)).chain.X k) := by
    intro k
    rw [SubData.chain_X]
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx : (x : (cellChain P hdd).X k) ∈ (⊥ : Submodule ℤ ((cellChain P hdd).X k)) := by
      rw [← cellSMod_empty P hdd k]; exact x.2
    have hy : (y : (cellChain P hdd).X k) ∈ (⊥ : Submodule ℤ ((cellChain P hdd).X k)) := by
      rw [← cellSMod_empty P hdd k]; exact y.2
    rw [Submodule.mem_bot] at hx hy
    rw [hx, hy]
  haveI := hsub
  have hsub' : ∀ k, Subsingleton ((sdS P (∅ : Finset P.Cell)).chain.X k) := by
    intro k
    rw [SubData.chain_X]
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx : (x : (sdChain P).X k) ∈ (⊥ : Submodule ℤ ((sdChain P).X k)) := by
      rw [← sdSMod_empty P k]; exact x.2
    have hy : (y : (sdChain P).X k) ∈ (⊥ : Submodule ℤ ((sdChain P).X k)) := by
      rw [← sdSMod_empty P k]; exact y.2
    rw [Submodule.mem_bot] at hx hy
    rw [hx, hy]
  haveI := hsub'
  haveI : ∀ k, IsIso ((stageMap P hdd haug (∅ : Finset P.Cell)
      (isLowerFinset_empty P)).f k) := fun k => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  haveI : IsIso (stageMap P hdd haug (∅ : Finset P.Cell) (isLowerFinset_empty P)) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact quasiIso_of_isIso _

/-! ### The cell-by-cell induction -/

/-- **The cell-by-cell induction over the stages of a lower set.**  For a lower set `S` and a
dimension `k`, the subdivision is a quasi-isomorphism on every stage
`stageBelow S k ∪ E`, for `E` a set of `k`-cells of `S`, as soon as the local condition holds at
every cell of `S`. -/
theorem stageLevel_quasiIso (hdd : P.HasDdZero) (haug : P.HasAugZero) (S : Finset P.Cell)
    (hS : IsLowerFinset P S) (hLS : ∀ a ∈ S, QuasiIso (locMap P hdd haug a)) :
    ∀ (k : ℕ) (E : Finset P.Cell) (hE : E ⊆ stageCells P S k),
      QuasiIso (stageMap P hdd haug (stageBelow P S k ∪ E) (isLowerFinset_stage P hS hE)) := by
  intro k
  induction k with
  | zero =>
      intro E
      refine Finset.induction_on (s := E) (motive := fun E => ∀ (hE : E ⊆ stageCells P S 0),
          QuasiIso (stageMap P hdd haug (stageBelow P S 0 ∪ E) (isLowerFinset_stage P hS hE))) ?_ ?_
      · intro hE
        refine (quasiIso_stageMap_congr P hdd haug ?_ _ _).mpr (stageMap_empty_quasiIso P hdd haug)
        rw [stageBelow_zero, Finset.empty_union]
      · intro a E haE ihE hE
        have hE' : E ⊆ stageCells P S 0 := fun f hf => hE (Finset.mem_insert_of_mem hf)
        have ha : a ∈ stageCells P S 0 := hE (Finset.mem_insert_self a E)
        have haS : a ∈ S := (Finset.mem_filter.mp ha).1
        exact stage_step P hdd haug S hS hE' ha haE (ihE hE') (hLS a haS)
  | succ k ih =>
      intro E
      have hbase : QuasiIso (stageMap P hdd haug (stageBelow P S (k + 1))
          (isLowerFinset_stageBelow P hS (k + 1))) :=
        (quasiIso_stageMap_congr P hdd haug (stageBelow_succ_union P S k) _ _).mp
          (ih (stageCells P S k) (fun f hf => hf))
      refine Finset.induction_on (s := E) (motive := fun E => ∀ (hE : E ⊆ stageCells P S (k + 1)),
          QuasiIso (stageMap P hdd haug (stageBelow P S (k + 1) ∪ E)
            (isLowerFinset_stage P hS hE))) ?_ ?_
      · intro hE
        refine (quasiIso_stageMap_congr P hdd haug ?_ _ _).mp hbase
        rw [Finset.union_empty]
      · intro a E haE ihE hE
        have hE' : E ⊆ stageCells P S (k + 1) := fun f hf => hE (Finset.mem_insert_of_mem hf)
        have ha : a ∈ stageCells P S (k + 1) := hE (Finset.mem_insert_self a E)
        have haS : a ∈ S := (Finset.mem_filter.mp ha).1
        exact stage_step P hdd haug S hS hE' ha haE (ihE hE') (hLS a haS)

end PolyCW

end

end Work.Subdivision
