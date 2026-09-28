import Mathlib
import Submission.Work.Serre.RangeOne.towerCompact
import Submission.Work.RatHurewicz.compressRel_attachCells_range
import Submission.Work.RatHurewicz.exists_killed_tower

/-!
# The compression property of the colimit of the truncation tower

* `compressRel_chain`: the stagewise compression property of the tower — the pair
  `(X T, range (upAt S T))` compresses in all dimensions `d ≤ S + 3` (the cells attached above
  stage `S` have dimension `≥ S+4`), proved by iterating
  `Work.RatHurewicz.compressRel_attachIncl_comp` from stage `S` to stage `T`;
* `compressRel_univ`: the trivial case of a range that is everything;
* `compressRel_colim_chain`: the compression property of the pair `(Z, range (ι S))` in the colimit,
  obtained from the stagewise one by factoring cubes through a stage
  (`Work.Serre.RangeOne.exists_stage_of_compact`).
-/

open scoped Topology

namespace Work.Serre.RangeOne

open Work.RatHurewicz

noncomputable section

variable {W : Type} [TopologicalSpace W] {w₀ : W}

/-- A pair whose second member is everything always compresses. -/
theorem compressRel_univ (Y : Type) [TopologicalSpace Y] (d : ℕ) :
    CompressRel Y Set.univ d := by
  intro f _
  exact ⟨f.comp ContinuousMap.fst, fun x => rfl, fun x _ t => rfl, fun x => trivial⟩

/-- **Stagewise compression of the tower**: the pair `(X T, range (upAt S T))` compresses in all
dimensions `d ≤ S + 3`. -/
theorem compressRel_chain (W : Type) [TopologicalSpace W] (w₀ : W) (S T d : ℕ) (hST : S ≤ T)
    (hd : d ≤ S + 3) :
    CompressRel ((chain W w₀).X T) (Set.range ((chain W w₀).upAt S T hST)) d := by
  induction T, hST using Nat.le_induction with
  | base =>
      have h1 : Set.range ((chain W w₀).upAt S S le_rfl) = Set.univ := by
        rw [show (chain W w₀).upAt S S le_rfl = id from
          funext fun z => (chain W w₀).upAt_self le_rfl z]
        exact Set.range_id
      rw [h1]
      exact compressRel_univ _ d
  | succ n hSn ih =>
      let iota := HomotopyGroup (Fin (2 + n + 1)) ((St W w₀ n).Y) ((St W w₀ n).incl (wK w₀))
      let fam : iota → C(cellSphere (2 + n), (St W w₀ n).Y) :=
        killFamily (2 + n) (St W w₀ n).Y ((St W w₀ n).incl (wK w₀))
      let g : C((chain W w₀).X S, (chain W w₀).X n) :=
        ⟨(chain W w₀).upAt S n hSn, ((chain W w₀).upAt_isClosedEmbedding hSn).continuous⟩
      have hstep := compressRel_attachIncl_comp (2 + n) ((chain W w₀).X n) iota fam g d
        (by omega) ih
      have hpt : ∀ z : (chain W w₀).X S,
          ((attachIncl (2 + n) ((chain W w₀).X n) iota fam).comp g).toFun z
            = (chain W w₀).upAt S (n + 1) (le_trans hSn (Nat.le_succ n)) z := by
        intro z
        have h1 : (attachIncl (2 + n) ((chain W w₀).X n) iota fam).toFun
            ((chain W w₀).upAt S n hSn z)
            = (chain W w₀).upAt n (n + 1) (Nat.le_succ n) ((chain W w₀).upAt S n hSn z) := by
          rw [show attachIncl (2 + n) ((chain W w₀).X n) iota fam
              = (chain W w₀).step n from rfl]
          exact (((chain W w₀).upAt_step (Nat.le_succ n) le_rfl (by omega) _).trans
            ((chain W w₀).upAt_self le_rfl _)).symm
        show (attachIncl (2 + n) ((chain W w₀).X n) iota fam).toFun (g.toFun z) = _
        exact h1.trans ((chain W w₀).upAt_comp (le_trans hSn (Nat.le_succ n)) hSn
          (Nat.le_succ n) z)
      have hrange : Set.range (⇑((attachIncl (2 + n) ((chain W w₀).X n) iota fam).comp g))
          = Set.range ((chain W w₀).upAt S (n + 1) (le_trans hSn (Nat.le_succ n))) :=
        congrArg Set.range (show ((attachIncl (2 + n) ((chain W w₀).X n) iota fam).comp g).toFun
          = (chain W w₀).upAt S (n + 1) (le_trans hSn (Nat.le_succ n)) from funext hpt)
      rw [hrange] at hstep
      exact hstep

/-- **The compression property of the colimit of the tower** in dimensions `≤ S + 3`: the pair
`(Z, range (ι S))` compresses. -/
theorem compressRel_colim_chain (W : Type) [TopologicalSpace W] (w₀ : W) (S d : ℕ) (hd : d ≤ S + 3) :
    CompressRel ((chain W w₀).Z) (Set.range ((chain W w₀).iota S)) d := by
  intro f hf
  obtain ⟨T₀, hT₀⟩ := exists_stage_of_compact W w₀ (isCompact_range f.continuous)
  have hST : S ≤ T₀ ⊔ S := le_max_right _ _
  have hle : T₀ ≤ T₀ ⊔ S := le_max_left _ _
  have hsub : Set.range (f : ICube d → (chain W w₀).Z) ⊆
      Set.range ((chain W w₀).iota (T₀ ⊔ S)) :=
    hT₀.trans ((chain W w₀).range_iota_subset hle)
  let e : (chain W w₀).X (T₀ ⊔ S) ≃ₜ
      ↥(Set.range ((chain W w₀).iota (T₀ ⊔ S))) :=
    ((chain W w₀).isEmbedding_iota _).toHomeomorph
  have hmem : ∀ x : ICube d, f x ∈ Set.range ((chain W w₀).iota (T₀ ⊔ S)) :=
    fun x => hsub (Set.mem_range_self x)
  have hcont : Continuous fun x : ICube d => e.symm ⟨f x, hmem x⟩ := by
    refine ((chain W w₀).isEmbedding_iota _).isInducing.continuous_iff.mpr ?_
    change Continuous fun x : ICube d => ((chain W w₀).iota (T₀ ⊔ S)) (e.symm ⟨f x, hmem x⟩)
    rw [show (fun x : ICube d => ((chain W w₀).iota (T₀ ⊔ S)) (e.symm ⟨f x, hmem x⟩))
        = fun x => f x from funext fun x =>
          congrArg Subtype.val (e.apply_symm_apply ⟨f x, hmem x⟩)]
    exact f.continuous
  let g : C(ICube d, (chain W w₀).X (T₀ ⊔ S)) :=
    ⟨fun x => e.symm ⟨f x, hmem x⟩, hcont⟩
  have hgx : ∀ x : ICube d, (chain W w₀).iota (T₀ ⊔ S) (g x) = f x := fun x =>
    congrArg Subtype.val (e.apply_symm_apply ⟨f x, hmem x⟩)
  have hg : ∀ x, x ∈ Cube.boundary (Fin d) → g x ∈
      Set.range ((chain W w₀).upAt S (T₀ ⊔ S) hST) := by
    intro x hx
    rw [← (chain W w₀).preimage_range_iota hST]
    obtain ⟨y, hy⟩ := hf x hx
    refine ⟨y, ?_⟩
    rw [hgx x]
    exact hy
  obtain ⟨G, hG0, hGb, hG1⟩ := compressRel_chain W w₀ S (T₀ ⊔ S) d hST hd g hg
  refine ⟨⟨fun p => (chain W w₀).iota (T₀ ⊔ S) (G p),
    ((chain W w₀).continuous_iota _).comp G.continuous⟩, ?_, ?_, ?_⟩
  · intro x
    show (chain W w₀).iota (T₀ ⊔ S) (G (x, 0)) = f x
    rw [hG0 x]
    exact hgx x
  · intro x hx t
    show (chain W w₀).iota (T₀ ⊔ S) (G (x, t)) = f x
    rw [hGb x hx t]
    exact hgx x
  · intro x
    obtain ⟨y, hy⟩ := hG1 x
    refine ⟨y, ((chain W w₀).iota_compat hST y).trans ?_⟩
    rw [hy]
    rfl

end

end Work.Serre.RangeOne
