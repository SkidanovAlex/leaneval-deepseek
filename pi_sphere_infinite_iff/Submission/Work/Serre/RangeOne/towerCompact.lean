import Mathlib
import Submission.Work.Serre.RangeOne.towerDefs
import Submission.Work.RatHurewicz.AttachPush.CellInterior

/-!
# Compact subsets of the colimit of the truncation tower lie in a stage

This file proves `Work.Serre.RangeOne.exists_stage_of_compact`, the key topological input of the
colimit construction: every compact subset of the colimit `Z` of the tower `chain W w₀` is
contained in the image of one stage.

The argument uses the cell structure of the tower through the following fact (proved here from
`Work.RatHurewicz.AttachPush.CellInterior`): a point of a stage which is *not* in the image of the
previous stage is a closed point.  Given a compact `K`, a sequence `x S ∈ K` with `x S` outside
stage `S`, and a cluster point `p` of the sequence (`exists_clusterPoint_of_isCompact`), one forms
the closed set `{x S : S} \ {p}` — closed because its trace in each stage is a finite set of closed
points — whose complement is an open neighbourhood `U` of `p` meeting the sequence only in `p`,
which is impossible for a cluster point.  Hence some stage contains `K`.
-/

open scoped Topology

namespace Work.Serre.RangeOne

open Work.RatHurewicz

noncomputable section

variable {W : Type} [TopologicalSpace W] {w₀ : W}

/-! ## A cluster point of a sequence in a compact set -/

/-- **A sequence with values in a compact set has a cluster point in that set**: a point every
neighbourhood of which contains the sequence infinitely often.  No separation axiom on the ambient
space is needed. -/
theorem exists_clusterPoint_of_isCompact {Z : Type} [TopologicalSpace Z] {K : Set Z}
    (hK : IsCompact K) (x : ℕ → Z) (hx : ∀ n, x n ∈ K) :
    ∃ p ∈ K, ∀ U ∈ nhds p, {n : ℕ | x n ∈ U}.Infinite := by
  obtain ⟨p, hpK, hp⟩ := hK.exists_mapClusterPt_of_frequently (l := Filter.atTop)
    (Filter.Frequently.of_forall hx)
  exact ⟨p, hpK, fun U hU => by
    rw [← Nat.frequently_atTop_iff_infinite]
    exact (mapClusterPt_iff_frequently.mp hp) U hU⟩

/-! ## Bookkeeping for `SeqChain`s -/

namespace SeqChain

variable (C : SeqChain)

/-- Every point of the colimit lies in one of the stages. -/
theorem exists_stage (z : C.Z) : ∃ t : ℕ, z ∈ Set.range (C.iota t) := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep z
  exact ⟨a.1, ⟨a.2, rfl⟩⟩

/-- The minimal stage at which `x S` appears. -/
noncomputable def stg (x : ℕ → C.Z) (S : ℕ) : ℕ := by
  classical
  exact Nat.find (p := fun t => x S ∈ Set.range (C.iota t)) (C.exists_stage (x S))

theorem stg_spec (x : ℕ → C.Z) (S : ℕ) : x S ∈ Set.range (C.iota (C.stg x S)) := by
  classical
  exact Nat.find_spec (C.exists_stage (x S))

theorem stg_min (x : ℕ → C.Z) (S : ℕ) {t : ℕ} (h : x S ∈ Set.range (C.iota t)) :
    C.stg x S ≤ t := by
  classical
  exact Nat.find_min' (C.exists_stage (x S)) h

theorem stg_lt_min (x : ℕ → C.Z) (S : ℕ) {t : ℕ} (h : t < C.stg x S) :
    x S ∉ Set.range (C.iota t) := by
  classical
  exact Nat.find_min (C.exists_stage (x S)) h

/-- The minimal stage grows at least as fast as the index. -/
theorem stg_gt (x : ℕ → C.Z) (hx : ∀ S, x S ∉ Set.range (C.iota S)) (S : ℕ) :
    S < C.stg x S := by
  by_contra h
  exact hx S (C.range_iota_subset (not_lt.mp h) (C.stg_spec x S))

/-- The representative of `x S` in its minimal stage. -/
noncomputable def rep (x : ℕ → C.Z) (S : ℕ) : C.X (C.stg x S) :=
  Classical.choose (C.stg_spec x S)

theorem rep_spec (x : ℕ → C.Z) (S : ℕ) : C.iota (C.stg x S) (C.rep x S) = x S :=
  Classical.choose_spec (C.stg_spec x S)

/-- The representative is a *new* point of its stage: it does not come from the previous stage. -/
theorem rep_notMem_range_upAt (x : ℕ → C.Z) (hx : ∀ S, x S ∉ Set.range (C.iota S)) (S : ℕ) :
    C.rep x S ∉ Set.range (C.upAt (C.stg x S - 1) (C.stg x S) (Nat.sub_le _ _)) := by
  intro hmem
  obtain ⟨z, hz⟩ := hmem
  have h1 : x S ∈ Set.range (C.iota (C.stg x S - 1)) :=
    ⟨z, (C.iota_compat (Nat.sub_le _ _) z).trans (hz ▸ C.rep_spec x S)⟩
  have h2 := C.stg_min x S h1
  have h3 := C.stg_gt x hx S
  omega

theorem range_upAt_proof_irrel {s t : ℕ} (h₁ h₂ : s ≤ t) :
    Set.range (C.upAt s t h₁) = Set.range (C.upAt s t h₂) := by
  rw [funext fun x => C.upAt_proof_irrel h₁ h₂ x]

/-- The range of the single step is the range of the corresponding `upAt`. -/
theorem range_upAt_pred_succ (s : ℕ) :
    Set.range (C.upAt s (s + 1) (Nat.le_succ s)) = Set.range (C.step s) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, ((C.upAt_step (Nat.le_succ s) le_rfl (by omega) x).trans
      (C.upAt_self le_rfl _)).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, (C.upAt_step (Nat.le_succ s) le_rfl (by omega) x).trans
      (C.upAt_self le_rfl _)⟩

end SeqChain

/-! ## Off-range points of an attachment are closed -/

/-- **A point of `attachCells n Y ι f` which is not in the image of the base is a closed point.**
This uses only that the point then lies in the interior of an attached cell, whose class in the
gluing relation is a singleton.  No separation axiom is needed on `Y`. -/
theorem isClosed_singleton_of_notMem_range_attachIncl {n : ℕ} {Y : Type} [TopologicalSpace Y]
    {ι : Type} {f : ι → C(cellSphere n, Y)} {y : attachCells n Y ι f}
    (hy : y ∉ Set.range (attachIncl n Y ι f)) :
    IsClosed ({y} : Set (attachCells n Y ι f)) := by
  have hy' : y ∈ ⋃ i, cellInterior n Y ι f i := by
    by_contra h
    exact hy (by rw [range_attachIncl_eq_compl_iUnion_cellInterior]; exact h)
  obtain ⟨i, x, hx, hxy⟩ := Set.mem_iUnion.mp hy'
  have hpre : (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f)) ⁻¹'
        ({y} : Set (attachCells n Y ι f))ᶜ)
      = ({(Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDisk n))} :
          Set (Y ⊕ (Σ _ : ι, cellDisk n)))ᶜ := by
    ext a
    rw [Set.mem_preimage, Set.mem_compl_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_singleton_iff]
    constructor
    · intro ha h'
      rw [h'] at ha
      exact ha hxy
    · intro ha h'
      have h2 : Relation.EqvGen (attachRel n Y ι f) a (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDisk n)) :=
        Quotient.exact (s := Relation.EqvGen.setoid (attachRel n Y ι f)) (h'.trans hxy.symm)
      rw [eq_of_eqvGen_inr_cellInner hx h2] at ha
      exact ha rfl
  have hclosed_sum : IsClosed ({(Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDisk n))} :
      Set (Y ⊕ (Σ _ : ι, cellDisk n))) := by
    have hsin : IsClosed ({(⟨i, x⟩ : Σ _ : ι, cellDisk n)} : Set (Σ _ : ι, cellDisk n)) :=
      isClosed_singleton
    have himg : ({(Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDisk n))} :
        Set (Y ⊕ (Σ _ : ι, cellDisk n))) = Sum.inr '' ({(⟨i, x⟩ : Σ _ : ι, cellDisk n)} :
          Set (Σ _ : ι, cellDisk n)) := Set.image_singleton.symm
    rw [himg]
    refine isOpen_compl_iff.mp ?_
    rw [isOpen_sum_iff]
    constructor
    · rw [Set.preimage_compl]
      have hnil : (Sum.inl : Y → Y ⊕ (Σ _ : ι, cellDisk n)) ⁻¹'
          (Sum.inr '' ({(⟨i, x⟩ : Σ _ : ι, cellDisk n)} :
            Set (Σ _ : ι, cellDisk n))) = ∅ := by
        ext a
        simp
      rw [hnil, Set.compl_empty]
      exact isOpen_univ
    · rw [Set.preimage_compl]
      have hpre2 : (Sum.inr : (Σ _ : ι, cellDisk n) → Y ⊕ (Σ _ : ι, cellDisk n)) ⁻¹'
          (Sum.inr '' ({(⟨i, x⟩ : Σ _ : ι, cellDisk n)} :
            Set (Σ _ : ι, cellDisk n))) = {(⟨i, x⟩ : Σ _ : ι, cellDisk n)} := by
        ext a
        simp
      rw [hpre2]
      exact hsin.isOpen_compl
  rw [← isOpen_compl_iff]
  have hq := (isQuotientMap_quotient_mk'
    (s := Relation.EqvGen.setoid (attachRel n Y ι f))).isCoinducing
  refine (hq.isOpen_preimage (s := ({y} : Set (attachCells n Y ι f))ᶜ)).mp ?_
  rw [hpre]
  exact hclosed_sum.isOpen_compl

/-! ## The concrete chain -/

theorem chain_isClosed_singleton_of_notMem_range_step (s : ℕ) (y : (chain W w₀).X (s + 1))
    (hy : y ∉ Set.range ((chain W w₀).step s)) :
    IsClosed ({y} : Set ((chain W w₀).X (s + 1))) :=
  isClosed_singleton_of_notMem_range_attachIncl (n := 2 + s) hy

theorem chain_isClosed_singleton_of_notMem_range_upAt (t : ℕ) (y : (chain W w₀).X t)
    (hy : y ∉ Set.range ((chain W w₀).upAt (t - 1) t (Nat.sub_le _ _))) :
    IsClosed ({y} : Set ((chain W w₀).X t)) := by
  rcases t with _ | s
  · have h1 : Set.range ((chain W w₀).upAt 0 0 (Nat.sub_le 0 0)) = Set.univ := by
      refine Set.eq_univ_of_forall fun z => ?_
      exact ⟨z, (chain W w₀).upAt_self _ z⟩
    exact absurd (h1 ▸ Set.mem_univ y) hy
  · refine chain_isClosed_singleton_of_notMem_range_step (W := W) (w₀ := w₀) s y ?_
    have hrange : Set.range ((chain W w₀).upAt s (s + 1) (Nat.sub_le (s + 1) 1))
        = Set.range ((chain W w₀).step s) := by
      rw [(chain W w₀).range_upAt_proof_irrel _ (Nat.le_succ s),
        (chain W w₀).range_upAt_pred_succ s]
    exact hrange ▸ hy

/-! ## The trace of the sequence in a stage is closed -/

namespace SeqChain

variable (C : SeqChain)

/-- The representative is a closed point. -/
theorem isClosed_singleton_rep
    (hnew : ∀ (t : ℕ) (y : C.X t), 0 < t →
      y ∉ Set.range (C.upAt (t - 1) t (Nat.sub_le _ _)) → IsClosed ({y} : Set (C.X t)))
    (x : ℕ → C.Z) (hx : ∀ S, x S ∉ Set.range (C.iota S)) (S : ℕ) :
    IsClosed ({C.rep x S} : Set (C.X (C.stg x S))) :=
  hnew (C.stg x S) (C.rep x S) (lt_of_le_of_lt (Nat.zero_le S) (C.stg_gt x hx S))
    (C.rep_notMem_range_upAt x hx S)

/-- The representative at a higher stage is a closed point. -/
theorem isClosed_singleton_upAt_rep
    (hnew : ∀ (t : ℕ) (y : C.X t), 0 < t →
      y ∉ Set.range (C.upAt (t - 1) t (Nat.sub_le _ _)) → IsClosed ({y} : Set (C.X t)))
    (x : ℕ → C.Z) (hx : ∀ S, x S ∉ Set.range (C.iota S)) (S t : ℕ) (h : C.stg x S ≤ t) :
    IsClosed ({C.upAt (C.stg x S) t h (C.rep x S)} : Set (C.X t)) := by
  have hclosed : IsClosed ({C.rep x S} : Set (C.X (C.stg x S))) :=
    C.isClosed_singleton_rep hnew x hx S
  have himg : C.upAt (C.stg x S) t h '' ({C.rep x S} : Set (C.X (C.stg x S)))
      = {C.upAt (C.stg x S) t h (C.rep x S)} := Set.image_singleton
  rw [← himg]
  exact (C.upAt_isClosedEmbedding h).isClosedMap _ hclosed

/-- **The trace of the sequence (with one point removed) in a stage is closed.** -/
theorem isClosed_preimage_range_sub_singleton
    (hnew : ∀ (t : ℕ) (y : C.X t), 0 < t →
      y ∉ Set.range (C.upAt (t - 1) t (Nat.sub_le _ _)) → IsClosed ({y} : Set (C.X t)))
    (x : ℕ → C.Z) (hx : ∀ S, x S ∉ Set.range (C.iota S)) (p : C.Z) (t : ℕ) :
    IsClosed {z : C.X t | C.iota t z ∈ Set.range x \ {p}} := by
  have hset : {z : C.X t | C.iota t z ∈ Set.range x \ {p}}
      = ⋃ S ∈ Set.Iio t, {z : C.X t | C.iota t z = x S ∧ x S ≠ p} := by
    ext z
    constructor
    · intro hz
      obtain ⟨h1, h2⟩ := hz
      obtain ⟨S, hS⟩ := h1
      refine Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · show S < t
        have hle : C.stg x S ≤ t := C.stg_min x S ⟨z, hS.symm⟩
        have hlt := C.stg_gt x hx S
        omega
      · exact ⟨hS.symm, fun hp => h2 (hS.symm.trans hp)⟩
    · intro hz
      obtain ⟨S, hS⟩ := Set.mem_iUnion.mp hz
      obtain ⟨-, hzS⟩ := Set.mem_iUnion.mp hS
      exact ⟨⟨S, hzS.1.symm⟩, fun hp => hzS.2 (hzS.1.symm.trans hp)⟩
  rw [hset]
  refine Set.Finite.isClosed_biUnion (Set.finite_Iio t) fun S _ => ?_
  by_cases hempty : ({z : C.X t | C.iota t z = x S ∧ x S ≠ p} : Set (C.X t)) = ∅
  · rw [hempty]; exact isClosed_empty
  · obtain ⟨z₀, hz₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    have hle : C.stg x S ≤ t := C.stg_min x S ⟨z₀, hz₀.1⟩
    have hsingle : {z : C.X t | C.iota t z = x S ∧ x S ≠ p}
        = {C.upAt (C.stg x S) t hle (C.rep x S)} := by
      ext z
      constructor
      · rintro ⟨hz, -⟩
        exact C.iota_injective t (hz.trans ((C.iota_compat hle (C.rep x S)).symm.trans
          (C.rep_spec x S)).symm)
      · intro hz
        rw [hz]
        exact ⟨(C.iota_compat hle (C.rep x S)).symm.trans (C.rep_spec x S), hz₀.2⟩
    rw [hsingle]
    exact C.isClosed_singleton_upAt_rep hnew x hx S t hle

/-- **The set of chosen points with one point removed is closed in the colimit.** -/
theorem isClosed_range_sub_singleton
    (hnew : ∀ (t : ℕ) (y : C.X t), 0 < t →
      y ∉ Set.range (C.upAt (t - 1) t (Nat.sub_le _ _)) → IsClosed ({y} : Set (C.X t)))
    (x : ℕ → C.Z) (hx : ∀ S, x S ∉ Set.range (C.iota S)) (p : C.Z) :
    IsClosed (Set.range x \ {p}) :=
  C.isClosed_iff.mpr fun t => C.isClosed_preimage_range_sub_singleton hnew x hx p t

end SeqChain

/-! ## The main theorem -/

/-- **A compact subset of the colimit of the truncation tower lies in a single stage.** -/
theorem exists_stage_of_compact (W : Type) [TopologicalSpace W] (w₀ : W) {K : Set (chain W w₀).Z}
    (hK : IsCompact K) : ∃ S : ℕ, K ⊆ Set.range ((chain W w₀).iota S) := by
  classical
  by_contra hcon
  have hx : ∀ S : ℕ, ∃ z : (chain W w₀).Z,
      z ∈ K ∧ z ∉ Set.range ((chain W w₀).iota S) := fun S =>
    (Set.not_subset_iff_exists_mem_notMem).mp (fun hsub => hcon ⟨S, hsub⟩)
  choose x hxK hxnot using hx
  obtain ⟨p, -, hplim⟩ := exists_clusterPoint_of_isCompact hK x hxK
  have hclosed : IsClosed (Set.range x \ {p}) :=
    (chain W w₀).isClosed_range_sub_singleton
      (fun t y _ hy => chain_isClosed_singleton_of_notMem_range_upAt t y hy) x hxnot p
  have hUopen : IsOpen ((Set.range x \ {p})ᶜ) := hclosed.isOpen_compl
  have hpmem : p ∈ (Set.range x \ {p})ᶜ := by
    intro h
    exact h.2 rfl
  have hinf : {n : ℕ | x n ∈ (Set.range x \ {p})ᶜ}.Infinite :=
    hplim _ (hUopen.mem_nhds hpmem)
  have hfin : {n : ℕ | x n = p}.Finite := by
    have hsub : {n : ℕ | x n = p} ⊆ Set.Iio ((chain W w₀).stg (fun _ : ℕ => p) 0) := by
      intro n hn
      show n < (chain W w₀).stg (fun _ : ℕ => p) 0
      by_contra hle
      have hle' : (chain W w₀).stg (fun _ : ℕ => p) 0 ≤ n := not_lt.mp hle
      have hmem : p ∈ Set.range ((chain W w₀).iota n) :=
        (chain W w₀).range_iota_subset hle'
          ((chain W w₀).stg_spec (fun _ : ℕ => p) 0)
      exact hxnot n (by rw [hn]; exact hmem)
    exact (Set.finite_Iio _).subset hsub
  have hset : {n : ℕ | x n ∈ (Set.range x \ {p})ᶜ} = {n : ℕ | x n = p} := by
    ext n
    constructor
    · intro hn
      by_contra hne
      exact hn ⟨⟨n, rfl⟩, hne⟩
    · intro hn
      show x n ∈ (Set.range x \ {p})ᶜ
      rw [hn]
      exact hpmem
  exact hfin.not_infinite (hset ▸ hinf)

/-- **Every map from a compact space into the colimit factors through a stage.** -/
theorem exists_factor (W : Type) [TopologicalSpace W] (w₀ : W) {K : Type} [TopologicalSpace K]
    [CompactSpace K] (g : C(K, (chain W w₀).Z)) :
    ∃ S : ℕ, ∃ h : C(K, (chain W w₀).X S), ∀ k : K, ((chain W w₀).iota S) (h k) = g k := by
  obtain ⟨S, hS⟩ := exists_stage_of_compact W w₀ (isCompact_range g.continuous)
  refine ⟨S, ?_⟩
  let e : (chain W w₀).X S ≃ₜ ↥(Set.range ((chain W w₀).iota S)) :=
    ((chain W w₀).isEmbedding_iota S).toHomeomorph
  have hcont : Continuous fun k : K => e.symm ⟨g k, hS (Set.mem_range_self k)⟩ := by
    refine ((chain W w₀).isEmbedding_iota S).isInducing.continuous_iff.mpr ?_
    change Continuous fun k : K =>
      ((chain W w₀).iota S) (e.symm ⟨g k, hS (Set.mem_range_self k)⟩)
    have hfun : (fun k : K => ((chain W w₀).iota S) (e.symm ⟨g k, hS (Set.mem_range_self k)⟩))
        = fun k => g k := by
      funext k
      exact congrArg Subtype.val (e.apply_symm_apply ⟨g k, hS (Set.mem_range_self k)⟩)
    rw [hfun]
    exact g.continuous
  exact ⟨⟨fun k => e.symm ⟨g k, hS (Set.mem_range_self k)⟩, hcont⟩,
    fun k => congrArg Subtype.val (e.apply_symm_apply ⟨g k, hS (Set.mem_range_self k)⟩)⟩

end

end Work.Serre.RangeOne
