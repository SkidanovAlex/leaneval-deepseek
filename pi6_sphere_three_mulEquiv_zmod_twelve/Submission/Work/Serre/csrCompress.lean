import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.CellStep.Tools
import Submission.Work.Serre.E2dEngine
import Submission.Work.RatHurewicz.AttachPush.PushOff

set_option synthInstance.maxHeartbeats 400000


/-!
# Compression of the complement of the cell centres

Vocabulary and the main result `Work.Serre.csrCompress`.
-/

set_option maxHeartbeats 1600000

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-! ## The push-off homotopy avoids the cell centres

The push-off homotopy of `Work.RatHurewicz.exists_pushOff_homotopy` is built from the radial push
`Work.RatHurewicz.pushGarbage`, which never meets a cell centre on its domain of definition: over
the `Y`-summand it is `attachIncl`, and over a punctured cell it is `cellMap` of a positive multiple
of a non-zero vector of the model disc.  We record this and the resulting strengthened push-off
homotopy (the statement of `Work.RatHurewicz.exists_pushOff_homotopy` with the additional
conjunct that every intermediate map avoids the centres), which is what lets us regard the homotopy
as a homotopy inside the complement `csrV` of the centres. -/

open Work.RatHurewicz

/-- The radial push `pushGarbage`, evaluated on its domain of definition `pushDomain`, never lands
on a cell centre. -/
theorem csrPushGarbage_ne_cellOrigin (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (a : Y ⊕ (Σ _ : ι, cellDisk n))
    (ha : a ∈ pushDomain n Y ι f) (s : I) (j : ι) :
    pushGarbage n Y ι f a s ≠ cellOrigin n Y ι f j := by
  rcases (mem_pushDomain_iff (n := n) (Y := Y) (ι := ι) (f := f) a).mp ha with
    ⟨y, rfl⟩ | ⟨i, x, hx, rfl⟩
  · rw [pushGarbage_inl]
    intro h
    exact cellOrigin_notMem_range_attachIncl (f := f) j ⟨y, h⟩
  · rw [pushGarbage_inr (i := i) (hx := hx)]
    refine cellMap_ne_cellOrigin (n := n) (Y := Y) (ι := ι) (f := f) (j := j) ?_
    rw [cellPush_apply]
    intro h0
    have hnorm := norm_cellPushVec n s hx
    rw [h0, norm_zero] at hnorm
    have hxpos : 0 < ‖(x : CellVec n)‖ := norm_pos_iff.mpr hx
    have hsge : (0 : ℝ) ≤ (s : ℝ) := s.2.1
    have hsle : (s : ℝ) ≤ 1 := s.2.2
    have hpos : 0 < (1 - (s : ℝ)) * ‖(x : CellVec n)‖ + (s : ℝ) := by
      rcases eq_or_lt_of_le hsle with h | h
      · rw [h]; norm_num
      · have h1 : 0 < 1 - (s : ℝ) := by linarith
        have h2 : 0 < (1 - (s : ℝ)) * ‖(x : CellVec n)‖ := mul_pos h1 hxpos
        linarith
    linarith [hnorm]

/-- **The push-off homotopy, through maps avoiding every cell centre.**  Strengthening of
`Work.RatHurewicz.exists_pushOff_homotopy` with the extra conjunct that every intermediate map
avoids all cell centres. -/
theorem csrExists_pushOff_homotopy (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) {X : Type} [TopologicalSpace X]
    (h : C(X, attachCells n Y ι f))
    (havoid : ∀ (i : ι) (x : X), h x ≠ cellOrigin n Y ι f i) :
    ∃ H : C(X × I, attachCells n Y ι f),
      (∀ x, H (x, 0) = h x) ∧
      (∀ x, h x ∈ Set.range (attachIncl n Y ι f) → ∀ t : I, H (x, t) = h x) ∧
      (∀ x, H (x, 1) ∈ Set.range (attachIncl n Y ι f)) ∧
      (∀ (x : X) (t : I) (i : ι), H (x, t) ≠ cellOrigin n Y ι f i) := by
  classical
  set qr : ↥(pushDomain n Y ι f) → ↥((cellCentres n Y ι f)ᶜ) :=
    ((cellCentres n Y ι f)ᶜ).restrictPreimage
      (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))) with hqrdef
  have hqr : Topology.IsQuotientMap qr :=
    Topology.IsQuotientMap.restrictPreimage_isOpen
      (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f)))
      (isClosed_cellCentres n Y ι f).isOpen_compl
  set G : ↥((cellCentres n Y ι f)ᶜ) × I → attachCells n Y ι f := fun p =>
    pushGarbage n Y ι f ((Classical.choose (hqr.surjective p.1) : ↥(pushDomain n Y ι f)) :
      Y ⊕ (Σ _ : ι, cellDisk n)) p.2 with hGdef
  have hG_zero : ∀ v : ↥((cellCentres n Y ι f)ᶜ), G (v, 0) = (v : attachCells n Y ι f) := by
    intro v
    show pushGarbage n Y ι f ((Classical.choose (hqr.surjective v) : ↥(pushDomain n Y ι f)) :
      Y ⊕ (Σ _ : ι, cellDisk n)) (0 : I) = (v : attachCells n Y ι f)
    rw [pushGarbage_zero_apply (Classical.choose (hqr.surjective v))]
    exact congrArg (fun w : ↥((cellCentres n Y ι f)ᶜ) => (w : attachCells n Y ι f))
      (Classical.choose_spec (hqr.surjective v))
  have hG_one : ∀ v : ↥((cellCentres n Y ι f)ᶜ),
      G (v, 1) ∈ Set.range (attachIncl n Y ι f) := by
    intro v
    show pushGarbage n Y ι f ((Classical.choose (hqr.surjective v) : ↥(pushDomain n Y ι f)) :
      Y ⊕ (Σ _ : ι, cellDisk n)) (1 : I) ∈ Set.range (attachIncl n Y ι f)
    exact pushGarbage_one_mem (Classical.choose (hqr.surjective v)).2
  have hG_fix : ∀ (v : ↥((cellCentres n Y ι f)ᶜ)) (t : I),
      (v : attachCells n Y ι f) ∈ Set.range (attachIncl n Y ι f) →
      G (v, t) = (v : attachCells n Y ι f) := by
    intro v t hv
    have hv' : (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
        ((Classical.choose (hqr.surjective v) : ↥(pushDomain n Y ι f)) :
          Y ⊕ (Σ _ : ι, cellDisk n)) : attachCells n Y ι f) ∈
        Set.range (attachIncl n Y ι f) := by
      have hspec := Classical.choose_spec (hqr.surjective v)
      have hq_eq : (qr (Classical.choose (hqr.surjective v)) : attachCells n Y ι f) =
          (v : attachCells n Y ι f) :=
        congrArg (fun w : ↥((cellCentres n Y ι f)ᶜ) => (w : attachCells n Y ι f)) hspec
      show (qr (Classical.choose (hqr.surjective v)) : attachCells n Y ι f) ∈
        Set.range (attachIncl n Y ι f)
      rw [hq_eq]
      exact hv
    show pushGarbage n Y ι f ((Classical.choose (hqr.surjective v) : ↥(pushDomain n Y ι f)) :
      Y ⊕ (Σ _ : ι, cellDisk n)) t = (v : attachCells n Y ι f)
    rw [pushGarbage_fix_apply (Classical.choose (hqr.surjective v)) hv' t]
    exact congrArg (fun w : ↥((cellCentres n Y ι f)ᶜ) => (w : attachCells n Y ι f))
      (Classical.choose_spec (hqr.surjective v))
  have hG_ne : ∀ (v : ↥((cellCentres n Y ι f)ᶜ)) (t : I) (i : ι),
      G (v, t) ≠ cellOrigin n Y ι f i := by
    intro v t i
    show pushGarbage n Y ι f ((Classical.choose (hqr.surjective v) : ↥(pushDomain n Y ι f)) :
      Y ⊕ (Σ _ : ι, cellDisk n)) t ≠ cellOrigin n Y ι f i
    exact csrPushGarbage_ne_cellOrigin n Y ι f _
      (Classical.choose (hqr.surjective v)).2 t i
  have hG_cont : Continuous G := by
    refine Topology.IsQuotientMap.continuous_lift_prod_left hqr ?_
    have hcomp : (fun p : ↥(pushDomain n Y ι f) × I => G (qr p.1, p.2)) =
        fun p : ↥(pushDomain n Y ι f) × I =>
          pushGarbage n Y ι f (p.1 : Y ⊕ (Σ _ : ι, cellDisk n)) p.2 := by
      funext p
      show pushGarbage n Y ι f ((Classical.choose (hqr.surjective (qr p.1)) :
        ↥(pushDomain n Y ι f)) : Y ⊕ (Σ _ : ι, cellDisk n)) p.2 = _
      exact pushGarbage_eq_of_eqvGen p.2
        (Quotient.exact (s := Relation.EqvGen.setoid (attachRel n Y ι f))
          (show (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
              ((Classical.choose (hqr.surjective (qr p.1)) : ↥(pushDomain n Y ι f)) :
                Y ⊕ (Σ _ : ι, cellDisk n)) : attachCells n Y ι f)
            = Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
              (p.1 : Y ⊕ (Σ _ : ι, cellDisk n))
            from congrArg (fun w : ↥((cellCentres n Y ι f)ᶜ) => (w : attachCells n Y ι f))
              (Classical.choose_spec (hqr.surjective (qr p.1)))))
        (Classical.choose (hqr.surjective (qr p.1))).2 p.1.2
    rw [hcomp]
    exact continuous_pushGarbage
  have hnotcentres : ∀ x : X, h x ∈ (cellCentres n Y ι f)ᶜ := by
    intro x
    rintro ⟨i, hi⟩
    exact havoid i x hi.symm
  have hmap : Continuous fun p : X × I => (⟨h p.1, hnotcentres p.1⟩ :
      ↥((cellCentres n Y ι f)ᶜ)) :=
    (h.continuous.comp continuous_fst).subtype_mk _
  refine ⟨⟨fun p : X × I => G ((⟨h p.1, hnotcentres p.1⟩ :
      ↥((cellCentres n Y ι f)ᶜ)), p.2), hG_cont.comp (hmap.prodMk continuous_snd)⟩,
    ?_, ?_, ?_, ?_⟩
  · intro x
    exact hG_zero ⟨h x, hnotcentres x⟩
  · intro x hx t
    exact hG_fix ⟨h x, hnotcentres x⟩ t hx
  · intro x
    exact hG_one ⟨h x, hnotcentres x⟩
  · intro x t i
    exact hG_ne ⟨h x, hnotcentres x⟩ t i

/-- **Compression of the old part.**  For `Z = attachCells n Y ι f` with `Y' = range attachIncl` and
`V = csrV` the complement of the cell centres, the pairs `(V, Y' ∩ V)` and `(q⁻¹V, q⁻¹Y' ∩ q⁻¹V)`
have vanishing integral relative homology in every degree: `V` deformation retracts onto `Y'` (push
every point of the punctured cells radially onto the boundary sphere, using
`Work.RatHurewicz.exists_pushOff_homotopy`, whose homotopy stays inside `V`), and the same homotopy
lifts through the Serre fibration `q` (relative cube HLP) to a deformation of `q⁻¹V` onto
`q⁻¹Y'`. -/
theorem csrCompress (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (m : ℕ) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
        (TopCat.of ↥(csrV n Y ι f))
        {x : ↥(csrV n Y ι f) | (x : Work.RatHurewicz.attachCells n Y ι f) ∈
          Set.range (Work.RatHurewicz.attachIncl n Y ι f)}).homology m) ∧
    CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
        (TopCat.of ↥(q ⁻¹' csrV n Y ι f))
        {x : ↥(q ⁻¹' csrV n Y ι f) | (x : E) ∈ q ⁻¹'
          (Set.range (Work.RatHurewicz.attachIncl n Y ι f))}).homology m) := by
  classical
  -- the range of `attachIncl` misses the cell centres
  have hsub : Set.range (Work.RatHurewicz.attachIncl n Y ι f) ⊆ csrV n Y ι f := by
    rintro z ⟨y, rfl⟩ ⟨i, hi⟩
    refine Work.RatHurewicz.cellOrigin_notMem_range_attachIncl (f := f) i ?_
    change csrCentre n Y ι f i ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f)
    exact hi ▸ ⟨y, rfl⟩
  -- the push-off homotopy of the complement of the centres, avoiding the centres throughout
  obtain ⟨H, hH0, hHfix, hH1, hHne⟩ :=
    csrExists_pushOff_homotopy n Y ι f (X := ↥(csrV n Y ι f))
      ⟨Subtype.val, continuous_subtype_val⟩
      (fun i x h => x.2 ⟨i, h.symm⟩)
  have hHmem : ∀ p : ↥(csrV n Y ι f) × I, H p ∈ csrV n Y ι f := by
    intro p
    rintro ⟨i, hi⟩
    exact hHne p.1 p.2 i hi.symm
  -- it is a deformation retraction of `csrV` onto the trace of `attachIncl`
  let c : C(↥(csrV n Y ι f) × I, ↥(csrV n Y ι f)) :=
    ⟨fun p => ⟨H p, hHmem p⟩, H.continuous.subtype_mk hHmem⟩
  have hc0 : ∀ v : ↥(csrV n Y ι f), c (v, 0) = v := fun v => Subtype.ext (hH0 v)
  have hc1 : ∀ v : ↥(csrV n Y ι f), c (v, 1) ∈
      {x : ↥(csrV n Y ι f) | (x : Work.RatHurewicz.attachCells n Y ι f) ∈
        Set.range (Work.RatHurewicz.attachIncl n Y ι f)} := fun v => hH1 v
  have hcA : ∀ v ∈ {x : ↥(csrV n Y ι f) |
        (x : Work.RatHurewicz.attachCells n Y ι f) ∈
          Set.range (Work.RatHurewicz.attachIncl n Y ι f)}, ∀ t : I, c (v, t) = v :=
    fun v hv t => Subtype.ext (hHfix v hv t)
  refine ⟨isZero_relChains_of_deformation c hc0 hc1 hcA m, ?_⟩
  exact isZero_relChains_preimage_of_compress q hq
    (W₀ := Set.range (Work.RatHurewicz.attachIncl n Y ι f)) (W := csrV n Y ι f) hsub
    (fun d => compressRel_of_deformation c hc0 hc1 hcA d) m

end

end Work.Serre
