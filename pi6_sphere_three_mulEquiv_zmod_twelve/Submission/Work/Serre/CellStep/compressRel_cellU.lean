import Mathlib
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Serre.CellStep.Tools
import Submission.Work.RatHurewicz.AttachPush.PushOff

set_option synthInstance.maxHeartbeats 400000


/-!
# The compression property of the pair `(cellU f ρ, cellU f ρ ∩ Γ)`

`Work.Serre.cellU f ρ` is the complement of the images of the closed model balls of radius `ρ`,
and `Work.RatHurewicz.attachIncl` embeds `Γ` into `Γ' = attachCells n Γ ι f` as the "old part".
Since the union of the closed balls contains all the cell centres, `cellU f ρ` misses every cell
centre whenever `ρ > 0`, and the radial push `Work.RatHurewicz.pushGarbage` of each punctured cell
onto its boundary sphere (which only *increases* the norm, hence preserves `‖x‖ > ρ`) is a strong
deformation retraction of `cellU f ρ` onto `Γ ⊆ cellU f ρ`.

This file constructs that deformation retraction as a descent of `pushGarbage` through the quotient
map `Γ ⊕ (Σ i, D) → Γ'`, restricted to the saturated open preimage of `cellU f ρ`
(`Work.RatHurewicz.exists_pushOff_homotopy` and `Work.Serre.csrCompress` are the models), and
deduces `Work.RatHurewicz.CompressRel`.
-/

set_option maxHeartbeats 1600000

open scoped Topology unitInterval

namespace Work.Serre.CellStep

noncomputable section

open Work.RatHurewicz Work.Serre

variable {n : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}

/-- The saturated preimage of `cellU f ρ` in the disjoint union `Γ ⊕ (Σ i, D^{n+2})`. -/
abbrev cellUpre (f : ι → C(cellSphere n, Γ)) (ρ : ℝ) : Set (Γ ⊕ (Σ _ : ι, cellDisk n)) :=
  (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Γ ι f))) ⁻¹' cellU f ρ

/-- **The characterisation of the closed-ball neighbourhood**: for `ρ < 1`, the point `χᵢ(x)` lies
in the union of the images of the closed balls of radius `ρ` exactly when `‖x‖ ≤ ρ`. -/
theorem cellMap_mem_cellBallImg_iff (f : ι → C(cellSphere n, Γ)) {ρ : ℝ} (hρ1 : ρ < 1)
    (i : ι) (x : cellDisk n) :
    cellMap n Γ ι f i x ∈ cellBallImg f ρ ↔ ‖(x : CellVec n)‖ ≤ ρ := by
  constructor
  · intro h
    obtain ⟨j, z, hz, hzj⟩ := (mem_cellBallImg f).mp h
    have hz_in : z ∈ cellInner n := lt_of_le_of_lt hz hρ1
    have hxle : ‖(x : CellVec n)‖ ≤ 1 := by
      have h' := Metric.mem_closedBall.mp x.2
      simpa [dist_eq_norm] using h'
    rcases lt_or_eq_of_le hxle with hxlt | hxeq
    · have hzi : cellMap n Γ ι f j z ∈ cellInterior n Γ ι f j :=
        cellMap_mem_cellInterior_of_norm_lt hz_in
      have hxi : cellMap n Γ ι f i x ∈ cellInterior n Γ ι f i :=
        cellMap_mem_cellInterior_of_norm_lt hxlt
      have hij : i = j := by
        by_contra hne
        exact Set.disjoint_left.mp (disjoint_cellInterior (f := f) i j hne) hxi (hzj ▸ hzi)
      subst hij
      have hxz : x = z := by
        have h' : (⟨x, hxlt⟩ : ↥(cellInner n)) = ⟨z, hz_in⟩ :=
          cellMap_injective_cellInner (f := f) i (by simpa using hzj.symm)
        exact congrArg Subtype.val h'
      rwa [hxz]
    · exfalso
      have hsp : (x : CellVec n) ∈ Metric.sphere (0 : CellVec n) 1 := by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hxeq
      have hmem : cellMap n Γ ι f i x ∈ Set.range (attachIncl n Γ ι f) := by
        let z' : cellSphere n := ⟨(x : CellVec n), hsp⟩
        have hc : cellSphereToDisk n z' = x := Subtype.ext rfl
        rw [← hc, ← attachIncl_attachRel n Γ ι f i z']
        exact ⟨f i z', rfl⟩
      have hzi : cellMap n Γ ι f j z ∈ cellInterior n Γ ι f j :=
        cellMap_mem_cellInterior_of_norm_lt hz_in
      have h2 : cellMap n Γ ι f i x ∈ ⋃ k, cellInterior n Γ ι f k :=
        Set.mem_iUnion.mpr ⟨j, hzj ▸ hzi⟩
      rw [(Work.Serre.AttachCompress.cellPartition n Γ ι f).1] at hmem
      exact hmem h2
  · intro h
    exact (mem_cellBallImg f).mpr ⟨i, x, h, rfl⟩

/-- **The radial push preserves `cellU f ρ`**: pushing a point of `cellU f ρ` (i.e. a point whose
class lies in `cellU f ρ`) radially towards the boundary sphere of its cell keeps it in
`cellU f ρ`, because the push does not decrease the norm. -/
theorem pushGarbage_mem_cellU (f : ι → C(cellSphere n, Γ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {a : Γ ⊕ (Σ _ : ι, cellDisk n)} (ha : a ∈ cellUpre f ρ) (s : I) :
    pushGarbage n Γ ι f a s ∈ cellU f ρ := by
  have ha' : (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Γ ι f)) a :
      attachCells n Γ ι f) ∈ cellU f ρ := ha
  rcases a with y | ⟨i, x⟩
  · rw [pushGarbage_inl]
    intro hmem
    exact Set.disjoint_left.mp (disjoint_cellBallImg_range f hρ1) hmem ⟨y, rfl⟩
  · have hxnorm : ρ < ‖(x : CellVec n)‖ := by
      by_contra hcon
      rw [not_lt] at hcon
      exact ha' ((mem_cellBallImg f).mpr ⟨i, x, hcon, rfl⟩)
    have hx0 : (x : CellVec n) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hxnorm; linarith
    rw [pushGarbage_inr (i := i) (x := x) hx0 s]
    intro hmem
    have hy : ‖(((cellPush n (⟨x, hx0⟩, s) : cellDisk n)) : CellVec n)‖ ≤ ρ :=
      (cellMap_mem_cellBallImg_iff f hρ1 i (cellPush n (⟨x, hx0⟩, s))).mp hmem
    rw [cellPush_apply, norm_cellPushVec n s hx0] at hy
    have hxle : ‖(x : CellVec n)‖ ≤ 1 := by
      have h' := Metric.mem_closedBall.mp x.2
      simpa [dist_eq_norm] using h'
    have hs : (0:ℝ) ≤ (s:ℝ) := s.2.1
    nlinarith

/-- **The compression property of `(cellU f ρ, cellU f ρ ∩ Γ)` in every dimension.**  The radial
push of the punctured cells onto their boundary spheres, restricted to `cellU f ρ`, is a strong
deformation retraction onto the old part `Γ ⊆ cellU f ρ`. -/
theorem compressRel_cellU (n : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Γ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (d : ℕ) :
    Work.RatHurewicz.CompressRel ↥(Work.Serre.cellU f ρ)
      {x : ↥(Work.Serre.cellU f ρ) |
        (x : Work.RatHurewicz.attachCells n Γ ι f) ∈
          Set.range (Work.RatHurewicz.attachIncl n Γ ι f)} d := by
  classical
  -- every cell centre lies in the union of the closed balls of radius `ρ`
  have hcent : ∀ i : ι, cellOrigin n Γ ι f i ∈ cellBallImg f ρ := fun i =>
    (mem_cellBallImg f).mpr ⟨i, cellDiskCentre n, by simp [cellDiskCentre]; linarith, rfl⟩
  -- so the saturated preimage of `cellU f ρ` is contained in the push domain
  have hpre_sub : cellUpre f ρ ⊆ pushDomain n Γ ι f := by
    intro a ha
    rw [cellUpre, Set.mem_preimage] at ha
    rw [pushDomain, Set.mem_preimage, Set.mem_compl_iff]
    rintro ⟨i, hi⟩
    exact ha (hi.symm ▸ hcent i)
  -- the quotient map on the saturated preimage
  set qU := (cellU f ρ).restrictPreimage
    (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Γ ι f))) with hqUdef
  have hqU : Topology.IsQuotientMap qU :=
    Topology.IsQuotientMap.restrictPreimage_isOpen
      (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (attachRel n Γ ι f)))
      (isOpen_cellU f hρ1)
  -- the descended push
  set G : ↥(cellU f ρ) × I → ↥(cellU f ρ) := fun p =>
    ⟨pushGarbage n Γ ι f ((Classical.choose (hqU.surjective p.1) : ↥(cellUpre f ρ)) :
        Γ ⊕ (Σ _ : ι, cellDisk n)) p.2,
      pushGarbage_mem_cellU f hρ0 hρ1 (Classical.choose (hqU.surjective p.1)).2 p.2⟩ with hGdef
  have hG_zero : ∀ v : ↥(cellU f ρ), G (v, 0) = v := by
    intro v
    apply Subtype.ext
    show pushGarbage n Γ ι f ((Classical.choose (hqU.surjective v) : ↥(cellUpre f ρ)) :
        Γ ⊕ (Σ _ : ι, cellDisk n)) (0 : I) = (v : attachCells n Γ ι f)
    rw [pushGarbage_zero (hpre_sub (Classical.choose (hqU.surjective v)).2)]
    exact congrArg (fun w : ↥(cellU f ρ) => (w : attachCells n Γ ι f))
      (Classical.choose_spec (hqU.surjective v))
  have hG_one : ∀ v : ↥(cellU f ρ),
      (G (v, 1) : attachCells n Γ ι f) ∈ Set.range (attachIncl n Γ ι f) := by
    intro v
    show pushGarbage n Γ ι f ((Classical.choose (hqU.surjective v) : ↥(cellUpre f ρ)) :
        Γ ⊕ (Σ _ : ι, cellDisk n)) (1 : I) ∈ Set.range (attachIncl n Γ ι f)
    exact pushGarbage_one_mem (hpre_sub (Classical.choose (hqU.surjective v)).2)
  have hG_fix : ∀ (v : ↥(cellU f ρ)) (t : I),
      (v : attachCells n Γ ι f) ∈ Set.range (attachIncl n Γ ι f) → G (v, t) = v := by
    intro v t hv
    apply Subtype.ext
    have hv' : (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Γ ι f))
        ((Classical.choose (hqU.surjective v) : ↥(cellUpre f ρ)) :
          Γ ⊕ (Σ _ : ι, cellDisk n)) : attachCells n Γ ι f) ∈
        Set.range (attachIncl n Γ ι f) := by
      have hspec := Classical.choose_spec (hqU.surjective v)
      have hq_eq : (qU (Classical.choose (hqU.surjective v)) : attachCells n Γ ι f) =
          (v : attachCells n Γ ι f) :=
        congrArg (fun w : ↥(cellU f ρ) => (w : attachCells n Γ ι f)) hspec
      show (qU (Classical.choose (hqU.surjective v)) : attachCells n Γ ι f) ∈
        Set.range (attachIncl n Γ ι f)
      rw [hq_eq]
      exact hv
    show pushGarbage n Γ ι f ((Classical.choose (hqU.surjective v) : ↥(cellUpre f ρ)) :
        Γ ⊕ (Σ _ : ι, cellDisk n)) t = (v : attachCells n Γ ι f)
    rw [pushGarbage_fix (hpre_sub (Classical.choose (hqU.surjective v)).2) hv' t]
    exact congrArg (fun w : ↥(cellU f ρ) => (w : attachCells n Γ ι f))
      (Classical.choose_spec (hqU.surjective v))
  have hG_cont : Continuous G := by
    refine Topology.IsQuotientMap.continuous_lift_prod_left hqU ?_
    have hcomp : (fun p : ↥(cellUpre f ρ) × I => G (qU p.1, p.2)) =
        fun p : ↥(cellUpre f ρ) × I =>
          (⟨pushGarbage n Γ ι f (p.1 : Γ ⊕ (Σ _ : ι, cellDisk n)) p.2,
            pushGarbage_mem_cellU f hρ0 hρ1 p.1.2 p.2⟩ : ↥(cellU f ρ)) := by
      funext p
      apply Subtype.ext
      show pushGarbage n Γ ι f ((Classical.choose (hqU.surjective (qU p.1)) :
          ↥(cellUpre f ρ)) : Γ ⊕ (Σ _ : ι, cellDisk n)) p.2 = _
      exact pushGarbage_eq_of_eqvGen p.2
        (Quotient.exact (s := Relation.EqvGen.setoid (attachRel n Γ ι f))
          (show (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Γ ι f))
              ((Classical.choose (hqU.surjective (qU p.1)) : ↥(cellUpre f ρ)) :
                Γ ⊕ (Σ _ : ι, cellDisk n)) : attachCells n Γ ι f)
            = Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Γ ι f))
              (p.1 : Γ ⊕ (Σ _ : ι, cellDisk n))
            from congrArg (fun w : ↥(cellU f ρ) => (w : attachCells n Γ ι f))
              (Classical.choose_spec (hqU.surjective (qU p.1)))))
        (hpre_sub (Classical.choose (hqU.surjective (qU p.1))).2) (hpre_sub p.1.2)
    rw [hcomp]
    exact Continuous.subtype_mk
      (continuous_pushGarbage.comp (Continuous.prodMap
        (Continuous.subtype_mk continuous_subtype_val (fun x : ↥(cellUpre f ρ) => hpre_sub x.2))
        continuous_id))
      (fun p => pushGarbage_mem_cellU f hρ0 hρ1 p.1.2 p.2)
  exact compressRel_of_deformation ⟨G, hG_cont⟩ hG_zero hG_one (fun v hv t => hG_fix v t hv) d

end

end Work.Serre.CellStep
