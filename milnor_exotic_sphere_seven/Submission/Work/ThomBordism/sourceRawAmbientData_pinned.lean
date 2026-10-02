import Mathlib
import Submission.Work.PTGeometric.nonempty_rawAmbientData_of_sourceRegion
import Submission.Work.ThomBordism.exists_localData_at_boundaryZero_pinned

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The raw ambient data of the source construction, with the reading maps *pinned*

`Work.PTGeometric.nonempty_rawAmbientData_of_sourceRegion` produces the `RawAmbientData` of the
source construction, but the linear maps `ellE j` it returns are abstract: they are the witnesses of
the pointwise local data `Work.PTGeometric.exists_localData_at_boundaryZero`.

This file runs the *same* construction with the *pinned* pointwise local data
(`Work.ThomBordism.exists_localData_at_boundaryZero_pinned`): at every boundary zero one has an
explicit reading map `Work.Tubular.readCLM (G.emb i) ND j w0 ∘ Work.PTGeometric.projEuc k G.mU G.hmU`,
and the finite cover is taken over the *pin data* (piece, base point, normal datum, cover index)
rather than over the abstract linear map.  The result
(`Work.ThomBordism.sourceRawAmbientData_pinned`) is the same existential statement as the unpinned
producer, with the extra conclusion that every `ellE j` is *literally* one of the pinned reading
maps.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom
open Work.PTGeometric.WeakRegion

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The degenerate case of the pinned producer** (an empty index type): the explicit ball model of
`Work.PTGeometric.nonempty_rawAmbientData_of_isEmpty_index`, this time with the *sharp* information
that its chart index is empty (`mE = 0`).  This is needed because the pinned conclusion only has a
witness for the indices `Fin D0.mE` for which a piece of the family exists. -/
theorem exists_rawAmbientData_isEmpty_index
    {k : ℕ} {ι : Type} [Fintype ι] [IsEmpty ι] {Fam : ι → Man8}
    (hk : 11 ≤ k) (mU : ℕ) (hmU : 8 ≤ mU) (m : ℕ) :
    ∃ D0 : RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2), D0.mE = 0 := by
  classical
  have hk0 : 0 < k := by omega
  haveI hMan : IsManifold (𝓡∂ ((8 + k) + 1)) ∞ (Work.SignatureBordism.Ball (8 + k)) :=
    Work.SignatureBordism.instIsManifoldBall (8 + k)
  haveI : CompactSpace (Work.SignatureBordism.Ball (8 + k)) :=
    Work.SignatureBordism.instCompactSpaceBall (8 + k)
  haveI : T2Space (Work.SignatureBordism.Ball (8 + k)) := inferInstance
  haveI : Nonempty (Work.SignatureBordism.Ball (8 + k)) :=
    ⟨0, by simp [Work.SignatureBordism.Ball]⟩
  haveI hRight : IsEmpty (Σ a : Fin m × ι, (Fam a.2).pt) :=
    ⟨fun y => isEmptyElim y.1.2⟩
  have hLeft : IsEmpty ↥((∅ : Set (Work.SignatureBordism.Ball (8 + k))) ∩
      {x : Work.SignatureBordism.Ball (8 + k) |
        (fun _ : Work.SignatureBordism.Ball (8 + k) => padEuc k mU hmU (stdVec k hk0)) x = 0}) :=
    ⟨fun x => Set.notMem_empty x.1 x.2.1⟩
  exact ⟨
    { M := Work.SignatureBordism.Ball (8 + k)
      P := fun _ => padEndEuc k mU hmU (stdProj k)
      v := fun _ => padEuc k mU hmU (stdVec k hk0)
      hPc := continuous_const
      hvc := continuous_const
      hProj := fun _ => padEndEuc_mem_Gr hmU (stdProj_mem_Gr k)
      hMem := fun _ => by
        rw [padEndEuc_apply_padEuc, stdProj_apply_stdVec k hk0]
      V := Set.univ
      hVopen := isOpen_univ
      S0 := ∅
      hS0cl := isClosed_empty
      hS0V := Set.empty_subset _
      hPsmV := contMDiff_const.contMDiffOn
      hvsmV := contMDiff_const.contMDiffOn
      S := ∅
      hScl := isClosed_empty
      hSsub := Set.empty_subset _
      hSS0 := Set.empty_subset _
      hend := homeoOfIsEmpty hLeft hRight
      hzero_sub := by
        intro x _ hx0
        exact absurd (padEuc_injective k mU hmU (by
          rw [hx0, map_zero])) (stdVec_ne_zero k hk0)
      δ := 1
      hδpos := one_pos
      hδ := by
        intro x _ _
        simp [norm_padEuc, norm_stdVec k hk0]
      mE := 0
      ellE := fun j => isEmptyElim j
      UE := fun _ => ∅
      isOpen_UE := fun _ => isOpen_empty
      UE_int := fun _ => Set.empty_subset _
      ellE_inj := fun j => isEmptyElim j
      ellE_inj_cl := fun j => isEmptyElim j
      bndZero_cov := by
        intro x _ hx0
        exact absurd (padEuc_injective k mU hmU (by rw [hx0, map_zero]))
          (stdVec_ne_zero k hk0)
      bndZero_trans := fun j => isEmptyElim j }, rfl⟩

/-- **The pinned raw ambient data of the source construction.**  Same statement as
`Work.PTGeometric.nonempty_rawAmbientData_of_sourceRegion`, with the extra information that each
reading map is one of the pinned tube reading maps
`Work.Tubular.readCLM (G.emb i) ND j w0 ∘ Work.PTGeometric.projEuc k G.mU G.hmU`. -/
theorem sourceRawAmbientData_pinned_aux
    {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt)
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
    (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (hwk : Work.PTGeometric.RegionManifoldTheoremOfIsCompactWeak k)
    (hphi : Work.PTGeometric.SourceRegionPhiInteriorSign k
      (Work.PTGeometric.sourceZeroSet G m hpow)
      {x : EuclideanHalfSpace ((8 + k) + 1) |
        Work.PTGeometric.flatSourceHomotopy8 (k := k)
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ x.1 = D.t₀}) :
    ∃ D0 : Work.PTGeometric.RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2),
      ∀ j : Fin D0.mE, ∃ (i : ι) (w0 : (Fam i).pt)
        (ND : Work.ThomBordism.PontryaginThom.NormalData (Fam i) k (G.emb i).e)
        (j' : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
        (hb : w0 ∈ ND.D.baseSet j'),
        D0.ellE j =
          (Work.Tubular.readCLM (G.emb i) ND j' w0).comp (Work.PTGeometric.projEuc k G.mU G.hmU) := by
  classical
  haveI := t2Space_halfSpace ((8 + k) + 1)
  -- ### Step 1: the clauses of the defining function
  obtain ⟨hΦ, hZsub, hdisj, hK, hzero, hsub, hone, hsign⟩ := sourcePhi_spec G m hpow hphi
  -- ### Step 2: the weak regularity clause
  have hweak : ∀ x : EuclideanHalfSpace ((8 + k) + 1),
      sourcePhi G m hpow hphi x = 0 →
      mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) (sourcePhi G m hpow hphi) x ≠ 0 :=
    mfderiv_ne_zero_of_phi_zero hΦ hsub hone
  -- ### Step 3: the region structure of the source
  let S := sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak
  let M := S.Region
  letI : ChartedSpace (EuclideanHalfSpace (8 + k + 1)) M := S.chartedSpaceOfRegion
  letI : IsManifold (𝓡∂ (8 + k + 1)) ∞ M := S.isManifoldOfRegion
  letI : CompactSpace M := S.compactSpaceOfRegion
  letI : T2Space M := S.t2SpaceOfRegion
  -- ### Step 3bis: the degenerate case of an empty index type
  rcases isEmpty_or_nonempty ι with hιempty | hιne
  · -- the family is empty: the conclusion is index-free, and the pin condition is vacuous because
    -- the produced chart family is empty
    haveI := hιempty
    obtain ⟨D0, hmE⟩ := exists_rawAmbientData_isEmpty_index (Fam := Fam) hk G.mU G.hmU m
    refine ⟨D0, ?_⟩
    intro j
    exact Fin.elim0 (hmE ▸ j)
  -- ### Step 3ter: the region is nonempty (the pieces are)
  haveI hMne : Nonempty M := by
    obtain ⟨i⟩ := hιne
    have hSig : Nonempty (Σ a : Fin m × ι, (Fam a.2).pt) :=
      ⟨⟨⟨0, hm⟩, i⟩, Classical.choice (hne i)⟩
    obtain ⟨hp⟩ := hSig.map (Classical.choice (sourceZeroSet_boundary_homeo G m hpow)).symm
    exact ⟨⟨hp.1, hZsub hp.2.1⟩⟩
  -- ### Step 4: the ambient field
  let Hf : EuclideanSpace ℝ (Fin ((8 + k) + 1)) → D.T :=
    Work.PTGeometric.flatSourceHomotopy8 (k := k)
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ
  have hne' : ∀ x : M, Hf x.1.1 ≠ D.t₀ := by
    intro x hx
    have h : x.1 ∈ ({x : EuclideanHalfSpace ((8 + k) + 1) |
        sourcePhi G m hpow hphi x ≤ 0} ∩
        sourceBasepoint (D := D) (Fam := Fam) G m hpow) := ⟨x.2, hx⟩
    rw [hdisj] at h
    exact h
  let P : M → Work.PTGeometric.EndOp (k + G.mU) := fun x =>
    (G.coord ⟨Hf x.1.1, hne' x⟩).1
  let v : M → Work.PTGeometric.Amb (k + G.mU) := fun x =>
    (G.coord ⟨Hf x.1.1, hne' x⟩).2
  have hbase : Continuous fun x : M => Hf x.1.1 :=
    (Work.PTGeometric.continuous_flatSourceHomotopy8 k
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hcont : Continuous fun x : M => (⟨Hf x.1.1, hne' x⟩ : {y : D.T // y ≠ D.t₀}) :=
    hbase.subtype_mk (fun x => hne' x)
  have hPc : Continuous P := (G.continuous_coord.comp hcont).fst
  have hvc : Continuous v := (G.continuous_coord.comp hcont).snd
  -- ### Step 5: the collar, the sub-collar, the collapse end
  let V : Set M := {x | x.1.1 0 < 1 / 2}
  let S0 : Set M := {x | x.1.1 0 ≤ 1 / 4}
  let Send : Set M := {x | x.1.1 0 = 0}
  have hcoord0 : Continuous fun x : M => x.1.1 0 :=
    ((continuous_apply (0 : Fin ((8 + k) + 1))).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin ((8 + k) + 1) => ℝ)).continuous).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hVopen : IsOpen V := isOpen_lt hcoord0 continuous_const
  have hS0cl : IsClosed S0 := isClosed_le hcoord0 continuous_const
  have hS0V : S0 ⊆ V := by intro x hx; dsimp [V, S0] at *; linarith
  have hScl : IsClosed Send := isClosed_eq hcoord0 continuous_const
  have hS0_cont : Continuous fun x : M => x.1.1 :=
    continuous_subtype_val.comp continuous_subtype_val
  -- the boundary of the half-space model, in coordinates
  have hbnd : ∀ y : EuclideanHalfSpace ((8 + k) + 1),
      y ∈ (𝓡∂ (8 + k + 1)).boundary (EuclideanHalfSpace ((8 + k) + 1)) ↔ y.1 0 = 0 :=
    fun y => mem_boundary_halfSpace_iff ((8 + k) + 1)
  have hSsub : Send ⊆ (𝓡∂ (8 + k + 1)).boundary M := by
    intro x hx
    rw [S.mem_boundary_iff]
    exact Or.inl ((hbnd x.1).mpr hx)
  have hSS0 : Send ⊆ S0 := by
    intro x hx; dsimp [Send, S0] at *; linarith
  -- ### Step 5bis: every boundary zero of `v` lies on the collapse end
  have hzero_sub : ∀ x ∈ (𝓡∂ (8 + k + 1)).boundary M, v x = 0 → x ∈ Send := by
    intro x hx hx0
    have hxZ : Hf x.1.1 ∈ G.core := (G.core_iff_vec ⟨Hf x.1.1, hne' x⟩).mpr hx0
    rw [S.mem_boundary_iff] at hx
    rcases hx with hA | hΦ
    · exact (hbnd x.1).mp hA
    · exact hzero ⟨hxZ, hΦ⟩
  -- ### Step 5ter: the smoothness of the ambient field on the collar
  have hsmval : ContMDiff (𝓡∂ (8 + k + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin ((8 + k) + 1)))) ∞
      (fun x : M => x.1.1) := by
    have h1 : ContMDiff (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞
        (fun m : S.Region => m.1) := S.contMDiff_val
    have h2 : ContMDiff (𝓡∂ (8 + k + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin ((8 + k) + 1)))) ∞
        ((𝓡∂ (8 + k + 1)) : EuclideanHalfSpace (8 + k + 1) →
          EuclideanSpace ℝ (Fin (8 + k + 1))) := ModelWithCorners.contMDiff (𝓡∂ (8 + k + 1))
    exact h2.comp h1
  have hcoord_sm := contMDiffOn_coord_flatSource_collar (D := D) (Fam := Fam) (M := M) G m hpow
    (e := fun x : M => x.1.1) hsmval (fun x => hne' x)
  have hPsmV : ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓘(ℝ, Work.PTGeometric.EndOp (k + G.mU))) ∞ P V :=
    ((ContinuousLinearMap.fst ℝ (Work.PTGeometric.EndOp (k + G.mU))
        (Work.PTGeometric.Amb (k + G.mU))).contMDiff.comp_contMDiffOn hcoord_sm)
  have hvsmV : ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓘(ℝ, Work.PTGeometric.Amb (k + G.mU))) ∞ v V :=
    ((ContinuousLinearMap.snd ℝ (Work.PTGeometric.EndOp (k + G.mU))
        (Work.PTGeometric.Amb (k + G.mU))).contMDiff.comp_contMDiffOn hcoord_sm)
  -- ### Step 5quater: the uniform lower bound
  have hbnd_closed : IsClosed {x : M | x ∈ (𝓡∂ (8 + k + 1)).boundary M} := by
    have hΦc : Continuous fun x : M => sourcePhi G m hpow hphi x.1 :=
      hΦ.continuous.comp continuous_subtype_val
    have hset : {x : M | x ∈ (𝓡∂ (8 + k + 1)).boundary M} =
        {x : M | x.1.1 0 = 0} ∪ {x : M | sourcePhi G m hpow hphi x.1 = 0} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_union]
      rw [S.mem_boundary_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl ((hbnd x.1).mp h)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl ((hbnd x.1).mpr h)
        · exact Or.inr h
    rw [hset]
    exact (isClosed_eq hcoord0 continuous_const).union (isClosed_eq hΦc continuous_const)
  have hKδ : IsCompact {x : M | x ∈ (𝓡∂ (8 + k + 1)).boundary M ∧ (1 : ℝ) / 4 ≤ x.1.1 0} :=
    (hbnd_closed.inter (isClosed_le continuous_const hcoord0)).isCompact
  have hv_ne : ∀ x ∈ {x : M | x ∈ (𝓡∂ (8 + k + 1)).boundary M ∧ (1 : ℝ) / 4 ≤ x.1.1 0},
      v x ≠ 0 := by
    intro x hx hvx
    have hS : x ∈ Send := hzero_sub x hx.1 hvx
    dsimp [Send] at hS
    linarith [hx.2, hS]
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ {x : M | x ∈ (𝓡∂ (8 + k + 1)).boundary M ∧ (1 : ℝ) / 4 ≤ x.1.1 0},
        δ ≤ ‖v x‖ := by
    by_cases hneK : ({x : M | x ∈ (𝓡∂ (8 + k + 1)).boundary M
        ∧ (1 : ℝ) / 4 ≤ x.1.1 0} : Set M).Nonempty
    · obtain ⟨x₀, hx₀, hmin⟩ := hKδ.exists_isMinOn hneK hvc.continuousOn.norm
      exact ⟨‖v x₀‖, norm_pos_iff.mpr (hv_ne x₀ hx₀), fun x hx => hmin hx⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hneK⟩
  -- ### Step 6: the *pinned* pointwise local datum at every boundary zero
  have hpoint : ∀ x ∈ ((𝓡∂ (8 + k + 1)).boundary M ∩ {x : M | v x = 0}),
      ∃ (a : { ℓ : Work.PTGeometric.Amb (k + G.mU) →L[ℝ] Work.PTGeometric.Amb k //
          ∃ (i : ι) (w0 : (Fam i).pt)
            (ND : Work.ThomBordism.PontryaginThom.NormalData (Fam i) k (G.emb i).e)
            (j : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
            (hb : w0 ∈ ND.D.baseSet j),
            ℓ = (Work.Tubular.readCLM (G.emb i) ND j w0).comp
              (Work.PTGeometric.projEuc k G.mU G.hmU) })
        (U : Set M),
        IsOpen U ∧ x ∈ U ∧ closure U ⊆ interior S0 ∧
        (∀ y ∈ closure U, ∀ z : Work.PTGeometric.Amb (k + G.mU), P y z = z → a.1 z = 0 →
          z = 0) ∧
        (∀ y ∈ U, ∀ (hy : y ∈ (𝓡∂ (8 + k + 1)).boundary M), v y = 0 →
          Manifold.IsSubmersionAt (𝓡∂ (8 + k + 1)) (𝓡 k) ∞ (fun y : M => a.1 (v y)) y ∧
          Manifold.IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
            (fun y : ↥((𝓡∂ (8 + k + 1)).boundary M) => a.1 (v y)) ⟨y, hy⟩) := by
    intro x hxK
    obtain ⟨i, w0, ND, j, hb, U, h1, h2, h3, h4, h5⟩ :=
      exists_localData_at_boundaryZero_pinned (D := D) (Fam := Fam) G m hpow hphi hweak hne'
        x hxK.1 hxK.2
    exact ⟨⟨(Work.Tubular.readCLM (G.emb i) ND j w0).comp
        (Work.PTGeometric.projEuc k G.mU G.hmU), ⟨i, w0, ND, j, hb, rfl⟩⟩,
      U, h1, h2, h3, h4, h5⟩
  -- ### Step 7: the finite cover of the boundary zeros, indexed by the pin data
  obtain ⟨mE, ℓU, UE, hUEopen, hUEcl, hUEinj, hUEtrans, hUEcov⟩ :=
    exists_finite_cover_of_pointwise
      (K := ((𝓡∂ (8 + k + 1)).boundary M ∩ {x : M | v x = 0}))
      (T := interior S0)
      (hbnd_closed.inter (isClosed_eq hvc continuous_const)).isCompact
      (fun (a : { ℓ : Work.PTGeometric.Amb (k + G.mU) →L[ℝ] Work.PTGeometric.Amb k //
          ∃ (i : ι) (w0 : (Fam i).pt)
            (ND : Work.ThomBordism.PontryaginThom.NormalData (Fam i) k (G.emb i).e)
            (j : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
            (hb : w0 ∈ ND.D.baseSet j),
            ℓ = (Work.Tubular.readCLM (G.emb i) ND j w0).comp
              (Work.PTGeometric.projEuc k G.mU G.hmU) }) (U : Set M) =>
        ∀ y ∈ U, ∀ (hy : y ∈ (𝓡∂ (8 + k + 1)).boundary M), v y = 0 →
          Manifold.IsSubmersionAt (𝓡∂ (8 + k + 1)) (𝓡 k) ∞ (fun y : M => a.1 (v y)) y ∧
          Manifold.IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
            (fun y : ↥((𝓡∂ (8 + k + 1)).boundary M) => a.1 (v y)) ⟨y, hy⟩)
      (fun (a : { ℓ : Work.PTGeometric.Amb (k + G.mU) →L[ℝ] Work.PTGeometric.Amb k //
          ∃ (i : ι) (w0 : (Fam i).pt)
            (ND : Work.ThomBordism.PontryaginThom.NormalData (Fam i) k (G.emb i).e)
            (j : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
            (hb : w0 ∈ ND.D.baseSet j),
            ℓ = (Work.Tubular.readCLM (G.emb i) ND j w0).comp
              (Work.PTGeometric.projEuc k G.mU G.hmU) }) (S' : Set M) =>
        ∀ y ∈ S', ∀ z : Work.PTGeometric.Amb (k + G.mU), P y z = z → a.1 z = 0 → z = 0)
      (by
        intro x hxK
        exact hpoint x hxK)
      (by
        intro a U U' hU hUU' y hy hyb hvy
        exact hU y (hUU' hy) hyb hvy)
  have hUEint : ∀ j, UE j ⊆ interior S0 := fun j => subset_trans subset_closure (hUEcl j)
  have hHend : ↥(Send ∩ {x : M | v x = 0}) ≃ₜ (Σ i : Fin m × ι, (Fam i.2).pt) := by
      have hzv : ∀ x : M, v x = 0 ↔ Hf x.1.1 ∈ G.core :=
        fun x => (G.core_iff_vec ⟨Hf x.1.1, hne' x⟩).symm
      have hset1 : (Send ∩ {x : M | v x = 0}) =
          {x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core} := by
        ext x
        constructor
        · rintro ⟨hx1, hx2⟩
          exact ⟨hx1, (hzv x).mp hx2⟩
        · rintro ⟨hx1, hx2⟩
          exact ⟨hx1, (hzv x).mpr hx2⟩
      have hmid : Nonempty ((↥{x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core}) ≃ₜ
          (↥(sourceZeroSet G m hpow ∩
            {y : EuclideanHalfSpace ((8 + k) + 1) | y.1 0 = 0}))) := by
        have hcl : IsClosed {x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core} :=
          (isClosed_eq hcoord0 continuous_const).inter (G.isClosed_core.preimage hbase)
        haveI : CompactSpace ↥{x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core} :=
          isCompact_iff_compactSpace.mp
            (IsCompact.of_isClosed_subset isCompact_univ hcl (fun _ _ => mem_univ _))
        let fwd : ↥{x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core} →
            ↥(sourceZeroSet G m hpow ∩
              {y : EuclideanHalfSpace ((8 + k) + 1) | y.1 0 = 0}) :=
          fun x => ⟨x.1.1, x.2.2, x.2.1⟩
        have hf : Continuous fun x : ↥{x : M | x.1.1 0 = 0 ∧ Hf x.1.1 ∈ G.core} => x.1.1 :=
          continuous_subtype_val.comp continuous_subtype_val
        have hfwd : Continuous fwd := hf.subtype_mk (fun x => ⟨x.2.2, x.2.1⟩)
        have hbij : Function.Bijective fwd := by
          constructor
          · intro a b hab
            have h2 : (a.1 : S.A) = (b.1 : S.A) := by
              have h3 := congrArg (fun t : ↥(sourceZeroSet G m hpow ∩
                {y : EuclideanHalfSpace ((8 + k) + 1) | y.1 0 = 0}) =>
                  (t.1 : EuclideanHalfSpace ((8 + k) + 1))) hab
              simpa only [fwd] using h3
            exact Subtype.ext (Subtype.ext h2)
          · rintro ⟨y, hyZ, hy0⟩
            refine ⟨⟨⟨y, hZsub hyZ⟩, hy0, hyZ⟩, ?_⟩
            rfl
        exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective fwd hbij) hfwd⟩
      exact Homeomorph.trans (Homeomorph.trans (Homeomorph.setCongr hset1)
        (Classical.choice hmid)) (Classical.choice (sourceZeroSet_boundary_homeo G m hpow))

  -- ### Step 8: the assembly
  refine ⟨{
    M := M
    P := P
    v := v
    hPc := hPc
    hvc := hvc
    hProj := by
      intro x
      exact G.coord_isProj ⟨Hf x.1.1, hne' x⟩
    hMem := by
      intro x
      exact G.coord_mem ⟨Hf x.1.1, hne' x⟩
    V := V
    hVopen := hVopen
    S0 := S0
    hS0cl := hS0cl
    hS0V := hS0V
    hPsmV := hPsmV
    hvsmV := hvsmV
    S := Send
    hScl := hScl
    hSsub := hSsub
    hSS0 := hSS0
    hend := hHend
    hzero_sub := hzero_sub
    δ := δ₀
    hδpos := hδ₀pos
    hδ := by
      intro x hx hxS0
      exact hδ₀ x ⟨hx, le_of_lt (not_le.mp hxS0)⟩
    mE := mE
    ellE := fun j => (ℓU j).1
    UE := UE
    isOpen_UE := hUEopen
    UE_int := hUEint
    ellE_inj := fun j y hy z hz hz0 => hUEinj j y (subset_closure hy) z hz hz0
    ellE_inj_cl := hUEinj
    bndZero_cov := fun x hx hvx => hUEcov x ⟨hx, hvx⟩
    bndZero_trans := fun j x hx hxb hvx => hUEtrans j x hx hxb hvx }, ?_⟩
  intro j
  exact (ℓU j).2

end

end Work.PTGeometric

namespace Work.ThomBordism

theorem sourceRawAmbientData_pinned
    {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt)
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
    (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (hwk : Work.PTGeometric.RegionManifoldTheoremOfIsCompactWeak k)
    (hphi : Work.PTGeometric.SourceRegionPhiInteriorSign k
      (Work.PTGeometric.sourceZeroSet G m hpow)
      {x : EuclideanHalfSpace ((8 + k) + 1) |
        Work.PTGeometric.flatSourceHomotopy8 (k := k)
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ x.1 = D.t₀}) :
    ∃ D0 : Work.PTGeometric.RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2),
      ∀ j : Fin D0.mE, ∃ (i : ι) (w0 : (Fam i).pt)
        (ND : Work.ThomBordism.PontryaginThom.NormalData (Fam i) k (G.emb i).e)
        (j' : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
        (hb : w0 ∈ ND.D.baseSet j'),
        D0.ellE j =
          (Work.Tubular.readCLM (G.emb i) ND j' w0).comp (Work.PTGeometric.projEuc k G.mU G.hmU) :=
  Work.PTGeometric.sourceRawAmbientData_pinned_aux hk hne G m hm hpow hwk hphi

end Work.ThomBordism
