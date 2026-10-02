import Mathlib
import Submission.Work.LerayHirsch.Punctum
import Submission.Work.LerayHirsch.TautLine
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_trivial
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype
import Submission.Work.LerayHirsch.nonempty_homeo_projFibre
import Submission.Work.LerayHirsch.ProjIsoOfBundleIso
import Submission.Work.LerayHirsch.t2Space_projSpace
import Submission.Work.Projective.Atlas
import Submission.Work.Projective.t2Space_CP

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# The projectivisation of a complex gluing-data bundle over a paracompact base is paracompact

`Work.LerayHirsch.ProjSpace Z = (E∖0)/ℂˣ` is the projectivisation of a complex bundle `Z` in the
gluing-data model over a base `B`.  This module proves

`Work.LerayHirsch.paracompactSpace_projSpace : ParacompactSpace (ProjSpace Z)`

whenever `B` is paracompact Hausdorff and the chart cover of `Z` is indexed by a finite type `ι`.

## The route

`ProjSpace Z` carries a continuous surjection `projMap Z` to `B` whose fibres are the compact spaces
`ProjFibre Z b ≃ₜ ℙ ℂ (ℂ^m)` (`Work.LerayHirsch.nonempty_homeo_projFibre`,
`compactSpace_modelProjectivization`), and it satisfies the **tube property**
`exists_nhds_projMap_subset`: an open set containing the fibre `π ⁻¹' {b}` contains a whole tube
`π ⁻¹' W` over a neighbourhood `W` of `b`.  The general topological lemma
`paracompactSpace_of_compact_fibres` then produces a locally finite open refinement of any open
cover: finitely many members cover each compact fibre, the tube property fattens them to a
neighbourhood of the base point, and the base cover is refined using the paracompactness of `B`.

The tube property is proved with the punctured total space: over the chart `i` of `b` the open
partial homeomorphism `(realification Z).localTriv i` (whose inverse is continuous, being a
`Bundle.Trivialization`) identifies a neighbourhood of the fibre with a product, and the finiteness
comes from the compactness of `ℙ ℂ (ℂ^m)` applied to `ℂˣ`-saturated open sets of the model fibre.

Note that no `T2Space` hypothesis on `B` is used for the paracompactness statement itself.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## The model fibre is compact -/

/-- **The projectivisation `ℙ ℂ (ℂ^m)` of the model fibre is compact.**  It is the quotient of the
unit sphere of `ℂ^m` by the action of the units of `ℂ`, and the sphere is compact. -/
theorem compactSpace_modelProjectivization (m : ℕ) :
    CompactSpace (Projectivization ℂ (EuclideanSpace ℂ (Fin m))) := by
  letI : CompactSpace ↥(Metric.sphere (0 : EuclideanSpace ℂ (Fin m)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  have hne : ∀ v : ↥(Metric.sphere (0 : EuclideanSpace ℂ (Fin m)) 1),
      (v : EuclideanSpace ℂ (Fin m)) ≠ 0 := by
    intro v hv
    have h1 : dist (v : EuclideanSpace ℂ (Fin m)) 0 = 1 := by
      rw [← Metric.mem_sphere]; exact v.2
    rw [hv, dist_self] at h1
    norm_num at h1
  have hcont : Continuous (fun v : ↥(Metric.sphere (0 : EuclideanSpace ℂ (Fin m)) 1) =>
      mkP m ⟨(v : EuclideanSpace ℂ (Fin m)), hne v⟩) :=
    (continuous_mkP m).comp (Continuous.subtype_mk continuous_subtype_val _)
  have hsurj : Function.Surjective (fun v : ↥(Metric.sphere (0 : EuclideanSpace ℂ (Fin m)) 1) =>
      mkP m ⟨(v : EuclideanSpace ℂ (Fin m)), hne v⟩) := by
    intro q
    obtain ⟨v, hv⟩ := surjective_mkP m q
    have hnorm : (v : EuclideanSpace ℂ (Fin m)) ≠ 0 := v.2
    have hne' : ‖(v : EuclideanSpace ℂ (Fin m))‖ ≠ 0 := norm_ne_zero_iff.mpr hnorm
    set x : EuclideanSpace ℂ (Fin m) := ((‖(v : EuclideanSpace ℂ (Fin m))‖ : ℂ))⁻¹ •
      (v : EuclideanSpace ℂ (Fin m)) with hx
    have hxnorm : ‖x‖ = 1 := by
      rw [hx, norm_smul, norm_inv]
      simp [hne']
    have hxmem : x ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin m)) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hxnorm
    refine ⟨⟨x, hxmem⟩, ?_⟩
    rw [← hv]
    exact (mkP_eq_iff (m := m)).mpr ⟨((‖(v : EuclideanSpace ℂ (Fin m))‖ : ℂ))⁻¹, hx⟩
  rw [← isCompact_univ_iff]
  have h := isCompact_univ.image hcont
  rwa [Set.image_univ, Set.range_eq_univ.mpr hsurj] at h

/-! ## A space with compact fibres and the tube property over a paracompact base is paracompact -/

/-- **A space fibre-bundled over a paracompact base with compact fibres and the tube property is
paracompact.**  See the module docstring. -/
theorem paracompactSpace_of_compact_fibres {X : Type} {B : Type} [TopologicalSpace X]
    [TopologicalSpace B] (π : C(X, B)) [ParacompactSpace B]
    (hcomp : ∀ b : B, CompactSpace {x : X // π x = b})
    (htube : ∀ (b : B) (O : Set X), IsOpen O → π ⁻¹' {b} ⊆ O →
      ∃ W ∈ nhds b, π ⁻¹' W ⊆ O) :
    ParacompactSpace X := by
  classical
  refine ⟨fun α s hs hcov => ?_⟩
  -- finitely many members of the cover already cover each fibre
  have hfin : ∀ b : B, ∃ t : Finset α, π ⁻¹' {b} ⊆ ⋃ a ∈ t, s a := by
    intro b
    haveI := hcomp b
    have hcov' : (Set.univ : Set {x : X // π x = b}) ⊆ ⋃ a, Subtype.val ⁻¹' (s a) := by
      intro y _
      have hy : (y : X) ∈ ⋃ a, s a := by rw [hcov]; exact Set.mem_univ _
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨a, ha⟩
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun a => Subtype.val ⁻¹' (s a))
      (fun a => (hs a).preimage continuous_subtype_val) hcov'
    refine ⟨t, fun x hx => ?_⟩
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ ⟨x, hx⟩))
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩
  choose t ht using hfin
  -- the tube around each fibre
  have htube' : ∀ b : B, ∃ W : Set B, W ∈ nhds b ∧ π ⁻¹' W ⊆ ⋃ a ∈ t b, s a := fun b =>
    htube b _ (isOpen_biUnion fun a _ => hs a) (ht b)
  choose W hW hWsub using htube'
  -- open neighbourhoods inside the tubes
  have hV : ∀ b : B, ∃ V : Set B, IsOpen V ∧ b ∈ V ∧ V ⊆ W b := by
    intro b
    obtain ⟨V, ⟨hbV, hVopen⟩, hVW⟩ := (nhds_basis_opens b).mem_iff.mp (hW b)
    exact ⟨V, hVopen, hbV, hVW⟩
  choose v hvopen hbv hvW using hV
  -- the locally finite refinement of the base cover
  obtain ⟨w, hwopen, hwcov, hwfin, hwsub⟩ := precise_refinement v hvopen
    (by rw [Set.eq_univ_iff_forall]; exact fun b => Set.mem_iUnion.mpr ⟨b, hbv b⟩)
  let f : B × α → Set X := fun γ => if γ.2 ∈ t γ.1 then π ⁻¹' (w γ.1) ∩ s γ.2 else ∅
  have hf : ∀ (b : B) (a : α), f (b, a) = if a ∈ t b then π ⁻¹' (w b) ∩ s a else ∅ :=
    fun b a => rfl
  refine ⟨B × α, f, ?_, ?_, ?_, ?_⟩
  · rintro ⟨b, a⟩
    rw [hf b a]
    by_cases h : a ∈ t b
    · rw [if_pos h]; exact ((hwopen b).preimage π.continuous).inter (hs a)
    · rw [if_neg h]; exact isOpen_empty
  · rw [Set.eq_univ_iff_forall]
    intro x
    have hxw : π x ∈ ⋃ b, w b := by rw [hwcov]; exact Set.mem_univ _
    obtain ⟨b, hbw⟩ := Set.mem_iUnion.mp hxw
    have hxO : x ∈ ⋃ a ∈ t b, s a :=
      hWsub b (by rw [Set.mem_preimage]; exact hvW b (hwsub b hbw))
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hxO
    refine Set.mem_iUnion.mpr ⟨(b, a), ?_⟩
    rw [hf b a, if_pos ha]
    exact ⟨by rw [Set.mem_preimage]; exact hbw, hxa⟩
  · -- local finiteness
    intro x
    have hxw : π x ∈ ⋃ b, w b := by rw [hwcov]; exact Set.mem_univ _
    obtain ⟨M, hM, hMfin⟩ := hwfin (π x)
    refine ⟨π ⁻¹' M, π.continuous.continuousAt.preimage_mem_nhds hM, ?_⟩
    refine (Set.Finite.prod hMfin (Set.Finite.biUnion hMfin fun b _ => (t b).finite_toSet)).subset ?_
    rintro ⟨b, a⟩ ⟨y, hyf, hyM⟩
    rw [hf b a] at hyf
    have ha : a ∈ t b := by
      by_contra h
      rw [if_neg h] at hyf
      exact hyf
    rw [if_pos ha] at hyf
    have hbS : b ∈ {b : B | (w b ∩ M).Nonempty} :=
      ⟨π y, by simpa using hyf.1, by simpa using hyM⟩
    exact ⟨hbS, Set.mem_iUnion₂.mpr ⟨b, hbS, ha⟩⟩
  · rintro ⟨b, a⟩
    refine ⟨a, ?_⟩
    rw [hf b a]
    by_cases h : a ∈ t b
    · rw [if_pos h]; exact Set.inter_subset_right
    · rw [if_neg h]; exact Set.empty_subset _


/-! ## The tube property of `projMap` -/

/-- **The tube property of the projectivisation.**  Every open set of `ProjSpace Z` containing the
fibre `projMap Z ⁻¹' {b}` over a point `b` of the base contains a whole tube `projMap Z ⁻¹' W` for
some neighbourhood `W` of `b`.

The proof reads the situation in the chart `i` of `b`: the local trivialisation
`(realification Z).localTriv i` is an open partial homeomorphism with continuous inverse, so the
punctured total space over the chart looks like `(baseSet i) × (ℂ^m ∖ 0)` and the fibre over `b`
like `{b} × (ℂ^m ∖ 0)`.  An open set containing the fibre therefore contains a product `N × L` with
`N ∋ b` and `L ∋ v`, and saturation under the `ℂˣ`-action spreads `L` to a saturated neighbourhood
of the fibre; the finitely many needed `v` come from the compactness of `ℙ ℂ (ℂ^m)`. -/
theorem exists_nhds_projMap_subset (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [CompactSpace (Projectivization ℂ (EuclideanSpace ℂ (Fin m)))]
    {b : B} {O : Set (ProjSpace Z)} (hO : IsOpen O) (hb : projMap Z ⁻¹' {b} ⊆ O) :
    ∃ W ∈ 𝓝 b, projMap Z ⁻¹' W ⊆ O := by
  classical
  set i : ι := (realification Z).indexAt b with hi
  have hbU : b ∈ Z.baseSet i := by
    rw [hi, realification_indexAt]; exact Z.mem_baseSet_at b
  have hUopen : IsOpen (Z.baseSet i) := Z.isOpen_baseSet i
  set Ω : Set (Punct Z) := mkProj Z ⁻¹' O with hΩ
  have hΩopen : IsOpen Ω := hO.preimage (continuous_mkProj Z)
  have hmk_smul : ∀ (c : ℂˣ) (y : Punct Z), mkProj Z (smulPunct Z c y) = mkProj Z y :=
    fun c y => (mkProj_eq_iff Z).mpr ⟨c, rfl⟩
  have hΩsat : ∀ (c : ℂˣ) (y : Punct Z), smulPunct Z c y ∈ Ω ↔ y ∈ Ω := by
    intro c y
    rw [hΩ, Set.mem_preimage, Set.mem_preimage, hmk_smul c y]
  -- the chart trivialisation at the preferred chart of `b`
  set T := (realification Z).localTriv i with hT
  have hT_val : ∀ p : (realification Z).TotalSpace,
      T p = (p.1, ((realification Z).coordChange ((realification Z).indexAt p.1) i p.1) p.2) := by
    intro p
    rw [hT]
    exact VectorBundleCore.localTriv_apply (Z := realification Z) (i := i) p
  have hT_coord : ∀ y : Punct Z, (T y.1).2 = chartCoord Z i y := by
    intro y
    rw [hT]
    exact (chartCoord_eq_realification Z i y).symm
  have hbaseT_of : ∀ {x : B}, x ∈ Z.baseSet i → x ∈ T.baseSet := by
    intro x hx
    rw [hT, ← VectorBundleCore.baseSet_at, realification_baseSet]
    exact hx
  -- the key neighbourhood statement, over each nonzero vector of the model fibre
  have key : ∀ v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0},
      ∃ N : Set B, N ∈ 𝓝 b ∧ ∃ L : Set (EuclideanSpace ℂ (Fin m)),
        L ∈ 𝓝 (v : EuclideanSpace ℂ (Fin m)) ∧
        (∀ w ∈ N, ∀ u ∈ L, ∃ y : Punct Z, y ∈ Ω ∧ y.1.proj = w ∧ chartCoord Z i y = u) := by
    intro v
    -- a point of the punctured total space over `b` whose chart coordinate is `v`
    have hyv : ∃ y : Punct Z, y.1.proj = b ∧
        chartCoord Z i y = (v : EuclideanSpace ℂ (Fin m)) := by
      refine ⟨⟨⟨b, (v : EuclideanSpace ℂ (Fin m))⟩, ?_⟩, rfl, ?_⟩
      · exact v.2
      · rw [hi]; exact chartCoord_indexAt_eq_snd Z b _ rfl
    obtain ⟨yv, hyvb, hyvc⟩ := hyv
    have hyvU : yv.1.proj ∈ Z.baseSet i := by rw [hyvb]; exact hbU
    have hyvΩ : yv ∈ Ω := by
      rw [hΩ, Set.mem_preimage]
      exact hb (by simp [projMap_mkProj, hyvb])
    obtain ⟨Ω', hΩ'open, hΩ'eq⟩ := isOpen_induced_iff.mp hΩopen
    have hyvΩ' : yv.1 ∈ Ω' := by
      have h : yv ∈ Subtype.val ⁻¹' Ω' := by rwa [hΩ'eq]
      exact h
    have hbaseT : yv.1.proj ∈ T.baseSet := hbaseT_of hyvU
    have hmemT_src : yv.1 ∈ T.source := T.mem_source.mpr hbaseT
    have hTpair : T yv.1 = (b, (v : EuclideanSpace ℂ (Fin m))) := by
      refine Prod.ext ?_ ?_
      · rw [T.coe_fst hmemT_src, hyvb]
      · rw [hT_coord yv, hyvc]
    have hsymm : T.toOpenPartialHomeomorph.symm (b, (v : EuclideanSpace ℂ (Fin m))) = yv.1 := by
      rw [← hTpair]
      exact T.left_inv hmemT_src
    have hbT : b ∈ T.baseSet := hbaseT_of hbU
    have htarget : (b, (v : EuclideanSpace ℂ (Fin m))) ∈ T.target := T.mem_target.mpr hbT
    have hS : T.toOpenPartialHomeomorph.symm ⁻¹' Ω'
        ∈ 𝓝 (b, (v : EuclideanSpace ℂ (Fin m))) := by
      have hcont : ContinuousAt T.toOpenPartialHomeomorph.symm
          (b, (v : EuclideanSpace ℂ (Fin m))) :=
        T.continuousOn_invFun.continuousAt (T.open_target.mem_nhds htarget)
      refine hcont.preimage_mem_nhds ?_
      rw [hsymm]
      exact hΩ'open.mem_nhds hyvΩ'
    rw [nhds_prod_eq] at hS
    obtain ⟨N, hN, L, hL, hNL⟩ := Filter.mem_prod_iff.mp hS
    refine ⟨N ∩ Z.baseSet i, Filter.inter_mem hN (hUopen.mem_nhds hbU),
      L ∩ {u : EuclideanSpace ℂ (Fin m) | u ≠ 0},
      Filter.inter_mem hL ((isOpen_ne (x := (0 : EuclideanSpace ℂ (Fin m)))).mem_nhds v.2), ?_⟩
    intro w hw u hu
    obtain ⟨hwN, hwU⟩ := hw
    obtain ⟨huL, hu0⟩ := hu
    set p := T.toOpenPartialHomeomorph.symm (w, u) with hp
    have hpΩ' : p ∈ Ω' := hNL ⟨hwN, huL⟩
    have hwtgt : (w, u) ∈ T.target := T.mem_target.mpr (hbaseT_of hwU)
    have hpT : T p = (w, u) := T.apply_symm_apply hwtgt
    have hpz : p.2 ≠ 0 := by
      intro h0
      have h2 : (T p).2 = 0 := by
        rw [hT_val]
        dsimp only
        rw [h0, map_zero]
      rw [hpT] at h2
      exact hu0 (by simpa using h2)
    refine ⟨⟨p, hpz⟩, ?_, ?_, ?_⟩
    · rw [← hΩ'eq]; exact hpΩ'
    · have hsrc2 : p ∈ T.source := T.map_target hwtgt
      have h1 : (T p).1 = p.proj := T.coe_fst hsrc2
      rw [hpT] at h1
      exact h1.symm
    · rw [chartCoord_eq_realification]
      have h2 : (T p).2 = u := by rw [hpT]
      exact h2
  choose N hN L hL hNL using key
  -- open versions of `L`, and their `ℂˣ`-saturations
  have hLopen' : ∀ v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0},
      ∃ L' : Set (EuclideanSpace ℂ (Fin m)),
        IsOpen L' ∧ (v : EuclideanSpace ℂ (Fin m)) ∈ L' ∧ L' ⊆ L v := by
    intro v
    obtain ⟨L', ⟨hvL', hL'open⟩, hL'sub⟩ :=
      (nhds_basis_opens (v : EuclideanSpace ℂ (Fin m))).mem_iff.mp (hL v)
    exact ⟨L', hL'open, hvL', hL'sub⟩
  choose L' hL'open hvL' hL'sub using hLopen'
  set Lsat : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} → Set (EuclideanSpace ℂ (Fin m)) :=
    fun v => ⋃ c : ℂˣ, (fun u : EuclideanSpace ℂ (Fin m) => (c : ℂ) • u) '' (L' v) with hLsat
  have hLsat_open : ∀ v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}, IsOpen (Lsat v) := by
    intro v
    rw [hLsat]
    exact isOpen_iUnion fun c => isOpenMap_smul₀ (Units.ne_zero c) (L' v) (hL'open v)
  have hsat : ∀ (v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}) (c : ℂˣ)
      (a : EuclideanSpace ℂ (Fin m)), (c : ℂ) • a ∈ Lsat v ↔ a ∈ Lsat v := by
    intro v c a
    constructor
    · intro h
      rw [hLsat, Set.mem_iUnion] at h
      obtain ⟨d, h⟩ := h
      rw [Set.mem_image] at h
      obtain ⟨u₀, hu₀, hu₀eq⟩ := h
      rw [hLsat, Set.mem_iUnion]
      refine ⟨c⁻¹ * d, ?_⟩
      rw [Set.mem_image]
      refine ⟨u₀, hu₀, ?_⟩
      have h1 : ((c⁻¹ * d : ℂˣ) : ℂ) • u₀ = ((c : ℂ))⁻¹ • (((d : ℂ)) • u₀) := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, ← smul_smul]
      rw [h1, hu₀eq, smul_smul, inv_mul_cancel₀ (Units.ne_zero c), one_smul]
    · intro h
      rw [hLsat, Set.mem_iUnion] at h
      obtain ⟨d, h⟩ := h
      rw [Set.mem_image] at h
      obtain ⟨u₀, hu₀, hu₀eq⟩ := h
      rw [hLsat, Set.mem_iUnion]
      refine ⟨c * d, ?_⟩
      rw [Set.mem_image]
      refine ⟨u₀, hu₀, ?_⟩
      have h1 : ((c * d : ℂˣ) : ℂ) • u₀ = ((c : ℂ)) • (((d : ℂ)) • u₀) := by
        rw [Units.val_mul, smul_smul]
      rw [h1, hu₀eq]
  have hLsat_self : ∀ v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0},
      (v : EuclideanSpace ℂ (Fin m)) ∈ Lsat v := by
    intro v
    rw [hLsat]
    refine Set.mem_iUnion.mpr ⟨1, ?_⟩
    rw [Set.mem_image]
    exact ⟨v, hvL' v, by simp⟩
  -- the key statement, saturated
  have hNLsat : ∀ v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}, ∀ w ∈ N v, ∀ u ∈ Lsat v,
      ∃ y : Punct Z, y ∈ Ω ∧ y.1.proj = w ∧ chartCoord Z i y = u := by
    intro v w hw u hu
    rw [hLsat, Set.mem_iUnion] at hu
    obtain ⟨c, hu⟩ := hu
    rw [Set.mem_image] at hu
    obtain ⟨u₀, hu₀, hu₀eq⟩ := hu
    obtain ⟨y₀, hy₀Ω, hy₀proj, hy₀coord⟩ := hNL v w hw u₀ (hL'sub v hu₀)
    refine ⟨smulPunct Z c y₀, (hΩsat c y₀).mpr hy₀Ω, ?_, ?_⟩
    · rw [smulPunct_proj]; exact hy₀proj
    · rw [chartCoord_smulPunct, hy₀coord, hu₀eq]
  -- the saturated sets as subsets of the punctured model fibre
  set LsatM : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} →
      Set {u : EuclideanSpace ℂ (Fin m) // u ≠ 0} := fun v => Subtype.val ⁻¹' (Lsat v)
    with hLsatM
  have hLsatM_open : ∀ v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}, IsOpen (LsatM v) := by
    intro v
    rw [hLsatM]
    exact isOpen_induced_iff.mpr ⟨Lsat v, hLsat_open v, rfl⟩
  have hLsatM_self : ∀ v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}, v ∈ LsatM v := by
    intro v
    rw [hLsatM]
    exact hLsat_self v
  have himg_open : ∀ v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0},
      IsOpen (mkP m '' LsatM v) := by
    intro v
    have hq : Topology.IsQuotientMap (mkP m) :=
      (isOpenMap_mkP m).isQuotientMap (continuous_mkP m) (surjective_mkP m)
    have hpre : (mkP m) ⁻¹' (mkP m '' LsatM v) = LsatM v := by
      ext u
      constructor
      · rintro ⟨u', hu', heq⟩
        obtain ⟨c, hc⟩ := (mkP_eq_iff (m := m)).mp heq
        have hc0 : c ≠ 0 := by
          intro hc_eq
          refine u'.2 ?_
          calc (u' : EuclideanSpace ℂ (Fin m)) = c • (u : EuclideanSpace ℂ (Fin m)) := hc.symm
            _ = 0 := by rw [hc_eq, zero_smul]
        have hu'v : (u' : EuclideanSpace ℂ (Fin m)) ∈ Lsat v := hu'
        have hmain : (u : EuclideanSpace ℂ (Fin m)) ∈ Lsat v := by
          have h1 : (↑(Units.mk0 c hc0) : ℂ) • (u : EuclideanSpace ℂ (Fin m)) ∈ Lsat v := by
            rw [Units.val_mk0, hc]
            exact hu'v
          exact (hsat v (Units.mk0 c hc0) (u : EuclideanSpace ℂ (Fin m))).mp h1
        rw [hLsatM]
        exact hmain
      · intro hu
        exact ⟨u, hu, rfl⟩
    rw [← hq.isCoinducing.isOpen_preimage (s := mkP m '' LsatM v), hpre]
    exact hLsatM_open v
  have hcov : (Set.univ : Set (Projectivization ℂ (EuclideanSpace ℂ (Fin m)))) ⊆
      ⋃ v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}, mkP m '' LsatM v := by
    intro q _
    obtain ⟨u, rfl⟩ := surjective_mkP m q
    exact Set.mem_iUnion.mpr ⟨u, Set.mem_image_of_mem _ (hLsatM_self u)⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} => mkP m '' LsatM v) himg_open hcov
  -- the tube
  refine ⟨Z.baseSet i ∩ ⋂ v ∈ T, N v, ?_, ?_⟩
  · refine Filter.inter_mem (hUopen.mem_nhds hbU) ?_
    rw [Filter.biInter_finset_mem]
    exact fun v _ => hN v
  · intro x hx
    rw [Set.mem_preimage, Set.mem_inter_iff] at hx
    obtain ⟨hxU, hxN⟩ := hx
    obtain ⟨y, hyx⟩ := surjective_mkProj Z x
    have hxy : projMap Z x = y.1.proj := by rw [← hyx, projMap_mkProj]
    have hyU : y.1.proj ∈ Z.baseSet i := by rw [← hxy]; exact hxU
    have huM : chartCoord Z i y ≠ 0 := chartCoord_ne_zero_of_mem_baseSet Z i y hyU
    -- the chart coordinate lies in one of the finitely many saturated sets
    have hmem : chartCoord Z i y ∈ ⋃ v ∈ T, Lsat v := by
      have hq : mkP m ⟨chartCoord Z i y, huM⟩ ∈ ⋃ v ∈ T, mkP m '' LsatM v :=
        hT (Set.mem_univ _)
      obtain ⟨v, hvT, u', hu', heq⟩ := Set.mem_iUnion₂.mp hq
      obtain ⟨c, hc⟩ := (mkP_eq_iff (m := m)).mp heq
      have hc0 : c ≠ 0 := by
        intro hc_eq
        refine u'.2 ?_
        calc (u' : EuclideanSpace ℂ (Fin m)) = c • (chartCoord Z i y) := hc.symm
          _ = 0 := by rw [hc_eq, zero_smul]
      have hu'v : (u' : EuclideanSpace ℂ (Fin m)) ∈ Lsat v := hu'
      have hcv : chartCoord Z i y ∈ Lsat v := by
        have h1 : (↑(Units.mk0 c hc0) : ℂ) • (chartCoord Z i y) ∈ Lsat v := by
          rw [Units.val_mk0, hc]
          exact hu'v
        exact (hsat v (Units.mk0 c hc0) (chartCoord Z i y)).mp h1
      exact Set.mem_iUnion₂.mpr ⟨v, hvT, hcv⟩
    obtain ⟨v, hvT, huv⟩ := Set.mem_iUnion₂.mp hmem
    have hwN : y.1.proj ∈ N v := by
      rw [← hxy]
      exact Set.mem_iInter₂.mp hxN v hvT
    obtain ⟨y', hy'Ω, hy'proj, hy'coord⟩ := hNLsat v y.1.proj hwN (chartCoord Z i y) huv
    have hy'U : y'.1.proj ∈ Z.baseSet i := by rw [hy'proj]; exact hyU
    have hyy' : y = y' := eq_of_chartCoord_eq Z (i := i) hyU hy'U hy'proj.symm hy'coord.symm
    have hyΩ : y ∈ Ω := by
      rw [← hyy'] at hy'Ω
      exact hy'Ω
    have hxO : x ∈ O := by
      rw [hΩ, Set.mem_preimage, hyx] at hyΩ
      exact hyΩ
    exact hxO

/-! ## The main theorem -/

/-- **The projectivisation of a complex gluing-data bundle over a paracompact Hausdorff base is
paracompact.**

This is the second of the two topological instances that make the splitting principle
`Work.LerayHirsch.splitsOverProj_of_paracompact` applicable: it supplies
`[ParacompactSpace (ProjSpace Z)]`.

The proof does not need `T2Space B`: it is the general topological lemma
`paracompactSpace_of_compact_fibres` applied to `projMap Z : ProjSpace Z → B` with the compact
fibres `ProjFibre Z b ≃ₜ ℙ ℂ (ℂ^m)` (`nonempty_homeo_projFibre`,
`compactSpace_modelProjectivization`) and the tube property `exists_nhds_projMap_subset`.  (The
`T2Space B` hypothesis is part of the interface the consumers of this lemma use, and it is what
`Work.LerayHirsch.t2Space_projSpace` needs in the other direction.) -/
theorem paracompactSpace_projSpace {m : ℕ} {B : Type} [TopologicalSpace B] [ParacompactSpace B]
    [T2Space B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    ParacompactSpace (Work.LerayHirsch.ProjSpace Z) := by
  haveI hK : CompactSpace (Projectivization ℂ (EuclideanSpace ℂ (Fin m))) :=
    compactSpace_modelProjectivization m
  refine paracompactSpace_of_compact_fibres (projMap Z) ?_ ?_
  · intro b
    obtain ⟨e⟩ := nonempty_homeo_projFibre Z b
    exact e.symm.compactSpace
  · intro b O hO hb
    exact exists_nhds_projMap_subset Z hO hb

end

end Work.LerayHirsch
