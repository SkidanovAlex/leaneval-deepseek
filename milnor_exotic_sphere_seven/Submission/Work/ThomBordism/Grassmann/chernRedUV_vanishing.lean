import Mathlib
import Submission.Work.ThomBordism.Grassmann.chernReducedSetup
import Submission.Work.ThomBordism.Grassmann.chernRedU_vanishing
import Submission.Work.ThomBordism.Grassmann.chernRedV_vanishing
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# `H³` of the intersection `chernRedU ∩ chernRedV`

The two-set cover of `chernRedX = (O(1) ⊕ O(-1)) ∖ 0` by

* `chernRedU = {first summand ≠ 0}` and
* `chernRedV = {second summand ≠ 0}`

has intersection `chernRedU ∩ chernRedV = {both summands ≠ 0}`, which is the zero complement of the
bundle `O(-1) = tautLine 2` pulled back along the projection

`π : O(1)∖0 → ℂP²`,  `π(b, v) = b`.

This module proves

  `Work.ThomBordism.Grassmann.chernRedUV_vanishing` :
    `Subsingleton (H³(chernRedU ∩ chernRedV; ℤ))`,

the last of the three vanishing statements that the Mayer–Vietoris computation of
`H⁴(chernRedX; ℤ)` needs (`chernRedU_vanishing`, `chernRedV_vanishing` being the other two).

## The route

The pullback `chernRedZ = realification (π^* tautLine 2)` of `O(-1)` to `B = O(1)∖0` is a real
rank-`2` bundle over `B`, and its zero complement is canonically

  `↥(zeroComplement chernRedZ) ≃ₜ {(b,v,w) : v ∈ O(1)_b∖0, w ∈ O(-1)_b∖0} ≃ₜ chernRedU ∩ chernRedV`

(the first homeomorphism is `Work.LerayHirsch.punctHomeo`, the second the explicit identification
`Φ : ((b,v),w) ↦ (b,(v,w))` of total spaces, a homeomorphism with inverse `Ψ`).

The base `B = O(1)∖0` is the punctured total space of `O(1)`, hence has the cohomology of `ℂ³∖0`
(`Work.Gen.puncturedTautDualTwoHZero`): `H²(B) = H³(B) = 0`.  The **Gysin sequence** of
`chernRedZ` (`Work.Thom.gysin_exact_at_sphere`) then forces `H³(Z∖0) = 0`: in

  `H¹(B) → H³(B) → H³(Z∖0) → H⁴(E,E∖0)`

the outer terms vanish (`H¹(B) = H³(B) = 0` and `H⁴(E,E∖0) ≅ H²(B) = 0` by the Thom
isomorphism), so the middle one does.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

/-! ## 1. The pullback of `O(-1)` to the punctured total space of `O(1)` -/

/-- **The base**: the punctured total space of the first summand `O(1) = tautDual 2`. -/
abbrev chernRedU0 : Set chernRedW₁.TotalSpace := Work.Thom.zeroComplement chernRedW₁

/-- The pullback of `O(-1) = tautLine 2` along the projection of the first summand: a complex line
bundle over the *whole* total space of `O(1)`. -/
abbrev chernRedZ'c :
    VectorBundleCore ℂ chernRedW₁.TotalSpace (EuclideanSpace ℂ (Fin 1)) (Fin 3) :=
  Work.Thom.bundleComap (Work.Gen.tautLine 2) (Work.Thom.bundleProj chernRedW₁)

/-- The realification of `chernRedZ'c`. -/
abbrev chernRedZ' : RealBundle chernRedW₁.TotalSpace (EuclideanSpace ℂ (Fin 1)) (Fin 3) :=
  Work.Thom.realification chernRedZ'c

/-- The pullback of `O(-1)` to the punctured total space `B = O(1)∖0` of the first summand. -/
abbrev chernRedZc : VectorBundleCore ℂ ↥chernRedU0 (EuclideanSpace ℂ (Fin 1)) (Fin 3) :=
  Work.Thom.bundleComap chernRedZ'c (Work.Thom.subtypeMap chernRedU0)

/-- The realification of `chernRedZc`: the rank-`2` real bundle over `B` whose zero complement is
`chernRedU ∩ chernRedV`. -/
abbrev chernRedZ : RealBundle ↥chernRedU0 (EuclideanSpace ℂ (Fin 1)) (Fin 3) :=
  Work.Thom.realification chernRedZc

/-! ## 2. The identification `((b,v),w) ↦ (b,(v,w))` of the two total spaces -/

/-- **`Φ`**: the identification `((b,v),w) ↦ (b,(v,w))` of the total space of `chernRedZ'` with
that of `chernRedE = O(1) ⊕ O(-1)`: the base point of the source contributes its fibre coordinate
`v` to the *first* summand of the target, and the fibre coordinate `w` goes to the second. -/
def chernRedPhi (p : chernRedZ'c.TotalSpace) : chernRedE.TotalSpace :=
  ⟨p.1.1, Work.Whitney.sumFibreC 1 1 (p.1.2, p.2)⟩

/-- **`Ψ`**: the inverse `(b,(v,w)) ↦ ((b,v),w)` of `chernRedPhi`. -/
def chernRedPsi (p : chernRedE.TotalSpace) : chernRedZ'c.TotalSpace :=
  ⟨⟨p.1, Work.Whitney.NZ.fstC 1 p.2⟩, Work.Whitney.NZ.sndC 1 p.2⟩

@[simp] theorem chernRedPhi_apply (p : chernRedZ'c.TotalSpace) :
    chernRedPhi p = ⟨p.1.1, Work.Whitney.sumFibreC 1 1 (p.1.2, p.2)⟩ := rfl

@[simp] theorem chernRedPsi_apply (p : chernRedE.TotalSpace) :
    chernRedPsi p = ⟨⟨p.1, Work.Whitney.NZ.fstC 1 p.2⟩,
      Work.Whitney.NZ.sndC 1 p.2⟩ := rfl

/-- `Ψ` is a left inverse of `Φ`. -/
theorem chernRedPsi_chernRedPhi (p : chernRedZ'c.TotalSpace) :
    chernRedPsi (chernRedPhi p) = p := by
  rw [show chernRedPsi (chernRedPhi p) =
      (⟨⟨p.1.1, Work.Whitney.NZ.fstC 1 (Work.Whitney.sumFibreC 1 1 (p.1.2, p.2))⟩,
        Work.Whitney.NZ.sndC 1 (Work.Whitney.sumFibreC 1 1 (p.1.2, p.2))⟩ :
          chernRedZ'c.TotalSpace) from rfl]
  rw [Work.Whitney.NZ.fstC_sumFibreC, Work.Whitney.NZ.sndC_sumFibreC]

/-- `Ψ` is a right inverse of `Φ`. -/
theorem chernRedPhi_chernRedPsi (p : chernRedE.TotalSpace) :
    chernRedPhi (chernRedPsi p) = p := by
  rw [show chernRedPhi (chernRedPsi p) =
      (⟨p.1, Work.Whitney.sumFibreC 1 1 (Work.Whitney.NZ.fstC 1 p.2,
        Work.Whitney.NZ.sndC 1 p.2)⟩ : chernRedE.TotalSpace) from rfl]
  rw [Work.Whitney.NZ.sumFibreC_fstC_sndC]

/-! ## 3. Continuity of `Φ` -/

/-- The projection of `chernRedZ'c` on its base. -/
def chernRedProjZ' : C(chernRedZ'c.TotalSpace, chernRedW₁.TotalSpace) :=
  ⟨fun p => p.1, chernRedZ'c.continuous_proj⟩

/-- The base projection `O(1) → ℂP²`. -/
def chernRedProjW₁ : C(chernRedW₁.TotalSpace, Work.Projective.CP 2) :=
  Work.Thom.bundleProj chernRedW₁

/-- **The "insert `w` into the second slot" half of `Φ`**, as a map of total spaces. -/
theorem continuous_chernRedInclC :
    Continuous (fun p : chernRedZ'c.TotalSpace =>
      (⟨p.1.1, chernRedInclC p.2⟩ : chernRedE.TotalSpace)) :=
  Work.Thom.continuous_totalSpaceMap_clm chernRedZ'c chernRedE chernRedProjW₁
    (fun _ => chernRedInclC)
    (fun i₁ i₂ => by
      have hmain := continuousOn_composite_incl i₁ i₂
      rw [show (fun b : chernRedW₁.TotalSpace =>
          chernRedE.coordChange (chernRedE.indexAt (chernRedProjW₁ b)) i₂ (chernRedProjW₁ b) ∘SL
            (chernRedInclC : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 2)) ∘SL
            chernRedZ'c.coordChange i₁ (chernRedZ'c.indexAt b) b)
          = (fun b' : Work.Projective.CP 2 =>
              chernRedE.coordChange (chernRedE.indexAt b') i₂ b' ∘SL
                (chernRedInclC : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 2)) ∘SL
                (Work.Gen.tautLine 2).coordChange i₁ ((Work.Gen.tautLine 2).indexAt b') b')
            ∘ chernRedProjW₁ from rfl]
      rw [show (chernRedZ'c.baseSet i₁ ∩ ⇑chernRedProjW₁ ⁻¹' chernRedE.baseSet i₂)
          = chernRedProjW₁ ⁻¹'
              ((Work.Gen.tautLine 2).baseSet i₁ ∩ chernRedE.baseSet i₂) from rfl]
      exact hmain.comp chernRedProjW₁.continuous.continuousOn (fun b hb => hb))

/-- The same map with the realification of `chernRedE` as target. -/
theorem continuous_chernRedInclC_W :
    Continuous (fun p : chernRedZ'c.TotalSpace =>
      (⟨p.1.1, chernRedInclC p.2⟩ : chernRedW.TotalSpace)) :=
  (Work.Thom.continuous_id_realification chernRedE).comp continuous_chernRedInclC

/-- **Continuity of `Φ`.**  On the first summand `Φ` inserts the base point's coordinate `v` and
forgets `w`, on the second it inserts `w`; the two pieces are summed by
`Work.Thom.continuous_add_section`. -/
theorem continuous_chernRedPhiC :
    Continuous (fun p : chernRedZ'c.TotalSpace =>
      (⟨p.1.1, Work.Whitney.sumFibreC 1 1 (p.1.2, p.2)⟩ : chernRedW.TotalSpace)) := by
  have h1 : Continuous (fun p : chernRedZ'c.TotalSpace =>
      (⟨p.1.1, chernRedInclC₁ p.1.2⟩ : chernRedW.TotalSpace)) :=
    continuous_inclC₁_totalMap_W.comp chernRedProjZ'.continuous
  have h2 : Continuous (fun p : chernRedZ'c.TotalSpace =>
      (⟨p.1.1, chernRedInclC p.2⟩ : chernRedW.TotalSpace)) := continuous_chernRedInclC_W
  let s1 : C(chernRedZ'c.TotalSpace, chernRedW.TotalSpace) :=
    ⟨fun p => (⟨p.1.1, chernRedInclC₁ p.1.2⟩ : chernRedW.TotalSpace), h1⟩
  let s2 : C(chernRedZ'c.TotalSpace, chernRedW.TotalSpace) :=
    ⟨fun p => (⟨p.1.1, chernRedInclC p.2⟩ : chernRedW.TotalSpace), h2⟩
  have hsum := Work.Thom.continuous_add_section chernRedW s1 s2 (fun p => rfl)
  refine hsum.congr (fun p => ?_)
  show (⟨p.1.1, chernRedInclC₁ p.1.2 + chernRedInclC p.2⟩ : chernRedW.TotalSpace) =
    (⟨p.1.1, Work.Whitney.sumFibreC 1 1 (p.1.2, p.2)⟩ : chernRedW.TotalSpace)
  rw [chernRedInclC₁_apply, chernRedInclC_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

/-- **Continuity of `Φ` in the real flavour**, from `continuous_chernRedPhiC` through the
identification of a bundle with its realification. -/
theorem continuous_chernRedPhi :
    Continuous (fun p : chernRedZ'.TotalSpace =>
      (⟨p.1.1, Work.Whitney.sumFibreC 1 1 (p.1.2, p.2)⟩ : chernRedW.TotalSpace)) :=
  (continuous_chernRedPhiC).comp (Work.Thom.continuous_id_realification_symm chernRedZ'c)

/-! ## 4. Continuity of `Ψ` -/

/-- The second summand projection of `chernRedE`, into the total space of `O(-1)`. -/
def chernRedSndP (p : chernRedE.TotalSpace) : (Work.Gen.tautLine 2).TotalSpace :=
  ⟨p.1, Work.Whitney.NZ.sndC 1 p.2⟩

theorem chernRedSndP_continuous : Continuous chernRedSndP := continuous_sndC_totalMap

/-- **The chart of `chernRedZ'` reads `Ψ` as the chart of `O(-1)` read at the second summand
projection.** -/
theorem chernRedZ'_localTriv_chernRedPsi (i : Fin 3) :
    (fun p : chernRedE.TotalSpace => (chernRedZ'c.localTriv i) (chernRedPsi p)) =
      (fun p : chernRedE.TotalSpace =>
        ((⟨p.1, Work.Whitney.NZ.fstC 1 p.2⟩ : chernRedW₁.TotalSpace),
          ((Work.Gen.tautLine 2).localTriv i (chernRedSndP p)).2)) := by
  funext p
  simp only [chernRedPsi, chernRedSndP, VectorBundleCore.localTriv_apply,
    Work.Thom.bundleComap_coordChange, Work.Thom.bundleComap_indexAt,
    Work.Thom.bundleProj_apply]

/-- **Continuity of `Ψ`.**  The bundle topology is tested in a fixed chart; there the map is the base
part `p ↦ (p.1, fstC 1 p.2)` together with the `O(-1)`-chart coordinate of the *second* summand
projection `p ↦ ⟨p.1, sndC 1 p.2⟩` (continuous, and lying in the chart near the point). -/
theorem continuous_chernRedPsiC :
    Continuous (fun p : chernRedE.TotalSpace =>
      (⟨⟨p.1, Work.Whitney.NZ.fstC 1 p.2⟩, Work.Whitney.NZ.sndC 1 p.2⟩ :
        chernRedZ'c.TotalSpace)) := by
  have hfst : Continuous (fun p : chernRedE.TotalSpace =>
      (⟨p.1, Work.Whitney.NZ.fstC 1 p.2⟩ : chernRedW₁.TotalSpace)) :=
    (Work.Thom.continuous_id_realification (Work.Gen.tautDual 2)).comp
      continuous_fstC_totalMap
  rw [continuous_iff_continuousAt]
  intro p₀
  set q₀ : chernRedW₁.TotalSpace := ⟨p₀.1, Work.Whitney.NZ.fstC 1 p₀.2⟩ with hq₀
  set i : Fin 3 := chernRedZ'c.indexAt q₀ with hi
  have hbase : q₀ ∈ chernRedZ'c.baseSet i := by rw [hi]; exact chernRedZ'c.mem_baseSet_at q₀
  have hsrc₀ : p₀.1 ∈ (Work.Gen.tautLine 2).baseSet i := by
    have h := hbase
    rw [Work.Thom.bundleComap_baseSet, Set.mem_preimage] at h
    simpa using h
  refine (chernRedZ'c.localTriv i).continuousAt_of_comp_left ?_ hbase ?_
  · show ContinuousAt (fun p => chernRedZ'c.proj (chernRedPsi p)) p₀
    refine hfst.continuousAt.congr (Filter.Eventually.of_forall (fun p => rfl))
  · have hmem : chernRedSndP p₀ ∈ ((Work.Gen.tautLine 2).localTriv i).source := by
      rw [Bundle.Trivialization.mem_source]
      exact hsrc₀
    have hloc : ContinuousAt
        (fun p => ((Work.Gen.tautLine 2).localTriv i) (chernRedSndP p)) p₀ :=
      (((Work.Gen.tautLine 2).localTriv i).toOpenPartialHomeomorph.continuousAt hmem).comp
        chernRedSndP_continuous.continuousAt
    have h2 : ContinuousAt
        (fun p => (((Work.Gen.tautLine 2).localTriv i) (chernRedSndP p)).2) p₀ :=
      continuous_snd.continuousAt.comp hloc
    have hpair : ContinuousAt (fun p : chernRedE.TotalSpace =>
        ((⟨p.1, Work.Whitney.NZ.fstC 1 p.2⟩ : chernRedW₁.TotalSpace),
          (((Work.Gen.tautLine 2).localTriv i) (chernRedSndP p)).2)) p₀ :=
      hfst.continuousAt.prodMk h2
    refine hpair.congr ?_
    filter_upwards with p
    exact (congrFun (chernRedZ'_localTriv_chernRedPsi i) p).symm

/-- **Continuity of `Ψ` in the real flavour.** -/
theorem continuous_chernRedPsi :
    Continuous (fun p : chernRedW.TotalSpace =>
      (⟨⟨p.1, Work.Whitney.NZ.fstC 1 p.2⟩,
        Work.Whitney.NZ.sndC 1 p.2⟩ : chernRedZ'.TotalSpace)) :=
  (Work.Thom.continuous_id_realification chernRedZ'c).comp
    ((continuous_chernRedPsiC).comp (Work.Thom.continuous_id_realification_symm chernRedE))

/-! ## 5. Coordinate lemmas -/

theorem chernRedPhi_fib_ne_zero {v w : EuclideanSpace ℂ (Fin 1)} (hv : v ≠ 0) (_hw : w ≠ 0) :
    Work.Whitney.sumFibreC 1 1 (v, w) ≠ 0 := by
  intro h
  have h1 : v = 0 := by
    have h2 := Work.Whitney.NZ.fstC_sumFibreC 1 v w
    rw [h] at h2
    simpa using h2.symm
  exact hv h1

theorem chernRedCoord0_eq_zero_iff (q : chernRedW.TotalSpace) :
    chernRedCoord0 q = 0 ↔ Work.Whitney.NZ.fstC 1 (chernRedFib q) = 0 := by
  rw [chernRedFstC_eq_zero_iff]
  rfl

theorem chernRedCoord1_eq_zero_iff (q : chernRedW.TotalSpace) :
    chernRedCoord1 q = 0 ↔ Work.Whitney.NZ.sndC 1 (chernRedFib q) = 0 := by
  rw [chernRedSndC_eq_zero_iff]
  rfl

/-! ## 6. The piece `P` over `B` and its homeomorphism with `chernRedU ∩ chernRedV` -/

/-- **The piece of `zeroComplement chernRedZ'` over the punctured first summand**: the points
`((b,v),w)` with `v ≠ 0` and `w ≠ 0`. -/
def chernRedP : Set ↥(Work.Thom.zeroComplement chernRedZ') :=
  {x | x.1.proj ∈ chernRedU0}

theorem chernRedPToUV_mem (z : ↥chernRedP) :
    chernRedPhi z.1.1 ∈ Work.Thom.zeroComplement chernRedW := by
  have hz1 : z.1.1.1.2 ≠ 0 := z.2
  have hz2 : z.1.1.2 ≠ 0 := z.1.2
  show Work.Whitney.sumFibreC 1 1 (z.1.1.1.2, z.1.1.2) ≠ 0
  exact chernRedPhi_fib_ne_zero hz1 hz2

theorem chernRedPToUV_coord0 (z : ↥chernRedP) : chernRedCoord0 (chernRedPhi z.1.1) ≠ 0 := by
  have hz1 : z.1.1.1.2 ≠ 0 := z.2
  show (Work.Whitney.sumFibreC 1 1 (z.1.1.1.2, z.1.1.2)).ofLp 0 ≠ 0
  have hu : Work.Whitney.NZ.fstC 1 (Work.Whitney.sumFibreC 1 1 (z.1.1.1.2, z.1.1.2)) ≠ 0 := by
    rw [Work.Whitney.NZ.fstC_sumFibreC]
    exact hz1
  exact fun h => hu ((chernRedFstC_eq_zero_iff _).2 h)

theorem chernRedPToUV_coord1 (z : ↥chernRedP) : chernRedCoord1 (chernRedPhi z.1.1) ≠ 0 := by
  have hz2 : z.1.1.2 ≠ 0 := z.1.2
  show (Work.Whitney.sumFibreC 1 1 (z.1.1.1.2, z.1.1.2)).ofLp 1 ≠ 0
  have hu : Work.Whitney.NZ.sndC 1 (Work.Whitney.sumFibreC 1 1 (z.1.1.1.2, z.1.1.2)) ≠ 0 := by
    rw [Work.Whitney.NZ.sndC_sumFibreC]
    exact hz2
  exact fun h => hu ((chernRedSndC_eq_zero_iff _).2 h)

/-- **The identification of the piece `P` with `chernRedU ∩ chernRedV`** (the map `Φ`). -/
def chernRedPToUV (z : ↥chernRedP) : ↥(chernRedU ∩ chernRedV) :=
  ⟨⟨chernRedPhi z.1.1, chernRedPToUV_mem z⟩,
    Set.mem_inter (chernRedPToUV_coord0 z) (chernRedPToUV_coord1 z)⟩

theorem chernRedUVToP_fib (z : ↥(chernRedU ∩ chernRedV)) :
    Work.Whitney.NZ.sndC 1 (chernRedFib z.1.1) ≠ 0 := by
  intro h
  exact (show chernRedCoord1 z.1.1 ≠ 0 from z.2.2) ((chernRedCoord1_eq_zero_iff z.1.1).2 h)

theorem chernRedUVToP_mem (z : ↥(chernRedU ∩ chernRedV)) :
    (chernRedPsi z.1.1).proj ∈ chernRedU0 := by
  show Work.Whitney.NZ.fstC 1 (chernRedFib z.1.1) ≠ 0
  intro h
  exact (show chernRedCoord0 z.1.1 ≠ 0 from z.2.1) ((chernRedCoord0_eq_zero_iff z.1.1).2 h)

/-- **The inverse identification** (the map `Ψ`). -/
def chernRedUVToP (z : ↥(chernRedU ∩ chernRedV)) : ↥chernRedP :=
  ⟨⟨chernRedPsi z.1.1, chernRedUVToP_fib z⟩, chernRedUVToP_mem z⟩

theorem continuous_chernRedPToUV : Continuous chernRedPToUV := by
  have h0 : Continuous (fun z : ↥chernRedP => z.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have h1 : Continuous (fun z : ↥chernRedP =>
      (⟨chernRedPhi z.1.1, chernRedPToUV_mem z⟩ :
        ↥(Work.Thom.zeroComplement chernRedW))) :=
    (continuous_chernRedPhi.comp h0).subtype_mk _
  exact h1.subtype_mk _

theorem continuous_chernRedUVToP : Continuous chernRedUVToP := by
  have h0 : Continuous (fun z : ↥(chernRedU ∩ chernRedV) => z.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have h1 : Continuous (fun z : ↥(chernRedU ∩ chernRedV) =>
      (⟨chernRedPsi z.1.1, chernRedUVToP_fib z⟩ :
        ↥(Work.Thom.zeroComplement chernRedZ'))) :=
    (continuous_chernRedPsi.comp h0).subtype_mk _
  exact h1.subtype_mk _

/-- **`P` is homeomorphic to `chernRedU ∩ chernRedV`.** -/
noncomputable def chernRedUVHomeo : ↥chernRedP ≃ₜ ↥(chernRedU ∩ chernRedV) where
  toFun := chernRedPToUV
  invFun := chernRedUVToP
  left_inv := fun z => by
    refine Subtype.ext (Subtype.ext ?_)
    show chernRedPsi (chernRedPhi z.1.1) = z.1.1
    rw [chernRedPsi_chernRedPhi]
  right_inv := fun z => by
    refine Subtype.ext (Subtype.ext ?_)
    show chernRedPhi (chernRedPsi z.1.1) = z.1.1
    rw [chernRedPhi_chernRedPsi]
  continuous_toFun := continuous_chernRedPToUV
  continuous_invFun := continuous_chernRedUVToP

/-- **`zeroComplement chernRedZ` is homeomorphic to the piece `P`**
(`Work.LerayHirsch.punctHomeo` applied to `O(-1)` over the whole total space of `O(1)`). -/
noncomputable def chernRedPHomeo :
    ↥(Work.Thom.zeroComplement chernRedZ) ≃ₜ ↥chernRedP :=
  Work.LerayHirsch.punctHomeo chernRedZ'c chernRedU0

/-! ## 7. The Gysin sequence of `chernRedZ` over `B` -/

/-- The Thom class of the rank-`2` real bundle `chernRedZ = realification (π^* O(-1))`. -/
noncomputable def chernRedZThom : Work.Thom.ThomClass chernRedZ 2 :=
  Work.Thom.thomClassOf (m := 1) (by norm_num) chernRedZc

/-- **`H³` of the zero complement of `chernRedZ` vanishes.**  The Gysin sequence of the rank-`2`
bundle `chernRedZ` over `B = O(1)∖0` reads

  `H¹(B) → H³(B) → H³(Z∖0) → H⁴(E,E∖0) → H²(B)`,

and the neighbouring terms vanish: `H¹(B) = H³(B) = H²(B) = 0` because `B ≃ ℂ³∖{0}`
(`Work.Gen.puncturedTautDualTwoHZero`), and `H⁴(E,E∖0) ≅ H²(B) = 0` by the Thom isomorphism. -/
theorem chernRedZ_vanishing :
    Subsingleton (Work.Thom.Coh ℤ 3 ↥(Work.Thom.zeroComplement chernRedZ)) := by
  haveI h2 : Subsingleton (Work.Thom.Coh ℤ 2 ↥chernRedU0) :=
    ModuleCat.subsingleton_of_isZero
      (puncturedTautDualTwoHZero 2 (by norm_num) (by norm_num))
  haveI h3 : Subsingleton (Work.Thom.Coh ℤ 3 ↥chernRedU0) :=
    ModuleCat.subsingleton_of_isZero
      (puncturedTautDualTwoHZero 3 (by norm_num) (by norm_num))
  haveI hO : Subsingleton ↥(Work.Thom.OpenThom chernRedZ 4) :=
    Function.Surjective.subsingleton (chernRedZThom.thomEquiv 2).surjective
  have hδ : (Work.Thom.pairδC (Work.Thom.zeroComplement chernRedZ) 3).hom = 0 :=
    LinearMap.ext (fun z => Subsingleton.elim _ _)
  have hsurj : Function.Surjective (Work.Thom.gysinπ chernRedZ 3) := by
    have hex := Work.Thom.gysin_exact_at_sphere chernRedZThom 1
    rw [show (1 : ℕ) + 2 = 3 from rfl] at hex
    intro y
    have hy : y ∈ Set.range (Work.Thom.gysinπ chernRedZ 3) := by
      rw [hex]
      simp [hδ]
    exact hy
  exact Function.Surjective.subsingleton hsurj

/-! ## 8. The vanishing -/

theorem chernRedUV_vanishing :
    Subsingleton (Work.Thom.Coh ℤ 3 ↥(Work.ThomBordism.Grassmann.chernRedU ∩
      Work.ThomBordism.Grassmann.chernRedV)) :=
  subsingleton_cohomology_of_homotopyEquiv'
    (chernRedPHomeo.trans chernRedUVHomeo).toHomotopyEquiv 3 chernRedZ_vanishing

end

end Work.ThomBordism.Grassmann
