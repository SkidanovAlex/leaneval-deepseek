import Submission.Work.Thom.comapAux
import Submission.Work.Thom.tautQuotientCore_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The total-space map of a pullback is proper

For a real bundle `Z` (as gluing data) over a base `B` and a continuous map `g : B' → B` out of a
**compact** base `B'`, the canonical map of total spaces

`Work.Thom.totalMap Z g : (g^*Z).TotalSpace → Z.TotalSpace`,  `⟨x, v⟩ ↦ ⟨g x, v⟩`

is *proper*: the preimage of a compact set is compact.  Equivalently (Mathlib's
`OnePoint.continuous_map_iff`), it extends to a continuous map of the one-point compactifications
`OnePoint (g^*Z).TotalSpace → OnePoint Z.TotalSpace` fixing `∞`.

This is exactly what is needed to pass a *bundle map* (the Gauss/classifying map `ν → γ`, an
isomorphism of gluing data) to a map of Thom spaces in the metric-free model
`Th = OnePoint (TotalSpace)`.  Nothing about `OnePoint` is used here: the content is the compactness
statement.

The proof: cover `proj K` by finitely many `Z.baseSet i`, shrink this to a finite cover by **closed**
sets `w i ⊆ Z.baseSet i` (the shrinking lemma `exists_subset_iUnion_closed_subset`, with one extra
open set `(proj K)ᶜ`); over `w i` the trivialisation of the pullback and that of `Z` have the same
fibre coordinate (`localTriv_snd_bundleComap`), so the preimage of `K ∩ proj ⁻¹' w i` is the image,
under the (continuous) inverse trivialisation, of the compact set `g ⁻¹' w i × closedBall 0 R`,
where `R` bounds the fibre coordinates of `K` in the chart `i`.
-/

open scoped Topology
open Function Topology Set Filter

namespace Work.Tubular

open Work.TangentClasses

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}

open Work.Thom

/-- **The preimage of a compact set under the total-space map of a pullback is compact.** -/
theorem isCompact_preimage_totalMap [CompactSpace B] [CompactSpace B'] [T2Space B] [ProperSpace F]
    (Z : RealBundle B F ι) (g : C(B', B)) {K : Set Z.TotalSpace} (hK : IsCompact K) :
    IsCompact ((Work.Thom.totalMap Z g) ⁻¹' K) := by
  classical
  have hKproj : IsCompact (Z.proj '' K) := hK.image Z.continuous_proj
  obtain ⟨s, hs⟩ := hKproj.elim_finite_subcover Z.baseSet (fun i => Z.isOpen_baseSet i)
    (fun x hx => mem_iUnion.mpr ⟨Z.indexAt x, Z.mem_baseSet_at x⟩)
  let u : Option {i // i ∈ s} → Set B := fun i => match i with
    | none => (Z.proj '' K)ᶜ
    | some j => Z.baseSet j.1
  have huopen : ∀ i, IsOpen (u i) := by
    rintro (_ | j)
    · exact hKproj.isClosed.isOpen_compl
    · exact Z.isOpen_baseSet j.1
  obtain ⟨v, hvuniv, hvclosed, hvsub⟩ := exists_subset_iUnion_closed_subset
    (isClosed_univ (X := B)) huopen
    (fun x _ => Set.toFinite _)
    (fun x _ => by
      by_cases hx : x ∈ Z.proj '' K
      · obtain ⟨i, his, hxi⟩ := mem_iUnion₂.mp (hs hx)
        exact mem_iUnion.mpr ⟨some ⟨i, his⟩, hxi⟩
      · exact mem_iUnion.mpr ⟨none, hx⟩)
  have hvsub' : ∀ j : {i // i ∈ s}, v (some j) ⊆ Z.baseSet j.1 := by
    intro j x hx
    exact hvsub (some j) hx
  have heq : (Work.Thom.totalMap Z g) ⁻¹' K = ⋃ j : {i // i ∈ s},
      (Work.Thom.totalMap Z g) ⁻¹' (K ∩ Z.proj ⁻¹' v (some j)) := by
    ext p
    constructor
    · intro hp
      have hmem : g p.1 ∈ ⋃ i, v i := hvuniv (mem_univ _)
      rcases mem_iUnion.mp hmem with ⟨i, hi⟩
      rcases i with _ | j
      · exact absurd ⟨Work.Thom.totalMap Z g p, hp, rfl⟩ (hvsub none hi)
      · exact mem_iUnion.mpr ⟨j, hp, hi⟩
    · intro hp
      rcases mem_iUnion.mp hp with ⟨j, hpj⟩
      exact hpj.1
  rw [heq]
  refine isCompact_iUnion (fun j => ?_)
  set i : ι := j.1 with hi
  set A : Set Z.TotalSpace := K ∩ Z.proj ⁻¹' v (some j) with hA
  set S : Set (bundleComap Z g).TotalSpace := (Work.Thom.totalMap Z g) ⁻¹' A with hS
  set T : Bundle.Trivialization F Bundle.TotalSpace.proj :=
    (bundleComap Z g).localTriv i with hT
  have hAmem : ∀ x : Z.TotalSpace, x ∈ A ↔ x ∈ K ∧ Z.proj x ∈ v (some j) := by
    intro x; rw [hA]; exact Iff.rfl
  have hAcomp : IsCompact A := hK.inter_right ((hvclosed (some j)).preimage Z.continuous_proj)
  have hAsub : A ⊆ (Z.localTriv i).source := by
    intro x hx
    rw [VectorBundleCore.mem_localTriv_source]
    exact hvsub' j ((hAmem x).mp hx).2
  have hcoord : IsCompact ((Z.localTriv i) '' A) :=
    hAcomp.image_of_continuousOn ((Z.localTriv i).continuousOn_toFun.mono hAsub)
  have hfst : IsCompact (Prod.snd '' ((Z.localTriv i) '' A)) := hcoord.image continuous_snd
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : F)).mp hfst.isBounded
  have hgv : IsCompact (g ⁻¹' v (some j)) :=
    ((hvclosed (some j)).preimage g.continuous).isCompact
  have hCcomp : IsCompact ((g ⁻¹' v (some j)) ×ˢ Metric.closedBall (0 : F) R) :=
    hgv.prod (isCompact_closedBall (0 : F) R)
  have hSp : ∀ p, p ∈ S ↔ Work.Thom.totalMap Z g p ∈ A := by
    intro p
    rw [hS]
    exact Iff.rfl
  have hSbase : ∀ p ∈ S, g p.1 ∈ Z.baseSet i := by
    intro p hp
    exact hvsub' j ((hAmem _).mp ((hSp p).mp hp)).2
  have hTfst : ∀ p : (bundleComap Z g).TotalSpace, (T p).1 = p.1 := by
    intro p
    rw [hT, VectorBundleCore.localTriv_apply]
  have hTsnd : ∀ p : (bundleComap Z g).TotalSpace,
      (T p).2 = (Z.localTriv i (Work.Thom.totalMap Z g p)).2 := by
    intro p
    rw [hT, localTriv_snd_bundleComap]
    rfl
  have hSsrc : S ⊆ T.source := by
    intro p hp
    rw [hT, VectorBundleCore.mem_localTriv_source]
    exact hSbase p hp
  have hφc : Continuous (fun q : B' × F => (g q.1, q.2) : B' × F → B × F) :=
    (g.continuous.comp continuous_fst).prodMk continuous_snd
  have hTS : T '' S = ((g ⁻¹' v (some j)) ×ˢ Metric.closedBall (0 : F) R) ∩
      {q : B' × F | (g q.1, q.2) ∈ (Z.localTriv i) '' A} := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hpA : Work.Thom.totalMap Z g p ∈ A := (hSp p).mp hp
      refine ⟨⟨((hAmem _).mp hpA).2, ?_⟩, ?_⟩
      · rw [hTsnd p]
        exact hR (mem_image_of_mem Prod.snd (mem_image_of_mem (Z.localTriv i) hpA))
      · have hpq : (g (T p).1, (T p).2) = (Z.localTriv i) (Work.Thom.totalMap Z g p) := by
          rw [hTfst p, hTsnd p, VectorBundleCore.localTriv_apply]
          rfl
        show (g (T p).1, (T p).2) ∈ (Z.localTriv i) '' A
        rw [hpq]
        exact mem_image_of_mem (Z.localTriv i) hpA
    · rintro ⟨hqC, hqW⟩
      obtain ⟨a, haA, haq⟩ := hqW
      have hqbase : g q.1 ∈ Z.baseSet i := hvsub' j hqC.1
      have hqmem : q ∈ T.target := by
        rw [hT, VectorBundleCore.mem_localTriv_target]
        exact hqbase
      have hTq : T (T.toPartialEquiv.symm q) = q := T.apply_symm_apply hqmem
      have hfirst : (Work.Thom.totalMap Z g (T.toPartialEquiv.symm q)).1 = g q.1 := by
        show g (T.toPartialEquiv.symm q).1 = g q.1
        rw [← hTfst (T.toPartialEquiv.symm q), hTq]
      have hcoord2 : (Z.localTriv i (Work.Thom.totalMap Z g (T.toPartialEquiv.symm q))).2 = q.2 := by
        rw [← hTsnd (T.toPartialEquiv.symm q), hTq]
      have hsrctot : Work.Thom.totalMap Z g (T.toPartialEquiv.symm q) ∈ (Z.localTriv i).source := by
        rw [VectorBundleCore.mem_localTriv_source, hfirst]
        exact hqbase
      have hsrca : a ∈ (Z.localTriv i).source := by
        rw [VectorBundleCore.mem_localTriv_source]
        exact hvsub' j ((hAmem a).mp haA).2
      have htot : Work.Thom.totalMap Z g (T.toPartialEquiv.symm q) = a := by
        have hL : (Z.localTriv i) (Work.Thom.totalMap Z g (T.toPartialEquiv.symm q)) = (g q.1, q.2) :=
          Prod.ext (by rw [(Z.localTriv i).coe_fst hsrctot]; exact hfirst) hcoord2
        have h1 : (Z.localTriv i) (Work.Thom.totalMap Z g (T.toPartialEquiv.symm q))
            = (Z.localTriv i) a := by rw [hL, haq]
        calc Work.Thom.totalMap Z g (T.toPartialEquiv.symm q)
            = (Z.localTriv i).toPartialEquiv.symm
                ((Z.localTriv i) (Work.Thom.totalMap Z g (T.toPartialEquiv.symm q))) :=
                ((Z.localTriv i).symm_apply_apply hsrctot).symm
          _ = (Z.localTriv i).toPartialEquiv.symm ((Z.localTriv i) a) := by rw [h1]
          _ = a := (Z.localTriv i).symm_apply_apply hsrca
      refine ⟨T.toPartialEquiv.symm q, ?_, ?_⟩
      · rw [hSp, htot]
        exact haA
      · exact hTq
  have hTScomp : IsCompact (T '' S) := by
    rw [hTS]
    exact hCcomp.inter_right (hcoord.isClosed.preimage hφc)
  have hcoverT : T '' S ⊆ T.target := by
    rintro _ ⟨p, hp, rfl⟩
    rw [hT, VectorBundleCore.mem_localTriv_target]
    exact hSbase p hp
  have hSeq : S = T.toPartialEquiv.symm '' (T.toPartialEquiv '' S) := by
    ext y
    constructor
    · intro hy
      exact ⟨T.toPartialEquiv y, ⟨y, hy, rfl⟩, T.symm_apply_apply (hSsrc hy)⟩
    · rintro ⟨p, hp, hpy⟩
      obtain ⟨z, hz, rfl⟩ := hp
      have h1 : T.toPartialEquiv.symm (T.toPartialEquiv z) = z := T.symm_apply_apply (hSsrc hz)
      rw [← hpy, h1]
      exact hz
  rw [hSeq]
  exact hTScomp.image_of_continuousOn
    (T.toOpenPartialHomeomorph.continuousOn_invFun.mono hcoverT)

/-- **The total-space map of a pullback extends to the one-point compactifications.**  This is the
map of Thom spaces induced by a map of bundles; it fixes `∞`. -/
theorem continuous_onePointMap_totalMap [CompactSpace B] [CompactSpace B'] [T2Space B]
    [ProperSpace F] (Z : RealBundle B F ι) (g : C(B', B)) :
    Continuous (OnePoint.map (Work.Thom.totalMap Z g)) := by
  refine OnePoint.continuous_map (totalMap Z g).continuous ?_
  rw [(Filter.hasBasis_coclosedCompact (X := (bundleComap Z g).TotalSpace)).tendsto_iff
    (Filter.hasBasis_coclosedCompact (X := Z.TotalSpace))]
  rintro K ⟨hKc, hKcomp⟩
  exact ⟨(Work.Thom.totalMap Z g) ⁻¹' K,
    ⟨hKc.preimage (totalMap Z g).continuous, isCompact_preimage_totalMap Z g hKcomp⟩,
    fun x hx hxK => hx hxK⟩

end

end Work.Tubular
