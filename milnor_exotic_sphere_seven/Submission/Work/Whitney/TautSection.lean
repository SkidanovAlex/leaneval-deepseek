import Mathlib
import Submission.Work.Thom.Basic
import Submission.Work.Thom.ThomClass
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.chernClass_zero_eq_oneH
import Submission.Work.Thom.chernClass_eq_zero_of_lt
import Submission.Work.Thom.chernClass_top_eq_zero_of_nowhereZeroSection

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-!
# The tautological section of the pullback of a bundle to its own punctured total space

For a real bundle `Z` over `B`, let `π : Z∖0 → B` be the projection of the complement of the zero
section and let `π^*Z` be the pullback of `Z` along `π`.  The **tautological section**

  `s x = ⟨x, (x : Z.TotalSpace).2⟩`,   `x ∈ ↥(zeroComplement Z)`,

is the "diagonal" section of `π^*Z`: its value in the fibre `(π^*Z)_x = Z_{π x}` is the vector `x`
itself, which is non-zero precisely because `x` lies in `Z∖0`.

This section is the geometric input of every "peel a line off" argument: the pullback `π^*Z` carries
a canonical nowhere-zero section, so its top Chern class vanishes.  The continuity is *not* formal:
`Z.TotalSpace` is a sigma type with the bundle topology (not the product topology), so
`x ↦ (x : Z.TotalSpace).2` is not continuous by itself; the proof below tests continuity in the
preferred trivialisation at the point.
-/

open Work.TangentClasses

open scoped Topology

namespace Work.Whitney

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type}

/-- **The tautological section of the pullback to the punctured total space is continuous.** -/
theorem continuous_tautologicalSection (Z : RealBundle B F ι) :
    Continuous (fun x : ↥(Work.Thom.zeroComplement Z) =>
      (⟨x, (x : Z.TotalSpace).2⟩ :
        (Work.Thom.bundleComap Z ((Work.Thom.bundleProj Z).comp
          (Work.Thom.subtypeMap (Work.Thom.zeroComplement Z)))).TotalSpace)) := by
  set π := (Work.Thom.bundleProj Z).comp (Work.Thom.subtypeMap (Work.Thom.zeroComplement Z))
    with hπ
  set P := Work.Thom.bundleComap Z π with hP
  have hπx : ∀ x : ↥(Work.Thom.zeroComplement Z), π x = (x : Z.TotalSpace).proj := by
    intro x
    rw [hπ, ContinuousMap.comp_apply, Work.Thom.bundleProj_apply]
    rfl
  rw [continuous_iff_continuousAt]
  intro x₀
  set i : ι := P.indexAt x₀ with hi
  have hbase : (x₀ : Z.TotalSpace).proj ∈ Z.baseSet i := by
    have h1 : x₀ ∈ P.baseSet i := P.mem_baseSet_at x₀
    rw [hi] at h1 ⊢
    simpa only [hP, Work.Thom.bundleComap_baseSet, Set.mem_preimage, hπx] using h1
  have hx0 : P.proj (⟨x₀, (x₀ : Z.TotalSpace).2⟩ : P.TotalSpace) ∈ (P.localTriv i).baseSet :=
    P.mem_baseSet_at x₀
  refine (P.localTriv i).continuousAt_of_comp_left ?_ hx0 ?_
  · have h : (Bundle.TotalSpace.proj ∘ fun x : ↥(Work.Thom.zeroComplement Z) =>
        (⟨x, (x : Z.TotalSpace).2⟩ : P.TotalSpace)) = fun x => x := by
      funext x; rfl
    rw [h]
    exact continuousAt_id
  · have hsrc : (x₀ : Z.TotalSpace) ∈ (Z.localTriv i).source := by
      rw [Bundle.Trivialization.mem_source]
      exact hbase
    have hcont : ContinuousAt (fun x : ↥(Work.Thom.zeroComplement Z) =>
        (Z.localTriv i) (x : Z.TotalSpace)) x₀ :=
      ((Z.localTriv i).toOpenPartialHomeomorph.continuousAt hsrc).comp continuousAt_subtype_val
    have h2 : ContinuousAt (fun x : ↥(Work.Thom.zeroComplement Z) =>
        (Z.localTriv i (x : Z.TotalSpace)).2) x₀ := continuous_snd.continuousAt.comp hcont
    have hpair : ContinuousAt (fun x : ↥(Work.Thom.zeroComplement Z) =>
        (x, (Z.localTriv i (x : Z.TotalSpace)).2)) x₀ := continuousAt_id.prodMk h2
    refine hpair.congr ?_
    have hU : ∀ᶠ x : ↥(Work.Thom.zeroComplement Z) in 𝓝 x₀, Z.proj x ∈ Z.baseSet i :=
      (Z.continuous_proj.continuousAt.comp continuousAt_subtype_val).preimage_mem_nhds
        ((Z.isOpen_baseSet i).mem_nhds hbase)
    filter_upwards [hU] with x hx
    rfl

/-! ## The Chern classes of the tautological quotient

The descent equation of the recursion (`Work.Thom.chernClass_succ_of_le`) identifies `c_j` of a
bundle of rank `m+1` in degrees `j ≤ m` as the *inverse image* of `c_j` of its tautological quotient
along `π : V∖0 → B`.  Applying `π^*` to both sides (`Work.Thom.chernClass_comap`) turns this into the
statement of this section: **in those degrees, `c_j(π^*V) = c_j(Q_V)`**.

For `j = m+1` the same identity holds with both sides zero — the left side because `π^*V` carries
the nowhere-zero tautological section (`Work.Whitney.continuous_tautologicalSection`), the right side
because `Q_V` has rank `m`; the version for all `j` is recorded as the delegation target
`Work.Whitney.chernClass_bundleComap_proj_eq_tautQuotient`. -/

variable {n : ℕ}

/-- **The Chern classes of the tautological quotient are the pullbacks of those of the bundle**,
in the degrees `j ≤ n` in which the descent equation of the recursion applies. -/
theorem chernClass_bundleComap_proj_eq_tautQuotient_le [Fintype ι] {j : ℕ} (hj : j ≤ n)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι) :
    Work.Thom.chernClass (n + 1) j
        (Work.Thom.bundleComap F ((Work.Thom.bundleProj (Work.Thom.realification F)).comp
          (Work.Thom.subtypeMap (Work.Thom.zeroComplement (Work.Thom.realification F)))))
      = Work.Thom.chernClass n j (Work.Thom.tautQuotient F) := by
  set π := (Work.Thom.bundleProj (Work.Thom.realification F)).comp
    (Work.Thom.subtypeMap (Work.Thom.zeroComplement (Work.Thom.realification F))) with hπ
  have hbij : Function.Bijective ((Work.Thom.CohMap π ℤ (2 * j)).hom) :=
    Work.Thom.bijective_proj_zeroComplementA (k := 2 * j) (Work.Thom.realification F)
      (Work.Thom.finrank_real_euclidean_complex (n + 1))
      (Work.Thom.thomClassRank (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) F) (by omega)
  rw [Work.Thom.chernClass_comap F π, Work.Thom.chernClass_succ_of_le F hj]
  exact LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective
    ((Work.Thom.CohMap π ℤ (2 * j)).hom) hbij)
    (Work.Thom.chernClass n j (Work.Thom.tautQuotient F))

/-- **The Chern classes of the tautological quotient are the pullbacks of those of the bundle**, in
every degree. -/
theorem chernClass_bundleComap_proj_eq_tautQuotient [Fintype ι] {j : ℕ}
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι) :
    Work.Thom.chernClass (n + 1) j
        (Work.Thom.bundleComap F ((Work.Thom.bundleProj (Work.Thom.realification F)).comp
          (Work.Thom.subtypeMap (Work.Thom.zeroComplement (Work.Thom.realification F)))))
      = Work.Thom.chernClass n j (Work.Thom.tautQuotient F) := by
  set π := (Work.Thom.bundleProj (Work.Thom.realification F)).comp
    (Work.Thom.subtypeMap (Work.Thom.zeroComplement (Work.Thom.realification F))) with hπ
  rcases Nat.lt_or_ge j (n + 1) with hjlt | hjge
  · exact chernClass_bundleComap_proj_eq_tautQuotient_le (Nat.lt_succ_iff.mp hjlt) F
  · rcases eq_or_lt_of_le hjge with heq | hgt
    · subst heq
      rw [Work.Thom.chernClass_eq_zero_of_lt (Work.Thom.tautQuotient F) (Nat.lt_succ_self n),
        Work.Thom.chernClass_succ_top']
      have hcont : Continuous (fun x : ↥(Work.Thom.zeroComplement (Work.Thom.realification F)) =>
          (⟨x, (x : (Work.Thom.realification F).TotalSpace).2⟩ :
            (Work.Thom.realification (Work.Thom.bundleComap F π)).TotalSpace)) := by
        rw [Work.Thom.realification_bundleComap]
        exact continuous_tautologicalSection (Z := Work.Thom.realification F)
      refine Work.Thom.ThomClass.eulerClass_eq_zero_of_nowhereZeroSection _
        ⟨fun x => ⟨x, (x : (Work.Thom.realification F).TotalSpace).2⟩, hcont⟩
        (fun x => rfl) (fun x => x.2)
    · rw [Work.Thom.chernClass_eq_zero_of_lt (Work.Thom.bundleComap F π) hgt,
        Work.Thom.chernClass_eq_zero_of_lt (Work.Thom.tautQuotient F) (by omega)]

end

end Work.Whitney
