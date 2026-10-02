import Mathlib
import Submission.Work.ThomBordism.Grassmann.p1RatAux
import Submission.Work.ThomBordism.Grassmann.chernReducedSetup
import Submission.Work.ThomBordism.Grassmann.chernRedU_vanishing
import Submission.Work.ThomBordism.Grassmann.chernRedV_vanishing
import Submission.Work.ThomBordism.Grassmann.chernRedUV_vanishing
import Submission.Work.LerayHirsch.mv2_exact
import Submission.Work.Cohomology.exists_smul_oneH
import Submission.Work.Gen.ChernGeneratorTwo
import Submission.Work.Projective.CP2Cohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# `1 ⊗ c₂(O(1) ⊕ O(-1)) ≠ 0` over `ℂP²`

The crux `Work.ThomBordism.Grassmann.chernReducedRatNeZero` of the GrAGen area: the reduced second
Chern class of `ℂ ⊗ O(1) = O(1) ⊕ O(-1)` over `ℂP²` survives rationalisation.

## The route

`c₂(E) = e(E_ℝ)` is the **top** Chern class of the rank-`2` complex bundle `E = chernRedE`
(`Work.Thom.chernClass_succ_top'`), i.e. the Euler class of the canonical Thom class of the rank-`4`
real bundle `chernRedW = realification chernRedE`.  The Gysin sequence of `chernRedW` reads

`H⁰(ℂP²) --∪e--> H⁴(ℂP²) → H⁴(chernRedX; ℤ) → H¹(ℂP²) = 0`,

so `e` generates `H⁴(ℂP²;ℤ) ≅ ℤ` as soon as `H⁴(chernRedX; ℤ) = 0`, where `chernRedX` is the
punctured total space of `chernRedW`.  The vanishing is the whole content: `chernRedX` is covered by
the two pieces

* `chernRedU = {first summand ≠ 0}` — a vector bundle over `S⁵` (`H⁴ = 0`),
* `chernRedV = {second summand ≠ 0}` — likewise (`H⁴ = 0`),

whose intersection `chernRedU ∩ chernRedV` is an `S¹ × S¹`-bundle over `S⁵` with `H³ = 0`; the
two-set Mayer–Vietoris sequence of `Work.LerayHirsch.mv2_exact` then gives `H⁴(chernRedX;ℤ) = 0`.

Finally `H⁴(ℂP²;ℤ) ≅ ℤ` (`Work.Cohomology.singularCohomology_four_cp2`, packaged in the area's
`cp2CohFourEquiv`), so a nonzero class survives `⊗ ℚ`.
-/

namespace Work.ThomBordism.Grassmann

/-! ### Local copies of the two general helpers the crux used to import

(defined here so that this module is self-contained; they are the general `ℤ`-module lemma and the
isomorphism `H⁴(ℂP²;ℤ) ≅ ℤ` from the Mayer–Vietoris computation.) -/

namespace P1Crux

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- `1 ⊗ x ≠ 0` in `M ⊗[ℤ] ℚ` when `M ≅ ℤ` and `x ≠ 0`. -/
theorem tmul_one_ne_zero_of_iso_int (e : M ≃ₗ[ℤ] ℤ) {x : M} (hx : x ≠ 0) :
    (1 : ℚ) ⊗ₜ[ℤ] x ≠ 0 := by
  intro h0
  have h1 : (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) e) ((1 : ℚ) ⊗ₜ[ℤ] x)
      = (1 : ℚ) ⊗ₜ[ℤ] (e x) := by
    rw [TensorProduct.congr_tmul]
    rfl
  have h3 : (1 : ℚ) ⊗ₜ[ℤ] (e x) = 0 := by
    rw [← h1, h0, map_zero]
  have h4 : ((e x : ℤ) : ℚ) = 0 := by
    have h5 := congrArg (TensorProduct.rid ℤ ℚ) h3
    rw [TensorProduct.rid_tmul, map_zero] at h5
    simpa using h5
  have h2 : e x = 0 := by exact_mod_cast h4
  exact hx (e.injective (by rw [h2, map_zero]))

/-- `H⁴(ℂP²;ℤ) ≃ₗ[ℤ] ℤ`, from the Mayer–Vietoris computation
`Work.Projective.singularCohomology_four_cp2`. -/
noncomputable def cp2CohFourEquiv :
    Work.Thom.Coh ℤ 4 (Work.Projective.CP 2) ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective (Classical.choice Work.Projective.singularCohomology_four_cp2).hom.hom
    ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
      (ModuleCat.epi_iff_surjective _).mp inferInstance⟩




open Work.TangentClasses
open CategoryTheory

noncomputable section

/-! ## 1. The complement of the zero section is open -/

/-- **The complement of the zero section of a real bundle is open.**  Locally in a chart
`Z.localTriv i` the condition `p.2 ≠ 0` becomes `(Z.coordChange _ i _ p.2) ≠ 0`, and the transition
functions are invertible. -/
theorem isOpen_zeroComplement {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) : IsOpen (Work.Thom.zeroComplement Z) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  set i := Z.indexAt p.1 with hi
  have hsource : p ∈ (Z.localTriv i).source := by
    rw [VectorBundleCore.mem_localTriv_source]
    exact Z.mem_baseSet_at p.1
  have hcont : ContinuousAt (fun q : Z.TotalSpace => ((Z.localTriv i) q).2) p :=
    ((Z.localTriv i).continuousOn.continuousAt
      ((Z.localTriv i).open_source.mem_nhds hsource)).snd
  have hfib : ((Z.localTriv i) p).2 = (show F from p.2) := by
    rw [VectorBundleCore.localTriv_apply]
    exact Z.coordChange_self i p.1 (Z.mem_baseSet_at p.1) (show F from p.2)
  have hpval : ((Z.localTriv i) p).2 ≠ 0 := by
    rw [hfib]
    exact hp
  filter_upwards [hcont.eventually (isOpen_ne.mem_nhds hpval)] with q hq
  intro hq0
  refine hq ?_
  rw [VectorBundleCore.localTriv_apply]
  simpa using congrArg (Z.coordChange (Z.indexAt q.1) i q.1) hq0

/-! ## 2. The two pieces of the cover are open -/

theorem isOpen_chernRedU : IsOpen chernRedU := by
  have hset : chernRedU = Subtype.val ⁻¹' ((fun p : chernRedW.TotalSpace =>
      (⟨p.1, Work.Whitney.NZ.fstC 1 p.2⟩ : chernRedW₁.TotalSpace)) ⁻¹'
        (Work.Thom.zeroComplement chernRedW₁)) := by
    ext p
    rw [chernRedU_mem_iff, Set.mem_preimage, Set.mem_preimage, Work.Thom.mem_zeroComplement_mk]
    constructor
    · intro hp hzero
      exact hp ((chernRedFstC_eq_zero_iff (chernRedFib p.1)).mp hzero)
    · intro hp hzero
      exact hp ((chernRedFstC_eq_zero_iff (chernRedFib p.1)).mpr hzero)
  rw [hset]
  exact ((isOpen_zeroComplement chernRedW₁).preimage continuous_fstC_totalMap_W).preimage
    continuous_subtype_val

theorem isOpen_chernRedV : IsOpen chernRedV := by
  have hset : chernRedV = Subtype.val ⁻¹' ((fun p : chernRedW.TotalSpace =>
      (⟨p.1, Work.Whitney.NZ.sndC 1 p.2⟩ : (Work.Thom.realification
        (Work.Gen.tautLine 2)).TotalSpace)) ⁻¹'
        (Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautLine 2)))) := by
    ext p
    rw [chernRedV_mem_iff, Set.mem_preimage, Set.mem_preimage, Work.Thom.mem_zeroComplement_mk]
    constructor
    · intro hp hzero
      exact hp ((chernRedSndC_eq_zero_iff (chernRedFib p.1)).mp hzero)
    · intro hp hzero
      exact hp ((chernRedSndC_eq_zero_iff (chernRedFib p.1)).mpr hzero)
  rw [hset]
  exact ((isOpen_zeroComplement (Work.Thom.realification (Work.Gen.tautLine 2))).preimage
    continuous_sndC_totalMap_W).preimage continuous_subtype_val

/-! ## 3. The Mayer–Vietoris reduction of `H⁴(chernRedX) = 0` -/

/-- **`H⁴` of the punctured total space of `chernRedW` vanishes**, from the vanishing on the two
pieces of the cover and on their intersection (the two-set Mayer–Vietoris sequence is exact,
`Work.LerayHirsch.mv2_exact`). -/
theorem subsingleton_chernRedX_of_pieces
    (hU : Subsingleton (Work.Thom.Coh ℤ 4 ↥chernRedU))
    (hV : Subsingleton (Work.Thom.Coh ℤ 4 ↥chernRedV))
    (hUV : Subsingleton (Work.Thom.Coh ℤ 3 ↥(chernRedU ∩ chernRedV))) :
    Subsingleton (Work.Thom.Coh ℤ 4 ↥chernRedX) := by
  have hcov := chernRedU_union_chernRedV
  have hex := Work.LerayHirsch.mv2_exact chernRedU chernRedV isOpen_chernRedU isOpen_chernRedV hcov
  -- the connecting map in degree `3` is zero
  have hδ : (Work.LerayHirsch.mv2δ chernRedU chernRedV isOpen_chernRedU isOpen_chernRedV hcov
      3).hom = 0 := by
    refine LinearMap.ext fun x => ?_
    haveI : Subsingleton ↥(Work.Thom.Coh ℤ 3 ↥(chernRedU ∩ chernRedV)) := hUV
    rw [Subsingleton.elim x 0]; simp
  have hδrange : (Work.LerayHirsch.mv2δ chernRedU chernRedV isOpen_chernRedU isOpen_chernRedV hcov
      3).hom.range = ⊥ := by rw [hδ, LinearMap.range_zero]
  -- the Mayer–Vietoris map in degree `4` is zero (its target is a subsingleton)
  have hFzero : Work.LerayHirsch.mv2F chernRedU chernRedV 4 = 0 := by
    apply CategoryTheory.Limits.biprod.hom_ext
    · rw [Work.LerayHirsch.mv2F_comp_fst, CategoryTheory.Limits.zero_comp]
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => ?_
      haveI : Subsingleton ↥(Work.Thom.Coh ℤ 4 ↥chernRedU) := hU
      exact Subsingleton.elim _ _
    · rw [Work.LerayHirsch.mv2F_comp_snd, CategoryTheory.Limits.zero_comp]
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => ?_
      haveI : Subsingleton ↥(Work.Thom.Coh ℤ 4 ↥chernRedV) := hV
      exact Subsingleton.elim _ _
  have hFker : (Work.LerayHirsch.mv2F chernRedU chernRedV 4).hom.ker = ⊤ := by
    rw [hFzero]; simp
  have hbot : (⊥ : Submodule ℤ ↥(Work.Thom.Coh ℤ 4 ↥chernRedX)) = ⊤ := by
    have hker := hex.2.2.1 3
    rw [hδrange, hFker] at hker
    exact hker
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    have hmem : a ∈ (⊥ : Submodule ℤ ↥(Work.Thom.Coh ℤ 4 ↥chernRedX)) := by
      rw [hbot]; trivial
    simpa using hmem
  have hb : b = 0 := by
    have hmem : b ∈ (⊥ : Submodule ℤ ↥(Work.Thom.Coh ℤ 4 ↥chernRedX)) := by
      rw [hbot]; trivial
    simpa using hmem
  rw [ha, hb]

/-! ## 4. The Gysin sequence: the canonical Euler class of `chernRedW` is nonzero -/

/-- **The canonical Thom class of `chernRedW = realification chernRedE`** (rank `4 = 2 · 2`): the
Thom class of the complex rank-`2` bundle `chernRedE`, whose Euler class is the top Chern class. -/
noncomputable def chernRedT : Work.Thom.ThomClass chernRedW 4 :=
  Work.Thom.thomClassRank 2 (by norm_num : 1 ≤ 2) chernRedE

/-- **The Euler class of the canonical Thom class of `chernRedW = realification chernRedE` is
nonzero.**  The Gysin sequence `H⁰(ℂP²) --∪e--> H⁴(ℂP²) → H⁴(chernRedX) → H¹(ℂP²) = 0` shows that
`e` generates `H⁴(ℂP²;ℤ)` once `H⁴(chernRedX) = 0`, and `H⁴(ℂP²;ℤ) ≅ ℤ` is nontrivial
(`cp2CohFourEquiv`). -/
theorem eulerClass_thomClassRank_ne_zero
    (hX : Subsingleton (Work.Thom.Coh ℤ 4 ↥chernRedX)) :
    chernRedT.eulerClass ≠ 0 := by
  haveI := hX
  have hsurj : Function.Surjective (Work.Thom.gysinEuler chernRedT 0) := by
    rw [← Set.range_eq_univ, Work.Thom.gysin_exact_at_base]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have he : Work.Thom.gysinEuler chernRedT 0
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (Work.Projective.CP 2))))
      = chernRedT.eulerClass := by
    rw [Work.Thom.gysinEuler_eq_cupEuler, Work.Cohomology.cupH'_one_left]
  have h0 : Submodule.span ℤ
      {Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (Work.Projective.CP 2)))} = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun x => ?_
    rw [Submodule.mem_span_singleton]
    haveI : PathConnectedSpace ↥(TopCat.of (Work.Projective.CP 2)) :=
      Work.Projective.pathConnectedSpace_CP 2
    obtain ⟨m, hm⟩ := Work.Cohomology.exists_smul_oneH (TopCat.of (Work.Projective.CP 2)) x
    refine ⟨m, ?_⟩
    rw [hm]
    exact int_smul_eq_zsmul (inferInstance : Module ℤ (Work.Thom.Coh ℤ 0 (Work.Projective.CP 2)))
      m (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (Work.Projective.CP 2))))
  have hgen : Submodule.span ℤ {chernRedT.eulerClass} = ⊤ := by
    have h := Work.Gen.span_singleton_map_eq_top' (Work.Thom.gysinEuler chernRedT 0) hsurj
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (Work.Projective.CP 2)))) h0
    rwa [he] at h
  intro hzero
  rw [hzero, Submodule.span_zero_singleton] at hgen
  haveI hsub : Subsingleton (Work.Thom.Coh ℤ 4 (Work.Projective.CP 2)) :=
    ⟨fun a b => by
      have ha : a ∈ (⊥ : Submodule ℤ (Work.Thom.Coh ℤ 4 (Work.Projective.CP 2))) := by
        rw [hgen]; trivial
      have hb : b ∈ (⊥ : Submodule ℤ (Work.Thom.Coh ℤ 4 (Work.Projective.CP 2))) := by
        rw [hgen]; trivial
      rw [Submodule.mem_bot] at ha hb
      rw [ha, hb]⟩
  exact Int.zero_ne_one (by
    have h' : cp2CohFourEquiv.symm (0 : ℤ) = cp2CohFourEquiv.symm 1 := Subsingleton.elim _ _
    simpa using congrArg (⇑cp2CohFourEquiv) h')

/-! ## 5. The top Chern class of `O(1) ⊕ O(-1)` is nonzero, and survives rationalisation -/

/-- **`c₂(O(1) ⊕ O(-1)) ≠ 0` in `H⁴(ℂP²;ℤ)`.** -/
theorem chernClass_two_two_ne_zero (hX : Subsingleton (Work.Thom.Coh ℤ 4 ↥chernRedX)) :
    Work.Thom.chernClass 2 2 chernRedE ≠ 0 := by
  have h : Work.Thom.chernClass (1 + 1) (1 + 1) chernRedE ≠ 0 := by
    rw [Work.Thom.chernClass_succ_top']
    exact eulerClass_thomClassRank_ne_zero hX
  exact h

/-- **The rationalised reduced second Chern class of `O(1) ⊕ O(-1)` is nonzero**, from
`H⁴(ℂP²;ℤ) ≅ ℤ`. -/
theorem chernReducedRatNeZero_of_ne_zero (h : Work.Thom.chernClass 2 2 chernRedE ≠ 0) :
    (1 : ℚ) ⊗ₜ[ℤ] (Work.Thom.chernClass 2 2
      (Work.Whitney.whitneySum (Work.Gen.tautDual 2) (Work.Gen.tautLine 2))) ≠ 0 :=
  tmul_one_ne_zero_of_iso_int cp2CohFourEquiv h

/-! ## 6. The crux -/

/-- **The reduced second Chern class of `O(1) ⊕ O(-1)` over `ℂP²` survives rationalisation.** -/
theorem chernReducedRatNeZero :
    (1 : ℚ) ⊗ₜ[ℤ] (Work.Thom.chernClass 2 2
        (Work.Whitney.whitneySum (Work.Gen.tautDual 2) (Work.Gen.tautLine 2)))
      ≠ 0 :=
  chernReducedRatNeZero_of_ne_zero
    (chernClass_two_two_ne_zero
      (subsingleton_chernRedX_of_pieces chernRedU_vanishing chernRedV_vanishing
        chernRedUV_vanishing))

end

end P1Crux
end Work.ThomBordism.Grassmann