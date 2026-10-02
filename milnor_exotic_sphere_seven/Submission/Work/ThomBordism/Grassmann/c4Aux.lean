import Mathlib
import Submission.Work.Gen.Basic
import Submission.Work.Gen.EulerDefs
import Submission.Work.Gen.uSqGenerates
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.p1RatAux
import Submission.Work.ThomBordism.Grassmann.p1CruxRatNeZero
import Submission.Work.Projective.CP4Concrete
import Submission.Work.Cohomology.exists_smul_oneH
import Submission.Work.Projective.pathConnectedSpace_CP
import Submission.Work.Thom.Gysin
import Submission.Work.LerayHirsch.mv2_exact
import Submission.Work.ThomBordism.Grassmann.subsingleton_zeroComplement_tautLineFour
import Submission.Work.ThomBordism.Grassmann.zeroComplementSum
import Submission.Work.ThomBordism.Grassmann.isOpen_pieceFst_pieceSnd
import Submission.Work.ThomBordism.Grassmann.subsingleton_zeroComplementSumPieces

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# Auxiliary material for `Work.ThomBordism.Grassmann.c4_tautSum4_CP4_rat_ne_zero`

The target is `1 ⊗ c₄((O(1) ⊕ O(-1)) ⊕ (O(1) ⊕ O(-1))) ≠ 0` over `ℂP⁴`, i.e. the non-vanishing of
the Euler class `e = c₄(E) = e(E_ℝ)` of the rank-`8` real bundle `E_ℝ` obtained by realifying the
rank-`4` complex bundle `E = lineC 4 ⊕ lineC 4` (`Work.Gen.lineC n = O(1) ⊕ O(-1)`).

Since `chernClass 4 4 E = e` is the **top** Chern class (`Work.Thom.chernClass_succ_top'`), the
statement is the vanishing criterion for the Euler class of a real bundle:

  `e ≠ 0` as soon as `H⁸(zeroComplement E_ℝ; ℤ) = 0` (the Gysin sequence `∪e` of the rank-`8`
  bundle `E_ℝ` over `ℂP⁴` is onto `H⁸(ℂP⁴)`, since `e = ∪e(1)` generates it).

The vanishing `H⁸(zeroComplement E_ℝ) = 0` is reduced, by the Mayer–Vietoris lemma
`subsingleton_zeroComplement_whitneySum`, to the vanishings of the punctured spaces of the rank-`2`
and rank-`4` bundles `O(±1)` and `O(1) ⊕ O(-1)`, and those to the known vanishing
`H^k(zeroComplement (realification (tautDual 4))) = 0` for `k ≠ 0, 9`
(`Work.Gen.uSqGen_puncturedTautDual4HZero`) together with the `tautLine` companion.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

/-- `O(1) = Work.Gen.tautDual 4` over `ℂP⁴`. -/
abbrev tautDual4 : VectorBundleCore ℂ (Work.Projective.CP 4) (EuclideanSpace ℂ (Fin 1))
    (Fin 5) := Work.Gen.tautDual 4

/-- `O(-1) = Work.Gen.tautLine 4` over `ℂP⁴`. -/
abbrev tautLine4 : VectorBundleCore ℂ (Work.Projective.CP 4) (EuclideanSpace ℂ (Fin 1))
    (Fin 5) := Work.Gen.tautLine 4

/-- `lineC 4 = O(1) ⊕ O(-1) = ℂ ⊗ O(1)`, the rank-`2` complex bundle of the statement. -/
abbrev lineC4 : VectorBundleCore ℂ (Work.Projective.CP 4) (EuclideanSpace ℂ (Fin 2))
    (Fin 5 × Fin 5) := Work.Gen.lineC 4

/-- The rank-`4` complex bundle `E = lineC 4 ⊕ lineC 4` of the statement. -/
abbrev tautSum4 : VectorBundleCore ℂ (Work.Projective.CP 4) (EuclideanSpace ℂ (Fin 4))
    ((Fin 5 × Fin 5) × (Fin 5 × Fin 5)) :=
  Work.Whitney.whitneySum lineC4 lineC4

/-! ## The known vanishing for the punctured `O(1)` -/

/-- **`H^k` of the punctured total space of `realification (tautDual 4)` vanishes** off the degrees
`0` and `9`. -/
theorem tautDual4_puncture_vanish (k : ℕ) (hk0 : k ≠ 0) (hk9 : k ≠ 9) :
    Subsingleton (Work.Thom.Coh ℤ k
      ↥(Work.Thom.zeroComplement (Work.Thom.realification tautDual4))) :=
  ModuleCat.subsingleton_of_isZero (Work.Gen.uSqGen_puncturedTautDual4HZero k hk0 hk9)

/-! ## The topological input: the vanishing for the punctured `O(-1)` -/

/-- **`H^k` of the punctured total space of `realification (tautLine 4)` vanishes** off the degrees
`0` and `9`; the punctured space is `{(x,λ) : λ ∈ L_x^*, λ ≠ 0} ≅ ℂ⁵∖{0} ≃ S⁹`. -/
theorem tautLine4_puncture_vanish (k : ℕ) (hk0 : k ≠ 0) (hk9 : k ≠ 9) :
    Subsingleton (Work.Thom.Coh ℤ k
      ↥(Work.Thom.zeroComplement (Work.Thom.realification tautLine4))) :=
  subsingleton_zeroComplement_tautLineFour k hk0 hk9

/-! ## The Mayer–Vietoris input for punctured sums -/

/-- **`H^m` of the zero complement of a direct sum of complex bundles vanishes** when the four
hypotheses of `Work.ThomBordism.Grassmann.subsingleton_zeroComplement_whitneySum` hold. -/
theorem zeroComplement_whitneySum_vanish
    {B : Type} [TopologicalSpace B] {a b : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) (m : ℕ) (hm : 1 ≤ m)
    (hA : Subsingleton (Work.Thom.Coh ℤ m
      ↥(Work.Thom.zeroComplement (Work.Thom.realification A))))
    (hA₁ : Subsingleton (Work.Thom.Coh ℤ (m - 1)
      ↥(Work.Thom.zeroComplement (Work.Thom.realification A))))
    (hA₂ : Subsingleton (Work.Thom.Coh ℤ (m - 2 * b)
      ↥(Work.Thom.zeroComplement (Work.Thom.realification A))))
    (hC : Subsingleton (Work.Thom.Coh ℤ m
      ↥(Work.Thom.zeroComplement (Work.Thom.realification C)))) :
    Subsingleton (Work.Thom.Coh ℤ m
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum A C)))) := by
  obtain ⟨h1, h2, h3⟩ := subsingleton_zeroComplementSumPieces A C m hA hA₁ hA₂ hC
  exact subsingleton_zeroComplementSum_of_pieces A C
    (isOpen_pieceFst_pieceSnd A C).1 (isOpen_pieceFst_pieceSnd A C).2 m hm h1 h2 h3

/-! ## The vanishings for the punctured `lineC 4` and for the bundle of the statement -/

/-- `H⁴` of the punctured `lineC 4` vanishes. -/
theorem lineC4_puncture_vanish_four :
    Subsingleton (Work.Thom.Coh ℤ 4
      ↥(Work.Thom.zeroComplement (Work.Thom.realification lineC4))) :=
  zeroComplement_whitneySum_vanish tautDual4 tautLine4 4 (by norm_num)
    (tautDual4_puncture_vanish 4 (by norm_num) (by norm_num))
    (tautDual4_puncture_vanish 3 (by norm_num) (by norm_num))
    (tautDual4_puncture_vanish 2 (by norm_num) (by norm_num))
    (tautLine4_puncture_vanish 4 (by norm_num) (by norm_num))

/-- `H⁵` of the punctured `lineC 4` vanishes. -/
theorem lineC4_puncture_vanish_five :
    Subsingleton (Work.Thom.Coh ℤ 5
      ↥(Work.Thom.zeroComplement (Work.Thom.realification lineC4))) :=
  zeroComplement_whitneySum_vanish tautDual4 tautLine4 5 (by norm_num)
    (tautDual4_puncture_vanish 5 (by norm_num) (by norm_num))
    (tautDual4_puncture_vanish 4 (by norm_num) (by norm_num))
    (tautDual4_puncture_vanish 3 (by norm_num) (by norm_num))
    (tautLine4_puncture_vanish 5 (by norm_num) (by norm_num))

/-- `H⁷` of the punctured `lineC 4` vanishes. -/
theorem lineC4_puncture_vanish_seven :
    Subsingleton (Work.Thom.Coh ℤ 7
      ↥(Work.Thom.zeroComplement (Work.Thom.realification lineC4))) :=
  zeroComplement_whitneySum_vanish tautDual4 tautLine4 7 (by norm_num)
    (tautDual4_puncture_vanish 7 (by norm_num) (by norm_num))
    (tautDual4_puncture_vanish 6 (by norm_num) (by norm_num))
    (tautDual4_puncture_vanish 5 (by norm_num) (by norm_num))
    (tautLine4_puncture_vanish 7 (by norm_num) (by norm_num))

/-- `H⁸` of the punctured `lineC 4` vanishes. -/
theorem lineC4_puncture_vanish_eight :
    Subsingleton (Work.Thom.Coh ℤ 8
      ↥(Work.Thom.zeroComplement (Work.Thom.realification lineC4))) :=
  zeroComplement_whitneySum_vanish tautDual4 tautLine4 8 (by norm_num)
    (tautDual4_puncture_vanish 8 (by norm_num) (by norm_num))
    (tautDual4_puncture_vanish 7 (by norm_num) (by norm_num))
    (tautDual4_puncture_vanish 6 (by norm_num) (by norm_num))
    (tautLine4_puncture_vanish 8 (by norm_num) (by norm_num))

/-- **`H⁸` of the punctured total space of the realification of the bundle `E = lineC 4 ⊕ lineC 4`
of the statement vanishes.** -/
theorem tautSum4_puncture_vanish_eight :
    Subsingleton (Work.Thom.Coh ℤ 8
      ↥(Work.Thom.zeroComplement (Work.Thom.realification tautSum4))) :=
  zeroComplement_whitneySum_vanish lineC4 lineC4 8 (by norm_num)
    lineC4_puncture_vanish_eight lineC4_puncture_vanish_seven
    lineC4_puncture_vanish_four lineC4_puncture_vanish_eight

/-! ## The Euler class of the statement's bundle -/

/-- The canonical Thom class of the rank-`8` real bundle underlying `E = tautSum4`. -/
noncomputable def tautSum4T : Work.Thom.ThomClass (Work.Thom.realification tautSum4) 8 :=
  Work.Thom.thomClassRank 4 (Nat.succ_le_succ (Nat.zero_le 3)) tautSum4

/-- **The top Chern class `c₄` of the statement's bundle is the Euler class of its realification.** -/
theorem chernClass_four_four_eq_euler :
    Work.Thom.chernClass 4 4 tautSum4 = tautSum4T.eulerClass :=
  Work.Thom.chernClass_succ_top' tautSum4

/-- `H⁸(ℂP⁴;ℤ) ≅ ℤ`. -/
noncomputable def cp4CohEightEquiv : Work.Thom.Coh ℤ 8 (Work.Projective.CP 4) ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective
    (Work.Projective.cpnCohIsoInt 4 8 ⟨by norm_num, by norm_num⟩).hom.hom
    ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
      (ModuleCat.epi_iff_surjective _).mp inferInstance⟩

/-- The image of a generator under a surjective linear map is a generator. -/
theorem span_singleton_map_eq_top {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) {x : M}
    (hx : Submodule.span ℤ {x} = ⊤) : Submodule.span ℤ {f x} = ⊤ := by
  have h1 : Submodule.map f (⊤ : Submodule ℤ M) = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top]
    exact hf
  have h2 : Submodule.map f (Submodule.span ℤ {x}) = Submodule.span ℤ {f x} := by
    rw [Submodule.map_span, Set.image_singleton]
  rw [← h2, hx, h1]

/-- **The Euler class of `tautSum4` is nonzero**, because the Gysin map `∪e` of the rank-`8` bundle
is onto `H⁸(ℂP⁴;ℤ) ≅ ℤ` as soon as `H⁸` of the punctured total space vanishes. -/
theorem tautSum4T_eulerClass_ne_zero
    (h : Subsingleton (Work.Thom.Coh ℤ 8
      ↥(Work.Thom.zeroComplement (Work.Thom.realification tautSum4)))) :
    tautSum4T.eulerClass ≠ 0 := by
  haveI := h
  have hsurj : Function.Surjective (Work.Thom.gysinEuler tautSum4T 0) := by
    rw [← Set.range_eq_univ, Work.Thom.gysin_exact_at_base]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have he : Work.Thom.gysinEuler tautSum4T 0
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (Work.Projective.CP 4))))
      = tautSum4T.eulerClass := by
    rw [Work.Thom.gysinEuler_eq_cupEuler, Work.Cohomology.cupH'_one_left]
  have h0 : Submodule.span ℤ
      {Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (Work.Projective.CP 4)))} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    rw [Submodule.mem_span_singleton]
    haveI : PathConnectedSpace ↥(TopCat.of (Work.Projective.CP 4)) :=
      Work.Projective.pathConnectedSpace_CP 4
    obtain ⟨m, hm⟩ := Work.Cohomology.exists_smul_oneH (TopCat.of (Work.Projective.CP 4)) x
    refine ⟨m, ?_⟩
    rw [hm]
    exact int_smul_eq_zsmul (inferInstance : Module ℤ
      (Work.Thom.Coh ℤ 0 (Work.Projective.CP 4))) m
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (Work.Projective.CP 4))))
  have hgen : Submodule.span ℤ {tautSum4T.eulerClass} = ⊤ := by
    have hsp : Submodule.span ℤ
        {((Work.Thom.gysinEuler tautSum4T 0)
          (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (Work.Projective.CP 4)))))} = ⊤ :=
      span_singleton_map_eq_top (Work.Thom.gysinEuler tautSum4T 0) hsurj h0
    rwa [he] at hsp
  intro hzero
  have hbot : (⊤ : Submodule ℤ (Work.Thom.Coh ℤ 8 (Work.Projective.CP 4))) = ⊥ :=
    hgen.symm.trans (by rw [hzero]; exact Submodule.span_zero_singleton ℤ)
  haveI hsub : Subsingleton (Work.Thom.Coh ℤ 8 (Work.Projective.CP 4)) :=
    ⟨fun a b => by
      have ha : a = 0 := (Submodule.mem_bot ℤ).mp (hbot ▸ Submodule.mem_top)
      have hb : b = 0 := (Submodule.mem_bot ℤ).mp (hbot ▸ Submodule.mem_top)
      rw [ha, hb]⟩
  have h01 : ((0 : ℤ) = 1) := by
    have h := Subsingleton.elim (cp4CohEightEquiv.symm (0 : ℤ)) (cp4CohEightEquiv.symm 1)
    simpa using congrArg (⇑cp4CohEightEquiv) h
  exact Int.zero_ne_one h01

/-- **The rationalised top Chern class `c₄` of the statement's bundle is nonzero.** -/
theorem c4_tautSum4_rat_ne_zero_aux :
    (1 : ℚ) ⊗ₜ[ℤ] (Work.Thom.chernClass 4 4 tautSum4) ≠ 0 := by
  rw [chernClass_four_four_eq_euler]
  exact P1Crux.tmul_one_ne_zero_of_iso_int cp4CohEightEquiv
    (tautSum4T_eulerClass_ne_zero tautSum4_puncture_vanish_eight)

end

end Work.ThomBordism.Grassmann
