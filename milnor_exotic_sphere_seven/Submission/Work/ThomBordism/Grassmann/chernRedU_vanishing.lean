import Mathlib
import Submission.Work.ThomBordism.Grassmann.chernReducedSetup
import Submission.Work.Gen.ConjIso
import Submission.Work.Gen.tautDual_iso_conjLine
import Submission.Work.Thom.coreMorphism
import Submission.Work.Thom.LineGeom
import Submission.Work.Thom.sphereInDisc_homotopyEquiv
import Submission.Work.Thom.exists_rhoC_compat

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
# `H⁴` of the piece `{first coordinate ≠ 0}` of the cover of `E ∖ 0`

This is the first-summand companion of `Submission/Work/ThomBordism/Grassmann/
chernRedV_vanishing.lean`: it proves

  `Subsingleton (H⁴(chernRedU; ℤ))`,

where `chernRedU = {p ∈ (O(1) ⊕ O(-1)) ∖ 0 : the O(1)-component of p is ≠ 0}`.

The proof is the mirror image of the `O(-1)` case: the first-summand projection
`⟨b,(x,y)⟩ ↦ ⟨b,x⟩` is a homotopy equivalence onto `zeroComplement (realification (tautDual 2)) ≃ S⁵`
(with inverse the first-summand inclusion `⟨b,x⟩ ↦ ⟨b,(x,0)⟩`), and `H⁴` of the latter vanishes by
`Work.Gen.puncturedTautDualTwoHZero`.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

/-! ## 1. The punctured total space of the first summand -/

/-- The realification of the first summand `O(1) = tautDual 2` of `chernRedE`. -/
abbrev chernRedW₁ : RealBundle (Work.Projective.CP 2) (EuclideanSpace ℂ (Fin 1)) (Fin 3) :=
  Work.Thom.realification (Work.Gen.tautDual 2)

/-- A homotopy equivalence induces an isomorphism on cohomology, hence transports `Subsingleton`. -/
theorem subsingleton_cohomology_of_homotopyEquiv' {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ)
    (h : Subsingleton (Work.Thom.Coh ℤ n X)) : Subsingleton (Work.Thom.Coh ℤ n Y) := by
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv e n
  have hsurj : Function.Surjective ⇑(iso.hom) :=
    (ModuleCat.epi_iff_surjective iso.hom).mp inferInstance
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    rw [h.elim a' b']⟩

/-- **`H⁴` of the punctured total space of the first summand `O(1)` vanishes.** -/
theorem subsingleton_zeroComplement_firstSummand :
    Subsingleton (Work.Thom.Coh ℤ 4 ↥(Work.Thom.zeroComplement chernRedW₁)) :=
  ModuleCat.subsingleton_of_isZero (puncturedTautDualTwoHZero 4 (by norm_num) (by norm_num))

/-! ## 2. The splitting of the model fibre `ℂ² = ℂ¹ ⊕ ℂ¹` -/

/-- The inclusion of the first summand `ℂ¹ → ℂ¹ ⊕ ℂ¹ = ℂ²` of the model fibre. -/
noncomputable def chernRedInclC₁ : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (Work.Whitney.sumFibreC 1 1 : (EuclideanSpace ℂ (Fin 1) × EuclideanSpace ℂ (Fin 1)) →L[ℂ]
      EuclideanSpace ℂ (Fin 2)).comp
    ((ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))).prod
      (0 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)))

/-- The fibre of `chernRedW₁` at a point, as an element of the model fibre. -/
def chernRedFib₁ (q : chernRedW₁.TotalSpace) : EuclideanSpace ℂ (Fin 1) := q.2

theorem chernRedInclC₁_apply (t : EuclideanSpace ℂ (Fin 1)) :
    chernRedInclC₁ t = Work.Whitney.sumFibreC 1 1 (t, 0) := by
  simp only [chernRedInclC₁, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply]
  rfl

/-- The first summand projection of the first summand inclusion is the identity. -/
theorem chernRedFstC_inclC₁ (t : EuclideanSpace ℂ (Fin 1)) :
    Work.Whitney.NZ.fstC 1 (chernRedInclC₁ t) = t := by
  rw [chernRedInclC₁_apply, Work.Whitney.NZ.fstC_sumFibreC]

/-- The zero-th coordinate of `fstC 1 v` is the zero-th coordinate of `v`. -/
theorem chernRedFstC_apply_eq (v : EuclideanSpace ℂ (Fin 2)) :
    (Work.Whitney.NZ.fstC 1 v).ofLp 0 = v.ofLp 0 := by
  have h1 : (Work.Whitney.NZ.fstC 1 v).ofLp 0
      = v.ofLp (finSumFinEquiv (m := 1) (n := 1) (Sum.inl (0 : Fin 1))) := by
    show (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := 1) (m := 1) v).1.ofLp 0 = _
    rw [Work.Thom.finAddEquivProd_fst]
  rw [h1, show finSumFinEquiv (m := 1) (n := 1) (Sum.inl (0 : Fin 1)) = (0 : Fin 2) from by
    rw [finSumFinEquiv_apply_left]; rfl]

/-- The zero-th coordinate of `chernRedInclC₁ t` is the zero-th coordinate of `t`. -/
theorem chernRedInclC₁_ofLp_zero (t : EuclideanSpace ℂ (Fin 1)) :
    (chernRedInclC₁ t).ofLp 0 = t.ofLp 0 := by
  rw [chernRedInclC₁_apply]
  have h := Work.Thom.finAddEquivProd_symm_apply_inl (𝕜 := ℂ) (n := 1) (m := 1)
    t (0 : EuclideanSpace ℂ (Fin 1)) 0
  rw [show finSumFinEquiv (Sum.inl (0 : Fin 1)) = (0 : Fin 2) from by
    rw [finSumFinEquiv_apply_left]; rfl] at h
  exact h

/-- `fstC 1 v = 0` iff the zero-th coordinate of `v` vanishes. -/
theorem chernRedFstC_eq_zero_iff (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Whitney.NZ.fstC 1 v = 0 ↔ v.ofLp 0 = 0 := by
  constructor
  · intro h
    have h1 := chernRedFstC_apply_eq v
    rw [h] at h1
    simpa using h1.symm
  · intro h
    have h1 := chernRedFstC_apply_eq v
    rw [h] at h1
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    simpa using h1

/-- The zero-th coordinate of `chernRedInclC₁ t` vanishes iff `t` does. -/
theorem chernRedInclC₁_ofLp_zero_eq_zero_iff (t : EuclideanSpace ℂ (Fin 1)) :
    (chernRedInclC₁ t).ofLp 0 = 0 ↔ t = 0 := by
  rw [chernRedInclC₁_ofLp_zero]
  constructor
  · intro h
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    simpa using h
  · intro h
    rw [h]
    rfl

/-- The straight-line combination `(1-t)·Incl(fstC v) + t·v` of the model fibre. -/
def chernRedHomotopyVec₁ (t : ℝ) (v : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  (1 - t) • (chernRedInclC₁ (Work.Whitney.NZ.fstC 1 v)) + t • v

/-- Its zero-th coordinate is that of `v`. -/
theorem chernRedHomotopyVec₁_ofLp_zero (t : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    (chernRedHomotopyVec₁ t v).ofLp 0 = v.ofLp 0 := by
  have h : (chernRedInclC₁ (Work.Whitney.NZ.fstC 1 v)).ofLp 0 = v.ofLp 0 := by
    rw [chernRedInclC₁_ofLp_zero, chernRedFstC_apply_eq]
  simp only [chernRedHomotopyVec₁, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
    Pi.smul_apply, h, ← add_smul, sub_add_cancel, one_smul]

/-! ## 3. The transition functions of `chernRedE` against the two components -/

theorem chernRedE_coordChange_apply' (i j : Fin 3 × Fin 3) (b : Work.Projective.CP 2)
    (v : EuclideanSpace ℂ (Fin 2)) :
    chernRedE.coordChange i j b v
      = Work.Whitney.sumFibreC 1 1
          ((Work.Gen.homCoord 2 j.1 i.1 b) • (Work.Whitney.NZ.fstC 1 v),
           (Work.Gen.homCoord 2 i.2 j.2 b) • (Work.Whitney.NZ.sndC 1 v)) := by
  simp only [Work.Whitney.whitneySum_coordChange, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.coe_prodMap',
    Work.Gen.tautDual_coordChange, Work.Gen.tautLine_coordChange,
    Work.Whitney.NZ.fstC, Work.Whitney.NZ.sndC, ContinuousLinearMap.comp_apply]
  rw [Prod.map_apply]
  simp only [smul_apply, ContinuousLinearMap.id_apply]
  rfl

/-- `fstC 1` absorbs the transition function of `chernRedE`. -/
theorem chernRedFstC_chernRedE_coordChange (i j : Fin 3 × Fin 3) (b : Work.Projective.CP 2)
    (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Whitney.NZ.fstC 1 (chernRedE.coordChange i j b v)
      = Work.Gen.homCoord 2 j.1 i.1 b • Work.Whitney.NZ.fstC 1 v := by
  rw [chernRedE_coordChange_apply', Work.Whitney.NZ.fstC_sumFibreC]

/-- The inclusion of the first summand is equivariant for the transition functions. -/
theorem chernRedE_coordChange_apply_inclC₁ (i j : Fin 3 × Fin 3) (b : Work.Projective.CP 2)
    (t : EuclideanSpace ℂ (Fin 1)) :
    chernRedE.coordChange i j b (chernRedInclC₁ t)
      = Work.Gen.homCoord 2 j.1 i.1 b • chernRedInclC₁ t := by
  rw [chernRedE_coordChange_apply', chernRedInclC₁_apply, Work.Whitney.NZ.fstC_sumFibreC,
    Work.Whitney.NZ.sndC_sumFibreC]
  rw [show ((Work.Gen.homCoord 2 j.1 i.1 b) • t,
        (Work.Gen.homCoord 2 i.2 j.2 b) • (0 : EuclideanSpace ℂ (Fin 1)))
      = (Work.Gen.homCoord 2 j.1 i.1 b) • (t, (0 : EuclideanSpace ℂ (Fin 1))) from by simp,
    map_smul]

/-- The composite transition function ending on the first summand. -/
theorem composite_fst_eq (i₁ : Fin 3 × Fin 3) (i₂ : Fin 3) (b : Work.Projective.CP 2)
    (h₁ : b ∈ chernRedE.baseSet i₁) (h₂ : b ∈ (Work.Gen.tautDual 2).baseSet i₂) :
    ((Work.Gen.tautDual 2).coordChange ((Work.Gen.tautDual 2).indexAt b) i₂ b).comp
      ((Work.Whitney.NZ.fstC 1).comp (chernRedE.coordChange i₁ (chernRedE.indexAt b) b))
    = (Work.Gen.homCoord 2 i₂ i₁.1 b) • (Work.Whitney.NZ.fstC 1) := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Work.Gen.tautDual_coordChange, smul_apply, ContinuousLinearMap.id_apply,
    chernRedFstC_chernRedE_coordChange, smul_apply, smul_smul, mul_comm]
  congr 1
  exact (Work.Gen.homCoord_mul i₂ (chernRedE.indexAt b).1 i₁.1
    h₂ ((Work.Gen.tautDual 2).mem_baseSet_at b) h₁.1).symm

/-- The composite transition function ending on the first summand (inclusion form). -/
theorem composite_incl₁_eq (i₁ : Fin 3) (i₂ : Fin 3 × Fin 3) (b : Work.Projective.CP 2)
    (h₁ : b ∈ (Work.Gen.tautDual 2).baseSet i₁) (h₂ : b ∈ chernRedE.baseSet i₂) :
    (chernRedE.coordChange (chernRedE.indexAt b) i₂ b).comp
      (chernRedInclC₁.comp ((Work.Gen.tautDual 2).coordChange i₁
        ((Work.Gen.tautDual 2).indexAt b) b))
    = (Work.Gen.homCoord 2 i₂.1 i₁ b) • chernRedInclC₁ := by
  refine ContinuousLinearMap.ext (fun t => ?_)
  show chernRedE.coordChange (chernRedE.indexAt b) i₂ b
      (chernRedInclC₁ (((Work.Gen.tautDual 2).coordChange i₁
        (chernRedE.indexAt b).1 b) t)) = Work.Gen.homCoord 2 i₂.1 i₁ b • chernRedInclC₁ t
  rw [Work.Gen.tautDual_coordChange, smul_apply, ContinuousLinearMap.id_apply]
  rw [map_smul, chernRedInclC₁_apply]
  rw [chernRedE_coordChange_apply']
  simp only [map_smul, Work.Whitney.NZ.fstC_sumFibreC, Work.Whitney.NZ.sndC_sumFibreC]
  rw [← map_smul]
  congr 1
  rw [Prod.smul_mk, Prod.mk.injEq]
  constructor
  · rw [smul_smul, mul_comm]
    congr 1
    exact (Work.Gen.homCoord_mul i₂.1 (chernRedE.indexAt b).1 i₁
      h₂.1 ((Work.Gen.tautDual 2).mem_baseSet_at b) h₁).symm
  · simp

/-! ## 4. Continuity of the two total-space maps -/

theorem continuousOn_composite_fst (i₁ : Fin 3 × Fin 3) (i₂ : Fin 3) :
    ContinuousOn (fun b : Work.Projective.CP 2 =>
      ((Work.Gen.tautDual 2).coordChange ((Work.Gen.tautDual 2).indexAt b) i₂ b).comp
        ((Work.Whitney.NZ.fstC 1).comp (chernRedE.coordChange i₁ (chernRedE.indexAt b) b)))
      (chernRedE.baseSet i₁ ∩ (Work.Gen.tautDual 2).baseSet i₂) := by
  have hconst : ContinuousOn (fun _ : Work.Projective.CP 2 => (Work.Whitney.NZ.fstC 1 :
      EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 1)))
      (chernRedE.baseSet i₁ ∩ (Work.Gen.tautDual 2).baseSet i₂) := continuousOn_const
  have hhom : ContinuousOn (fun b : Work.Projective.CP 2 => Work.Gen.homCoord 2 i₂ i₁.1 b)
      (chernRedE.baseSet i₁ ∩ (Work.Gen.tautDual 2).baseSet i₂) :=
    (Work.Gen.continuousOn_homCoord (n := 2) i₂ i₁.1).mono (fun b hb => hb.2)
  exact ContinuousOn.congr (hhom.smul hconst)
    (fun b hb => composite_fst_eq i₁ i₂ b hb.1 hb.2)

theorem continuousOn_composite_incl₁ (i₁ : Fin 3) (i₂ : Fin 3 × Fin 3) :
    ContinuousOn (fun b : Work.Projective.CP 2 =>
      (chernRedE.coordChange (chernRedE.indexAt b) i₂ b).comp
        (chernRedInclC₁.comp ((Work.Gen.tautDual 2).coordChange i₁
          ((Work.Gen.tautDual 2).indexAt b) b)))
      ((Work.Gen.tautDual 2).baseSet i₁ ∩ chernRedE.baseSet i₂) := by
  have hconst : ContinuousOn (fun _ : Work.Projective.CP 2 => (chernRedInclC₁ :
      EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
      ((Work.Gen.tautDual 2).baseSet i₁ ∩ chernRedE.baseSet i₂) := continuousOn_const
  have hhom : ContinuousOn (fun b : Work.Projective.CP 2 => Work.Gen.homCoord 2 i₂.1 i₁ b)
      ((Work.Gen.tautDual 2).baseSet i₁ ∩ chernRedE.baseSet i₂) :=
    (Work.Gen.continuousOn_homCoord (n := 2) i₂.1 i₁).mono (fun b hb => hb.2.1)
  exact ContinuousOn.congr (hhom.smul hconst)
    (fun b hb => composite_incl₁_eq i₁ i₂ b hb.1 hb.2)

/-- The first-summand projection of `chernRedE`, as a map of total spaces. -/
theorem continuous_fstC_totalMap :
    Continuous (fun p : chernRedE.TotalSpace =>
      (⟨p.1, Work.Whitney.NZ.fstC 1 p.2⟩ : (Work.Gen.tautDual 2).TotalSpace)) :=
  Work.Thom.continuous_totalSpaceMap_clm chernRedE (Work.Gen.tautDual 2) (ContinuousMap.id _)
    (fun _ => Work.Whitney.NZ.fstC 1)
    (fun i₁ i₂ => by
      rw [show (⇑(ContinuousMap.id (Work.Projective.CP 2))) = (id : Work.Projective.CP 2 →
        Work.Projective.CP 2) from rfl, Set.preimage_id]
      exact continuousOn_composite_fst i₁ i₂)

/-- The inclusion of the first summand, as a map of total spaces. -/
theorem continuous_inclC₁_totalMap :
    Continuous (fun p : (Work.Gen.tautDual 2).TotalSpace =>
      (⟨p.1, chernRedInclC₁ p.2⟩ : chernRedE.TotalSpace)) :=
  Work.Thom.continuous_totalSpaceMap_clm (Work.Gen.tautDual 2) chernRedE (ContinuousMap.id _)
    (fun _ => chernRedInclC₁)
    (fun i₁ i₂ => by
      rw [show (⇑(ContinuousMap.id (Work.Projective.CP 2))) = (id : Work.Projective.CP 2 →
        Work.Projective.CP 2) from rfl, Set.preimage_id]
      exact continuousOn_composite_incl₁ i₁ i₂)

/-- The first-summand projection of `chernRedW`, as a map of total spaces. -/
theorem continuous_fstC_totalMap_W :
    Continuous (fun p : chernRedW.TotalSpace =>
      (⟨p.1, Work.Whitney.NZ.fstC 1 p.2⟩ : chernRedW₁.TotalSpace)) :=
  (Work.Thom.continuous_id_realification (Work.Gen.tautDual 2)).comp
    (continuous_fstC_totalMap.comp (Work.Thom.continuous_id_realification_symm chernRedE))

/-- The inclusion of the first summand into `chernRedW`, as a map of total spaces. -/
theorem continuous_inclC₁_totalMap_W :
    Continuous (fun p : chernRedW₁.TotalSpace =>
      (⟨p.1, chernRedInclC₁ p.2⟩ : chernRedW.TotalSpace)) :=
  (Work.Thom.continuous_id_realification chernRedE).comp
    (continuous_inclC₁_totalMap.comp
      (Work.Thom.continuous_id_realification_symm (Work.Gen.tautDual 2)))

/-! ## 5. The two maps of the punctured spaces -/

/-- Two elements of `chernRedW₁` with the same base and the same fibre are equal. -/
theorem chernRedW₁_eq_of_fib {p q : chernRedW₁.TotalSpace} (h1 : p.1 = q.1)
    (h2 : chernRedFib₁ p = chernRedFib₁ q) : p = q := by
  obtain ⟨b, v⟩ := p
  obtain ⟨b', v'⟩ := q
  simp only at h1
  subst h1
  exact congrArg (fun w : EuclideanSpace ℂ (Fin 1) => (⟨b, w⟩ : chernRedW₁.TotalSpace)) h2

/-- **The projection of `chernRedU` onto the punctured total space of the first summand.** -/
def chernRedUProj : C(↥chernRedU, ↥(Work.Thom.zeroComplement chernRedW₁)) where
  toFun := fun p => ⟨⟨p.1.1.1, Work.Whitney.NZ.fstC 1 p.1.1.2⟩, by
    show Work.Whitney.NZ.fstC 1 (p.1.1.2 : EuclideanSpace ℂ (Fin 2)) ≠ 0
    exact fun h => p.2 ((chernRedFstC_eq_zero_iff _).mp h)⟩
  continuous_toFun :=
    (continuous_fstC_totalMap_W.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk (fun p => by
        show Work.Whitney.NZ.fstC 1 (p.1.1.2 : EuclideanSpace ℂ (Fin 2)) ≠ 0
        exact fun h => p.2 ((chernRedFstC_eq_zero_iff _).mp h))

/-- **The inclusion of the first summand into `chernRedU`.** -/
def chernRedUIncl : C(↥(Work.Thom.zeroComplement chernRedW₁), ↥chernRedU) where
  toFun := fun q => ⟨⟨⟨q.1.1, chernRedInclC₁ (chernRedFib₁ q.1)⟩, by
      show chernRedInclC₁ (chernRedFib₁ q.1) ≠ 0
      exact fun h => q.2 (by
        show (chernRedFib₁ q.1 : EuclideanSpace ℂ (Fin 1)) = 0
        rw [← chernRedFstC_inclC₁ (chernRedFib₁ q.1), h]; rfl)⟩, by
      show (chernRedInclC₁ (chernRedFib₁ q.1)).ofLp 0 ≠ 0
      exact fun h => q.2 ((chernRedInclC₁_ofLp_zero_eq_zero_iff _).mp h)⟩
  continuous_toFun :=
    ((continuous_inclC₁_totalMap_W.comp continuous_subtype_val).subtype_mk (fun q => by
      show chernRedInclC₁ (chernRedFib₁ q.1) ≠ 0
      exact fun h => q.2 (by
        show (chernRedFib₁ q.1 : EuclideanSpace ℂ (Fin 1)) = 0
        rw [← chernRedFstC_inclC₁ (chernRedFib₁ q.1), h]; rfl))).subtype_mk (fun q => by
      show (chernRedInclC₁ (chernRedFib₁ q.1)).ofLp 0 ≠ 0
      exact fun h => q.2 ((chernRedInclC₁_ofLp_zero_eq_zero_iff _).mp h))

theorem chernRedUProj_comp_chernRedUIncl :
    chernRedUProj.comp chernRedUIncl = ContinuousMap.id _ := by
  refine ContinuousMap.ext (fun q => ?_)
  apply Subtype.ext
  apply chernRedW₁_eq_of_fib
  · rfl
  · show Work.Whitney.NZ.fstC 1 (chernRedInclC₁ (chernRedFib₁ q.1)) = chernRedFib₁ q.1
    exact chernRedFstC_inclC₁ _

/-! ## 6. The straight-line homotopy retracting the second summand -/

/-- The straight-line homotopy `(t,p) ↦ (1-t)·Incl(Proj p) + t·p`, as a map of total spaces. -/
theorem continuous_homotopyFun_totalMap₁ :
    Continuous (fun y : unitInterval × ↥chernRedU =>
      (⟨y.2.1.1.1, chernRedHomotopyVec₁ (y.1 : ℝ) (chernRedFib (y.2.1.1))⟩ :
        chernRedW.TotalSpace)) := by
  have hval : Continuous (fun y : unitInterval × ↥chernRedU => y.2.1.1) :=
    (continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd
  have hσ₁ : Continuous (fun y : unitInterval × ↥chernRedU =>
      (⟨(y.2.1.1 : chernRedW.TotalSpace).1,
        chernRedInclC₁ (Work.Whitney.NZ.fstC 1 (chernRedFib (y.2.1.1)))⟩ :
        chernRedW.TotalSpace)) :=
    continuous_inclC₁_totalMap_W.comp (continuous_fstC_totalMap_W.comp hval)
  have hσ₂ : Continuous (fun y : unitInterval × ↥chernRedU =>
      (⟨(y.2.1.1 : chernRedW.TotalSpace).1, (y.2.1.1 : chernRedW.TotalSpace).2⟩ :
        chernRedW.TotalSpace)) := hval
  have hc₁ : Continuous (fun y : unitInterval × ↥chernRedU => (1 - (y.1 : ℝ) : ℝ)) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  have hc₂ : Continuous (fun y : unitInterval × ↥chernRedU => (y.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hs₁ := Work.Thom.SphereInDisc.continuous_smul_section' chernRedW
    (⟨_, hσ₁⟩ : C(unitInterval × ↥chernRedU, chernRedW.TotalSpace)) ⟨_, hc₁⟩
  have hs₂ := Work.Thom.SphereInDisc.continuous_smul_section' chernRedW
    (⟨_, hσ₂⟩ : C(unitInterval × ↥chernRedU, chernRedW.TotalSpace)) ⟨_, hc₂⟩
  have hsum := Work.Thom.continuous_add_section chernRedW
    (⟨_, hs₁⟩ : C(unitInterval × ↥chernRedU, chernRedW.TotalSpace)) ⟨_, hs₂⟩ (fun y => rfl)
  refine hsum.congr (fun y => ?_)
  rfl

/-- The straight-line homotopy, as a homotopy from `Incl ∘ Proj` to the identity of `chernRedU`. -/
def chernRedUHomotopy : ContinuousMap.Homotopy (chernRedUIncl.comp chernRedUProj)
    (ContinuousMap.id ↥chernRedU) where
  toContinuousMap :=
    ⟨fun y =>
      ⟨⟨⟨y.2.1.1.1, chernRedHomotopyVec₁ (y.1 : ℝ) (chernRedFib (y.2.1.1))⟩, by
        show chernRedHomotopyVec₁ (y.1 : ℝ) (chernRedFib (y.2.1.1)) ≠ 0
        exact fun h => y.2.2 (by
          have h1 := chernRedHomotopyVec₁_ofLp_zero (y.1 : ℝ) (chernRedFib (y.2.1.1))
          rw [h] at h1
          exact h1.symm)⟩, by
        show (chernRedHomotopyVec₁ (y.1 : ℝ) (chernRedFib (y.2.1.1))).ofLp 0 ≠ 0
        rw [chernRedHomotopyVec₁_ofLp_zero]
        exact fun h => y.2.2 h⟩,
      ((continuous_homotopyFun_totalMap₁.subtype_mk (fun y => by
        show chernRedHomotopyVec₁ (y.1 : ℝ) (chernRedFib (y.2.1.1)) ≠ 0
        exact fun h => y.2.2 (by
          have h1 := chernRedHomotopyVec₁_ofLp_zero (y.1 : ℝ) (chernRedFib (y.2.1.1))
          rw [h] at h1
          exact h1.symm))).subtype_mk (fun y => by
        show (chernRedHomotopyVec₁ (y.1 : ℝ) (chernRedFib (y.2.1.1))).ofLp 0 ≠ 0
        rw [chernRedHomotopyVec₁_ofLp_zero]
        exact fun y' => y.2.2 y'))⟩
  map_zero_left := fun p => by
    apply Subtype.ext
    apply Subtype.ext
    apply chernRed_eq_of_fib
    · rfl
    · show chernRedHomotopyVec₁ 0 (chernRedFib p.1.1)
        = chernRedInclC₁ (Work.Whitney.NZ.fstC 1 (chernRedFib p.1.1))
      simp [chernRedHomotopyVec₁]
  map_one_left := fun p => by
    apply Subtype.ext
    apply Subtype.ext
    apply chernRed_eq_of_fib
    · rfl
    · show chernRedHomotopyVec₁ 1 (chernRedFib p.1.1) = chernRedFib p.1.1
      simp [chernRedHomotopyVec₁]

/-- **`chernRedU` is homotopy equivalent to the punctured first summand.** -/
def chernRedUHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↥chernRedU ↥(Work.Thom.zeroComplement chernRedW₁) where
  toFun := chernRedUProj
  invFun := chernRedUIncl
  left_inv := ⟨chernRedUHomotopy⟩
  right_inv := by
    rw [chernRedUProj_comp_chernRedUIncl]

/-! ## 7. The vanishing -/

theorem chernRedU_vanishing :
    Subsingleton (Work.Thom.Coh ℤ 4 ↥Work.ThomBordism.Grassmann.chernRedU) := by
  haveI : Subsingleton (Work.Thom.Coh ℤ 4 ↥(Work.Thom.zeroComplement chernRedW₁)) :=
    subsingleton_zeroComplement_firstSummand
  have hbij := Work.Thom.bijective_CohMap_of_homotopyEquiv chernRedUHomotopyEquiv ℤ 4
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', ha'⟩ := hbij.2 a
  obtain ⟨b', hb'⟩ := hbij.2 b
  rw [← ha', ← hb', Subsingleton.elim a' b']

end

end Work.ThomBordism.Grassmann
