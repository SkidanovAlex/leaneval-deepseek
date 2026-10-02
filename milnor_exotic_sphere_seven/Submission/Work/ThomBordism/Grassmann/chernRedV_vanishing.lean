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
# `H⁴` of the piece `{second coordinate ≠ 0}` of the cover of `E ∖ 0`

`Submission/Work/ThomBordism/Grassmann/chernReducedSetup.lean` fixes the vocabulary of the crux
`Work.ThomBordism.Grassmann.chernReducedRatNeZero`: the complex rank-`2` bundle
`chernRedE = O(1) ⊕ O(-1)` over `ℂP²`, its realification `chernRedW`, the punctured total space
`chernRedX = chernRedW ∖ 0` and the two pieces

* `chernRedU = {first summand ≠ 0}`, `chernRedV = {second summand ≠ 0}`

of the two-set cover of `chernRedX`.  This module proves

  `Subsingleton (H⁴(chernRedV; ℤ))`,

one of the three vanishing cohomology groups that the Mayer–Vietoris argument for
`H⁴(chernRedX; ℤ) = 0` needs.

## The mathematics

Let `W₂ = realification (tautLine 2)` be the realification of the second summand
`O(-1) = tautLine 2`, so that `zeroComplement W₂` is the total space of the punctured tautological
line bundle.  Two total-space maps

* `Proj : chernRedV → zeroComplement W₂`, the *second summand projection* `⟨b,(x,y)⟩ ↦ ⟨b,y⟩`;
* `Incl : zeroComplement W₂ → chernRedV`, the *inclusion of the second summand*
  `⟨b,y⟩ ↦ ⟨b,(0,y)⟩`;

satisfy `Proj ∘ Incl = id` and are homotopic in the other order through the straight-line homotopy
`(t,p) ↦ (1-t)·Incl(Proj p) + t·p` (which scales the first summand of the fibre by `t`, so it stays
inside `chernRedV`).  Hence `Proj` is a homotopy equivalence, so it is bijective on cohomology
(`Work.Thom.bijective_CohMap_of_homotopyEquiv`); since the target has vanishing `H⁴` (it is a
punctured tautological line bundle, i.e. `S⁵`), so has `chernRedV`.

The vanishing `H⁴(zeroComplement W₂) = 0` is reduced to the already proved
`Work.Gen.puncturedTautDualTwoHZero` (`H^k(tautDual ∖ 0) = 0` off `0, 5`) along the bundle
isomorphisms `O(1) ≅ conj(O(-1))` (`Work.Gen.tautDual_iso_conjLine`, complex) and
`conj(O(-1)) ≅ O(-1)` (`Work.Gen.conjIso`, real).

The continuity of `Proj`, `Incl` and of the homotopy is `Work.Thom.continuous_totalSpaceMap_clm`
(the chartwise form of a bundle morphism), `Work.Thom.continuous_smul_section'` (fibrewise rescaling
by a continuous real function) and `Work.Thom.continuous_add_section` (fibrewise sum); the chartwise
computations use only the cocycle identity `Work.Gen.homCoord_mul` of the homogeneous coordinates.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

/-! ## 1. The punctured total space of the second summand -/

/-- The realification of the second summand `O(-1) = tautLine 2` of `chernRedE`. -/
abbrev chernRedW₂ : RealBundle (Work.Projective.CP 2) (EuclideanSpace ℂ (Fin 1)) (Fin 3) :=
  Work.Thom.realification (Work.Gen.tautLine 2)

/-- A homotopy equivalence induces an isomorphism on cohomology, hence transports `Subsingleton`. -/
private theorem subsingleton_cohomology_of_homotopyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ)
    (h : Subsingleton (Work.Thom.Coh ℤ n X)) : Subsingleton (Work.Thom.Coh ℤ n Y) := by
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv e n
  have hsurj : Function.Surjective ⇑(iso.hom) :=
    (ModuleCat.epi_iff_surjective iso.hom).mp inferInstance
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    rw [h.elim a' b']⟩

/-- **`H⁴` of the punctured total space of the second summand `O(-1)` vanishes.** -/
theorem subsingleton_zeroComplement_secondSummand :
    Subsingleton (Work.Thom.Coh ℤ 4 ↥(Work.Thom.zeroComplement chernRedW₂)) := by
  obtain ⟨eDC⟩ := Work.Gen.tautDual_iso_conjLine 2
  have h₁ : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautDual 2))) ≃ₜ
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.conjLine 2))) :=
    Work.Thom.punctHomeo (Work.Gen.tautDual 2) (Work.Gen.conjLine 2) eDC
  have h₂ : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.conjLine 2))) ≃ₜ
      ↥(Work.Thom.zeroComplement chernRedW₂) :=
    Work.Thom.BundleIso.punctHomeomorph (Work.Gen.conjIso 2)
  have hz : Subsingleton (Work.Thom.Coh ℤ 4
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautDual 2)))) :=
    ModuleCat.subsingleton_of_isZero (puncturedTautDualTwoHZero 4 (by norm_num) (by norm_num))
  exact subsingleton_cohomology_of_homotopyEquiv h₂.toHomotopyEquiv 4
    (subsingleton_cohomology_of_homotopyEquiv h₁.toHomotopyEquiv 4 hz)

/-! ## 2. The splitting of the model fibre `ℂ² = ℂ¹ ⊕ ℂ¹`

We use the explicit splitting `Work.Whitney.sumFibreC 1 1` (the one along which `chernRedE` is
glued) and its two components `Work.Whitney.NZ.fstC 1` / `Work.Whitney.NZ.sndC 1`. -/

/-- The inclusion of the second summand `ℂ¹ → ℂ¹ ⊕ ℂ¹ = ℂ²` of the model fibre. -/
noncomputable def chernRedInclC : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (Work.Whitney.sumFibreC 1 1 : (EuclideanSpace ℂ (Fin 1) × EuclideanSpace ℂ (Fin 1)) →L[ℂ]
      EuclideanSpace ℂ (Fin 2)).comp
    ((0 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)).prod
      (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))))

/-- The fibre of `chernRedW₂` at a point, as an element of the model fibre. -/
def chernRedFib₂ (q : chernRedW₂.TotalSpace) : EuclideanSpace ℂ (Fin 1) := q.2

theorem chernRedInclC_apply (t : EuclideanSpace ℂ (Fin 1)) :
    chernRedInclC t = Work.Whitney.sumFibreC 1 1 (0, t) := by
  simp only [chernRedInclC, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply]
  rfl

/-- The second summand projection applied to the second summand inclusion is the identity. -/
theorem chernRedSndC_inclC (t : EuclideanSpace ℂ (Fin 1)) :
    Work.Whitney.NZ.sndC 1 (chernRedInclC t) = t := by
  rw [chernRedInclC_apply, Work.Whitney.NZ.sndC_sumFibreC]

/-- The zero-th coordinate of `sndC 1 v` is the first coordinate of `v`. -/
theorem chernRedSndC_apply_eq (v : EuclideanSpace ℂ (Fin 2)) :
    (Work.Whitney.NZ.sndC 1 v).ofLp 0 = v.ofLp 1 := by
  have h1 : (Work.Whitney.NZ.sndC 1 v).ofLp 0
      = v.ofLp (finSumFinEquiv (Sum.inr (0 : Fin 1))) := by
    show (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := 1) (m := 1) v).2.ofLp 0 = _
    rw [Work.Thom.finAddEquivProd_snd]
  rw [h1, show finSumFinEquiv (Sum.inr (0 : Fin 1)) = (1 : Fin 2) from by
    rw [finSumFinEquiv_apply_right]; rfl]

/-- The first coordinate of `chernRedInclC t` is the zero-th coordinate of `t`. -/
theorem chernRedInclC_ofLp_one (t : EuclideanSpace ℂ (Fin 1)) :
    (chernRedInclC t).ofLp 1 = t.ofLp 0 := by
  rw [chernRedInclC_apply]
  have h := Work.Thom.finAddEquivProd_symm_apply_inr (𝕜 := ℂ) (n := 1) (m := 1)
    (0 : EuclideanSpace ℂ (Fin 1)) t 0
  rw [show finSumFinEquiv (Sum.inr (0 : Fin 1)) = (1 : Fin 2) from by
    rw [finSumFinEquiv_apply_right]; rfl] at h
  exact h

/-- `sndC 1 v = 0` iff the first coordinate of `v` vanishes. -/
theorem chernRedSndC_eq_zero_iff (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Whitney.NZ.sndC 1 v = 0 ↔ v.ofLp 1 = 0 := by
  constructor
  · intro h
    have h1 := chernRedSndC_apply_eq v
    rw [h] at h1
    simpa using h1.symm
  · intro h
    have h1 := chernRedSndC_apply_eq v
    rw [h] at h1
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    simpa using h1

/-- The first coordinate of `chernRedInclC t` vanishes iff `t` does. -/
theorem chernRedInclC_ofLp_one_eq_zero_iff (t : EuclideanSpace ℂ (Fin 1)) :
    (chernRedInclC t).ofLp 1 = 0 ↔ t = 0 := by
  rw [chernRedInclC_ofLp_one]
  constructor
  · intro h
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    simpa using h
  · intro h
    rw [h]
    rfl

/-- The straight-line combination `(1-t)·Incl(sndC v) + t·v` of the model fibre. -/
def chernRedHomotopyVec (t : ℝ) (v : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  (1 - t) • (chernRedInclC (Work.Whitney.NZ.sndC 1 v)) + t • v

/-- Its first coordinate is that of `v`. -/
theorem chernRedHomotopyVec_ofLp_one (t : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    (chernRedHomotopyVec t v).ofLp 1 = v.ofLp 1 := by
  have h : (chernRedInclC (Work.Whitney.NZ.sndC 1 v)).ofLp 1 = v.ofLp 1 := by
    rw [chernRedInclC_ofLp_one, chernRedSndC_apply_eq]
  simp only [chernRedHomotopyVec, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
    h, ← add_smul, sub_add_cancel, one_smul]

/-! ## 3. The transition functions of `chernRedE` against the two components -/

theorem chernRedE_coordChange_apply (i j : Fin 3 × Fin 3) (b : Work.Projective.CP 2)
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

/-- `sndC 1` absorbs the transition function of `chernRedE`. -/
theorem chernRedSndC_chernRedE_coordChange (i j : Fin 3 × Fin 3) (b : Work.Projective.CP 2)
    (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Whitney.NZ.sndC 1 (chernRedE.coordChange i j b v)
      = Work.Gen.homCoord 2 i.2 j.2 b • Work.Whitney.NZ.sndC 1 v := by
  rw [chernRedE_coordChange_apply, Work.Whitney.NZ.sndC_sumFibreC]

/-- The inclusion of the second summand is equivariant for the transition functions. -/
theorem chernRedE_coordChange_apply_inclC (i j : Fin 3 × Fin 3) (b : Work.Projective.CP 2)
    (t : EuclideanSpace ℂ (Fin 1)) :
    chernRedE.coordChange i j b (chernRedInclC t)
      = Work.Gen.homCoord 2 i.2 j.2 b • chernRedInclC t := by
  rw [chernRedE_coordChange_apply, chernRedInclC_apply, Work.Whitney.NZ.fstC_sumFibreC,
    Work.Whitney.NZ.sndC_sumFibreC]
  rw [show ((Work.Gen.homCoord 2 j.1 i.1 b) • (0 : EuclideanSpace ℂ (Fin 1)),
        Work.Gen.homCoord 2 i.2 j.2 b • t)
      = (Work.Gen.homCoord 2 i.2 j.2 b) • ((0 : EuclideanSpace ℂ (Fin 1)), t) from by simp,
    map_smul]

/-- The composite transition function ending on the second summand. -/
theorem composite_snd_eq (i₁ : Fin 3 × Fin 3) (i₂ : Fin 3) (b : Work.Projective.CP 2)
    (h₁ : b ∈ chernRedE.baseSet i₁) (h₂ : b ∈ (Work.Gen.tautLine 2).baseSet i₂) :
    ((Work.Gen.tautLine 2).coordChange ((Work.Gen.tautLine 2).indexAt b) i₂ b).comp
      ((Work.Whitney.NZ.sndC 1).comp (chernRedE.coordChange i₁ (chernRedE.indexAt b) b))
    = (Work.Gen.homCoord 2 i₁.2 i₂ b) • (Work.Whitney.NZ.sndC 1) := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Work.Gen.tautLine_coordChange, smul_apply, ContinuousLinearMap.id_apply,
    chernRedSndC_chernRedE_coordChange, smul_apply, smul_smul]
  congr 1
  exact (Work.Gen.homCoord_mul i₁.2 (chernRedE.indexAt b).2 i₂
    h₁.2 ((Work.Gen.tautLine 2).mem_baseSet_at b) h₂).symm

/-- The composite transition function ending on the first summand. -/
theorem composite_incl_eq (i₁ : Fin 3) (i₂ : Fin 3 × Fin 3) (b : Work.Projective.CP 2)
    (h₁ : b ∈ (Work.Gen.tautLine 2).baseSet i₁) (h₂ : b ∈ chernRedE.baseSet i₂) :
    (chernRedE.coordChange (chernRedE.indexAt b) i₂ b).comp
      (chernRedInclC.comp ((Work.Gen.tautLine 2).coordChange i₁
        ((Work.Gen.tautLine 2).indexAt b) b))
    = (Work.Gen.homCoord 2 i₁ i₂.2 b) • chernRedInclC := by
  refine ContinuousLinearMap.ext (fun t => ?_)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Work.Gen.tautLine_coordChange, smul_apply, ContinuousLinearMap.id_apply, smul_apply,
    map_smul, map_smul, chernRedInclC_apply, chernRedE_coordChange_apply,
    Work.Whitney.NZ.fstC_sumFibreC, Work.Whitney.NZ.sndC_sumFibreC]
  rw [show ((Work.Gen.homCoord 2 i₂.1 (chernRedE.indexAt b).1 b) • (0 : EuclideanSpace ℂ (Fin 1)),
        (Work.Gen.homCoord 2 (chernRedE.indexAt b).2 i₂.2 b) • t)
      = Work.Gen.homCoord 2 (chernRedE.indexAt b).2 i₂.2 b •
          ((0 : EuclideanSpace ℂ (Fin 1)), t) from by simp,
    map_smul, smul_smul, mul_comm]
  congr 1
  exact (Work.Gen.homCoord_mul i₁ (chernRedE.indexAt b).2 i₂.2
    h₁ ((Work.Gen.tautLine 2).mem_baseSet_at b) h₂.2).symm

/-! ## 4. Continuity of the two total-space maps -/

theorem continuousOn_composite_snd (i₁ : Fin 3 × Fin 3) (i₂ : Fin 3) :
    ContinuousOn (fun b : Work.Projective.CP 2 =>
      ((Work.Gen.tautLine 2).coordChange ((Work.Gen.tautLine 2).indexAt b) i₂ b).comp
        ((Work.Whitney.NZ.sndC 1).comp (chernRedE.coordChange i₁ (chernRedE.indexAt b) b)))
      (chernRedE.baseSet i₁ ∩ (Work.Gen.tautLine 2).baseSet i₂) := by
  have hconst : ContinuousOn (fun _ : Work.Projective.CP 2 => (Work.Whitney.NZ.sndC 1 :
      EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 1)))
      (chernRedE.baseSet i₁ ∩ (Work.Gen.tautLine 2).baseSet i₂) := continuousOn_const
  have hhom : ContinuousOn (fun b : Work.Projective.CP 2 => Work.Gen.homCoord 2 i₁.2 i₂ b)
      (chernRedE.baseSet i₁ ∩ (Work.Gen.tautLine 2).baseSet i₂) :=
    (Work.Gen.continuousOn_homCoord (n := 2) i₁.2 i₂).mono (fun b hb => hb.1.2)
  exact ContinuousOn.congr (hhom.smul hconst)
    (fun b hb => composite_snd_eq i₁ i₂ b hb.1 hb.2)

theorem continuousOn_composite_incl (i₁ : Fin 3) (i₂ : Fin 3 × Fin 3) :
    ContinuousOn (fun b : Work.Projective.CP 2 =>
      (chernRedE.coordChange (chernRedE.indexAt b) i₂ b).comp
        (chernRedInclC.comp ((Work.Gen.tautLine 2).coordChange i₁
          ((Work.Gen.tautLine 2).indexAt b) b)))
      ((Work.Gen.tautLine 2).baseSet i₁ ∩ chernRedE.baseSet i₂) := by
  have hconst : ContinuousOn (fun _ : Work.Projective.CP 2 => (chernRedInclC :
      EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
      ((Work.Gen.tautLine 2).baseSet i₁ ∩ chernRedE.baseSet i₂) := continuousOn_const
  have hhom : ContinuousOn (fun b : Work.Projective.CP 2 => Work.Gen.homCoord 2 i₁ i₂.2 b)
      ((Work.Gen.tautLine 2).baseSet i₁ ∩ chernRedE.baseSet i₂) :=
    (Work.Gen.continuousOn_homCoord (n := 2) i₁ i₂.2).mono (fun b hb => hb.1)
  exact ContinuousOn.congr (hhom.smul hconst)
    (fun b hb => composite_incl_eq i₁ i₂ b hb.1 hb.2)

/-- The second-summand projection of `chernRedE`, as a map of total spaces. -/
theorem continuous_sndC_totalMap :
    Continuous (fun p : chernRedE.TotalSpace =>
      (⟨p.1, Work.Whitney.NZ.sndC 1 p.2⟩ : (Work.Gen.tautLine 2).TotalSpace)) :=
  Work.Thom.continuous_totalSpaceMap_clm chernRedE (Work.Gen.tautLine 2) (ContinuousMap.id _)
    (fun _ => Work.Whitney.NZ.sndC 1)
    (fun i₁ i₂ => by
      rw [show (⇑(ContinuousMap.id (Work.Projective.CP 2))) = (id : Work.Projective.CP 2 →
        Work.Projective.CP 2) from rfl, Set.preimage_id]
      exact continuousOn_composite_snd i₁ i₂)

/-- The inclusion of the second summand, as a map of total spaces. -/
theorem continuous_inclC_totalMap :
    Continuous (fun p : (Work.Gen.tautLine 2).TotalSpace =>
      (⟨p.1, chernRedInclC p.2⟩ : chernRedE.TotalSpace)) :=
  Work.Thom.continuous_totalSpaceMap_clm (Work.Gen.tautLine 2) chernRedE (ContinuousMap.id _)
    (fun _ => chernRedInclC)
    (fun i₁ i₂ => by
      rw [show (⇑(ContinuousMap.id (Work.Projective.CP 2))) = (id : Work.Projective.CP 2 →
        Work.Projective.CP 2) from rfl, Set.preimage_id]
      exact continuousOn_composite_incl i₁ i₂)

/-- The second-summand projection of `chernRedW`, as a map of total spaces. -/
theorem continuous_sndC_totalMap_W :
    Continuous (fun p : chernRedW.TotalSpace =>
      (⟨p.1, Work.Whitney.NZ.sndC 1 p.2⟩ : chernRedW₂.TotalSpace)) :=
  (Work.Thom.continuous_id_realification (Work.Gen.tautLine 2)).comp
    (continuous_sndC_totalMap.comp (Work.Thom.continuous_id_realification_symm chernRedE))

/-- The inclusion of the second summand into `chernRedW`, as a map of total spaces. -/
theorem continuous_inclC_totalMap_W :
    Continuous (fun p : chernRedW₂.TotalSpace =>
      (⟨p.1, chernRedInclC p.2⟩ : chernRedW.TotalSpace)) :=
  (Work.Thom.continuous_id_realification chernRedE).comp
    (continuous_inclC_totalMap.comp
      (Work.Thom.continuous_id_realification_symm (Work.Gen.tautLine 2)))

/-! ## 5. The two maps of the punctured spaces -/

/-- Two elements of `chernRedW₂` with the same base and the same fibre are equal. -/
theorem chernRedW₂_eq_of_fib {p q : chernRedW₂.TotalSpace} (h1 : p.1 = q.1)
    (h2 : chernRedFib₂ p = chernRedFib₂ q) : p = q := by
  obtain ⟨b, v⟩ := p
  obtain ⟨b', v'⟩ := q
  simp only at h1
  subst h1
  exact congrArg (fun w : EuclideanSpace ℂ (Fin 1) => (⟨b, w⟩ : chernRedW₂.TotalSpace)) h2

/-- **The projection of `chernRedV` onto the punctured total space of the second summand.** -/
def chernRedVProj : C(↥chernRedV, ↥(Work.Thom.zeroComplement chernRedW₂)) where
  toFun := fun p => ⟨⟨p.1.1.1, Work.Whitney.NZ.sndC 1 p.1.1.2⟩, by
    show Work.Whitney.NZ.sndC 1 (p.1.1.2 : EuclideanSpace ℂ (Fin 2)) ≠ 0
    exact fun h => p.2 ((chernRedSndC_eq_zero_iff _).mp h)⟩
  continuous_toFun :=
    (continuous_sndC_totalMap_W.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk (fun p => by
        show Work.Whitney.NZ.sndC 1 (p.1.1.2 : EuclideanSpace ℂ (Fin 2)) ≠ 0
        exact fun h => p.2 ((chernRedSndC_eq_zero_iff _).mp h))

/-- **The inclusion of the second summand into `chernRedV`.** -/
def chernRedVIncl : C(↥(Work.Thom.zeroComplement chernRedW₂), ↥chernRedV) where
  toFun := fun q => ⟨⟨⟨q.1.1, chernRedInclC (chernRedFib₂ q.1)⟩, by
      show chernRedInclC (chernRedFib₂ q.1) ≠ 0
      exact fun h => q.2 (by
        show (chernRedFib₂ q.1 : EuclideanSpace ℂ (Fin 1)) = 0
        rw [← chernRedSndC_inclC (chernRedFib₂ q.1), h]; rfl)⟩, by
      show (chernRedInclC (chernRedFib₂ q.1)).ofLp 1 ≠ 0
      exact fun h => q.2 ((chernRedInclC_ofLp_one_eq_zero_iff _).mp h)⟩
  continuous_toFun :=
    ((continuous_inclC_totalMap_W.comp continuous_subtype_val).subtype_mk (fun q => by
      show chernRedInclC (chernRedFib₂ q.1) ≠ 0
      exact fun h => q.2 (by
        show (chernRedFib₂ q.1 : EuclideanSpace ℂ (Fin 1)) = 0
        rw [← chernRedSndC_inclC (chernRedFib₂ q.1), h]; rfl))).subtype_mk (fun q => by
      show (chernRedInclC (chernRedFib₂ q.1)).ofLp 1 ≠ 0
      exact fun h => q.2 ((chernRedInclC_ofLp_one_eq_zero_iff _).mp h))

theorem chernRedVProj_comp_chernRedVIncl :
    chernRedVProj.comp chernRedVIncl = ContinuousMap.id _ := by
  refine ContinuousMap.ext (fun q => ?_)
  apply Subtype.ext
  apply chernRedW₂_eq_of_fib
  · rfl
  · show Work.Whitney.NZ.sndC 1 (chernRedInclC (chernRedFib₂ q.1)) = chernRedFib₂ q.1
    exact chernRedSndC_inclC _

/-! ## 6. The straight-line homotopy retracting the first summand -/

/-- The straight-line homotopy `(t,p) ↦ (1-t)·Incl(Proj p) + t·p`, as a map of total spaces. -/
theorem continuous_homotopyFun_totalMap :
    Continuous (fun y : unitInterval × ↥chernRedV =>
      (⟨y.2.1.1.1, chernRedHomotopyVec (y.1 : ℝ) (chernRedFib (y.2.1.1))⟩ :
        chernRedW.TotalSpace)) := by
  have hval : Continuous (fun y : unitInterval × ↥chernRedV => y.2.1.1) :=
    (continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd
  have hσ₁ : Continuous (fun y : unitInterval × ↥chernRedV =>
      (⟨(y.2.1.1 : chernRedW.TotalSpace).1,
        chernRedInclC (Work.Whitney.NZ.sndC 1 (chernRedFib (y.2.1.1)))⟩ :
        chernRedW.TotalSpace)) :=
    continuous_inclC_totalMap_W.comp (continuous_sndC_totalMap_W.comp hval)
  have hσ₂ : Continuous (fun y : unitInterval × ↥chernRedV =>
      (⟨(y.2.1.1 : chernRedW.TotalSpace).1, (y.2.1.1 : chernRedW.TotalSpace).2⟩ :
        chernRedW.TotalSpace)) := hval
  have hc₁ : Continuous (fun y : unitInterval × ↥chernRedV => (1 - (y.1 : ℝ) : ℝ)) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  have hc₂ : Continuous (fun y : unitInterval × ↥chernRedV => (y.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hs₁ := Work.Thom.SphereInDisc.continuous_smul_section' chernRedW
    (⟨_, hσ₁⟩ : C(unitInterval × ↥chernRedV, chernRedW.TotalSpace)) ⟨_, hc₁⟩
  have hs₂ := Work.Thom.SphereInDisc.continuous_smul_section' chernRedW
    (⟨_, hσ₂⟩ : C(unitInterval × ↥chernRedV, chernRedW.TotalSpace)) ⟨_, hc₂⟩
  have hsum := Work.Thom.continuous_add_section chernRedW
    (⟨_, hs₁⟩ : C(unitInterval × ↥chernRedV, chernRedW.TotalSpace)) ⟨_, hs₂⟩ (fun y => rfl)
  refine hsum.congr (fun y => ?_)
  rfl

/-- The straight-line homotopy, as a homotopy from `Incl ∘ Proj` to the identity of `chernRedV`. -/
def chernRedVHomotopy : ContinuousMap.Homotopy (chernRedVIncl.comp chernRedVProj)
    (ContinuousMap.id ↥chernRedV) where
  toContinuousMap :=
    ⟨fun y =>
      ⟨⟨⟨y.2.1.1.1, chernRedHomotopyVec (y.1 : ℝ) (chernRedFib (y.2.1.1))⟩, by
        show chernRedHomotopyVec (y.1 : ℝ) (chernRedFib (y.2.1.1)) ≠ 0
        exact fun h => y.2.2 (by
          have h1 := chernRedHomotopyVec_ofLp_one (y.1 : ℝ) (chernRedFib (y.2.1.1))
          rw [h] at h1
          exact h1.symm)⟩, by
        show (chernRedHomotopyVec (y.1 : ℝ) (chernRedFib (y.2.1.1))).ofLp 1 ≠ 0
        rw [chernRedHomotopyVec_ofLp_one]
        exact fun h => y.2.2 h⟩,
      ((continuous_homotopyFun_totalMap.subtype_mk (fun y => by
        show chernRedHomotopyVec (y.1 : ℝ) (chernRedFib (y.2.1.1)) ≠ 0
        exact fun h => y.2.2 (by
          have h1 := chernRedHomotopyVec_ofLp_one (y.1 : ℝ) (chernRedFib (y.2.1.1))
          rw [h] at h1
          exact h1.symm))).subtype_mk (fun y => by
        show (chernRedHomotopyVec (y.1 : ℝ) (chernRedFib (y.2.1.1))).ofLp 1 ≠ 0
        rw [chernRedHomotopyVec_ofLp_one]
        exact fun h => y.2.2 h))⟩
  map_zero_left := fun p => by
    apply Subtype.ext
    apply Subtype.ext
    apply chernRed_eq_of_fib
    · rfl
    · show chernRedHomotopyVec 0 (chernRedFib p.1.1)
        = chernRedInclC (Work.Whitney.NZ.sndC 1 (chernRedFib p.1.1))
      simp [chernRedHomotopyVec]
  map_one_left := fun p => by
    apply Subtype.ext
    apply Subtype.ext
    apply chernRed_eq_of_fib
    · rfl
    · show chernRedHomotopyVec 1 (chernRedFib p.1.1) = chernRedFib p.1.1
      simp [chernRedHomotopyVec]

/-- **`chernRedV` is homotopy equivalent to the punctured second summand.** -/
def chernRedVHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↥chernRedV ↥(Work.Thom.zeroComplement chernRedW₂) where
  toFun := chernRedVProj
  invFun := chernRedVIncl
  left_inv := ⟨chernRedVHomotopy⟩
  right_inv := by
    rw [chernRedVProj_comp_chernRedVIncl]

/-! ## 7. The vanishing -/

theorem chernRedV_vanishing :
    Subsingleton (Work.Thom.Coh ℤ 4 ↥Work.ThomBordism.Grassmann.chernRedV) := by
  haveI : Subsingleton (Work.Thom.Coh ℤ 4 ↥(Work.Thom.zeroComplement chernRedW₂)) :=
    subsingleton_zeroComplement_secondSummand
  have hbij := Work.Thom.bijective_CohMap_of_homotopyEquiv chernRedVHomotopyEquiv ℤ 4
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', ha'⟩ := hbij.2 a
  obtain ⟨b', hb'⟩ := hbij.2 b
  rw [← ha', ← hb', Subsingleton.elim a' b']

end

end Work.ThomBordism.Grassmann
