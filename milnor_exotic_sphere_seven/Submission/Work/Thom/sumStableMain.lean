import Mathlib
import Submission.Work.Thom.sumStableDefs
import Submission.Work.Thom.continuousOn_chartExpressionCLM
import Submission.Work.Thom.Iso
import Submission.Work.Thom.IsoPunct
import Submission.Work.Thom.chernClass_homeo
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.chernClass_top_eq_zero_of_nowhereZeroSection
import Submission.Work.Thom.sumToZ_sumToQ
import Submission.Work.Thom.sumToQ_sumToZ
import Submission.Work.Thom.sumEps_coordChange_Epart
import Submission.Work.Thom.sumQuotient_baseSet

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
# Stability of the Chern classes: the isomorphism `s^*(Z ⊕ ε¹ / ℂ·s) ≅ Z`
-/

namespace Work.Thom

open Work.TangentClasses

open scoped Topology

noncomputable section

variable {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} {ι₀ : Type} [Inhabited ι₀]

/-! ## Elementary linear algebra of the two summands -/

/-- The `E`-part of the standard fibre, on the nose. -/
theorem EpartCLM_prodFinEquiv_apply (m : ℕ) (y : EuclideanSpace ℂ (Fin m))
    (c : EuclideanSpace ℂ (Fin 1)) : EpartCLM m (prodFinEquiv m (y, c)) = y := by
  rw [EpartCLM, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- The `E`-part of the unit vector of the trivial summand vanishes. -/
theorem EpartCLM_sumUnit (m : ℕ) : EpartCLM m (sumUnit m) = 0 := by
  rw [sumUnit, EpartCLM_prodFinEquiv_apply]

/-- The section `ℂ^m → ℂ^{m+1}` of the `ε`-coordinate, on the nose. -/
theorem jCLM_apply (m : ℕ) (y : EuclideanSpace ℂ (Fin m)) :
    jCLM m y = prodFinEquiv m (y, 0) := by
  rw [jCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  rfl

/-- **In the `ℂ^m`-part the transition functions of the sum are those of `Z`**; the `ε`-part of the
trivial summand is untouched. -/
theorem sumEps_coordChange_jCLM (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i j : ι × ι₀) (b : B) (y : EuclideanSpace ℂ (Fin m)) :
    (sumEps ι₀ Z).coordChange i j b (jCLM m y) = jCLM m (Z.coordChange i.1 j.1 b y) := by
  have hs : ((prodFinEquiv m).symm : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1))) ((prodFinEquiv m) (y, 0))
      = (y, 0) := ContinuousLinearEquiv.symm_apply_apply (prodFinEquiv m) (y, 0)
  rw [sumEps_coordChange, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    jCLM_apply, hs, bundleSum_coordChange, ContinuousLinearMap.coe_prodMap', Prod.map_apply,
    jCLM_apply]
  rfl

/-- The index of `sumEps ι₀ Z` at `b`, explicitly. -/
theorem sumEps_indexAt_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    (sumEps ι₀ Z).indexAt b = (Z.indexAt b, default) := by
  rw [sumEps_indexAt, bundleSum_indexAt]
  rfl

/-- The chart coordinate of the tautological section point is the unit vector, at **any** index. -/
theorem localTriv_sumPoint_snd (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (a : ι × ι₀) (b : B) :
    ((sumEps ι₀ Z).localTriv a (sumPoint ι₀ Z b)).2 = sumUnit m := by
  rw [VectorBundleCore.localTriv_apply]
  exact sumEps_coordChange_sumUnit ι₀ Z _ a b

/-- **The coordinate supplied by `Work.Thom.sumCoord` really is a coordinate at which the unit
vector of the trivial summand does not vanish.** -/
theorem sumUnit_sumCoord_ne_zero (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (b : B) : (sumUnit m) (sumCoord ι₀ Z b) ≠ 0 := by
  have h := tqCoord_spec (sumEps ι₀ Z) (sumSection ι₀ Z b)
  have hs : ((sumEps ι₀ Z).localTriv
      ((sumEps ι₀ Z).indexAt ((sumSection ι₀ Z b :
        ↥(zeroComplement (realification (sumEps ι₀ Z)))) :
        (realification (sumEps ι₀ Z)).TotalSpace).1)
      ((sumSection ι₀ Z b : ↥(zeroComplement (realification (sumEps ι₀ Z)))) :
        (realification (sumEps ι₀ Z)).TotalSpace)).2 = sumUnit m := by
    rw [VectorBundleCore.localTriv_apply]
    exact (sumEps ι₀ Z).coordChange_self _ _ ((sumEps ι₀ Z).mem_baseSet_at _) (sumUnit m)
  rw [hs] at h
  exact h

/-! ## The explicit transition functions of the pullback of the tautological quotient -/

/-- `quoFun k w` only depends on its argument modulo the line `ℂ·w`. -/
theorem quoFun_sub_smul_self {n : ℕ} (k : Fin (n + 1)) (w : EuclideanSpace ℂ (Fin (n + 1)))
    (u : EuclideanSpace ℂ (Fin (n + 1))) (c : ℂ) (hw : w k ≠ 0) :
    quoFun k w (u - c • w) = quoFun k w u := by
  rw [sub_eq_add_neg, ← neg_smul, quoFun_add, quoFun_smul, quoFun_self k w hw, smul_zero,
    add_zero]

/-- The inverse form of `Work.Thom.sub_fillFun_quoFun`. -/
theorem fillFun_quoFun {n : ℕ} (k : Fin (n + 1)) (w u : EuclideanSpace ℂ (Fin (n + 1)))
    (hw : w k ≠ 0) : fillFun k (quoFun k w u) = u - (u k / w k) • w :=
  eq_sub_iff_add_eq.mpr (sub_eq_iff_eq_add'.mp (sub_fillFun_quoFun k w u hw)).symm

/-- **The transition function of the pullback of the tautological quotient along the tautological
section, explicitly.** -/
theorem sumQuotient_coordChange_apply (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i j : (ι × ι₀) × Fin (m + 1)) (b : B) (z : EuclideanSpace ℂ (Fin m)) :
    (sumQuotient ι₀ Z).coordChange i j b z
      = quoFun j.2 (sumUnit m) ((sumEps ι₀ Z).coordChange i.1 j.1 b (fillFun i.2 z)) := by
  have hp : (↑((sumSection ι₀ Z) b) : (realification (sumEps ι₀ Z)).TotalSpace)
      = sumPoint ι₀ Z b := rfl
  rw [sumQuotient, bundleComap_coordChange, tautQuotientCore_coordChange]
  rw [hp, show (sumPoint ι₀ Z b).proj = b from rfl]
  rw [show ((sumEps ι₀ Z).localTriv j.1 (sumPoint ι₀ Z b)).2 = sumUnit m from
    localTriv_sumPoint_snd ι₀ Z j.1 b]

/-- The base index of the pullback of the tautological quotient. -/
theorem sumQuotient_indexAt_fst (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    ((sumQuotient ι₀ Z).indexAt b).1 = (Z.indexAt b, default) := by
  rw [sumQuotient_indexAt]

/-- The fibre index of the pullback of the tautological quotient. -/
theorem sumQuotient_indexAt_snd (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    ((sumQuotient ι₀ Z).indexAt b).2 = sumCoord ι₀ Z b := by
  rw [sumQuotient_indexAt]

/-- The unit vector of the trivial summand is preserved by every transition function of the sum. -/
theorem sumEps_coordChange_sumUnit' (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i j : ι × ι₀) (b : B) :
    (sumEps ι₀ Z).coordChange i j b (sumUnit m) = sumUnit m :=
  sumEps_coordChange_sumUnit ι₀ Z i j b

/-- The membership condition of a chart of the pullback of the tautological quotient, in the form
used below. -/
theorem sumQuotient_mem_baseSet (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (a : ι × ι₀) (c : Fin (m + 1)) (b : B)
    (hb : b ∈ (sumQuotient ι₀ Z).baseSet (a, c)) : (sumUnit m) c ≠ 0 := by
  have h := hb
  simp only [sumQuotient, bundleComap_baseSet, Set.mem_preimage] at h
  rw [tautQuotientCore_baseSet] at h
  simp only [tqBaseSet, Set.mem_ofPred_eq] at h
  simpa only [show (↑((sumSection ι₀ Z) b) : (realification (sumEps ι₀ Z)).TotalSpace)
      = sumPoint ι₀ Z b from rfl, localTriv_sumPoint_snd ι₀ Z a b] using h.2

/-- **The chart expression of `Work.Thom.sumToQ`**, pointwise: the *varying* indices `indexAt b`
disappear and only the chart expression of the *identity* isomorphism of `Z` remains. -/
theorem sumQuotient_coordChange_sumToQ (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i₁ : ι) (a₂ : ι × ι₀) (c₂ : Fin (m + 1)) (b : B)
    (hb : b ∈ (sumQuotient ι₀ Z).baseSet (a₂, c₂)) (y : EuclideanSpace ℂ (Fin m)) :
    (sumQuotient ι₀ Z).coordChange ((sumQuotient ι₀ Z).indexAt b) (a₂, c₂) b
        (sumToQ ι₀ Z b (Z.coordChange i₁ (Z.indexAt b) b y))
      = (quoCLM c₂ (sumUnit m)) (jCLM m (Z.coordChange (Z.indexAt b) a₂.1 b
          (Z.coordChange i₁ (Z.indexAt b) b y))) := by
  have hw : (sumUnit m) (sumCoord ι₀ Z b) ≠ 0 := sumUnit_sumCoord_ne_zero ι₀ Z b
  have hc₂ : (sumUnit m) c₂ ≠ 0 := sumQuotient_mem_baseSet ι₀ Z a₂ c₂ b hb
  have hfill := fillFun_quoFun (sumCoord ι₀ Z b) (sumUnit m)
    (jCLM m (Z.coordChange i₁ (Z.indexAt b) b y)) hw
  rw [sumQuotient_coordChange_apply, sumQuotient_indexAt_fst, sumQuotient_indexAt_snd]
  rw [sumToQ, ContinuousLinearMap.comp_apply, quoCLM_apply, hfill]
  rw [map_sub, map_smul, sumEps_coordChange_sumUnit',
    quoFun_sub_smul_self c₂ (sumUnit m) _ _ hc₂, sumEps_coordChange_jCLM, quoCLM_apply]

/-- The same identity, as an identity of **continuous linear maps**. -/
theorem sumQuotient_coordChange_sumToQ_clm (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i₁ : ι) (a₂ : ι × ι₀) (c₂ : Fin (m + 1)) (b : B)
    (hb : b ∈ (sumQuotient ι₀ Z).baseSet (a₂, c₂)) :
    ((sumQuotient ι₀ Z).coordChange ((sumQuotient ι₀ Z).indexAt b) (a₂, c₂) b).comp
        ((sumToQ ι₀ Z b).comp (Z.coordChange i₁ (Z.indexAt b) b))
      = (quoCLM c₂ (sumUnit m)).comp ((jCLM m).comp
          ((Z.coordChange (Z.indexAt b) a₂.1 b).comp (Z.coordChange i₁ (Z.indexAt b) b))) := by
  refine ContinuousLinearMap.ext fun y => ?_
  exact sumQuotient_coordChange_sumToQ ι₀ Z i₁ a₂ c₂ b hb y

/-- **The chart expression of `Work.Thom.sumToZ`**, pointwise. -/
theorem sumQuotient_coordChange_sumToZ (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (a₁ : ι × ι₀) (c₁ : Fin (m + 1)) (i₂ : ι) (b : B) (z : EuclideanSpace ℂ (Fin m)) :
    (Z.coordChange (Z.indexAt b) i₂ b)
        (sumToZ ι₀ Z b ((sumQuotient ι₀ Z).coordChange (a₁, c₁)
          ((sumQuotient ι₀ Z).indexAt b) b z))
      = (Z.coordChange (Z.indexAt b) i₂ b)
          (Z.coordChange a₁.1 (Z.indexAt b) b (EpartCLM m (fillFun c₁ z))) := by
  have hw : (sumUnit m) (sumCoord ι₀ Z b) ≠ 0 := sumUnit_sumCoord_ne_zero ι₀ Z b
  rw [sumQuotient_coordChange_apply, sumQuotient_indexAt_fst, sumQuotient_indexAt_snd]
  rw [sumToZ, ContinuousLinearMap.comp_apply, fillCLM_apply, fillFun_quoFun _ _ _ hw]
  rw [map_sub, map_smul, EpartCLM_sumUnit, smul_zero, sub_zero]
  rw [sumEps_coordChange_Epart]

/-- The same identity, as an identity of **continuous linear maps**. -/
theorem sumQuotient_coordChange_sumToZ_clm (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (a₁ : ι × ι₀) (c₁ : Fin (m + 1)) (i₂ : ι) (b : B) :
    ((Z.coordChange (Z.indexAt b) i₂ b).comp
        ((sumToZ ι₀ Z b).comp ((sumQuotient ι₀ Z).coordChange (a₁, c₁)
          ((sumQuotient ι₀ Z).indexAt b) b)))
      = ((Z.coordChange (Z.indexAt b) i₂ b).comp (Z.coordChange a₁.1 (Z.indexAt b) b)).comp
          ((EpartCLM m).comp (fillCLM c₁)) := by
  refine ContinuousLinearMap.ext fun z => ?_
  exact sumQuotient_coordChange_sumToZ ι₀ Z a₁ c₁ i₂ b z

/-! ## Continuity of the chart expressions -/

/-- The chart expression of the *identity* isomorphism of a bundle: the composite of a transition
function into the preferred chart and one out of it is a transition function. -/
theorem continuousOn_coordChange_indexAt_comp {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} (Z : VectorBundleCore 𝕜 B F ι) (i i' : ι) :
    ContinuousOn (fun b : B =>
      (Z.coordChange (Z.indexAt b) i' b).comp (Z.coordChange i (Z.indexAt b) b))
      (Z.baseSet i ∩ Z.baseSet i') := by
  refine (Z.continuousOn_coordChange i i').congr (fun b hb => ?_)
  ext v
  exact Z.coordChange_comp i (Z.indexAt b) i' b ⟨⟨hb.1, Z.mem_baseSet_at b⟩, hb.2⟩ v

/-- A chart of the pullback of the tautological quotient lies over a chart of `Z`. -/
theorem sumQuotient_mem_baseSet_base (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (a : ι × ι₀) (c : Fin (m + 1)) (b : B)
    (hb : b ∈ (sumQuotient ι₀ Z).baseSet (a, c)) : b ∈ Z.baseSet a.1 := by
  have h := hb
  simp only [sumQuotient, bundleComap_baseSet, Set.mem_preimage] at h
  rw [tautQuotientCore_baseSet] at h
  simp only [tqBaseSet, Set.mem_ofPred_eq] at h
  have h1 : b ∈ (sumEps ι₀ Z).baseSet a := by
    simpa only [show (↑((sumSection ι₀ Z) b) : (realification (sumEps ι₀ Z)).TotalSpace)
      = sumPoint ι₀ Z b from rfl, show (sumPoint ι₀ Z b).proj = b from rfl] using h.1
  rw [sumEps_baseSet, bundleSum_baseSet] at h1
  exact h1.1

/-- **Continuity of the chart expression of `Work.Thom.sumToQ`** (the expression that the
continuity of the total-space map of `sumToQ` requires). -/
theorem continuousOn_sumToQ_chart (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i₁ : ι) (i₂ : (ι × ι₀) × Fin (m + 1)) :
    ContinuousOn (fun b : B =>
      ((sumQuotient ι₀ Z).coordChange ((sumQuotient ι₀ Z).indexAt b) i₂ b).comp
        ((sumToQ ι₀ Z b).comp (Z.coordChange i₁ (Z.indexAt b) b)))
      (Z.baseSet i₁ ∩ (sumQuotient ι₀ Z).baseSet i₂) := by
  have hsub : Z.baseSet i₁ ∩ (sumQuotient ι₀ Z).baseSet i₂ ⊆ Z.baseSet i₁ ∩ Z.baseSet i₂.1.1 := by
    intro b hb
    exact ⟨hb.1, sumQuotient_mem_baseSet_base ι₀ Z i₂.1 i₂.2 b hb.2⟩
  have hQ : ContinuousOn (fun _ : B => quoCLM i₂.2 (sumUnit m))
      (Z.baseSet i₁ ∩ (sumQuotient ι₀ Z).baseSet i₂) := continuousOn_const
  have hJ : ContinuousOn (fun _ : B => jCLM m)
      (Z.baseSet i₁ ∩ (sumQuotient ι₀ Z).baseSet i₂) := continuousOn_const
  have hC : ContinuousOn (fun b : B =>
      (Z.coordChange (Z.indexAt b) i₂.1.1 b).comp (Z.coordChange i₁ (Z.indexAt b) b))
      (Z.baseSet i₁ ∩ (sumQuotient ι₀ Z).baseSet i₂) :=
    (continuousOn_coordChange_indexAt_comp Z i₁ i₂.1.1).mono hsub
  refine (hQ.clm_comp (hJ.clm_comp hC)).congr ?_
  intro b hb
  exact sumQuotient_coordChange_sumToQ_clm ι₀ Z i₁ i₂.1 i₂.2 b hb.2

/-- **Continuity of the chart expression of `Work.Thom.sumToZ`**. -/
theorem continuousOn_sumToZ_chart (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i₁ : (ι × ι₀) × Fin (m + 1)) (i₂ : ι) :
    ContinuousOn (fun b : B =>
      (Z.coordChange (Z.indexAt b) i₂ b).comp
        ((sumToZ ι₀ Z b).comp
          ((sumQuotient ι₀ Z).coordChange i₁ ((sumQuotient ι₀ Z).indexAt b) b)))
      ((sumQuotient ι₀ Z).baseSet i₁ ∩ Z.baseSet i₂) := by
  have hsub : (sumQuotient ι₀ Z).baseSet i₁ ∩ Z.baseSet i₂ ⊆ Z.baseSet i₁.1.1 ∩ Z.baseSet i₂ := by
    intro b hb
    exact ⟨sumQuotient_mem_baseSet_base ι₀ Z i₁.1 i₁.2 b hb.1, hb.2⟩
  have hC : ContinuousOn (fun b : B =>
      (Z.coordChange (Z.indexAt b) i₂ b).comp (Z.coordChange i₁.1.1 (Z.indexAt b) b))
      ((sumQuotient ι₀ Z).baseSet i₁ ∩ Z.baseSet i₂) :=
    (continuousOn_coordChange_indexAt_comp Z i₁.1.1 i₂).mono hsub
  have hK : ContinuousOn (fun _ : B => (EpartCLM m).comp (fillCLM i₁.2))
      ((sumQuotient ι₀ Z).baseSet i₁ ∩ Z.baseSet i₂) := continuousOn_const
  refine (hC.clm_comp hK).congr ?_
  intro b hb
  exact sumQuotient_coordChange_sumToZ_clm ι₀ Z i₁.1 i₁.2 i₂ b

/-! ## The isomorphism `s^*(Z ⊕ ε¹ / ℂ·s) ≅ Z` and stability -/

/-- **The canonical isomorphism `s^*(Z ⊕ ε¹ / ℂ·s) ≅ Z`** of the pullback of the tautological
quotient of the sum along the tautological section with `Z` itself. -/
noncomputable def sumIso (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    BundleIso Z (sumQuotient ι₀ Z) where
  hom b := (sumToQ ι₀ Z b).toLinearMap
  inv b := (sumToZ ι₀ Z b).toLinearMap
  left_inv b x := sumToZ_sumToQ Z b x
  right_inv b y := sumToQ_sumToZ Z b y
  continuous_hom := continuous_totalSpaceMap_clm Z (sumQuotient ι₀ Z) (ContinuousMap.id B)
    (sumToQ ι₀ Z) (fun i₁ i₂ => continuousOn_sumToQ_chart ι₀ Z i₁ i₂)
  continuous_inv := continuous_totalSpaceMap_clm (sumQuotient ι₀ Z) Z (ContinuousMap.id B)
    (sumToZ ι₀ Z) (fun i₁ i₂ => continuousOn_sumToZ_chart ι₀ Z i₁ i₂)

/-- **Isomorphism-invariance, applied**: the Chern classes of the pullback of the tautological
quotient along the tautological section are those of `Z`. -/
theorem chernClass_sumQuotient [Fintype ι] [Fintype ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (j : ℕ) :
    chernClass m j (sumQuotient ι₀ Z) = chernClass m j Z :=
  (chernClass_BundleIso Z (sumQuotient ι₀ Z) (sumIso ι₀ Z)).symm

/-- The projection of the punctured total space of the sum `Z ⊕ ε¹` used in the stability proof. -/
abbrev sumPi (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    C(↥(zeroComplement (realification (sumEps ι₀ Z))), B) :=
  (bundleProj (realification (sumEps ι₀ Z))).comp
    (subtypeMap (zeroComplement (realification (sumEps ι₀ Z))))

/-- The projection of the punctured total space of the sum has the tautological section as a
section. -/
theorem sumPi_comp_sumSection (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (sumPi ι₀ Z).comp (sumSection ι₀ Z) = ContinuousMap.id B := by
  ext b
  rfl

/-- **`π^*` after `s^*` is the identity on the cohomology of the base**, for the projection of the
punctured total space of the sum and its tautological section. -/
theorem CohMap_sumPi_comp_sumSection (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (k : ℕ) :
    ((CohMap (sumSection ι₀ Z) ℤ k).hom).comp ((CohMap (sumPi ι₀ Z) ℤ k).hom) = LinearMap.id := by
  have h := CohMap_comp (sumSection ι₀ Z) (sumPi ι₀ Z) ℤ k
  rw [sumPi_comp_sumSection, CohMap_id] at h
  have h2 := congrArg (fun g : Coh ℤ k B ⟶ Coh ℤ k B => g.hom) h
  simpa [ModuleCat.hom_comp] using h2.symm

/-- **STABILITY**: the Chern classes do not change when a trivial line bundle is added. -/
theorem chernClass_sumEps [Fintype ι] [Fintype ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (j : ℕ) :
    chernClass (m + 1) j (sumEps ι₀ Z) = chernClass m j Z := by
  by_cases hle : j ≤ m
  · have hdes := chernClass_succ_of_le (m := m) (sumEps ι₀ Z) hle
    set eZ := LinearEquiv.ofBijective ((CohMap (sumPi ι₀ Z) ℤ (2 * j)).hom)
      (bijective_proj_zeroComplementA (realification (sumEps ι₀ Z))
        (finrank_real_euclidean_complex (m + 1))
        (thomClassRank (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) (sumEps ι₀ Z))
        (by omega)) with heZ
    have h1 : (CohMap (sumPi ι₀ Z) ℤ (2 * j)).hom (chernClass (m + 1) j (sumEps ι₀ Z))
        = chernClass m j (tautQuotient (m := m) (sumEps ι₀ Z)) := by
      rw [hdes]
      exact LinearEquiv.apply_symm_apply eZ _
    have h2 : (CohMap (sumSection ι₀ Z) ℤ (2 * j)).hom
        ((CohMap (sumPi ι₀ Z) ℤ (2 * j)).hom (chernClass (m + 1) j (sumEps ι₀ Z)))
        = chernClass (m + 1) j (sumEps ι₀ Z) :=
      LinearMap.congr_fun (CohMap_sumPi_comp_sumSection ι₀ Z (2 * j))
        (chernClass (m + 1) j (sumEps ι₀ Z))
    have h3 : (CohMap (sumSection ι₀ Z) ℤ (2 * j)).hom
        (chernClass m j (tautQuotient (m := m) (sumEps ι₀ Z)))
        = chernClass m j (sumQuotient ι₀ Z) := by
      rw [← chernClass_comap (tautQuotient (m := m) (sumEps ι₀ Z)) (sumSection ι₀ Z)]
      rfl
    rw [← h2, h1, h3, chernClass_sumQuotient]
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · -- `m = 0`: the sum is a complex line bundle, so its only Chern class is the top one.
      subst hm
      by_cases hj1 : j = 1
      · subst hj1
        rw [chernClass_top_eq_zero_of_nowhereZeroSection (m := 1) (by omega) (sumEps ι₀ Z)
          ((subtypeMap (zeroComplement (realification (sumEps ι₀ Z)))).comp (sumSection ι₀ Z))
          (fun x => rfl) (fun x => sumPoint_ne_zero ι₀ Z x), chernClass_zero_rank]
        unfold chernClassZero
        rw [dif_neg (by omega : ¬ (1 : ℕ) = 0)]
      · rw [chernClass_succ_of_gt (sumEps ι₀ Z) (by omega), chernClass_zero_rank]
        unfold chernClassZero
        rw [dif_neg (by omega : ¬ j = 0)]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      by_cases htop : j = k + 1 + 1
      · subst htop
        rw [chernClass_top_eq_zero_of_nowhereZeroSection (m := k + 1 + 1) (by omega) (sumEps ι₀ Z)
          ((subtypeMap (zeroComplement (realification (sumEps ι₀ Z)))).comp (sumSection ι₀ Z))
          (fun x => rfl) (fun x => sumPoint_ne_zero ι₀ Z x),
          chernClass_succ_of_gt Z (by omega)]
      · rw [chernClass_succ_of_gt (sumEps ι₀ Z) (by omega), chernClass_succ_of_gt Z (by omega)]

end

end Work.Thom
