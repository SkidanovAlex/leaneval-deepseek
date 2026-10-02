import Mathlib
import Submission.Work.LerayHirsch.ProjIsoOfBundleIso
import Submission.Work.LerayHirsch.TautLine
import Submission.Work.Thom.coreMorphism

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Naturality of the tautological line bundle under an isomorphism of the underlying bundle

For `e : BundleIso Z Z'`, the pullback of the tautological line bundle `ℓ_{Z'}` along the induced
map `projIsoMap Z Z' e : P(Z) → P(Z')` is isomorphic to `ℓ_Z`.  Both gluing data are of rank one
with the model fibre, so the isomorphism is given fibrewise by a nonzero scalar; the scalar that
makes the two chart systems agree is

`c x := chartCoord Z' i'.1 (punctIsoMap Z Z' e p) i'.2 / chartCoord Z i.1 p i.2`

(with `p` a representative of `x = mkProj Z p`, `i = (tautLine Z).indexAt x` and
`i' = (tautLine Z').indexAt (projIsoMap Z Z' e x)`), a representative-independent quantity.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι ι' : Type} {m : ℕ}

/-! ## The normalising scalar -/

/-- The `k`-th coordinate of a `ℂ`-multiple of a vector of the Euclidean space. -/
theorem smul_coord {m : ℕ} (c : ℂ) (v : EuclideanSpace ℂ (Fin m)) (k : Fin m) :
    (c • v) k = c * v k := by
  simp only [PiLp.smul_apply]
  exact smul_eq_mul c (v k)

/-- **The scalar comparing the tautological frames at a point**, on representatives:
`chartCoord Z' i' q k' / chartCoord Z i p k`, where `i` and `i'` are the *preferred* charts of the
two tautological line bundles and `q = punctIsoMap Z Z' e p`. -/
noncomputable def tautIsoCoeffFun (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (p : ↥(zeroComplement (realification Z))) : ℂ :=
  chartCoord Z' ((tautLine Z').indexAt (mkProj Z' (punctIsoMap Z Z' e p))).1
      (punctIsoMap Z Z' e p) ((tautLine Z').indexAt (mkProj Z' (punctIsoMap Z Z' e p))).2
    / chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
      ((tautLine Z).indexAt (mkProj Z p)).2

/-- The numerator of `tautIsoCoeffFun` does not vanish. -/
theorem chartCoord_pref_ne_zero_left (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) :
    chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
      ((tautLine Z).indexAt (mkProj Z p)).2 ≠ 0 :=
  ((mem_tautBaseSetProj_mk Z ((tautLine Z).indexAt (mkProj Z p)) p).mp
    ((tautLine Z).mem_baseSet_at (mkProj Z p))).2

/-- The denominator of `tautIsoCoeffFun` does not vanish. -/
theorem chartCoord_pref_ne_zero_right (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (q : ↥(zeroComplement (realification Z'))) :
    chartCoord Z' ((tautLine Z').indexAt (mkProj Z' q)).1 q
      ((tautLine Z').indexAt (mkProj Z' q)).2 ≠ 0 :=
  ((mem_tautBaseSetProj_mk Z' ((tautLine Z').indexAt (mkProj Z' q)) q).mp
    ((tautLine Z').mem_baseSet_at (mkProj Z' q))).2

/-- **`tautIsoCoeffFun` is invariant under the `ℂˣ`-action**, hence descends to `P(Z)`. -/
theorem tautIsoCoeffFun_smulPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (c : ℂˣ) (p : ↥(zeroComplement (realification Z))) :
    tautIsoCoeffFun Z Z' e (smulPunct Z c p) = tautIsoCoeffFun Z Z' e p := by
  have hx : mkProj Z (smulPunct Z c p) = mkProj Z p := by
    rw [mkProj_eq_iff]; exact ⟨c, rfl⟩
  have hy : mkProj Z' (punctIsoMap Z Z' e (smulPunct Z c p)) = mkProj Z' (punctIsoMap Z Z' e p) := by
    rw [punctIsoMap_smulPunct, mkProj_eq_iff]; exact ⟨c, rfl⟩
  simp only [tautIsoCoeffFun]
  rw [hx, hy, punctIsoMap_smulPunct, chartCoord_smulPunct, chartCoord_smulPunct]
  simp only [smul_coord]
  rw [mul_div_mul_left _ _ (Units.ne_zero c)]

/-- **The normalising scalar** `c : P(Z) → ℂ`, well defined by the preceding lemma. -/
noncomputable def tautIsoCoeff (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z') :
    ProjSpace Z → ℂ :=
  Quotient.lift (tautIsoCoeffFun Z Z' e) (fun a b h => by
    obtain ⟨c, hc⟩ := h
    rw [← hc, tautIsoCoeffFun_smulPunct])

@[simp] theorem tautIsoCoeff_mk (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (p : ↥(zeroComplement (realification Z))) :
    tautIsoCoeff Z Z' e (mkProj Z p) = tautIsoCoeffFun Z Z' e p := rfl

/-- The normalising scalar does not vanish. -/
theorem tautIsoCoeff_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (x : ProjSpace Z) : tautIsoCoeff Z Z' e x ≠ 0 := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  rw [tautIsoCoeff_mk, tautIsoCoeffFun]
  exact div_ne_zero (chartCoord_pref_ne_zero_right Z' (punctIsoMap Z Z' e p))
    (chartCoord_pref_ne_zero_left Z p)

/-! ## The frame ratio of the two tautological charts

The scalar `chartCoord Z' i' (punctIsoMap Z Z' e p) k' / chartCoord Z i p k` is independent of the
representative `p` of `x = mkProj Z p` and is continuous on the piece on which both charts are
defined; it is the local matrix of the isomorphism. -/

/-- **The frame ratio**, on representatives. -/
noncomputable def frameRatioFun (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (i : ι) (k : Fin m) (i' : ι') (k' : Fin m) (p : ↥(zeroComplement (realification Z))) : ℂ :=
  chartCoord Z' i' (punctIsoMap Z Z' e p) k' / chartCoord Z i p k

/-- The frame ratio is invariant under the `ℂˣ`-action. -/
theorem frameRatioFun_smulPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (i : ι) (k : Fin m) (i' : ι') (k' : Fin m) (c : ℂˣ)
    (p : ↥(zeroComplement (realification Z))) :
    frameRatioFun Z Z' e i k i' k' (smulPunct Z c p) = frameRatioFun Z Z' e i k i' k' p := by
  simp only [frameRatioFun]
  rw [punctIsoMap_smulPunct, chartCoord_smulPunct, chartCoord_smulPunct]
  simp only [smul_coord]
  rw [mul_div_mul_left _ _ (Units.ne_zero c)]

/-- **The frame ratio**, as a function of `P(Z)`. -/
noncomputable def frameRatio (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (i : ι) (k : Fin m) (i' : ι') (k' : Fin m) : ProjSpace Z → ℂ :=
  Quotient.lift (frameRatioFun Z Z' e i k i' k') (fun a b h => by
    obtain ⟨c, hc⟩ := h
    rw [← hc, frameRatioFun_smulPunct])

@[simp] theorem frameRatio_mk (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (i : ι) (k : Fin m) (i' : ι') (k' : Fin m)
    (p : ↥(zeroComplement (realification Z))) :
    frameRatio Z Z' e i k i' k' (mkProj Z p) = frameRatioFun Z Z' e i k i' k' p := rfl

/-- **Continuity of the frame ratio** on the piece where both charts are defined. -/
theorem continuousOn_frameRatio (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (i : ι) (k : Fin m) (i' : ι') (k' : Fin m) :
    ContinuousOn (frameRatio Z Z' e i k i' k')
      (tautBaseSetProj Z (i, k)
        ∩ (projIsoMap Z Z' e) ⁻¹' tautBaseSetProj Z' (i', k')) := by
  refine (Topology.IsQuotientMap.continuousOn_isOpen_iff (f := mkProj Z)
    (isQuotientMap_quotient_mk' (s := projSetoid Z)) ?_).mpr ?_
  · exact (isOpen_tautBaseSetProj Z (i, k)).inter
      ((isOpen_tautBaseSetProj Z' (i', k')).preimage (projIsoMap Z Z' e).continuous)
  · have h2 : (mkProj Z) ⁻¹' ((projIsoMap Z Z' e) ⁻¹' tautBaseSetProj Z' (i', k'))
        = (punctIsoMap Z Z' e) ⁻¹' tautBaseSet Z' i' k' := by
      have hcomp : (⇑(projIsoMap Z Z' e)) ∘ (mkProj Z)
          = (mkProj Z') ∘ (punctIsoMap Z Z' e) := by
        funext p
        exact projIsoMap_mkProj Z Z' e p
      rw [← Set.preimage_comp, hcomp, Set.preimage_comp, preimage_tautBaseSetProj]
    have hpre : (mkProj Z) ⁻¹' (tautBaseSetProj Z (i, k)
        ∩ (projIsoMap Z Z' e) ⁻¹' tautBaseSetProj Z' (i', k'))
        = tautBaseSet Z i k ∩ (punctIsoMap Z Z' e) ⁻¹' tautBaseSet Z' i' k' := by
      rw [Set.preimage_inter, preimage_tautBaseSetProj, h2]
    rw [hpre]
    have hnum : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
        chartCoord Z' i' (punctIsoMap Z Z' e p) k')
        (tautBaseSet Z i k ∩ (punctIsoMap Z Z' e) ⁻¹' tautBaseSet Z' i' k') := by
      have hbase : Set.MapsTo (punctIsoMap Z Z' e)
          (tautBaseSet Z i k ∩ (punctIsoMap Z Z' e) ⁻¹' tautBaseSet Z' i' k')
          {q : ↥(zeroComplement (realification Z')) | q.1.proj ∈ Z'.baseSet i'} :=
        fun p hp => ((mem_tautBaseSet Z' i' k' (punctIsoMap Z Z' e p)).mp hp.2).1
      have h1 : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
          chartCoord Z' i' (punctIsoMap Z Z' e p))
          (tautBaseSet Z i k ∩ (punctIsoMap Z Z' e) ⁻¹' tautBaseSet Z' i' k') :=
        (continuousOn_chartCoord Z' i').comp
          (punctIsoHomeo Z Z' e).continuous.continuousOn hbase
      exact (by fun_prop : Continuous (fun v : EuclideanSpace ℂ (Fin m) => v k')).comp_continuousOn
        h1
    have hden : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
        chartCoord Z i p k)
        (tautBaseSet Z i k ∩ (punctIsoMap Z Z' e) ⁻¹' tautBaseSet Z' i' k') := by
      have hbase : Set.MapsTo (id : ↥(zeroComplement (realification Z)) →
          ↥(zeroComplement (realification Z)))
          (tautBaseSet Z i k ∩ (punctIsoMap Z Z' e) ⁻¹' tautBaseSet Z' i' k')
          {p : ↥(zeroComplement (realification Z)) | p.1.proj ∈ Z.baseSet i} :=
        fun p hp => ((mem_tautBaseSet Z i k p).mp hp.1).1
      have h1 := (continuousOn_chartCoord Z i).comp continuousOn_id hbase
      exact (by fun_prop : Continuous (fun v : EuclideanSpace ℂ (Fin m) => v k)).comp_continuousOn h1
    refine (hnum.div hden ?_).congr (fun p hp => ?_)
    · intro p hp
      exact ((mem_tautBaseSet Z i k p).mp hp.1).2
    · rfl

/-- **The frame ratio does not vanish** on the piece on which both charts are defined. -/
theorem frameRatio_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    {i₁ : ι × Fin m} {i₂ : ι' × Fin m} {x : ProjSpace Z}
    (h₁ : x ∈ tautBaseSetProj Z i₁) (h₂ : projIsoMap Z Z' e x ∈ tautBaseSetProj Z' i₂) :
    frameRatio Z Z' e i₁.1 i₁.2 i₂.1 i₂.2 x ≠ 0 := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  set q := punctIsoMap Z Z' e p with hq
  have hqmk : mkProj Z' q = projIsoMap Z Z' e (mkProj Z p) :=
    (projIsoMap_mkProj Z Z' e p).symm
  have h1 : chartCoord Z i₁.1 p i₁.2 ≠ 0 := ((mem_tautBaseSetProj_mk Z i₁ p).mp h₁).2
  have h2 : chartCoord Z' i₂.1 q i₂.2 ≠ 0 :=
    ((mem_tautBaseSetProj_mk Z' i₂ q).mp (hqmk ▸ h₂)).2
  have hD : frameRatio Z Z' e i₁.1 i₁.2 i₂.1 i₂.2 (mkProj Z p)
      = chartCoord Z' i₂.1 q i₂.2 / chartCoord Z i₁.1 p i₁.2 := rfl
  rw [hD]
  exact div_ne_zero h2 h1

/-! ## The scalar identities -/

/-- **The local matrix of the induced isomorphism** in the charts `i₁` of `ℓ_Z` and `i₂` of
`ℓ_{Z'}` is the frame ratio: the two coordinate changes multiplied by the normalising scalar give
`chartCoord Z' i₂.1 q i₂.2 / chartCoord Z i₁.1 p i₁.2`. -/
theorem tautCoeffLift_mul_tautIsoCoeff_mul
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    {i₁ : ι × Fin m} {i₂ : ι' × Fin m} {x : ProjSpace Z}
    (h₁ : x ∈ tautBaseSetProj Z i₁) (h₂ : projIsoMap Z Z' e x ∈ tautBaseSetProj Z' i₂) :
    (tautCoeffLift Z' ((tautLine Z').indexAt (projIsoMap Z Z' e x)) i₂
        (projIsoMap Z Z' e x) * tautIsoCoeff Z Z' e x)
      * tautCoeffLift Z i₁ ((tautLine Z).indexAt x) x
      = frameRatio Z Z' e i₁.1 i₁.2 i₂.1 i₂.2 x := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  set q := punctIsoMap Z Z' e p with hq
  have hqmk : mkProj Z' q = projIsoMap Z Z' e (mkProj Z p) :=
    (projIsoMap_mkProj Z Z' e p).symm
  have h1 : chartCoord Z i₁.1 p i₁.2 ≠ 0 := ((mem_tautBaseSetProj_mk Z i₁ p).mp h₁).2
  have h2 : chartCoord Z' i₂.1 q i₂.2 ≠ 0 :=
    ((mem_tautBaseSetProj_mk Z' i₂ q).mp (hqmk ▸ h₂)).2
  have hA := tautLine_coordChange_eq_ratio Z' ((tautLine Z').indexAt (mkProj Z' q)) i₂ q
    (chartCoord_pref_ne_zero_right Z' q)
  have hB := tautLine_coordChange_eq_ratio Z i₁ ((tautLine Z).indexAt (mkProj Z p)) p h1
  have hC : tautIsoCoeff Z Z' e (mkProj Z p)
      = chartCoord Z' ((tautLine Z').indexAt (mkProj Z' q)).1 q
          ((tautLine Z').indexAt (mkProj Z' q)).2
        / chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
          ((tautLine Z).indexAt (mkProj Z p)).2 := rfl
  have hD : frameRatio Z Z' e i₁.1 i₁.2 i₂.1 i₂.2 (mkProj Z p)
      = chartCoord Z' i₂.1 q i₂.2 / chartCoord Z i₁.1 p i₁.2 := rfl
  have hd1 : chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
      ((tautLine Z).indexAt (mkProj Z p)).2 ≠ 0 := chartCoord_pref_ne_zero_left Z p
  have hd2 : chartCoord Z' ((tautLine Z').indexAt (mkProj Z' q)).1 q
      ((tautLine Z').indexAt (mkProj Z' q)).2 ≠ 0 := chartCoord_pref_ne_zero_right Z' q
  rw [hqmk] at hA
  rw [hA, hB, hC, hD, ← hqmk]
  field_simp

/-- **The scalar identity for the inverse direction**: the local matrix of the inverse isomorphism
is the inverse of the frame ratio. -/
theorem tautCoeffLift_mul_inv_tautIsoCoeff_mul
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    {i₁ : ι × Fin m} {i₂ : ι' × Fin m} {x : ProjSpace Z}
    (h₁ : x ∈ tautBaseSetProj Z i₁) (h₂ : projIsoMap Z Z' e x ∈ tautBaseSetProj Z' i₂) :
    (tautCoeffLift Z ((tautLine Z).indexAt x) i₁ x * (tautIsoCoeff Z Z' e x)⁻¹)
      * tautCoeffLift Z' i₂ ((tautLine Z').indexAt (projIsoMap Z Z' e x)) (projIsoMap Z Z' e x)
      = (frameRatio Z Z' e i₁.1 i₁.2 i₂.1 i₂.2 x)⁻¹ := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  set q := punctIsoMap Z Z' e p with hq
  have hqmk : mkProj Z' q = projIsoMap Z Z' e (mkProj Z p) :=
    (projIsoMap_mkProj Z Z' e p).symm
  have h1 : chartCoord Z i₁.1 p i₁.2 ≠ 0 := ((mem_tautBaseSetProj_mk Z i₁ p).mp h₁).2
  have h2 : chartCoord Z' i₂.1 q i₂.2 ≠ 0 :=
    ((mem_tautBaseSetProj_mk Z' i₂ q).mp (hqmk ▸ h₂)).2
  have hA := tautLine_coordChange_eq_ratio Z ((tautLine Z).indexAt (mkProj Z p)) i₁ p
    (chartCoord_pref_ne_zero_left Z p)
  have hB := tautLine_coordChange_eq_ratio Z' i₂ ((tautLine Z').indexAt (mkProj Z' q)) q h2
  have hC : tautIsoCoeff Z Z' e (mkProj Z p)
      = chartCoord Z' ((tautLine Z').indexAt (mkProj Z' q)).1 q
          ((tautLine Z').indexAt (mkProj Z' q)).2
        / chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
          ((tautLine Z).indexAt (mkProj Z p)).2 := rfl
  have hD : frameRatio Z Z' e i₁.1 i₁.2 i₂.1 i₂.2 (mkProj Z p)
      = chartCoord Z' i₂.1 q i₂.2 / chartCoord Z i₁.1 p i₁.2 := rfl
  have hd1 : chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
      ((tautLine Z).indexAt (mkProj Z p)).2 ≠ 0 := chartCoord_pref_ne_zero_left Z p
  have hd2 : chartCoord Z' ((tautLine Z').indexAt (mkProj Z' q)).1 q
      ((tautLine Z').indexAt (mkProj Z' q)).2 ≠ 0 := chartCoord_pref_ne_zero_right Z' q
  rw [hqmk] at hB
  rw [hA, hB, hC, hD, ← hqmk]
  field_simp

/-! ## The isomorphism -/

/-- **The isomorphism `ℓ_Z ≅ P(e)^*ℓ_{Z'}`** between the tautological line bundle of `Z` and the
pullback along the induced map of projectivisations of the tautological line bundle of `Z'`. -/
noncomputable def tautLineBundleIso (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z') :
    BundleIso (tautLine Z) (bundleComap (tautLine Z') (projIsoMap Z Z' e)) where
  hom := fun x => tautIsoCoeff Z Z' e x • (LinearMap.id : LineFibre →ₗ[ℂ] LineFibre)
  inv := fun x => (tautIsoCoeff Z Z' e x)⁻¹ • (LinearMap.id : LineFibre →ₗ[ℂ] LineFibre)
  left_inv := fun x v => by
    change (tautIsoCoeff Z Z' e x)⁻¹ • (tautIsoCoeff Z Z' e x • v) = v
    rw [smul_smul, inv_mul_cancel₀ (tautIsoCoeff_ne_zero Z Z' e x), one_smul]
  right_inv := fun x v => by
    change tautIsoCoeff Z Z' e x • ((tautIsoCoeff Z Z' e x)⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (tautIsoCoeff_ne_zero Z Z' e x), one_smul]
  continuous_hom := by
    refine (continuous_totalSpaceMap_clm (tautLine Z)
      (bundleComap (tautLine Z') (projIsoMap Z Z' e)) (ContinuousMap.id (ProjSpace Z))
      (fun x => tautIsoCoeff Z Z' e x • (ContinuousLinearMap.id ℂ LineFibre)) ?_).congr
      (fun p => rfl)
    intro i₁ i₂
    have hbase : (tautLine Z).baseSet i₁
          ∩ ⇑(ContinuousMap.id (ProjSpace Z)) ⁻¹'
              (bundleComap (tautLine Z') (projIsoMap Z Z' e)).baseSet i₂
        = tautBaseSetProj Z i₁ ∩ (projIsoMap Z Z' e) ⁻¹' tautBaseSetProj Z' i₂ := by
      rw [ContinuousMap.coe_id, Set.preimage_id, tautLine_baseSet, bundleComap_baseSet,
        tautLine_baseSet]
    rw [hbase]
    refine ((continuousOn_frameRatio Z Z' e i₁.1 i₁.2 i₂.1 i₂.2).smul
      (continuousOn_const : ContinuousOn
        (fun _ : ProjSpace Z =>
          (ContinuousLinearMap.id ℂ LineFibre : LineFibre →L[ℂ] LineFibre))
        (tautBaseSetProj Z i₁
          ∩ (projIsoMap Z Z' e) ⁻¹' tautBaseSetProj Z' i₂))).congr ?_
    intro x hx
    change ((bundleComap (tautLine Z') (projIsoMap Z Z' e)).coordChange
          ((bundleComap (tautLine Z') (projIsoMap Z Z' e)).indexAt x) i₂ x).comp
        (((tautIsoCoeff Z Z' e x) • (ContinuousLinearMap.id ℂ LineFibre)).comp
          ((tautLine Z).coordChange i₁ ((tautLine Z).indexAt x) x))
      = frameRatio Z Z' e i₁.1 i₁.2 i₂.1 i₂.2 x • (ContinuousLinearMap.id ℂ LineFibre)
    have hV : (bundleComap (tautLine Z') (projIsoMap Z Z' e)).coordChange
          ((bundleComap (tautLine Z') (projIsoMap Z Z' e)).indexAt x) i₂ x
        = tautCoeffCLM Z' ((tautLine Z').indexAt (projIsoMap Z Z' e x)) i₂
            (projIsoMap Z Z' e x) := by
      rw [bundleComap_coordChange, bundleComap_indexAt, tautLine_coordChange]
    have hW : (tautLine Z).coordChange i₁ ((tautLine Z).indexAt x) x
        = tautCoeffCLM Z i₁ ((tautLine Z).indexAt x) x := rfl
    rw [hV, hW, tautCoeffCLM, tautCoeffCLM]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    rw [smul_smul, smul_smul,
      tautCoeffLift_mul_tautIsoCoeff_mul Z Z' e hx.1 hx.2]
  continuous_inv := by
    refine (continuous_totalSpaceMap_clm
      (bundleComap (tautLine Z') (projIsoMap Z Z' e)) (tautLine Z) (ContinuousMap.id (ProjSpace Z))
      (fun x => (tautIsoCoeff Z Z' e x)⁻¹ • (ContinuousLinearMap.id ℂ LineFibre)) ?_).congr
      (fun p => rfl)
    intro i₂ i₁
    have hbase : (bundleComap (tautLine Z') (projIsoMap Z Z' e)).baseSet i₂
          ∩ ⇑(ContinuousMap.id (ProjSpace Z)) ⁻¹' (tautLine Z).baseSet i₁
        = tautBaseSetProj Z i₁ ∩ (projIsoMap Z Z' e) ⁻¹' tautBaseSetProj Z' i₂ := by
      rw [ContinuousMap.coe_id, Set.preimage_id, tautLine_baseSet, bundleComap_baseSet,
        tautLine_baseSet, Set.inter_comm]
    rw [hbase]
    refine (((continuousOn_frameRatio Z Z' e i₁.1 i₁.2 i₂.1 i₂.2).inv₀
      (fun x hx => frameRatio_ne_zero Z Z' e hx.1 hx.2)).smul
      (continuousOn_const : ContinuousOn
        (fun _ : ProjSpace Z =>
          (ContinuousLinearMap.id ℂ LineFibre : LineFibre →L[ℂ] LineFibre))
        (tautBaseSetProj Z i₁
          ∩ (projIsoMap Z Z' e) ⁻¹' tautBaseSetProj Z' i₂))).congr ?_
    intro x hx
    change ((tautLine Z).coordChange ((tautLine Z).indexAt x) i₁ x).comp
        ((((tautIsoCoeff Z Z' e x)⁻¹) • (ContinuousLinearMap.id ℂ LineFibre)).comp
          ((bundleComap (tautLine Z') (projIsoMap Z Z' e)).coordChange i₂
            ((bundleComap (tautLine Z') (projIsoMap Z Z' e)).indexAt x) x))
      = (frameRatio Z Z' e i₁.1 i₁.2 i₂.1 i₂.2 x)⁻¹ • (ContinuousLinearMap.id ℂ LineFibre)
    have hV : (bundleComap (tautLine Z') (projIsoMap Z Z' e)).coordChange i₂
          ((bundleComap (tautLine Z') (projIsoMap Z Z' e)).indexAt x) x
        = tautCoeffCLM Z' i₂ ((tautLine Z').indexAt (projIsoMap Z Z' e x))
            (projIsoMap Z Z' e x) := by
      rw [bundleComap_coordChange, bundleComap_indexAt, tautLine_coordChange]
    have hW : (tautLine Z).coordChange ((tautLine Z).indexAt x) i₁ x
        = tautCoeffCLM Z ((tautLine Z).indexAt x) i₁ x := rfl
    rw [hV, hW, tautCoeffCLM, tautCoeffCLM]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    rw [smul_smul, smul_smul,
      tautCoeffLift_mul_inv_tautIsoCoeff_mul Z Z' e hx.1 hx.2]

/-- **Naturality of the tautological line bundle**: the pullback of `ℓ_{Z'}` along the induced map
of projectivisations is isomorphic to `ℓ_Z`. -/
theorem nonempty_tautLine_bundleIso_of_projIso
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z') :
    Nonempty (Work.Thom.BundleIso (Work.LerayHirsch.tautLine Z)
      (Work.Thom.bundleComap (Work.LerayHirsch.tautLine Z')
        (Work.LerayHirsch.projIsoMap Z Z' e))) :=
  ⟨tautLineBundleIso Z Z' e⟩

end

end Work.LerayHirsch
