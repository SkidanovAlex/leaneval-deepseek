import Mathlib
import Submission.Work.ThomBordism.Grassmann.P2Base.Gauge
import Submission.Work.ThomBordism.Grassmann.P2Base.coefL
import Submission.Work.ThomBordism.Grassmann.P2Base.spanC
import Submission.Work.ThomBordism.Grassmann.CxModel
import Submission.Work.ThomBordism.Grassmann.PlaneEval
import Submission.Work.ThomBordism.Grassmann.probePlane
import Submission.Work.Gen.tautDual_iso_conjLine
import Submission.Work.Thom.BundleIsoGauge
import Submission.Work.Thom.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

/-!
# The gauge `V₄ ≅ Z₄` (copy of P2Base/gaugeIso.lean, finished here)

The pullback `V4 = p2Map^* γ_{4,8}` of the tautological oriented `4`-plane bundle along
`p2Map : ℂP⁴ → G̃r₄(ℝ¹²)` is the realification of `O(-1) ⊕ O(-1)`; here we build the gauge
isomorphism `V4 ≅ Z4 = A4 ⊕_ℝ A4` explicitly, reading the coordinates of a plane vector in the
basis `(Λ(s_{t₁}), Λ'(s_{t₂}))`.
-/

namespace Work.ThomBordism.Grassmann.LowDegree

open Work.TangentClasses
open Work.ThomBordism.Grassmann.P2Base

noncomputable section

abbrev CP4 : Type := Work.Projective.CP 4

/-! ## Small continuous linear maps -/

/-- The coordinate `ℂ¹ → ℂ`. -/
noncomputable def c1ToCCLM : EuclideanSpace ℂ (Fin 1) →L[ℝ] ℂ :=
  (((ContinuousLinearMap.proj (φ := fun _ : Fin 1 => ℂ) (0 : Fin 1)) :
      (Fin 1 → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).comp
    (((EuclideanSpace.equiv (Fin 1) ℂ : EuclideanSpace ℂ (Fin 1) ≃L[ℂ] (Fin 1 → ℂ)) :
      EuclideanSpace ℂ (Fin 1) →L[ℂ] (Fin 1 → ℂ)).restrictScalars ℝ)

theorem c1ToCCLM_apply (z : EuclideanSpace ℂ (Fin 1)) : c1ToCCLM z = z.ofLp 0 := rfl

/-- `WithLp.ofLp` as an `ℝ`-linear continuous map. -/
noncomputable def ambOfLpCLM (n : ℕ) : Amb n →L[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ : Amb n ≃L[ℝ] (Fin n → ℝ))

theorem ambOfLpCLM_apply (n : ℕ) (v : Amb n) : ambOfLpCLM n v = v.ofLp := rfl

/-- `WithLp.toLp` as an `ℝ`-linear continuous map. -/
noncomputable def ambToLpCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] Amb n :=
  ((EuclideanSpace.equiv (Fin n) ℝ).symm : (Fin n → ℝ) →L[ℝ] Amb n)

theorem ambToLpCLM_apply (n : ℕ) (v : Fin n → ℝ) : ambToLpCLM n v = WithLp.toLp 2 v := rfl

/-- The splitting `ℝ² × ℝ² ≃ ℝ⁴` as a continuous linear map. -/
noncomputable def sumFibreRCLM : (Amb 2 × Amb 2) →L[ℝ] Amb 4 := Work.Whitney.sumFibreR 2 2

theorem sumFibreRCLM_apply (z : Amb 2 × Amb 2) : sumFibreRCLM z = Work.Whitney.sumFibreR 2 2 z :=
  rfl

/-- The linear map `v ↦ coordEval S f v` as a continuous linear map. -/
noncomputable def coordEvalCLM (S : ChartIdx 4 8) (f : Stiefel 4 8) : Amb 4 →L[ℝ] Amb 12 :=
  Finset.sum Finset.univ (fun i : Fin 4 =>
    (((ContinuousLinearMap.proj (φ := fun _ : Fin 4 => ℝ) i) :
        (Fin 4 → ℝ) →L[ℝ] ℝ).comp (ambOfLpCLM 4)).smulRight (coordVec S f i))

theorem coordEvalCLM_apply (S : ChartIdx 4 8) (f : Stiefel 4 8) (v : Amb 4) :
    coordEvalCLM S f v = coordEval S f v := by
  simp only [coordEvalCLM, ContinuousLinearMap.sum_apply, coordEval,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ambOfLpCLM_apply, smul_eq_mul]

/-- The complex number of a vector of the standard fibre `ℝ²`. -/
noncomputable def zOfCLM : Amb 2 →L[ℝ] ℂ :=
  c1ToCCLM.comp (equivC1R2.symm : Amb 2 →L[ℝ] EuclideanSpace ℂ (Fin 1))

/-- `ℂ⁶ → ℝ¹²`. -/
noncomputable def cE6CLM : E6 →L[ℝ] Amb 12 := cE6

/-- `ℝ¹² → ℂ⁶`. -/
noncomputable def cE6symmCLM : Amb 12 →L[ℝ] E6 := cE6.symm

theorem cE6CLM_apply (x : E6) : cE6CLM x = cE6 x := rfl
theorem cE6symmCLM_apply (x : Amb 12) : cE6symmCLM x = cE6.symm x := rfl

theorem cE6CLM_cE6symmCLM (y : Amb 12) : cE6CLM (cE6symmCLM y) = y :=
  LinearIsometryEquiv.apply_symm_apply cE6 y

theorem cE6symmCLM_cE6CLM (y : E6) : cE6symmCLM (cE6CLM y) = y :=
  LinearIsometryEquiv.symm_apply_apply cE6 y

/-- Right multiplication by a complex number, as an `ℝ`-linear continuous map. -/
noncomputable def hsmulCLM (h : ℂ) : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℂ).smulRight h

theorem hsmulCLM_apply (h z : ℂ) : hsmulCLM h z = z * h := by
  rw [hsmulCLM, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- Left multiplication by a complex number, as an `ℝ`-linear continuous map `ℂ⁶ → ℂ⁶`. -/
noncomputable def smulCLM (y : E6) : ℂ →L[ℝ] E6 := (ContinuousLinearMap.id ℝ ℂ).smulRight y

theorem smulCLM_apply (y : E6) (c : ℂ) : smulCLM y c = c • y := by
  rw [smulCLM, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]

/-! ## The round trip `ℂ ≅ ℝ²` -/

theorem smul_oneC_eq (z : ℂ) : z • oneC = WithLp.toLp 2 (fun _ : Fin 1 => z) := by
  rw [oneC, EuclideanSpace.single, ← WithLp.toLp_smul]
  congr 1
  funext i
  fin_cases i
  simp

theorem zOfCLM_mkAmbC (a : ℂ) : zOfCLM (mkAmbC a) = a := by
  have h : ((equivC1R2.symm : Amb 2 →L[ℝ] EuclideanSpace ℂ (Fin 1))
      ((equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] Amb 2) (a • oneC))) = a • oneC :=
    ContinuousLinearEquiv.symm_apply_apply equivC1R2 (a • oneC)
  show c1ToCCLM (((equivC1R2.symm : Amb 2 →L[ℝ] EuclideanSpace ℂ (Fin 1))
      ((equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] Amb 2) (a • oneC)))) = a
  rw [h, c1ToCCLM_apply, smul_oneC_eq, WithLp.ofLp_toLp]

theorem mkAmbC_zOfCLM (d : Amb 2) : mkAmbC (zOfCLM d) = d := by
  have h1 : ((equivC1R2.symm : Amb 2 →L[ℝ] EuclideanSpace ℂ (Fin 1)) d).ofLp 0 • oneC
      = (equivC1R2.symm : Amb 2 →L[ℝ] EuclideanSpace ℂ (Fin 1)) d := by
    rw [smul_oneC_eq]
    apply WithLp.ofLp_injective 2
    funext i
    rw [WithLp.ofLp_toLp]
    rw [show i = (0 : Fin 1) from Subsingleton.elim i 0]
  show equivC1R2 (((equivC1R2.symm : Amb 2 →L[ℝ] EuclideanSpace ℂ (Fin 1)) d).ofLp 0 • oneC) = d
  rw [h1]
  exact ContinuousLinearEquiv.apply_symm_apply equivC1R2 d

theorem exists_mkAmbC_pair (d : Amb 4) :
    ∃ a b : ℂ, d = Work.Whitney.sumFibreR 2 2 (mkAmbC a, mkAmbC b) := by
  refine ⟨zOfCLM (Prod.fst ((Work.Whitney.sumFibreR 2 2).symm d)),
    zOfCLM (Prod.snd ((Work.Whitney.sumFibreR 2 2).symm d)), ?_⟩
  rw [mkAmbC_zOfCLM, mkAmbC_zOfCLM]
  exact (ContinuousLinearEquiv.apply_symm_apply (Work.Whitney.sumFibreR 2 2) d).symm

/-! ## The gauge family -/

/-- The chart representative of `x` in the chart `t`, pushed into the `ℂ⁶`-plane of `p2Map x`. -/
noncomputable def srcCLM (S : ChartIdx 4 8) (t₁ : Fin 5) (x : CP4) : Amb 4 →L[ℝ] Amb 12 :=
  (coordEvalCLM S (p2StiefelF ⟨repF t₁ x, repF_ne_zero t₁ x⟩)).comp
    (matLin (orientMat S (p2Map x)))

theorem srcCLM_apply_eval (S : ChartIdx 4 8) (t₁ : Fin 5) (x : CP4)
    (hx : x ∈ Work.Projective.chartSet t₁) (hS : p2Map x ∈ baseSet S) (c : Amb 4) :
    srcCLM S t₁ x c = evalChartO S ⟨p2Map x, hS⟩ c := by
  set f : Stiefel 4 8 := p2StiefelF ⟨repF t₁ x, repF_ne_zero t₁ x⟩ with hfdef
  have hmk : (Quotient.mk'' f : OG 4 8) = p2Map x := by
    rw [hfdef]
    change ogMk 4 8 (p2StiefelF ⟨repF t₁ x, repF_ne_zero t₁ x⟩) = p2Map x
    rw [← p2Map_apply ⟨repF t₁ x, repF_ne_zero t₁ x⟩,
      show Projectivization.mk' ℂ ⟨repF t₁ x, repF_ne_zero t₁ x⟩ = x from
        cpMk_repF t₁ x hx]
  have hfmem : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hmk.symm ▸ hS)
  have hPt : (⟨p2Map x, hS⟩ : ↥(baseSet S)) =
      ⟨(Quotient.mk'' f), (mem_baseSet_iff S f).mpr hfmem⟩ := Subtype.ext hmk.symm
  rw [srcCLM, ContinuousLinearMap.comp_apply, coordEvalCLM_apply, hPt,
    evalChartO_spec S f hfmem, hmk]

/-- **The gauge family `Φ`**: read the `S`-coordinates of the plane vector, extract the coefficients
in the basis `(Λ(s₁), Λ'(s₁))` of the chart-`t.1` representative, and pair them (the second one
scaled by the cocycle `homCoord t.1 t.2`) into `Z4`'s coordinates. -/
noncomputable def phiCLM (S : ChartIdx 4 8) (t : Fin 5 × Fin 5) (x : CP4) :
    Amb 4 →L[ℝ] Amb 4 :=
  sumFibreRCLM.comp
    (((mkAmbCCLM.comp (aCoefL (rep4 t.1 x))).comp
        (cE6symmCLM.comp (srcCLM S t.1 x))).prod
      ((mkAmbCCLM.comp ((hsmulCLM (Work.Gen.homCoord 4 t.1 t.2 x)).comp
          (bCoefL (rep4 t.1 x)))).comp
        (cE6symmCLM.comp (srcCLM S t.1 x))))

theorem phiCLM_apply_eval (S : ChartIdx 4 8) (t : Fin 5 × Fin 5) (x : CP4)
    (hx : x ∈ Work.Projective.chartSet t.1) (hS : p2Map x ∈ baseSet S) (c : Amb 4) :
    phiCLM S t x c = Work.Whitney.sumFibreR 2 2
      (mkAmbC (aCoefL (rep4 t.1 x) (cE6.symm (evalChartO S ⟨p2Map x, hS⟩ c))),
       mkAmbC (bCoefL (rep4 t.1 x) (cE6.symm (evalChartO S ⟨p2Map x, hS⟩ c))
          * Work.Gen.homCoord 4 t.1 t.2 x)) := by
  rw [phiCLM]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    cE6symmCLM_apply, sumFibreRCLM_apply]
  rw [srcCLM_apply_eval S t.1 x hx hS c, hsmulCLM_apply, mkAmbCCLM_apply, mkAmbCCLM_apply]

/-- The reconstruction of a vector of `ℂ⁶` from the `Z4`-coordinates `(a, b)`. -/
noncomputable def reconCLM (t : Fin 5 × Fin 5) (x : CP4) : Amb 4 →L[ℝ] E6 :=
  ((smulCLM (lamL (rep4 t.1 x))).comp (zOfCLM.comp
      ((ContinuousLinearMap.fst ℝ (Amb 2) (Amb 2)).comp
        ((Work.Whitney.sumFibreR 2 2).symm : Amb 4 →L[ℝ] (Amb 2 × Amb 2)))))
  + ((smulCLM (lamR (rep4 t.2 x))).comp (zOfCLM.comp
      ((ContinuousLinearMap.snd ℝ (Amb 2) (Amb 2)).comp
        ((Work.Whitney.sumFibreR 2 2).symm : Amb 4 →L[ℝ] (Amb 2 × Amb 2)))))

theorem reconCLM_apply_gen (t : Fin 5 × Fin 5) (x : CP4) (d : Amb 4) :
    reconCLM t x d
      = zOfCLM ((Work.Whitney.sumFibreR 2 2).symm d).1 • lamL (rep4 t.1 x)
        + zOfCLM ((Work.Whitney.sumFibreR 2 2).symm d).2 • lamR (rep4 t.2 x) := by
  rw [reconCLM, ContinuousLinearMap.add_apply]
  simp only [ContinuousLinearMap.comp_apply, smulCLM_apply]
  rfl

theorem reconCLM_apply (t : Fin 5 × Fin 5) (x : CP4) (a b : ℂ) :
    reconCLM t x (Work.Whitney.sumFibreR 2 2 (mkAmbC a, mkAmbC b))
      = a • lamL (rep4 t.1 x) + b • lamR (rep4 t.2 x) := by
  rw [reconCLM_apply_gen, ContinuousLinearEquiv.symm_apply_apply, zOfCLM_mkAmbC, zOfCLM_mkAmbC]

/-- The oriented `S`-coordinate of an ambient vector. -/
noncomputable def toECoordCLM (S : ChartIdx 4 8) (x : CP4) : Amb 12 →L[ℝ] Amb 4 :=
  (matLin (orientMat S (p2Map x))).comp
    ((ambToLpCLM 4).comp ((coordProj S).toContinuousLinearMap.comp (ambOfLpCLM 12)))

theorem toECoordCLM_apply (S : ChartIdx 4 8) (x : CP4) (w : Amb 12) :
    toECoordCLM S x w = toECoordAt S (p2Map x) w := rfl

/-- **The inverse gauge family**. -/
noncomputable def phiInvCLM (S : ChartIdx 4 8) (t : Fin 5 × Fin 5) (x : CP4) :
    Amb 4 →L[ℝ] Amb 4 :=
  (toECoordCLM S x).comp (cE6CLM.comp (reconCLM t x))

theorem phiInvCLM_apply (S : ChartIdx 4 8) (t : Fin 5 × Fin 5) (x : CP4) (d : Amb 4) :
    phiInvCLM S t x d = toECoordAt S (p2Map x) (cE6 (reconCLM t x d)) := by
  rw [phiInvCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    toECoordCLM_apply, cE6CLM_apply]

/-! ## Membership bookkeeping -/

theorem mem_baseSet_of_mem_V4 {S : ChartIdx 4 8} {x : CP4} (hx : x ∈ V4.baseSet S) :
    p2Map x ∈ baseSet S := by
  rwa [V4_baseSet] at hx

theorem chartSet_of_mem_Z4 {t : Fin 5 × Fin 5} {x : CP4} (hx : x ∈ Z4.baseSet t) :
    x ∈ Work.Projective.chartSet t.1 ∧ x ∈ Work.Projective.chartSet t.2 := by
  rwa [Z4_baseSet] at hx

theorem homCoord_ne_zero' {i j : Fin 5} {x : CP4}
    (hi : x ∈ Work.Projective.chartSet i) (hj : x ∈ Work.Projective.chartSet j) :
    Work.Gen.homCoord 4 i j x ≠ 0 := by
  intro h0
  have h := Work.Gen.homCoord_mul_inv_eq_one (n := 4) i j hi hj
  rw [h0, mul_zero] at h
  exact one_ne_zero h.symm

theorem homCoord_cocycle (t t' : Fin 5 × Fin 5) {x : CP4}
    (h1 : x ∈ Work.Projective.chartSet t.1) (h1' : x ∈ Work.Projective.chartSet t'.1)
    (h2 : x ∈ Work.Projective.chartSet t.2) (h2' : x ∈ Work.Projective.chartSet t'.2) :
    Work.Gen.homCoord 4 t.2 t'.2 x * Work.Gen.homCoord 4 t.1 t.2 x
      = Work.Gen.homCoord 4 t'.1 t'.2 x * Work.Gen.homCoord 4 t.1 t'.1 x :=
  (Work.Gen.homCoord_mul (n := 4) t.1 t.2 t'.2 h1 h2 h2').symm.trans
    (Work.Gen.homCoord_mul (n := 4) t.1 t'.1 t'.2 h1 h1' h2')

/-! ## The two transition identities -/

theorem phi_htgt (S : ChartIdx 4 8) (t t' : Fin 5 × Fin 5) (x : CP4)
    (hS : x ∈ V4.baseSet S) (ht : x ∈ Z4.baseSet t) (ht' : x ∈ Z4.baseSet t') :
    (Z4.coordChange t t' x).comp (phiCLM S t x) = phiCLM S t' x := by
  have hS' : p2Map x ∈ baseSet S := mem_baseSet_of_mem_V4 hS
  obtain ⟨h1, h2⟩ := chartSet_of_mem_Z4 ht
  obtain ⟨h1', h2'⟩ := chartSet_of_mem_Z4 ht'
  have hne1 : Work.Gen.homCoord 4 t.1 t'.1 x ≠ 0 := homCoord_ne_zero' h1 h1'
  have hs : rep4 t.1 x = Work.Gen.homCoord 4 t.1 t'.1 x • rep4 t'.1 x :=
    rep4_eq_smul t.1 t'.1 ⟨h1, h1'⟩
  have hcoc := homCoord_cocycle t t' h1 h1' h2 h2'
  apply ContinuousLinearMap.ext
  intro c
  rw [ContinuousLinearMap.comp_apply, phiCLM_apply_eval S t x h1 hS' c,
    phiCLM_apply_eval S t' x h1' hS' c, Z4_coordChange_pair]
  congr 1
  refine Prod.ext ?_ ?_
  · show mkAmbC (Work.Gen.homCoord 4 t.1 t'.1 x
        * aCoefL (rep4 t.1 x) (cE6.symm (evalChartO S ⟨p2Map x, hS'⟩ c)))
      = mkAmbC (aCoefL (rep4 t'.1 x) (cE6.symm (evalChartO S ⟨p2Map x, hS'⟩ c)))
    rw [hs, aCoefLScale (rep4 t'.1 x) hne1, ← mul_assoc, mul_inv_cancel₀ hne1, one_mul]
  · show mkAmbC (Work.Gen.homCoord 4 t.2 t'.2 x
        * (bCoefL (rep4 t.1 x) (cE6.symm (evalChartO S ⟨p2Map x, hS'⟩ c))
          * Work.Gen.homCoord 4 t.1 t.2 x))
      = mkAmbC (bCoefL (rep4 t'.1 x) (cE6.symm (evalChartO S ⟨p2Map x, hS'⟩ c))
          * Work.Gen.homCoord 4 t'.1 t'.2 x)
    rw [hs, bCoefLScale (rep4 t'.1 x) hne1]
    rw [show Work.Gen.homCoord 4 t.2 t'.2 x
          * ((Work.Gen.homCoord 4 t.1 t'.1 x)⁻¹
              * bCoefL (rep4 t'.1 x) (cE6.symm (evalChartO S ⟨p2Map x, hS'⟩ c))
              * Work.Gen.homCoord 4 t.1 t.2 x)
        = (Work.Gen.homCoord 4 t.2 t'.2 x * Work.Gen.homCoord 4 t.1 t.2 x)
          * ((Work.Gen.homCoord 4 t.1 t'.1 x)⁻¹
              * bCoefL (rep4 t'.1 x) (cE6.symm (evalChartO S ⟨p2Map x, hS'⟩ c)))
        from by ring]
    rw [hcoc]
    rw [show (Work.Gen.homCoord 4 t'.1 t'.2 x * Work.Gen.homCoord 4 t.1 t'.1 x)
          * ((Work.Gen.homCoord 4 t.1 t'.1 x)⁻¹
              * bCoefL (rep4 t'.1 x) (cE6.symm (evalChartO S ⟨p2Map x, hS'⟩ c)))
        = Work.Gen.homCoord 4 t'.1 t'.2 x
          * (Work.Gen.homCoord 4 t.1 t'.1 x * (Work.Gen.homCoord 4 t.1 t'.1 x)⁻¹)
          * bCoefL (rep4 t'.1 x) (cE6.symm (evalChartO S ⟨p2Map x, hS'⟩ c))
        from by ring]
    rw [mul_inv_cancel₀ hne1, mul_one, mul_comm]

theorem phi_hsrc (S S' : ChartIdx 4 8) (t : Fin 5 × Fin 5) (x : CP4)
    (hS : x ∈ V4.baseSet S) (hS' : x ∈ V4.baseSet S') (ht : x ∈ Z4.baseSet t) :
    (phiCLM S t x).comp (V4.coordChange S' S x) = phiCLM S' t x := by
  have hbS : p2Map x ∈ baseSet S := mem_baseSet_of_mem_V4 hS
  have hbS' : p2Map x ∈ baseSet S' := mem_baseSet_of_mem_V4 hS'
  obtain ⟨h1, _⟩ := chartSet_of_mem_Z4 ht
  apply ContinuousLinearMap.ext
  intro c
  rw [ContinuousLinearMap.comp_apply, V4_coordChange_apply,
    phiCLM_apply_eval S t x h1 hbS (coordChangeO S' S (p2Map x) c),
    phiCLM_apply_eval S' t x h1 hbS' c,
    evalChartO_glue S' S (p2Map x) ⟨hbS', hbS⟩ c]

/-! ## The inverse identities -/

theorem phi_right (S : ChartIdx 4 8) (t : Fin 5 × Fin 5) (x : CP4) (d : Amb 4)
    (hx : x ∈ V4.baseSet S ∩ Z4.baseSet t) :
    phiCLM S t x (phiInvCLM S t x d) = d := by
  have hS : p2Map x ∈ baseSet S := mem_baseSet_of_mem_V4 hx.1
  obtain ⟨h1, h2⟩ := chartSet_of_mem_Z4 hx.2
  have hne : Work.Gen.homCoord 4 t.1 t.2 x ≠ 0 := homCoord_ne_zero' h1 h2
  obtain ⟨a, b, rfl⟩ := exists_mkAmbC_pair d
  have hs : rep4 t.1 x = Work.Gen.homCoord 4 t.1 t.2 x • rep4 t.2 x :=
    rep4_eq_smul t.1 t.2 ⟨h1, h2⟩
  have hlamR : lamR (rep4 t.2 x) = (Work.Gen.homCoord 4 t.1 t.2 x)⁻¹ • lamR (rep4 t.1 x) := by
    rw [hs, map_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hvmem : a • lamL (rep4 t.1 x) + b • lamR (rep4 t.2 x) ∈
      Submodule.span ℂ ({lamL (rep4 t.1 x), lamR (rep4 t.1 x)} : Set E6) := by
    rw [hlamR, smul_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hev : evalChartO S ⟨p2Map x, hS⟩
      (toECoordAt S (p2Map x) (cE6 (a • lamL (rep4 t.1 x) + b • lamR (rep4 t.2 x))))
      = cE6 (a • lamL (rep4 t.1 x) + b • lamR (rep4 t.2 x)) :=
    evalChartO_toECoordAt S (p2Map x) hS _ (memPlane_p2Map (t := t.1) (x := x) h1 hvmem)
  rw [phiInvCLM_apply, reconCLM_apply, phiCLM_apply_eval S t x h1 hS, hev,
    show cE6.symm (cE6 (a • lamL (rep4 t.1 x) + b • lamR (rep4 t.2 x)))
      = a • lamL (rep4 t.1 x) + b • lamR (rep4 t.2 x) from
        LinearIsometryEquiv.symm_apply_apply cE6 _,
    show a • lamL (rep4 t.1 x) + b • lamR (rep4 t.2 x)
      = a • lamL (rep4 t.1 x) + (b * (Work.Gen.homCoord 4 t.1 t.2 x)⁻¹)
          • lamR (rep4 t.1 x) from by rw [hlamR, smul_smul],
    aCoefL_recon (rep4 t.1 x) (rep4_ne_zero t.1 x) a (b * (Work.Gen.homCoord 4 t.1 t.2 x)⁻¹),
    bCoefL_recon (rep4 t.1 x) (rep4_ne_zero t.1 x) a (b * (Work.Gen.homCoord 4 t.1 t.2 x)⁻¹)]
  rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]

theorem phi_left (S : ChartIdx 4 8) (t : Fin 5 × Fin 5) (x : CP4) (c : Amb 4)
    (hx : x ∈ V4.baseSet S ∩ Z4.baseSet t) :
    phiInvCLM S t x (phiCLM S t x c) = c := by
  have hS : p2Map x ∈ baseSet S := mem_baseSet_of_mem_V4 hx.1
  obtain ⟨h1, h2⟩ := chartSet_of_mem_Z4 hx.2
  have hne : Work.Gen.homCoord 4 t.1 t.2 x ≠ 0 := homCoord_ne_zero' h1 h2
  have hs₁ : rep4 t.1 x ≠ 0 := rep4_ne_zero t.1 x
  have hs : rep4 t.1 x = Work.Gen.homCoord 4 t.1 t.2 x • rep4 t.2 x :=
    rep4_eq_smul t.1 t.2 ⟨h1, h2⟩
  have hlamR : lamR (rep4 t.2 x) = (Work.Gen.homCoord 4 t.1 t.2 x)⁻¹ • lamR (rep4 t.1 x) := by
    rw [hs, map_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hcoef := coefLRecon (rep4 t.1 x) hs₁ (cE6SymmEvalChartOMem S t.1 x h1 hS c)
  rw [phiCLM_apply_eval S t x h1 hS c, phiInvCLM_apply, reconCLM_apply]
  rw [hlamR, smul_smul, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  rw [hcoef]
  rw [show cE6 (cE6.symm (evalChartO S ⟨p2Map x, hS⟩ c)) = evalChartO S ⟨p2Map x, hS⟩ c from
    LinearIsometryEquiv.apply_symm_apply cE6 _]
  exact toECoordAt_evalChartO S (p2Map x) hS c

/-! ## The inverse transition identities -/

theorem phi_htgtinv (S : ChartIdx 4 8) (t t' : Fin 5 × Fin 5) (x : CP4)
    (hS : x ∈ V4.baseSet S) (ht : x ∈ Z4.baseSet t) (ht' : x ∈ Z4.baseSet t') :
    (phiInvCLM S t x).comp (Z4.coordChange t' t x) = phiInvCLM S t' x := by
  apply ContinuousLinearMap.ext
  intro d
  have hM : phiCLM S t x (phiInvCLM S t' x d) = Z4.coordChange t' t x d := by
    rw [← phi_htgt S t' t x hS ht' ht]
    show Z4.coordChange t' t x (phiCLM S t' x (phiInvCLM S t' x d)) = Z4.coordChange t' t x d
    rw [phi_right S t' x d ⟨hS, ht'⟩]
  rw [ContinuousLinearMap.comp_apply, ← hM]
  exact phi_left S t x (phiInvCLM S t' x d) ⟨hS, ht⟩

theorem phi_hsrcinv (S S' : ChartIdx 4 8) (t : Fin 5 × Fin 5) (x : CP4)
    (hS : x ∈ V4.baseSet S) (hS' : x ∈ V4.baseSet S') (ht : x ∈ Z4.baseSet t) :
    (V4.coordChange S S' x).comp (phiInvCLM S t x) = phiInvCLM S' t x := by
  apply ContinuousLinearMap.ext
  intro d
  have hM : phiCLM S' t x (V4.coordChange S S' x (phiInvCLM S t x d)) = d := by
    rw [← ContinuousLinearMap.comp_apply, phi_hsrc S' S t x hS' hS ht]
    exact phi_right S t x d ⟨hS, ht⟩
  calc (V4.coordChange S S' x) (phiInvCLM S t x d)
      = phiInvCLM S' t x (phiCLM S' t x
          ((V4.coordChange S S' x) (phiInvCLM S t x d))) :=
        (phi_left S' t x _ ⟨hS', ht⟩).symm
    _ = phiInvCLM S' t x d := by rw [hM]

/-! ## Continuity -/

theorem phiCLM_cont_pair (S : ChartIdx 4 8) (t : Fin 5 × Fin 5) :
    Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      phiCLM S t (p.1 : CP4) p.2 := by
  have hSof : ∀ p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4,
      p2Map (p.1 : CP4) ∈ baseSet S := fun p => mem_baseSet_of_mem_V4 p.1.2.1
  have hx1 : ∀ p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4,
      (p.1 : CP4) ∈ Work.Projective.chartSet t.1 :=
    fun p => (chartSet_of_mem_Z4 p.1.2.2).1
  have hs1 : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      rep4 t.1 (p.1 : CP4) :=
    ContinuousOn.comp_continuous (g := fun x : CP4 => rep4 t.1 x) (continuousOn_rep4 t.1)
      (continuous_subtype_val.comp continuous_fst) hx1
  have hs1' : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      (⟨rep4 t.1 (p.1 : CP4), rep4_ne_zero t.1 (p.1 : CP4)⟩ : {z : E5 // z ≠ 0}) :=
    Continuous.subtype_mk hs1 (fun p => rep4_ne_zero t.1 (p.1 : CP4))
  have hW : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      cE6.symm (evalChartO S ⟨p2Map (p.1 : CP4), hSof p⟩ p.2) := by
    have hsub : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
        (⟨p2Map (p.1 : CP4), hSof p⟩ : ↥(baseSet S)) :=
      Continuous.subtype_mk (p2Map.continuous.comp (continuous_subtype_val.comp continuous_fst)) hSof
    exact cE6symmCLM.continuous.comp
      ((continuous_evalChartO S).comp (hsub.prodMk continuous_snd))
  have hbCoefFun : Continuous fun q : {z : E5 // z ≠ 0} × E6 => bCoefL q.1.1 q.2 := by
    have h1 : Continuous fun q : {z : E5 // z ≠ 0} × E6 =>
        (((‖wVec q.1.1‖ ^ 2)⁻¹ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        (Continuous.inv₀ ((continuous_norm.comp (continuous_wVec_subtype.comp continuous_fst)).pow 2)
          (fun q => pow_ne_zero 2 (norm_ne_zero_iff.mpr (wVec_ne_zero _ q.1.2))))
    have h2 : Continuous fun q : {z : E5 // z ≠ 0} × E6 =>
        inner ℂ (wVec q.1.1) q.2 :=
      continuous_inner.comp ((continuous_wVec_subtype.comp continuous_fst).prodMk continuous_snd)
    refine (h1.mul h2).congr (fun q => ?_)
    rw [Pi.mul_apply, bCoefL_apply]
  have haCoefFun : Continuous fun q : {z : E5 // z ≠ 0} × E6 => aCoefL q.1.1 q.2 := by
    have h1 : Continuous fun q : {z : E5 // z ≠ 0} × E6 =>
        (((‖lamL q.1.1‖)⁻¹ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        (Continuous.inv₀ (continuous_norm.comp (lamL.continuous.comp
          (continuous_subtype_val.comp continuous_fst)))
          (fun q => norm_ne_zero_iff.mpr (lamL_ne_zero q.1.2)))
    have hA : Continuous fun q : {z : E5 // z ≠ 0} × E6 => inner ℂ (lamUnit q.1.1) q.2 :=
      continuous_inner.comp ((continuous_lamUnit_subtype.comp continuous_fst).prodMk continuous_snd)
    have hB : Continuous fun q : {z : E5 // z ≠ 0} × E6 =>
        inner ℂ (lamUnit q.1.1) (lamR q.1.1) :=
      continuous_inner.comp ((continuous_lamUnit_subtype.comp continuous_fst).prodMk
        (lamR.continuous.comp (continuous_subtype_val.comp continuous_fst)))
    have hC : Continuous fun q : {z : E5 // z ≠ 0} × E6 =>
        inner ℂ (lamUnit q.1.1) (lamR q.1.1) * bCoefL q.1.1 q.2 := hB.mul hbCoefFun
    refine (h1.mul (hA.sub hC)).congr (fun q => ?_)
    rw [Pi.mul_apply, Pi.sub_apply, aCoefL_apply]
  have hpair := hs1'.prodMk hW
  have hbCoef := hbCoefFun.comp hpair
  have haCoef := haCoefFun.comp hpair
  have hhom : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      Work.Gen.homCoord 4 t.1 t.2 (p.1 : CP4) :=
    ContinuousOn.comp_continuous (g := fun x : CP4 => Work.Gen.homCoord 4 t.1 t.2 x)
      (Work.Gen.continuousOn_homCoord t.1 t.2)
      (continuous_subtype_val.comp continuous_fst) hx1
  have hpair2 := (mkAmbCCLM.continuous.comp haCoef).prodMk (mkAmbCCLM.continuous.comp (hbCoef.mul hhom))
  have hsum := sumFibreRCLM.continuous.comp hpair2
  refine hsum.congr (fun p => ?_)
  rw [phiCLM_apply_eval S t (p.1 : CP4) (hx1 p) (hSof p) p.2]
  simp only [Function.comp_apply, Pi.mul_apply, mkAmbCCLM_apply, sumFibreRCLM_apply]


theorem phiInvCLM_cont_pair (S : ChartIdx 4 8) (t : Fin 5 × Fin 5) :
    Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      phiInvCLM S t (p.1 : CP4) p.2 := by
  have hSof : ∀ p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4,
      p2Map (p.1 : CP4) ∈ baseSet S := fun p => mem_baseSet_of_mem_V4 p.1.2.1
  have hx1 : ∀ p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4,
      (p.1 : CP4) ∈ Work.Projective.chartSet t.1 := fun p => (chartSet_of_mem_Z4 p.1.2.2).1
  have hx2 : ∀ p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4,
      (p.1 : CP4) ∈ Work.Projective.chartSet t.2 := fun p => (chartSet_of_mem_Z4 p.1.2.2).2
  have hsub : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      (⟨p2Map (p.1 : CP4), hSof p⟩ : ↥(baseSet S)) :=
    Continuous.subtype_mk (p2Map.continuous.comp (continuous_subtype_val.comp continuous_fst)) hSof
  have hmat : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      matLin (orientMat S (⟨p2Map (p.1 : CP4), hSof p⟩ : ↥(baseSet S))) :=
    continuous_matLin.comp ((continuous_orientMat_subtype S).comp hsub)
  have hs1 : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      rep4 t.1 (p.1 : CP4) :=
    ContinuousOn.comp_continuous (g := fun x : CP4 => rep4 t.1 x) (continuousOn_rep4 t.1)
      (continuous_subtype_val.comp continuous_fst) hx1
  have hs2 : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      rep4 t.2 (p.1 : CP4) :=
    ContinuousOn.comp_continuous (g := fun x : CP4 => rep4 t.2 x) (continuousOn_rep4 t.2)
      (continuous_subtype_val.comp continuous_fst) hx2
  have hsnd : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      (Work.Whitney.sumFibreR 2 2).symm p.2 :=
    ((Work.Whitney.sumFibreR 2 2).symm : Amb 4 →L[ℝ] (Amb 2 × Amb 2)).continuous.comp
      continuous_snd
  have hd1 : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      zOfCLM ((Work.Whitney.sumFibreR 2 2).symm p.2).1 := zOfCLM.continuous.comp hsnd.fst
  have hd2 : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      zOfCLM ((Work.Whitney.sumFibreR 2 2).symm p.2).2 := zOfCLM.continuous.comp hsnd.snd
  have hterm1 : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      zOfCLM ((Work.Whitney.sumFibreR 2 2).symm p.2).1 • lamL (rep4 t.1 (p.1 : CP4)) :=
    hd1.smul (lamL.continuous.comp hs1)
  have hterm2 : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      zOfCLM ((Work.Whitney.sumFibreR 2 2).symm p.2).2 • lamR (rep4 t.2 (p.1 : CP4)) :=
    hd2.smul (lamR.continuous.comp hs2)
  have hrec : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      reconCLM t (p.1 : CP4) p.2 :=
    (hterm1.add hterm2).congr (fun p => (reconCLM_apply_gen t (p.1 : CP4) p.2).symm)
  have hcE : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      cE6 (reconCLM t (p.1 : CP4) p.2) := cE6CLM.continuous.comp hrec
  have hinner : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      (ambToLpCLM 4) ((coordProj S)
        (ambOfLpCLM 12 (cE6 (reconCLM t (p.1 : CP4) p.2)))) :=
    (ambToLpCLM 4).continuous.comp (((coordProj S).toContinuousLinearMap).continuous.comp
      ((ambOfLpCLM 12).continuous.comp hcE))
  have hfin : Continuous fun p : ↥(V4.baseSet S ∩ Z4.baseSet t) × Amb 4 =>
      matLin (orientMat S (⟨p2Map (p.1 : CP4), hSof p⟩ : ↥(baseSet S)))
        ((ambToLpCLM 4) ((coordProj S)
          (ambOfLpCLM 12 (cE6 (reconCLM t (p.1 : CP4) p.2))))) :=
    hmat.clm_apply hinner
  refine hfin.congr (fun p => ?_)
  rw [phiInvCLM_apply]
  rfl

theorem phi_cont (S : ChartIdx 4 8) (t : Fin 5 × Fin 5) :
    ContinuousOn (fun x : CP4 => phiCLM S t x) (V4.baseSet S ∩ Z4.baseSet t) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact Work.Thom.continuous_clm_of_continuous_apply
    (X := ↥(V4.baseSet S ∩ Z4.baseSet t)) (n := 4)
    (fun x : ↥(V4.baseSet S ∩ Z4.baseSet t) => phiCLM S t (x : CP4))
    (phiCLM_cont_pair S t)

theorem phi_contInv (S : ChartIdx 4 8) (t : Fin 5 × Fin 5) :
    ContinuousOn (fun x : CP4 => phiInvCLM S t x) (V4.baseSet S ∩ Z4.baseSet t) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact Work.Thom.continuous_clm_of_continuous_apply
    (X := ↥(V4.baseSet S ∩ Z4.baseSet t)) (n := 4)
    (fun x : ↥(V4.baseSet S ∩ Z4.baseSet t) => phiInvCLM S t (x : CP4))
    (phiInvCLM_cont_pair S t)

/-! ## The gauge isomorphism -/

theorem gaugeIso : Nonempty (Work.Thom.BundleIso
    (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle 4 8) p2Map)
    (Work.Whitney.whitneySumR
      (RealBundle.mapFibre equivC1R2 (Work.Thom.realification (Work.Gen.tautLine 4)))
      (RealBundle.mapFibre equivC1R2 (Work.Thom.realification (Work.Gen.tautLine 4))))) :=
  Work.Thom.nonempty_bundleIso_of_gauge V4 Z4 phiCLM phiInvCLM
    phi_cont phi_contInv phi_htgt (fun S t S' => phi_hsrc S S' t) phi_htgtinv
    (fun S t S' => phi_hsrcinv S S' t) phi_left phi_right

end

end Work.ThomBordism.Grassmann.LowDegree
