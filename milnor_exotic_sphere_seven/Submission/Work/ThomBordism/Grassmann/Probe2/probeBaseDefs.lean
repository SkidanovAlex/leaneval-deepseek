import Mathlib
import Submission.Work.ThomBordism.Grassmann.probeMap
import Submission.Work.ThomBordism.Grassmann.PlaneEval
import Submission.Work.ThomBordism.Grassmann.PlaneCoord
import Submission.Work.ThomBordism.Grassmann.CxFibre
import Submission.Work.Gen.EulerGauge
import Submission.Work.Gen.EulerToolkit
import Submission.Work.Thom.pontryagin1_comap
import Submission.Work.Thom.pontryaginClass_one
import Submission.Work.ThomBordism.Grassmann.Probe2.p1RatNeZero_of_twoTwo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-!
# The probe `ℂP² → G̃r₂(ℝ⁶)` and the gauge comparing `σ^*γ` with `zStd`

The base case `(k, m) = (2, 4)` of the probe of `Work.ThomBordism.Grassmann.probeP1`:
the map `σ = probeSigma 2 4`, its frame-level description, and the gauge comparing the pullback
`σ^*γ` of the tautological oriented `2`-plane bundle with `zStd` (the realification of the
tautological dual line bundle of `ℂP²`).

The gauge (in the chart `S` of the Grassmannian and the chart `i` of `ℂP²`) reads the `S`-coordinate
of a plane vector in `ℂ³` and pairs it with the chart-`i` representative: with
`W = cxE.symm (coordEval S f (orientMat S (σ x) c))` the *unnormalised* coordinates of the plane
vector,
`Φ(S,i)(x)(c) = equivC1R2 (∑_t W_t conj(v_t))`,  `v = Fin.insertNth i 1 (chartFun i x)`.
The representative scaling `v_i = (z_i/z_j) v_j` is exactly the transition law of `zStd`, which is
the content of the identity `phi_htgt` below.
-/

namespace Work.ThomBordism.Grassmann.Probe2

open Work.TangentClasses
open Work.Projective

noncomputable section

theorem cxOf_ofLp (w : Fin 3 → ℂ) : (cxOf w).ofLp = w := by
  rw [cxOf, WithLp.ofLp_toLp]

/-! ## The base-case probe -/

theorem two_le_two : 2 ≤ 2 := by norm_num
theorem four_le_four : 4 ≤ 4 := by norm_num

/-- **The base-case probe** `σ = probeSigma 2 4 : ℂP² → G̃r₂(ℝ⁶)`. -/
def sigma2 : C(CP 2, OG 2 4) := probeSigma 2 4 two_le_two four_le_four

/-- The frame-level computation of the base-case probe at a point of the chart `i`. -/
theorem sigma2_apply_chart (i : Fin 3) (x : CP 2)
    (hx : x ∈ Work.Projective.chartSet i) :
    sigma2 x = ogMk 2 4 (probeStiefelRep 2 4 two_le_two four_le_four (Work.Gen.uVec i x)
      (Work.Gen.uVec_ne_zero i x)) :=
  probeSigma_apply_uVec 2 4 two_le_two four_le_four i x hx

/-- The probe frame of the chart-`i` representative of `x`. -/
def chartFrame2 (i : Fin 3) (x : CP 2) : Stiefel 2 4 :=
  probeStiefelRep 2 4 two_le_two four_le_four (Work.Gen.uVec i x)
    (Work.Gen.uVec_ne_zero i x)

@[simp] theorem chartFrame2_val (i : Fin 3) (x : CP 2) :
    (chartFrame2 i x).1 = probeFrameRep 2 4 two_le_two four_le_four (Work.Gen.uVec i x) := rfl

theorem sigma2_apply_frame (i : Fin 3) (x : CP 2)
    (hx : x ∈ Work.Projective.chartSet i) :
    sigma2 x = ogMk 2 4 (chartFrame2 i x) := sigma2_apply_chart i x hx

/-! ## The plane of the probe -/

/-- The index bookkeeping `probeAmbIdx` is the identity for `(k, m) = (2, 4)`. -/
theorem probeAmbIdx_24 (i : Fin 6) :
    probeAmbIdx 2 4 two_le_two four_le_four i = i := by
  rw [probeAmbIdx]
  have hmap : ∀ x : Fin 2 ⊕ Fin 4,
      Sum.map (idxTwo 2 two_le_two) (Fin.castLE four_le_four) x = x := by
    rintro (a | b)
    · rw [Sum.map_inl]
      exact congrArg Sum.inl (Fin.ext rfl)
    · rw [Sum.map_inr]
      exact congrArg Sum.inr (Fin.ext rfl)
  rw [hmap, Equiv.apply_symm_apply]

/-- The chart isometry `probeEmb 2 4` is the identity. -/
theorem probeEmb_24 : probeEmb 2 4 two_le_two four_le_four
    = ContinuousLinearMap.id ℝ (Amb 6) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [probeEmb_apply, ContinuousLinearMap.id_apply]
  rw [Finset.sum_congr rfl (fun i _ => by rw [probeAmbIdx_24 i])]
  exact sum_single_eq 6 u

theorem range_probeFrameRep (v : Fin 3 → ℂ) :
    Set.range (probeFrameRep 2 4 two_le_two four_le_four v)
      = Set.range (probePairVec 2 4 two_le_two four_le_four v) := by
  ext w
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨p, rfl⟩ := (probeSplit 2 two_le_two).surjective j
    rcases p with a | l
    · exact ⟨a, (probeFrameRep_inl 2 4 two_le_two four_le_four v a).symm⟩
    · exact Fin.elim0 l
  · rintro ⟨a, rfl⟩
    exact ⟨probeSplit 2 two_le_two (Sum.inl a),
      probeFrameRep_inl 2 4 two_le_two four_le_four v a⟩

theorem cxOf_eq_norm_smul_cxUnit {v : Fin 3 → ℂ} (hv : v ≠ 0) :
    cxOf v = (‖cxOf v‖) • cxUnit v := by
  rw [cxUnit, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (cxOf_ne_zero hv)), one_smul]

/-- **The `ℝ`-span of the probe frame of a nonzero representative `v` is the `cxE`-image of the
complex line `ℂ·v`.** -/
theorem span_probeFrameRep (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    Submodule.span ℝ (Set.range (probeFrameRep 2 4 two_le_two four_le_four v))
      = Submodule.map (cxE : E3 →ₗ[ℝ] Amb 6)
          ((Submodule.span ℂ {cxOf v}).restrictScalars ℝ) := by
  have hnorm : ‖cxOf v‖ ≠ 0 := norm_ne_zero_iff.mpr (cxOf_ne_zero hv)
  have hu : cxOf v = (‖cxOf v‖) • cxUnit v := cxOf_eq_norm_smul_cxUnit hv
  have hIu : Complex.I • cxOf v = (‖cxOf v‖) • (Complex.I • cxUnit v) := by
    conv_lhs => rw [hu]
    rw [smul_comm]
  have h0 : probePairVec 2 4 two_le_two four_le_four v 0
      = (cxE : E3 →ₗ[ℝ] Amb 6) (cxUnit v) := by
    rw [probePairVec_zero, probeEmb_24, ContinuousLinearMap.id_apply]
    rfl
  have h1 : probePairVec 2 4 two_le_two four_le_four v 1
      = -((cxE : E3 →ₗ[ℝ] Amb 6) (Complex.I • cxUnit v)) := by
    rw [probePairVec_one, probeEmb_24, ContinuousLinearMap.id_apply]
    rfl
  have hcu : cxUnit v ∈ Submodule.span ℂ {cxOf v} := by
    rw [Submodule.mem_span_singleton]
    exact ⟨((‖cxOf v‖)⁻¹ : ℝ), by rw [Complex.coe_smul, cxUnit]⟩
  have hIcu : Complex.I • cxUnit v ∈ Submodule.span ℂ {cxOf v} :=
    Submodule.smul_mem _ Complex.I hcu
  rw [range_probeFrameRep]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨j, rfl⟩
    have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hj with rfl | rfl
    · rw [h0]
      exact Submodule.mem_map.mpr ⟨cxUnit v, hcu, rfl⟩
    · rw [h1]
      exact Submodule.neg_mem _ (Submodule.mem_map.mpr ⟨Complex.I • cxUnit v, hIcu, rfl⟩)
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    rw [Submodule.restrictScalars_mem] at hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hgen0 : (cxE : E3 →ₗ[ℝ] Amb 6) (cxUnit v)
        ∈ Submodule.span ℝ (Set.range (probePairVec 2 4 two_le_two four_le_four v)) := by
      rw [← h0]; exact Submodule.subset_span ⟨0, rfl⟩
    have hgen1 : (cxE : E3 →ₗ[ℝ] Amb 6) (Complex.I • cxUnit v)
        ∈ Submodule.span ℝ (Set.range (probePairVec 2 4 two_le_two four_le_four v)) := by
      have h : (cxE : E3 →ₗ[ℝ] Amb 6) (Complex.I • cxUnit v)
          = -(probePairVec 2 4 two_le_two four_le_four v 1) := by rw [h1, neg_neg]
      rw [h]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨1, rfl⟩)
    have hA : (cxE : E3 →ₗ[ℝ] Amb 6) (c.re • cxOf v)
        = c.re • ((‖cxOf v‖) • (cxE : E3 →ₗ[ℝ] Amb 6) (cxUnit v)) := by
      conv_lhs => rw [map_smul, hu, map_smul]
    have hB : (cxE : E3 →ₗ[ℝ] Amb 6) (c.im • (Complex.I • cxOf v))
        = c.im • ((‖cxOf v‖) • (cxE : E3 →ₗ[ℝ] Amb 6) (Complex.I • cxUnit v)) := by
      conv_lhs => rw [map_smul, hIu, map_smul]
    rw [complex_smul_eq c (cxOf v), map_add, hA, hB]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hgen0))
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hgen1))

/-- The `SO(k)`-action on frames preserves the span. -/
theorem span_soActFun_subset {k m : ℕ} (A : SOk k) (f : Fin k → Amb (k + m)) :
    Submodule.span ℝ (Set.range (soActFun A.1 f)) ≤ Submodule.span ℝ (Set.range f) := by
  refine Submodule.span_le.mpr ?_
  rintro - ⟨j, rfl⟩
  rw [soActFun]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, rfl⟩))

/-- **The `ℂ³`-vector of a vector of the plane of `sigma2 x` lies in the complex line of the
chart-`i` representative.** -/
theorem plane_line (i : Fin 3) (x : CP 2) (hx : x ∈ Work.Projective.chartSet i) {w : Amb 6}
    (hw : memPlane (sigma2 x) w) :
    (cxE.symm w).ofLp ∈ Submodule.span ℂ {Work.Gen.uVec i x} := by
  obtain ⟨f, hf, hwspan⟩ := hw
  have hfr : (Quotient.mk'' f : OG 2 4) = Quotient.mk'' (chartFrame2 i x) := by
    rw [hf, sigma2_apply_frame i x hx]
    rfl
  obtain ⟨A, hA⟩ := Quotient.exact hfr
  have hspanle : Submodule.span ℝ (Set.range (f.1 : Fin 2 → Amb 6))
      ≤ Submodule.span ℝ (Set.range (chartFrame2 i x).1) := by
    have h2 : f = A.transpose.act (chartFrame2 i x) := by
      rw [hA, SOk.act_transpose_act]
    rw [h2]
    exact span_soActFun_subset A.transpose (chartFrame2 i x).1
  have hw' : w ∈ Submodule.span ℝ
      (Set.range (probeFrameRep 2 4 two_le_two four_le_four (Work.Gen.uVec i x))) := by
    have h := hspanle hwspan
    simpa only [chartFrame2_val] using h
  rw [span_probeFrameRep (Work.Gen.uVec i x) (Work.Gen.uVec_ne_zero i x)] at hw'
  obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.mp hw'
  rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hy
  obtain ⟨c, hc⟩ := hy
  have hyw' : w = (cxE : E3 →ₗ[ℝ] Amb 6) (c • cxOf (Work.Gen.uVec i x)) := by
    rw [hc]; exact hyw.symm
  rw [hyw', Submodule.mem_span_singleton]
  refine ⟨c, ?_⟩
  have hsymm : (cxE.symm ((cxE : E3 →ₗ[ℝ] Amb 6) (c • cxOf (Work.Gen.uVec i x)))).ofLp
      = c • Work.Gen.uVec i x := by
    rw [show cxE.symm ((cxE : E3 →ₗ[ℝ] Amb 6) (c • cxOf (Work.Gen.uVec i x)))
        = c • cxOf (Work.Gen.uVec i x) from LinearIsometryEquiv.symm_apply_apply cxE _,
      WithLp.ofLp_smul, cxOf_ofLp]
  exact hsymm.symm

/-! ## The chart evaluation and the oriented coordinate -/

/-- **The oriented coordinate is the inverse of the chart evaluation** on the plane. -/
theorem evalChartO_toECoordAt' (S : ChartIdx 2 4) (P : OG 2 4) (hPS : P ∈ baseSet S)
    {w : Amb 6} (hw : memPlane P w) :
    evalChartO S ⟨P, hPS⟩ (toECoordAt S P w) = w := by
  obtain ⟨f, hf, hwspan⟩ := hw
  subst hf
  have hfc : f ∈ chartSet S :=
    (mem_baseSet_iff S f).mp (show Quotient.mk'' f ∈ baseSet S from hPS)
  show evalChartO S ⟨Quotient.mk'' f, (mem_baseSet_iff S f).mpr hfc⟩ (toECoordAt S _ w) = w
  rw [evalChartO_spec S f hfc (toECoordAt S (Quotient.mk'' f) w), toECoordAt]
  have hinv : matLin (orientMat S (Quotient.mk'' f)) (matLin (orientMat S (Quotient.mk'' f))
      (WithLp.toLp 2 (coordProj S (WithLp.ofLp w))))
      = WithLp.toLp 2 (coordProj S (WithLp.ofLp w)) := by
    rw [← ContinuousLinearMap.comp_apply, ← matLin_mul,
      orientMat_mul_self (S := S) (x := Quotient.mk'' f) hPS]
    simp
  rw [hinv]
  exact coordEval_coordProj S f hfc hwspan

/-- **The oriented coordinate of a chart evaluation is the coordinate.** -/
theorem toECoordAt_evalChartO' (S : ChartIdx 2 4) (P : OG 2 4) (hPS : P ∈ baseSet S)
    (v : Amb 2) :
    toECoordAt S P (evalChartO S ⟨P, hPS⟩ v) = v := by
  obtain ⟨f, hfmk⟩ : ∃ f : Stiefel 2 4, Quotient.mk'' f = P := Quotient.exists_rep _
  have hfc : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hfmk ▸ hPS)
  have hspec := evalChart_spec S ⟨P, hPS⟩ f hfc hfmk.symm (matLin (orientMat S P) v)
  rw [evalChartO, hspec, toECoordAt,
    show WithLp.toLp 2 (coordProj S (WithLp.ofLp (coordEval S f (matLin (orientMat S P) v))))
        = WithLp.toLp 2 (WithLp.ofLp (matLin (orientMat S P) v)) from by
      rw [coordProj_coordEval S f (matLin (orientMat S P) v) hfc],
    WithLp.toLp_ofLp]
  exact orientMat_involutive S P hPS v

/-- **The oriented coordinate of a chart evaluation in another chart is the transition function.** -/
theorem toECoordAt_evalChartO_other (S T : ChartIdx 2 4) (P : OG 2 4) (hPS : P ∈ baseSet S)
    (hPT : P ∈ baseSet T) (v : Amb 2) :
    toECoordAt T P (evalChartO S ⟨P, hPS⟩ v) = coordChangeO S T P v := by
  rw [evalChartO_glue S T P ⟨hPS, hPT⟩ v]
  exact toECoordAt_evalChartO' T P hPT (coordChangeO S T P v)

/-- **The chart evaluation is independent of the frame representing the plane.** -/
theorem coordEval_eq_of_mk_eq {k m : ℕ} (S : ChartIdx k m) {f g : Stiefel k m}
    (h : (Quotient.mk'' f : OG k m) = Quotient.mk'' g) : coordEval S f = coordEval S g := by
  obtain ⟨A, hA⟩ := Quotient.exact h
  rw [hA]
  funext v
  exact (coordEval_soActFun S f v A).symm

theorem coordEval_chartFrame2_eq (S : ChartIdx 2 4) (i j : Fin 3) (x : CP 2)
    (hi : x ∈ Work.Projective.chartSet i) (hj : x ∈ Work.Projective.chartSet j) :
    coordEval S (chartFrame2 i x) = coordEval S (chartFrame2 j x) := by
  refine coordEval_eq_of_mk_eq S ?_
  change ogMk 2 4 (chartFrame2 i x) = ogMk 2 4 (chartFrame2 j x)
  rw [← sigma2_apply_frame i x hi, ← sigma2_apply_frame j x hj]

/-! ## The chart representatives -/

theorem uVec_eq_homCoord_smul (i j : Fin 3) (x : CP 2)
    (hi : x ∈ Work.Projective.chartSet i) (hj : x ∈ Work.Projective.chartSet j) :
    Work.Gen.uVec j x = Work.Gen.homCoord 2 j i x • Work.Gen.uVec i x := by
  have hx : Work.Projective.chartInv i (Work.Projective.chartFun i x) = x :=
    Work.Projective.chartInv_chartFun i x hi
  have h1 := Work.Gen.vVec_eq_lam_smul (n := 2) (i := i) (j := j)
    (u := Work.Projective.chartFun i x) (by rw [hx]; exact hj)
  have h2 : Work.Gen.vVec j (Work.Gen.Phi i j (Work.Projective.chartFun i x))
      = Work.Gen.uVec j x := by
    rw [Work.Gen.Phi, hx]
    rfl
  have h3 : Work.Gen.lam i j (Work.Projective.chartFun i x)
      = Work.Gen.homCoord 2 i j x := by
    rw [Work.Gen.lam_eq_homCoord, hx]
  have h1' : Work.Gen.uVec i x = Work.Gen.homCoord 2 i j x • Work.Gen.uVec j x := by
    rw [← h2, ← h3]
    exact h1
  rw [h1', smul_smul, Work.Gen.homCoord_mul_inv_eq_one i j hi hj, one_smul]


/-! ## The gauge family -/

/-- `WithLp.ofLp` as an `ℝ`-linear continuous map `ℝⁿ → (Fin n → ℝ)`. -/
def ambOfLpCLM (n : ℕ) : Amb n →L[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ : Amb n ≃L[ℝ] (Fin n → ℝ))

@[simp] theorem ambOfLpCLM_apply (n : ℕ) (v : Amb n) : ambOfLpCLM n v = v.ofLp := rfl

/-- `WithLp.toLp` as an `ℝ`-linear continuous map `(Fin n → ℝ) → ℝⁿ`. -/
def ambToLpCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] Amb n :=
  ((EuclideanSpace.equiv (Fin n) ℝ).symm : (Fin n → ℝ) →L[ℝ] Amb n)

@[simp] theorem ambToLpCLM_apply (n : ℕ) (v : Fin n → ℝ) : ambToLpCLM n v = WithLp.toLp 2 v := rfl

/-- `WithLp.ofLp` as an `ℝ`-linear continuous map `ℂ³ → (Fin 3 → ℂ)`. -/
def e3OfLpCLM : E3 →L[ℝ] (Fin 3 → ℂ) :=
  ((EuclideanSpace.equiv (Fin 3) ℂ : E3 ≃L[ℂ] (Fin 3 → ℂ)) :
    E3 →L[ℂ] (Fin 3 → ℂ)).restrictScalars ℝ

/-- `WithLp.toLp` as an `ℝ`-linear continuous map `(Fin 3 → ℂ) → ℂ³`. -/
def e3ToLpCLM : (Fin 3 → ℂ) →L[ℝ] E3 :=
  ((EuclideanSpace.equiv (Fin 3) ℂ).symm : (Fin 3 → ℂ) →L[ℂ] E3).restrictScalars ℝ

theorem e3OfLpCLM_apply (z : E3) : e3OfLpCLM z = z.ofLp := rfl

theorem e3ToLpCLM_apply (z : Fin 3 → ℂ) : e3ToLpCLM z = WithLp.toLp 2 z := rfl

/-- The vector `1` of the one-dimensional fibre `ℂ¹`. -/
def v1C1 : EuclideanSpace ℂ (Fin 1) := WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℂ))

theorem smul_v1C1 (z : ℂ) : z • v1C1 = WithLp.toLp 2 (fun _ : Fin 1 => z) := by
  rw [v1C1, ← WithLp.toLp_smul]
  congr 1
  funext i
  fin_cases i
  simp

/-- The vector `z • 1` of the fibre `ℂ¹`, as an `ℝ`-linear continuous map. -/
def ofCCLM : ℂ →L[ℝ] EuclideanSpace ℂ (Fin 1) :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight v1C1

@[simp] theorem ofCCLM_apply (z : ℂ) : ofCCLM z = WithLp.toLp 2 (fun _ : Fin 1 => z) := by
  rw [ofCCLM, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, smul_v1C1]

/-- The coordinate `ℂ¹ → ℂ`, as an `ℝ`-linear continuous map. -/
def c1ToCCLM : EuclideanSpace ℂ (Fin 1) →L[ℝ] ℂ :=
  (((ContinuousLinearMap.proj (φ := fun _ : Fin 1 => ℂ) (0 : Fin 1)) :
      (Fin 1 → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).comp
    (((EuclideanSpace.equiv (Fin 1) ℂ : EuclideanSpace ℂ (Fin 1) ≃L[ℂ] (Fin 1 → ℂ)) :
      EuclideanSpace ℂ (Fin 1) →L[ℂ] (Fin 1 → ℂ)).restrictScalars ℝ)

@[simp] theorem c1ToCCLM_apply (z : EuclideanSpace ℂ (Fin 1)) : c1ToCCLM z = z.ofLp 0 := rfl

/-- The linear map `v ↦ coordEval S f v`, packaged as a continuous linear map. -/
def coordEvalCLM {k m : ℕ} (S : ChartIdx k m) (f : Stiefel k m) : Amb k →L[ℝ] Amb (k + m) :=
  Finset.sum Finset.univ (fun i : Fin k =>
    (((ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i) :
        (Fin k → ℝ) →L[ℝ] ℝ).comp (ambOfLpCLM k)).smulRight (coordVec S f i))

theorem coordEvalCLM_apply {k m : ℕ} (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k) :
    coordEvalCLM S f v = coordEval S f v := by
  simp only [coordEvalCLM, ContinuousLinearMap.sum_apply, coordEval,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ambOfLpCLM_apply, smul_eq_mul]

/-- The Hermitian pairing `w ↦ ∑_m v_m * conj(w_m)`, as an `ℝ`-linear continuous map. -/
def ipRealCLM (v : Fin 3 → ℂ) : (Fin 3 → ℂ) →L[ℝ] ℂ :=
  Finset.sum Finset.univ (fun m : Fin 3 =>
    (((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
      (((ContinuousLinearMap.proj (φ := fun _ : Fin 3 => ℂ) m) :
        (Fin 3 → ℂ) →L[ℂ] ℂ).restrictScalars ℝ))).smulRight (v m))

@[simp] theorem ipRealCLM_apply (v w : Fin 3 → ℂ) :
    ipRealCLM v w = ∑ m, star (w m) * v m := by
  rw [ipRealCLM, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.proj_apply, smul_eq_mul,
    starRingEnd_apply]

theorem ipRealCLM_smul_left (v : Fin 3 → ℂ) (c : ℂ) (w : Fin 3 → ℂ) :
    ipRealCLM (c • v) w = c * ipRealCLM v w := by
  rw [ipRealCLM_apply, ipRealCLM_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]; ring

theorem ipRealCLM_conj_smul (v w : Fin 3 → ℂ) (c : ℂ) :
    ipRealCLM v (c • w) = star c * ipRealCLM v w := by
  rw [ipRealCLM_apply, ipRealCLM_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, star_mul]; ring

theorem ipRealCLM_self (v : Fin 3 → ℂ) : ipRealCLM v v = Work.Gen.ipCLM v v := by
  rw [ipRealCLM_apply, Work.Gen.ipCLM_apply]

theorem star_ipCLM_self (v : Fin 3 → ℂ) : star (Work.Gen.ipCLM v v) = Work.Gen.ipCLM v v := by
  rw [Work.Gen.ipCLM_apply, star_sum]
  exact Finset.sum_congr rfl fun m _ => by
    rw [star_mul, star_star, Complex.star_def, Complex.conj_mul']

theorem ipCLM_self_ne_zero' {v : Fin 3 → ℂ} (hv : v ≠ 0) : Work.Gen.ipCLM v v ≠ 0 :=
  Work.Gen.ipCLM_self_ne_zero hv

/-- The complex number `d ↦ (equivC1R2.symm d)₀`. -/
def zCLM : Amb 2 →L[ℝ] ℂ := c1ToCCLM.comp (equivC1R2.symm : Amb 2 →L[ℝ] EuclideanSpace ℂ (Fin 1))

theorem zCLM_apply (d : Amb 2) : zCLM d = (equivC1R2.symm d).ofLp 0 := rfl

/-- **The inverse dictionary**: `d ↦ (conj z / ‖v‖²) • v` with `z = zCLM d`. -/
def gammaCLM (i : Fin 3) (x : CP 2) : Amb 2 →L[ℝ] (Fin 3 → ℂ) :=
  (((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp zCLM).smulRight
      ((Work.Gen.ipCLM (Work.Gen.uVec i x) (Work.Gen.uVec i x))⁻¹)).smulRight
    (Work.Gen.uVec i x)

theorem gammaCLM_apply (i : Fin 3) (x : CP 2) (d : Amb 2) :
    gammaCLM i x d
      = (star (zCLM d) * (Work.Gen.ipCLM (Work.Gen.uVec i x)
          (Work.Gen.uVec i x))⁻¹) • Work.Gen.uVec i x := by
  rw [gammaCLM, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, starRingEnd_apply]

/-- **The gauge `Φ`**: read the `S`-coordinate of the plane vector in `ℂ³` and pair it with the
chart representative. -/
def phiCLM (S : ChartIdx 2 4) (i : Fin 3) (x : CP 2) : Amb 2 →L[ℝ] Amb 2 :=
  (equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] Amb 2).comp
    (ofCCLM.comp
      ((ipRealCLM (Work.Gen.uVec i x)).comp
        (e3OfLpCLM.comp
          ((cxE.symm : Amb 6 →L[ℝ] E3).comp
            ((coordEvalCLM S (chartFrame2 i x)).comp
              (matLin (orientMat S (sigma2 x))))))))

/-- **The oriented `S`-coordinate** of a plane vector. -/
def orCoord (S : ChartIdx 2 4) (x : CP 2) : Amb 6 →L[ℝ] Amb 2 :=
  (matLin (orientMat S (sigma2 x))).comp
    ((ambToLpCLM 2).comp
      (((coordProj S : (Fin (2 + 4) → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)).toContinuousLinearMap).comp
        (ambOfLpCLM 6)))

theorem orCoord_eq_toECoordAt (S : ChartIdx 2 4) (x : CP 2) :
    orCoord S x = (fun w : Amb 6 => toECoordAt S (sigma2 x) w) := rfl

/-- **The inverse gauge `Φ⁻¹`**. -/
def phiInvCLM (S : ChartIdx 2 4) (i : Fin 3) (x : CP 2) : Amb 2 →L[ℝ] Amb 2 :=
  (orCoord S x).comp
    ((cxE : E3 →L[ℝ] Amb 6).comp (e3ToLpCLM.comp (gammaCLM i x)))


/-- The pullback of the tautological bundle along the base-case probe. -/
abbrev pullGamma : RealBundle (CP 2) (Amb 2) (ChartIdx 2 4) :=
  Work.Thom.bundleComap (tautologicalBundle 2 4) sigma2

theorem zStd_baseSet (i : Fin 3) : zStd.baseSet i = Work.Projective.chartSet i := by
  unfold zStd
  rw [RealBundle.mapFibre_baseSet, Work.Thom.realification_baseSet, Work.Gen.tautDual_baseSet]

theorem pullGamma_baseSet (S : ChartIdx 2 4) :
    pullGamma.baseSet S = sigma2 ⁻¹' (baseSet S) :=
  Work.Thom.bundleComap_baseSet (tautologicalBundle 2 4) sigma2 S

theorem pullGamma_coordChange (S T : ChartIdx 2 4) (x : CP 2) :
    pullGamma.coordChange S T x = coordChangeO S T (sigma2 x) :=
  Work.Thom.bundleComap_coordChange (tautologicalBundle 2 4) sigma2 S T x


theorem ofCCLM_smul (μ z : ℂ) : μ • ofCCLM z = ofCCLM (μ * z) := by
  rw [ofCCLM_apply, ofCCLM_apply]
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  rw [PiLp.smul_apply, smul_eq_mul]

/-- The `ℂ³`-vector of the plane vector with `S`-coordinate `c`, read along the chart-`i` frame. -/
def phiVec (S : ChartIdx 2 4) (i : Fin 3) (x : CP 2) (c : Amb 2) : Fin 3 → ℂ :=
  (e3OfLpCLM : E3 →L[ℝ] (Fin 3 → ℂ)) ((cxE.symm : Amb 6 →L[ℝ] E3)
    ((coordEvalCLM S (chartFrame2 i x)) (matLin (orientMat S (sigma2 x)) c)))

theorem phiVec_eq (S : ChartIdx 2 4) (i : Fin 3) (x : CP 2) (c : Amb 2) :
    phiVec S i x c = e3OfLpCLM ((cxE.symm : Amb 6 →L[ℝ] E3)
      (coordEval S (chartFrame2 i x) (matLin (orientMat S (sigma2 x)) c))) := by
  simp only [phiVec, coordEvalCLM_apply]

/-- The Hermitian pairing of the representative with the plane vector. -/
def phiCoeff (S : ChartIdx 2 4) (i : Fin 3) (x : CP 2) (c : Amb 2) : ℂ :=
  ipRealCLM (Work.Gen.uVec i x) (phiVec S i x c)

theorem phiCLM_apply (S : ChartIdx 2 4) (i : Fin 3) (x : CP 2) (c : Amb 2) :
    phiCLM S i x c
      = (equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] Amb 2) (ofCCLM (phiCoeff S i x c)) := rfl

theorem phiInvCLM_apply (S : ChartIdx 2 4) (i : Fin 3) (x : CP 2) (d : Amb 2) :
    phiInvCLM S i x d = orCoord S x (cxE (e3ToLpCLM (gammaCLM i x d))) := rfl

theorem chartSet_of_mem_zStd_baseSet {i : Fin 3} {x : CP 2} (hi : x ∈ zStd.baseSet i) :
    x ∈ Work.Projective.chartSet i := by
  have h := hi; rwa [zStd_baseSet i] at h

theorem chartFrame2_mem_chartSet {S : ChartIdx 2 4} {i : Fin 3} {x : CP 2}
    (hS : sigma2 x ∈ baseSet S) (hci : x ∈ Work.Projective.chartSet i) :
    chartFrame2 i x ∈ chartSet S := by
  rw [← mem_baseSet_iff S (chartFrame2 i x)]
  have h : (Quotient.mk'' (chartFrame2 i x) : OG 2 4) = sigma2 x := by
    change ogMk 2 4 (chartFrame2 i x) = sigma2 x
    exact (sigma2_apply_frame i x hci).symm
  rw [h]
  exact hS

theorem sigma2_eq_chartFrame2_mk {i : Fin 3} {x : CP 2}
    (hci : x ∈ Work.Projective.chartSet i) :
    (sigma2 x : OG 2 4) = Quotient.mk'' (chartFrame2 i x) := by
  change sigma2 x = ogMk 2 4 (chartFrame2 i x)
  exact sigma2_apply_frame i x hci

/-- A chart evaluation read in a frame is the evaluation in the chart. -/
theorem coordEval_eq_evalChartO (S : ChartIdx 2 4) (x : ↥(baseSet S)) (f : Stiefel 2 4)
    (hf : f ∈ chartSet S) (hmk : (x : OG 2 4) = Quotient.mk'' f) (v : Amb 2) :
    coordEval S f (matLin (orientMat S (x : OG 2 4)) v) = evalChartO S x v := by
  obtain rfl : x = ⟨Quotient.mk'' f, (mem_baseSet_iff S f).mpr hf⟩ := Subtype.ext hmk
  rw [evalChartO_spec S f hf v]

/-- The coordinate of a chart evaluation in the other chart is the transition function. -/
theorem coordEval_glue_frame (S T : ChartIdx 2 4) (i : Fin 3) (x : CP 2)
    (hS : sigma2 x ∈ baseSet S) (hT : sigma2 x ∈ baseSet T)
    (hci : x ∈ Work.Projective.chartSet i) (c : Amb 2) :
    coordEval S (chartFrame2 i x)
        (matLin (orientMat S (sigma2 x)) (coordChangeO T S (sigma2 x) c))
      = coordEval T (chartFrame2 i x) (matLin (orientMat T (sigma2 x)) c) := by
  have hfS : chartFrame2 i x ∈ chartSet S := chartFrame2_mem_chartSet hS hci
  have hfT : chartFrame2 i x ∈ chartSet T := chartFrame2_mem_chartSet hT hci
  have hmkS : ((⟨sigma2 x, hS⟩ : ↥(baseSet S)) : OG 2 4) = Quotient.mk'' (chartFrame2 i x) :=
    sigma2_eq_chartFrame2_mk hci
  have hmkT : ((⟨sigma2 x, hT⟩ : ↥(baseSet T)) : OG 2 4) = Quotient.mk'' (chartFrame2 i x) :=
    sigma2_eq_chartFrame2_mk hci
  rw [coordEval_eq_evalChartO S ⟨sigma2 x, hS⟩ (chartFrame2 i x) hfS hmkS
      (coordChangeO T S (sigma2 x) c),
    coordEval_eq_evalChartO T ⟨sigma2 x, hT⟩ (chartFrame2 i x) hfT hmkT c]
  exact (evalChartO_glue T S (sigma2 x) ⟨hT, hS⟩ c).symm

/-- **The `zStd`-transition identity of the gauge.** -/
theorem phi_htgt (S : ChartIdx 2 4) (i j : Fin 3) (x : CP 2)
    (hS : x ∈ pullGamma.baseSet S) (hi : x ∈ zStd.baseSet i) (hj : x ∈ zStd.baseSet j) :
    (zStd.coordChange i j x).comp (phiCLM S i x) = phiCLM S j x := by
  have hci : x ∈ Work.Projective.chartSet i := chartSet_of_mem_zStd_baseSet hi
  have hcj : x ∈ Work.Projective.chartSet j := chartSet_of_mem_zStd_baseSet hj
  have hfr : coordEval S (chartFrame2 i x) = coordEval S (chartFrame2 j x) :=
    coordEval_chartFrame2_eq S i j x hci hcj
  apply ContinuousLinearMap.ext
  intro c
  have hW : phiVec S i x c = phiVec S j x c := by
    simp only [phiVec, coordEvalCLM_apply]
    rw [hfr]
  have hval : Work.Gen.homCoord 2 j i x * phiCoeff S i x c = phiCoeff S j x c := by
    rw [phiCoeff, phiCoeff, ← hW, uVec_eq_homCoord_smul i j x hci hcj, ipRealCLM_smul_left]
  rw [ContinuousLinearMap.comp_apply, phiCLM_apply, phiCLM_apply, zStd_coordChange_eq i j x]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    cmulLM_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [ofCCLM_smul, hval]

/-- **The `pullGamma`-transition identity of the gauge.** -/
theorem phi_hsrc (S T : ChartIdx 2 4) (i : Fin 3) (x : CP 2)
    (hS : x ∈ pullGamma.baseSet S) (hT : x ∈ pullGamma.baseSet T) (hi : x ∈ zStd.baseSet i) :
    (phiCLM S i x).comp (pullGamma.coordChange T S x) = phiCLM T i x := by
  have hci : x ∈ Work.Projective.chartSet i := chartSet_of_mem_zStd_baseSet hi
  have hS' : sigma2 x ∈ baseSet S := hS
  have hT' : sigma2 x ∈ baseSet T := hT
  apply ContinuousLinearMap.ext
  intro c
  have hW : phiVec S i x (pullGamma.coordChange T S x c) = phiVec T i x c := by
    simp only [phiVec, coordEvalCLM_apply, pullGamma_coordChange]
    rw [coordEval_glue_frame S T i x hS' hT' hci c]
  have hval : phiCoeff S i x (pullGamma.coordChange T S x c) = phiCoeff T i x c := by
    rw [phiCoeff, phiCoeff, hW]
  rw [ContinuousLinearMap.comp_apply, phiCLM_apply, phiCLM_apply, hval]

/-! ## The inverse identities of the gauge -/

theorem ofCCLM_ofLp (w : EuclideanSpace ℂ (Fin 1)) : ofCCLM (w.ofLp 0) = w := by
  rw [ofCCLM_apply,
    show (fun _ : Fin 1 => w.ofLp 0) = w.ofLp from funext (fun i => by fin_cases i; rfl)]

theorem zCLM_eCr2_ofCCLM (z : ℂ) :
    zCLM ((equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] Amb 2) (ofCCLM z)) = z := by
  have h : (equivC1R2.symm : Amb 2 →L[ℝ] EuclideanSpace ℂ (Fin 1))
      ((equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] Amb 2) (ofCCLM z))
      = ofCCLM z := ContinuousLinearEquiv.symm_apply_apply equivC1R2 (ofCCLM z)
  rw [zCLM, ContinuousLinearMap.comp_apply, h, c1ToCCLM_apply, ofCCLM_apply]

theorem zCLM_self (d : Amb 2) : ofCCLM (zCLM d) = equivC1R2.symm d :=
  ofCCLM_ofLp (equivC1R2.symm d)

theorem e3ToLp_e3OfLp (w : E3) : e3ToLpCLM (e3OfLpCLM w) = w := by
  rw [e3ToLpCLM_apply, e3OfLpCLM_apply, WithLp.toLp_ofLp]

/-- A vector of the span of the chart frame is a vector of the plane. -/
theorem memPlane_of_mem_chartFrame (S : ChartIdx 2 4) {i : Fin 3} {x : CP 2}
    (hci : x ∈ Work.Projective.chartSet i) {W : Amb 6}
    (hW : W ∈ Submodule.span ℝ (Set.range (chartFrame2 i x).1)) :
    memPlane (sigma2 x) W :=
  ⟨chartFrame2 i x, (sigma2_apply_frame i x hci).symm, hW⟩

/-- The chart evaluation is a vector of the plane. -/
theorem evalChartO_memPlane (S : ChartIdx 2 4) (P : OG 2 4) (hPS : P ∈ baseSet S) (v : Amb 2) :
    memPlane P (evalChartO S ⟨P, hPS⟩ v) := by
  obtain ⟨f, hfmk⟩ : ∃ f : Stiefel 2 4, Quotient.mk'' f = P := Quotient.exists_rep _
  have hfc : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hfmk ▸ hPS)
  refine ⟨f, hfmk, ?_⟩
  rw [evalChartO, evalChart_spec S ⟨P, hPS⟩ f hfc hfmk.symm (matLin (orientMat S P) v),
    coordEval_eq_sum_frame]
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

/-- The `ℂ³`-vector of the plane vector of the gauge lies in the complex line. -/
theorem phiVec_mem_line (S : ChartIdx 2 4) (i : Fin 3) (x : CP 2)
    (hS : sigma2 x ∈ baseSet S) (hci : x ∈ Work.Projective.chartSet i) (c : Amb 2) :
    phiVec S i x c ∈ Submodule.span ℂ {Work.Gen.uVec i x} := by
  have hfS : chartFrame2 i x ∈ chartSet S := chartFrame2_mem_chartSet hS hci
  have hmkS : ((⟨sigma2 x, hS⟩ : ↥(baseSet S)) : OG 2 4) = Quotient.mk'' (chartFrame2 i x) :=
    sigma2_eq_chartFrame2_mk hci
  rw [phiVec_eq, e3OfLpCLM_apply,
    coordEval_eq_evalChartO S ⟨sigma2 x, hS⟩ (chartFrame2 i x) hfS hmkS c]
  exact plane_line i x hci (evalChartO_memPlane S (sigma2 x) hS c)

/-- **The gauge reads a vector of the plane through its `ℂ³`-coordinates.** -/
theorem phiCoeff_orCoord (S : ChartIdx 2 4) (i : Fin 3) (x : CP 2)
    (hS : sigma2 x ∈ baseSet S) (hci : x ∈ Work.Projective.chartSet i) {W : Amb 6}
    (hW : W ∈ Submodule.span ℝ (Set.range (chartFrame2 i x).1)) :
    phiCoeff S i x (orCoord S x W)
      = ipRealCLM (Work.Gen.uVec i x) (e3OfLpCLM ((cxE.symm : Amb 6 →L[ℝ] E3) W)) := by
  have hfS : chartFrame2 i x ∈ chartSet S := chartFrame2_mem_chartSet hS hci
  have hmkS : ((⟨sigma2 x, hS⟩ : ↥(baseSet S)) : OG 2 4) = Quotient.mk'' (chartFrame2 i x) :=
    sigma2_eq_chartFrame2_mk hci
  have hinner : coordEval S (chartFrame2 i x) (matLin (orientMat S (sigma2 x)) (orCoord S x W))
      = W := by
    rw [orCoord_eq_toECoordAt]
    rw [coordEval_eq_evalChartO S ⟨sigma2 x, hS⟩ (chartFrame2 i x) hfS hmkS]
    exact evalChartO_toECoordAt' S (sigma2 x) hS (memPlane_of_mem_chartFrame S hci hW)
  rw [phiCoeff, phiVec, coordEvalCLM_apply, hinner]

/-- The `ℂ³`-vector of the plane vector `cxE (cxOf (γ • u))`. -/
theorem e3OfLp_cxE_cxOf_smul (γ : ℂ) (v : Fin 3 → ℂ) :
    e3OfLpCLM ((cxE.symm : Amb 6 →L[ℝ] E3) (cxE (cxOf (γ • v)))) = γ • v := by
  rw [show (cxE.symm : Amb 6 →L[ℝ] E3) (cxE (cxOf (γ • v))) = cxOf (γ • v) from
    LinearIsometryEquiv.symm_apply_apply cxE (cxOf (γ • v))]
  rw [show cxOf (γ • v) = γ • cxOf v from WithLp.toLp_smul 2 γ v]
  rfl

/-- The plane vector `cxE (cxOf (γ • u))` lies in the plane of the probe. -/
theorem cxE_cxOf_smul_mem_chartFrame (S : ChartIdx 2 4) {i : Fin 3} {x : CP 2}
    (hci : x ∈ Work.Projective.chartSet i) (γ : ℂ) :
    cxE (cxOf (γ • Work.Gen.uVec i x))
      ∈ Submodule.span ℝ (Set.range (chartFrame2 i x).1) := by
  have hkey := span_probeFrameRep (Work.Gen.uVec i x) (Work.Gen.uVec_ne_zero i x)
  rw [show Submodule.span ℝ (Set.range (chartFrame2 i x).1)
      = Submodule.span ℝ (Set.range (probeFrameRep 2 4 two_le_two four_le_four
          (Work.Gen.uVec i x))) from by rw [chartFrame2_val],
    hkey]
  refine Submodule.mem_map.mpr ⟨γ • cxOf (Work.Gen.uVec i x), ?_, rfl⟩
  rw [Submodule.restrictScalars_mem]
  exact Submodule.smul_mem _ γ (Submodule.subset_span rfl)

/-- **The right inverse identity of the gauge.** -/
theorem phi_right (S : ChartIdx 2 4) (i : Fin 3) (x : CP 2) (d : Amb 2)
    (hx : x ∈ pullGamma.baseSet S ∩ zStd.baseSet i) :
    phiCLM S i x (phiInvCLM S i x d) = d := by
  have hS : sigma2 x ∈ baseSet S := hx.1
  have hci : x ∈ Work.Projective.chartSet i := chartSet_of_mem_zStd_baseSet hx.2
  have hQV : Work.Gen.ipCLM (Work.Gen.uVec i x) (Work.Gen.uVec i x) ≠ 0 :=
    Work.Gen.ipCLM_self_ne_zero (Work.Gen.uVec_ne_zero i x)
  have hmem : cxE (cxOf ((star (zCLM d) * (Work.Gen.ipCLM (Work.Gen.uVec i x)
        (Work.Gen.uVec i x))⁻¹) • Work.Gen.uVec i x))
      ∈ Submodule.span ℝ (Set.range (chartFrame2 i x).1) :=
    cxE_cxOf_smul_mem_chartFrame S hci _
  have hcoeff : phiCoeff S i x (phiInvCLM S i x d)
      = ipRealCLM (Work.Gen.uVec i x) (e3OfLpCLM ((cxE.symm : Amb 6 →L[ℝ] E3)
          (cxE (cxOf ((star (zCLM d) * (Work.Gen.ipCLM (Work.Gen.uVec i x)
            (Work.Gen.uVec i x))⁻¹) • Work.Gen.uVec i x))))) := by
    rw [phiInvCLM_apply]
    exact phiCoeff_orCoord S i x hS hci hmem
  have hfin : phiCoeff S i x (phiInvCLM S i x d) = zCLM d := by
    rw [hcoeff, e3OfLp_cxE_cxOf_smul, ipRealCLM_conj_smul, ipRealCLM_self,
      star_mul, star_inv₀, star_ipCLM_self, star_star]
    rw [mul_comm (Work.Gen.ipCLM (Work.Gen.uVec i x) (Work.Gen.uVec i x))⁻¹ (zCLM d),
      mul_assoc, inv_mul_cancel₀ hQV, mul_one]
  rw [phiCLM_apply, hfin, zCLM_self]
  exact ContinuousLinearEquiv.apply_symm_apply equivC1R2 d

/-- **The left inverse identity of the gauge.** -/
theorem phi_left (S : ChartIdx 2 4) (i : Fin 3) (x : CP 2) (c : Amb 2)
    (hx : x ∈ pullGamma.baseSet S ∩ zStd.baseSet i) :
    phiInvCLM S i x (phiCLM S i x c) = c := by
  have hS : sigma2 x ∈ baseSet S := hx.1
  have hci : x ∈ Work.Projective.chartSet i := chartSet_of_mem_zStd_baseSet hx.2
  have hfS : chartFrame2 i x ∈ chartSet S := chartFrame2_mem_chartSet hS hci
  have hmkS : ((⟨sigma2 x, hS⟩ : ↥(baseSet S)) : OG 2 4) = Quotient.mk'' (chartFrame2 i x) :=
    sigma2_eq_chartFrame2_mk hci
  have hQ : Work.Gen.ipCLM (Work.Gen.uVec i x) (Work.Gen.uVec i x) ≠ 0 :=
    Work.Gen.ipCLM_self_ne_zero (Work.Gen.uVec_ne_zero i x)
  obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp (phiVec_mem_line S i x hS hci c)
  have hz : phiCoeff S i x c = star γ * Work.Gen.ipCLM (Work.Gen.uVec i x)
      (Work.Gen.uVec i x) := by
    rw [phiCoeff, ← hγ, ipRealCLM_conj_smul, ipRealCLM_self]
  have hgamma : gammaCLM i x ((equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] Amb 2)
      (ofCCLM (phiCoeff S i x c))) = phiVec S i x c := by
    rw [gammaCLM_apply, zCLM_eCr2_ofCCLM]
    have h3 : star (phiCoeff S i x c) * (Work.Gen.ipCLM (Work.Gen.uVec i x)
        (Work.Gen.uVec i x))⁻¹ = γ := by
      rw [hz, star_mul, star_star, star_ipCLM_self,
        mul_comm (Work.Gen.ipCLM (Work.Gen.uVec i x) (Work.Gen.uVec i x)) γ,
        mul_assoc, mul_inv_cancel₀ hQ, mul_one]
    rw [h3, hγ]
  rw [phiCLM_apply, phiInvCLM_apply, hgamma, phiVec_eq, e3ToLp_e3OfLp,
    show cxE ((cxE.symm : Amb 6 →L[ℝ] E3) (coordEval S (chartFrame2 i x)
        (matLin (orientMat S (sigma2 x)) c)))
      = coordEval S (chartFrame2 i x) (matLin (orientMat S (sigma2 x)) c) from
      LinearIsometryEquiv.apply_symm_apply cxE _,
    coordEval_eq_evalChartO S ⟨sigma2 x, hS⟩ (chartFrame2 i x) hfS hmkS c,
    orCoord_eq_toECoordAt]
  exact toECoordAt_evalChartO' S (sigma2 x) hS c

/-! ## The inverse transition identities of the gauge -/

/-- **The inverse `zStd`-transition identity of the gauge.** -/
theorem phi_htgtinv (S : ChartIdx 2 4) (i j : Fin 3) (x : CP 2)
    (hS : x ∈ pullGamma.baseSet S) (hi : x ∈ zStd.baseSet i) (hj : x ∈ zStd.baseSet j) :
    (phiInvCLM S i x).comp (zStd.coordChange j i x) = phiInvCLM S j x := by
  apply ContinuousLinearMap.ext
  intro d
  have hM : phiCLM S i x (phiInvCLM S j x d) = zStd.coordChange j i x d := by
    rw [← phi_htgt S j i x hS hj hi]
    show zStd.coordChange j i x (phiCLM S j x (phiInvCLM S j x d)) = zStd.coordChange j i x d
    rw [phi_right S j x d ⟨hS, hj⟩]
  rw [ContinuousLinearMap.comp_apply, ← hM]
  exact phi_left S i x (phiInvCLM S j x d) ⟨hS, hi⟩

/-- **The inverse `pullGamma`-transition identity of the gauge.** -/
theorem phi_hsrcinv (S T : ChartIdx 2 4) (i : Fin 3) (x : CP 2)
    (hS : x ∈ pullGamma.baseSet S) (hT : x ∈ pullGamma.baseSet T) (hi : x ∈ zStd.baseSet i) :
    (pullGamma.coordChange S T x).comp (phiInvCLM S i x) = phiInvCLM T i x := by
  apply ContinuousLinearMap.ext
  intro d
  have hM : phiCLM T i x (pullGamma.coordChange S T x (phiInvCLM S i x d)) = d := by
    rw [← ContinuousLinearMap.comp_apply, phi_hsrc T S i x hT hS hi]
    exact phi_right S i x d ⟨hS, hi⟩
  calc (pullGamma.coordChange S T x) (phiInvCLM S i x d)
      = phiInvCLM T i x (phiCLM T i x
          ((pullGamma.coordChange S T x) (phiInvCLM S i x d))) :=
        (phi_left T i x _ ⟨hT, hi⟩).symm
    _ = phiInvCLM T i x d := by rw [hM]

/-! ## Continuity of the gauge -/

theorem continuous_ipRealCLM :
    Continuous fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => ipRealCLM p.1 p.2 := by
  simp only [ipRealCLM_apply]
  exact continuous_finsetSum _ fun m _ =>
    ((continuous_apply m).comp continuous_snd).star.mul
      ((continuous_apply m).comp continuous_fst)

theorem continuous_ipCLM :
    Continuous fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => Work.Gen.ipCLM p.1 p.2 := by
  simp only [Work.Gen.ipCLM_apply]
  exact continuous_finsetSum _ fun m _ =>
    ((continuous_apply m).comp continuous_fst).star.mul
      ((continuous_apply m).comp continuous_snd)

theorem continuousOn_uVec (i : Fin 3) :
    ContinuousOn (fun x : CP 2 => Work.Gen.uVec i x) (Work.Projective.chartSet i) :=
  (continuous_insertNth_one (n := 2) i).continuousOn.comp
    (Work.Projective.continuousOn_chartFun i) (fun _ _ => Set.mem_univ _)

theorem mem_baseSet_of_mem_pullGamma {S : ChartIdx 2 4} {x : CP 2}
    (hx : x ∈ pullGamma.baseSet S) : sigma2 x ∈ baseSet S := by
  have h := hx
  rw [pullGamma_baseSet S] at h
  exact h

theorem phiVec_evalChartO (S : ChartIdx 2 4) (i : Fin 3) (x : CP 2) (hS : sigma2 x ∈ baseSet S)
    (hci : x ∈ Work.Projective.chartSet i) (c : Amb 2) :
    phiVec S i x c = e3OfLpCLM ((cxE.symm : Amb 6 →L[ℝ] E3) (evalChartO S ⟨sigma2 x, hS⟩ c)) := by
  rw [phiVec_eq, coordEval_eq_evalChartO S ⟨sigma2 x, hS⟩ (chartFrame2 i x)
    (chartFrame2_mem_chartSet (S := S) (i := i) (x := x) hS hci)
    (sigma2_eq_chartFrame2_mk hci) c]

theorem phiCLM_cont_pair (S : ChartIdx 2 4) (i : Fin 3) :
    Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      phiCLM S i (p.1 : CP 2) p.2 := by
  have hSof : ∀ p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2,
      sigma2 (p.1 : CP 2) ∈ baseSet S := fun p => mem_baseSet_of_mem_pullGamma p.1.2.1
  have hci : ∀ p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2,
      (p.1 : CP 2) ∈ Work.Projective.chartSet i :=
    fun p => chartSet_of_mem_zStd_baseSet p.1.2.2
  have hsub : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      (⟨sigma2 (p.1 : CP 2), hSof p⟩ : ↥(baseSet S)) :=
    Continuous.subtype_mk (sigma2.continuous.comp (continuous_subtype_val.comp continuous_fst))
      hSof
  have hE : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      evalChartO S (⟨sigma2 (p.1 : CP 2), hSof p⟩ : ↥(baseSet S)) p.2 :=
    (continuous_evalChartO S).comp (hsub.prodMk continuous_snd)
  have hu : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      Work.Gen.uVec i (p.1 : CP 2) :=
    (continuousOn_uVec i).comp_continuous (continuous_subtype_val.comp continuous_fst) hci
  have hw : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      e3OfLpCLM ((cxE.symm : Amb 6 →L[ℝ] E3)
        (evalChartO S (⟨sigma2 (p.1 : CP 2), hSof p⟩ : ↥(baseSet S)) p.2)) :=
    e3OfLpCLM.continuous.comp ((cxE.symm : Amb 6 →L[ℝ] E3).continuous.comp hE)
  have hclm : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      ipRealCLM (Work.Gen.uVec i (p.1 : CP 2))
        (e3OfLpCLM ((cxE.symm : Amb 6 →L[ℝ] E3)
          (evalChartO S (⟨sigma2 (p.1 : CP 2), hSof p⟩ : ↥(baseSet S)) p.2))) :=
    continuous_ipRealCLM.comp (hu.prodMk hw)
  have hfin : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      (equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] Amb 2)
        (ofCCLM (ipRealCLM (Work.Gen.uVec i (p.1 : CP 2))
          (e3OfLpCLM ((cxE.symm : Amb 6 →L[ℝ] E3)
            (evalChartO S (⟨sigma2 (p.1 : CP 2), hSof p⟩ : ↥(baseSet S)) p.2))))) :=
    (equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] Amb 2).continuous.comp
      (ofCCLM.continuous.comp hclm)
  refine hfin.congr (fun p => ?_)
  rw [phiCLM_apply, phiCoeff, phiVec_evalChartO S i (p.1 : CP 2) (hSof p) (hci p) p.2]

theorem phi_cont (S : ChartIdx 2 4) (i : Fin 3) :
    ContinuousOn (fun x : CP 2 => phiCLM S i x)
      (pullGamma.baseSet S ∩ zStd.baseSet i) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact Work.Thom.continuous_clm_of_continuous_apply (n := 2) _ (phiCLM_cont_pair S i)


theorem gammaCLM_cont_pair (S : ChartIdx 2 4) (i : Fin 3) :
    Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      gammaCLM i (p.1 : CP 2) p.2 := by
  have hu : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      Work.Gen.uVec i (p.1 : CP 2) :=
    (continuousOn_uVec i).comp_continuous (continuous_subtype_val.comp continuous_fst)
      (fun p => chartSet_of_mem_zStd_baseSet p.1.2.2)
  have hQ : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      Work.Gen.ipCLM (Work.Gen.uVec i (p.1 : CP 2)) (Work.Gen.uVec i (p.1 : CP 2)) :=
    continuous_ipCLM.comp (hu.prodMk hu)
  have hQne : ∀ p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2,
      Work.Gen.ipCLM (Work.Gen.uVec i (p.1 : CP 2)) (Work.Gen.uVec i (p.1 : CP 2)) ≠ 0 :=
    fun p => Work.Gen.ipCLM_self_ne_zero (Work.Gen.uVec_ne_zero i (p.1 : CP 2))
  have hz : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      star (zCLM p.2) := (zCLM.continuous.comp continuous_snd).star
  have hmain : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      (star (zCLM p.2) * (Work.Gen.ipCLM (Work.Gen.uVec i (p.1 : CP 2))
        (Work.Gen.uVec i (p.1 : CP 2)))⁻¹) • Work.Gen.uVec i (p.1 : CP 2) :=
    (hz.mul (hQ.inv₀ hQne)).smul hu
  exact hmain.congr (fun p => (gammaCLM_apply i (p.1 : CP 2) p.2).symm)

theorem phiInvCLM_cont_pair (S : ChartIdx 2 4) (i : Fin 3) :
    Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      phiInvCLM S i (p.1 : CP 2) p.2 := by
  have hSof : ∀ p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2,
      sigma2 (p.1 : CP 2) ∈ baseSet S := fun p => mem_baseSet_of_mem_pullGamma p.1.2.1
  have hsub : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      (⟨sigma2 (p.1 : CP 2), hSof p⟩ : ↥(baseSet S)) :=
    Continuous.subtype_mk (sigma2.continuous.comp (continuous_subtype_val.comp continuous_fst))
      hSof
  have hmat : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      matLin (orientMat S (⟨sigma2 (p.1 : CP 2), hSof p⟩ : ↥(baseSet S))) :=
    continuous_matLin.comp ((continuous_orientMat_subtype S).comp hsub)
  have hgam := gammaCLM_cont_pair S i
  have hinner : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      cxE (e3ToLpCLM (gammaCLM i (p.1 : CP 2) p.2)) :=
    (cxE : E3 →L[ℝ] Amb 6).continuous.comp (e3ToLpCLM.continuous.comp hgam)
  have hcoord : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      (ambToLpCLM 2) ((coordProj S)
        (ambOfLpCLM 6 (cxE (e3ToLpCLM (gammaCLM i (p.1 : CP 2) p.2))))) :=
    (ambToLpCLM 2).continuous.comp (((coordProj S).toContinuousLinearMap).continuous.comp
      ((ambOfLpCLM 6).continuous.comp hinner))
  have hfin : Continuous fun p : ↥(pullGamma.baseSet S ∩ zStd.baseSet i) × Amb 2 =>
      matLin (orientMat S (⟨sigma2 (p.1 : CP 2), hSof p⟩ : ↥(baseSet S)))
        ((ambToLpCLM 2) ((coordProj S)
          (ambOfLpCLM 6 (cxE (e3ToLpCLM (gammaCLM i (p.1 : CP 2) p.2)))))) :=
    hmat.clm_apply hcoord
  refine hfin.congr (fun p => ?_)
  rw [phiInvCLM_apply]
  rfl

theorem phi_contInv (S : ChartIdx 2 4) (i : Fin 3) :
    ContinuousOn (fun x : CP 2 => phiInvCLM S i x)
      (pullGamma.baseSet S ∩ zStd.baseSet i) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact Work.Thom.continuous_clm_of_continuous_apply (n := 2) _ (phiInvCLM_cont_pair S i)


/-- **The isomorphism `σ^*γ ≅ zStd`** for the base-case probe `σ = probeSigma 2 4`: the gauge
`phiCLM`/`phiInvCLM` satisfies the eight hypotheses of `Work.Thom.nonempty_bundleIso_of_gauge`. -/
theorem probeSigma_iso : Nonempty (Work.Thom.BundleIso pullGamma zStd) :=
  Work.Thom.nonempty_bundleIso_of_gauge pullGamma zStd phiCLM phiInvCLM
    phi_cont phi_contInv phi_htgt (fun S t T => phi_hsrc S T t) phi_htgtinv
    (fun S t T => phi_hsrcinv S T t) phi_left phi_right

end

end Work.ThomBordism.Grassmann.Probe2