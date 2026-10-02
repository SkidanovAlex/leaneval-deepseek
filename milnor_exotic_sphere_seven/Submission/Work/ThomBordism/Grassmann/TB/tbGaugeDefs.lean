import Mathlib
import Submission.Work.ThomBordism.Grassmann.TB.Defs
import Submission.Work.ThomBordism.Grassmann.PlaneEval
import Submission.Work.ThomBordism.Grassmann.PlaneCoord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

/-!
# The gauge of the two-block bundle isomorphism `tbZ ≅ tbW`

Vocabulary for the proof of `Work.ThomBordism.Grassmann.TB.tbBundleIso`: the comparison of the
pullback `tbZ = tbMap^*γ₄` of the tautological oriented `4`-plane bundle along the two-block map
`tbMap : ℂP⁴ → G̃r₄(ℝ²⁰)` with `tbW = tbZL ⊕ tbZL`, the realification of the tautological complex
line bundle of `ℂP⁴` doubled.

The plane `tbMap x = L ⊕ L ⊂ ℝ¹⁰ ⊕ ℝ¹⁰` (`L` the complex line of `x`) is trivialised in two ways:

* the Grassmannian chart `S` reads a plane vector through the block frame `tbFrame (uVec i x)`
  (`tbEW`);
* the charts `(i, j)` of `ℂP⁴` read it through the two complex coefficients of its blocks along the
  chart representatives `uVec i x`, `uVec j x` (`tbVecL`, `tbVecR`, `tbCoefL`, `tbCoefR`).

`tbPhi` extracts those two coefficients and realifies them with `expC` — matching
`tbZL = mapFibre expC (realification (tautLine 4))`, whose transition functions are exactly
`expCMul (homCoord 4 i j x)`.  `tbPhiInv` rebuilds the plane vector from two coefficients (`tbGeo`)
and reads its `S`-coordinates (`tbToECoordAtCLM`).
-/

namespace Work.ThomBordism.Grassmann.TBG

open Work.TangentClasses Work.Projective

noncomputable section

/-! ## 1. The coordinate re-indexing `ℝⁿ ↔ (Fin n → ℝ)` and `ℝ¹⁰ ↔ ℂ⁵` -/

/-- `WithLp.ofLp`, as a continuous linear map `ℝⁿ → (Fin n → ℝ)`. -/
def tbOfLp (n : ℕ) : Amb n →L[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ : Amb n ≃L[ℝ] (Fin n → ℝ))

theorem tbOfLp_apply (n : ℕ) (v : Amb n) : tbOfLp n v = v.ofLp := rfl

/-- `WithLp.toLp`, as a continuous linear map `(Fin n → ℝ) → ℝⁿ`. -/
def tbToLp (n : ℕ) : (Fin n → ℝ) →L[ℝ] Amb n :=
  ((EuclideanSpace.equiv (Fin n) ℝ).symm : (Fin n → ℝ) →L[ℝ] Amb n)

theorem tbToLp_apply (n : ℕ) (v : Fin n → ℝ) : tbToLp n v = WithLp.toLp 2 v := rfl

/-- `WithLp.toLp`, as a continuous linear map `(Fin 5 → ℂ) → ℂ⁵`. -/
def tbOfLpC : (Fin 5 → ℂ) →L[ℝ] E5 :=
  (((EuclideanSpace.equiv (Fin 5) ℂ).symm : (Fin 5 → ℂ) →L[ℂ] E5)).restrictScalars ℝ

theorem tbOfLpC_apply (z : Fin 5 → ℂ) : tbOfLpC z = WithLp.toLp 2 z := rfl

theorem tbOfLpC_smul (μ : ℂ) (z : Fin 5 → ℂ) : tbOfLpC (μ • z) = μ • tbOfLpC z := by
  rw [tbOfLpC_apply, tbOfLpC_apply]
  exact (WithLp.toLp_smul 2 μ z).symm

theorem tbOfLpC_ne_zero {v : Fin 5 → ℂ} (hv : v ≠ 0) : tbOfLpC v ≠ 0 := by
  intro h
  refine hv (funext fun j => ?_)
  have := congrArg (fun z : E5 => z.ofLp j) h
  simpa [tbOfLpC_apply] using this

/-- **The coordinate re-indexing `ℝ¹⁰ → (Fin 5 → ℂ)` inverse to the realification `tbReal`**: it
reads the `j`-th *pair* of real coordinates as `Re + i·Im`. -/
def tbcOfLpCLM : Amb 10 →L[ℝ] (Fin 5 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w j => ((w.ofLp (tbIdx10 j 0) : ℝ) : ℂ)
        + ((w.ofLp (tbIdx10 j 1) : ℝ) : ℂ) * Complex.I
      map_add' := fun x y => by
        funext j
        simp only [WithLp.ofLp_add, Pi.add_apply]
        push_cast
        ring
      map_smul' := fun r x => by
        funext j
        show ((r • x).ofLp (tbIdx10 j 0) : ℂ)
            + ((r • x).ofLp (tbIdx10 j 1) : ℂ) * Complex.I
          = r • (((x.ofLp (tbIdx10 j 0) : ℝ) : ℂ)
            + ((x.ofLp (tbIdx10 j 1) : ℝ) : ℂ) * Complex.I)
        rw [show ((r • x).ofLp (tbIdx10 j 0) : ℝ) = r * x.ofLp (tbIdx10 j 0) from by
              rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul],
            show ((r • x).ofLp (tbIdx10 j 1) : ℝ) = r * x.ofLp (tbIdx10 j 1) from by
              rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul],
            Complex.ofReal_mul, Complex.ofReal_mul, Complex.real_smul]
        ring }

theorem tbcOfLpCLM_apply (w : Amb 10) (j : Fin 5) :
    tbcOfLpCLM w j = ((w.ofLp (tbIdx10 j 0) : ℝ) : ℂ)
      + ((w.ofLp (tbIdx10 j 1) : ℝ) : ℂ) * Complex.I := rfl

/-- **The round trip `ℂ⁵ → ℝ¹⁰ → ℂ⁵`**: the re-indexing inverts the realification. -/
theorem tbcOfLpCLM_tbReal (z : E5) : tbcOfLpCLM (tbReal z) = z.ofLp := by
  funext j
  rw [tbcOfLpCLM_apply, tbReal_coord, tbReal_coord]
  apply Complex.ext <;> simp

/-- The inverse of the realification as a continuous linear map. -/
def tbZOf : Amb 10 →L[ℝ] E5 := tbOfLpC.comp tbcOfLpCLM

theorem tbZOf_tbReal (z : E5) : tbZOf (tbReal z) = z := by
  rw [tbZOf, ContinuousLinearMap.comp_apply, tbcOfLpCLM_tbReal, tbOfLpC_apply,
    WithLp.toLp_ofLp]

theorem tbcOfLpCLM_injective : Function.Injective tbcOfLpCLM := by
  intro w w' h
  refine PiLp.ext fun k => ?_
  obtain ⟨⟨j, a⟩, rfl⟩ := tbIdx10_surjective k
  have hj := congrFun h j
  rw [tbcOfLpCLM_apply, tbcOfLpCLM_apply] at hj
  have h1 := congrArg Complex.re hj
  have h2 := congrArg Complex.im hj
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add] at h1 h2
  fin_cases a
  · simpa using h1
  · simpa using h2

/-! ## 2. The explicit identification `ℂ ≅ ℝ²` used by `tbZL` -/

/-- The vector `1` of the one-dimensional complex space `ℂ¹`. -/
def tbOneC : EuclideanSpace ℂ (Fin 1) := WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℂ))

/-- The vector `z • 1` of `ℂ¹`, as an `ℝ`-linear map. -/
def tbOfC1 : ℂ →L[ℝ] EuclideanSpace ℂ (Fin 1) :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight tbOneC

theorem tbOfC1_apply (z : ℂ) : tbOfC1 z = WithLp.toLp 2 (fun _ : Fin 1 => z) := by
  rw [tbOfC1, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, tbOneC,
    ← WithLp.toLp_smul]
  congr 1
  funext i
  fin_cases i
  simp

/-- **The realification `ℂ → ℝ²`, `z ↦ (Re z, Im z)`**, in the normalisation of `tbZL`. -/
def tbCof : ℂ →L[ℝ] Amb 2 := (expC : EuclideanSpace ℂ (Fin 1) →L[ℝ] Amb 2).comp tbOfC1

theorem tbCof_apply (z : ℂ) : tbCof z = expC (WithLp.toLp 2 (fun _ : Fin 1 => z)) := by
  rw [tbCof, ContinuousLinearMap.comp_apply, tbOfC1_apply]
  rfl

/-- The coordinate `ℝ² → ℂ`, the inverse of `tbCof`. -/
def tbZExp : Amb 2 →L[ℝ] ℂ :=
  ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).restrictScalars ℝ).comp
    (expC.symm : Amb 2 →L[ℝ] EuclideanSpace ℂ (Fin 1))

theorem tbZExp_apply (d : Amb 2) : tbZExp d = (expC.symm d).ofLp 0 := rfl

theorem tbZExp_tbCof (z : ℂ) : tbZExp (tbCof z) = z := by
  rw [tbZExp_apply, tbCof_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem tbCof_tbZExp (d : Amb 2) : tbCof (tbZExp d) = d := by
  rw [tbZExp_apply, tbCof_apply]
  have h : (fun _ : Fin 1 => (expC.symm d).ofLp 0) = (expC.symm d).ofLp :=
    funext (fun i => by fin_cases i; rfl)
  rw [h, WithLp.toLp_ofLp, ContinuousLinearEquiv.apply_symm_apply]

/-- **`tbCof` intertwines the complex multiplication with `expCMul`.** -/
theorem tbOfC1_mul (μ z : ℂ) : tbOfC1 (μ * z) = cmulLM μ (tbOfC1 z) := by
  rw [tbOfC1_apply, tbOfC1_apply, cmulLM_apply, ← WithLp.toLp_smul]
  congr 1

theorem tbCof_smul (μ z : ℂ) : tbCof (μ * z) = expCMul μ (tbCof z) := by
  have h2 : expCMul μ (tbCof z) = expC (cmulLM μ (tbOfC1 z)) := by
    rw [expCMul, tbCof, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    exact congrArg (fun w : EuclideanSpace ℂ (Fin 1) => expC (cmulLM μ w))
      (ContinuousLinearEquiv.symm_apply_apply expC (tbOfC1 z))
  rw [h2, tbCof, ContinuousLinearMap.comp_apply, tbOfC1_mul]
  rfl

/-! ## 3. The chart frame of a point of `ℂP⁴` -/

/-- The frame of the plane of `x` built from the chart-`i` representative `uVec i x`: this is a
frame of the plane `tbMap x` (proved in `TB.Defs`), used to compute chart coordinates. -/
def tbCF (i : Fin 5) (x : CP 4) : Stiefel 4 16 :=
  tbFrameW ⟨Work.Gen.uVec i x, Work.Gen.uVec_ne_zero i x⟩

@[simp] theorem tbCF_val (i : Fin 5) (x : CP 4) :
    (tbCF i x).1 = tbFrame (Work.Gen.uVec i x) := rfl

/-! ## 4. The extraction of the complex coefficient of a plane vector -/

/-- **The coefficient of `z` along the vector `u`**, normalised by `‖u‖²`: the `ℝ`-linear map
`z ↦ ⟨u,z⟩/‖u‖²`.  For `z = lam • u` it is `lam`. -/
def tbExtract (u : Fin 5 → ℂ) : (Fin 5 → ℂ) →L[ℝ] ℂ :=
  ((Work.Gen.ipCLM u).restrictScalars ℝ).smulRight ((Work.Gen.ipCLM u u)⁻¹)

theorem tbExtract_apply (u z : Fin 5 → ℂ) :
    tbExtract u z = Work.Gen.ipCLM u z * (Work.Gen.ipCLM u u)⁻¹ := by
  rw [tbExtract, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rfl

theorem tbExtract_smul (u : Fin 5 → ℂ) (hu : u ≠ 0) (lam : ℂ) :
    tbExtract u (lam • u) = lam := by
  have h1 : Work.Gen.ipCLM u (lam • u) = lam * Work.Gen.ipCLM u u := by
    rw [map_smul, smul_eq_mul]
  rw [tbExtract_apply, h1, mul_assoc, mul_inv_cancel₀ (Work.Gen.ipCLM_self_ne_zero hu), mul_one]

/-- **The extraction is compatible with a change of spanning vector**: if `u = mu • u'` and `z` is a
multiple of `u`, then the coefficient along `u'` is `mu` times the coefficient along `u`. -/
theorem tbExtract_smul_left {u u' : Fin 5 → ℂ} (hu : u ≠ 0) (hu' : u' ≠ 0) {mu : ℂ}
    (h : u = mu • u') {z : Fin 5 → ℂ} (hz : ∃ lam : ℂ, z = lam • u) :
    tbExtract u' z = mu * tbExtract u z := by
  obtain ⟨lam, rfl⟩ := hz
  rw [tbExtract_smul u hu lam, h, smul_smul, tbExtract_smul u' hu' (lam * mu)]
  ring

/-! ## 5. The gauge family -/

/-- `v ↦ ∑ i, v.ofLp i • coordVec S f i`, the chart evaluation as a continuous linear map. -/
def tbCoordEvalCLM (S : ChartIdx 4 16) (f : Stiefel 4 16) : Amb 4 →L[ℝ] Amb 20 :=
  ∑ i : Fin 4, (((ContinuousLinearMap.proj (φ := fun _ : Fin 4 => ℝ) i) :
      (Fin 4 → ℝ) →L[ℝ] ℝ).comp (tbOfLp 4)).smulRight (coordVec S f i)

theorem tbCoordEvalCLM_apply (S : ChartIdx 4 16) (f : Stiefel 4 16) (v : Amb 4) :
    tbCoordEvalCLM S f v = coordEval S f v := by
  simp only [tbCoordEvalCLM, ContinuousLinearMap.sum_apply, coordEval,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, tbOfLp_apply, smul_eq_mul]

/-- **The plane vector of the `S`-coordinates `c`**, read through the chart frame of `uVec i x`
(with the orientation gauge applied): this is `evalChartO S ⟨tbMap x, _⟩ c` whenever the frame is a
frame of `tbMap x` in the chart `S`. -/
def tbEW (S : ChartIdx 4 16) (i : Fin 5) (x : CP 4) : Amb 4 →L[ℝ] Amb 20 :=
  ContinuousLinearMap.comp (tbCoordEvalCLM S (tbCF i x)) (matLin (orientMat S (tbMap x)))

theorem tbEW_apply (S : ChartIdx 4 16) (i : Fin 5) (x : CP 4) (c : Amb 4) :
    tbEW S i x c = coordEval S (tbCF i x) (matLin (orientMat S (tbMap x)) c) := by
  rw [tbEW, ContinuousLinearMap.comp_apply, tbCoordEvalCLM_apply]

/-- The `ℂ⁵`-coordinates of the first block of the plane vector with `S`-coordinates `c`. -/
def tbVecL (S : ChartIdx 4 16) (i : Fin 5) (x : CP 4) : Amb 4 →L[ℝ] (Fin 5 → ℂ) :=
  ContinuousLinearMap.comp tbcOfLpCLM (ContinuousLinearMap.comp tbUnL (tbEW S i x))

theorem tbVecL_apply (S : ChartIdx 4 16) (i : Fin 5) (x : CP 4) (c : Amb 4) :
    tbVecL S i x c = tbcOfLpCLM (tbUnL (tbEW S i x c)) := rfl

/-- The `ℂ⁵`-coordinates of the second block of the plane vector with `S`-coordinates `c`. -/
def tbVecR (S : ChartIdx 4 16) (j : Fin 5) (x : CP 4) : Amb 4 →L[ℝ] (Fin 5 → ℂ) :=
  ContinuousLinearMap.comp tbcOfLpCLM (ContinuousLinearMap.comp tbUnR (tbEW S j x))

theorem tbVecR_apply (S : ChartIdx 4 16) (j : Fin 5) (x : CP 4) (c : Amb 4) :
    tbVecR S j x c = tbcOfLpCLM (tbUnR (tbEW S j x c)) := rfl

/-- **The chart-`i` coefficient of the first block**, realified. -/
def tbCoefL (S : ChartIdx 4 16) (i : Fin 5) (x : CP 4) : Amb 4 →L[ℝ] Amb 2 :=
  ContinuousLinearMap.comp (ContinuousLinearMap.comp tbCof (tbExtract (Work.Gen.uVec i x)))
    (tbVecL S i x)

theorem tbCoefL_apply (S : ChartIdx 4 16) (i : Fin 5) (x : CP 4) (c : Amb 4) :
    tbCoefL S i x c = tbCof (tbExtract (Work.Gen.uVec i x) (tbVecL S i x c)) := rfl

/-- **The chart-`j` coefficient of the second block**, realified. -/
def tbCoefR (S : ChartIdx 4 16) (j : Fin 5) (x : CP 4) : Amb 4 →L[ℝ] Amb 2 :=
  ContinuousLinearMap.comp (ContinuousLinearMap.comp tbCof (tbExtract (Work.Gen.uVec j x)))
    (tbVecR S j x)

theorem tbCoefR_apply (S : ChartIdx 4 16) (j : Fin 5) (x : CP 4) (c : Amb 4) :
    tbCoefR S j x c = tbCof (tbExtract (Work.Gen.uVec j x) (tbVecR S j x c)) := rfl

/-- The pairing `c ↦ (f c, g c)`, as a continuous linear map. -/
def tbPairUp (f g : Amb 4 →L[ℝ] Amb 2) : Amb 4 →L[ℝ] (Amb 2 × Amb 2) :=
  LinearMap.toContinuousLinearMap ((f : Amb 4 →ₗ[ℝ] Amb 2).prod (g : Amb 4 →ₗ[ℝ] Amb 2))

theorem tbPairUp_apply (f g : Amb 4 →L[ℝ] Amb 2) (c : Amb 4) :
    tbPairUp f g c = (f c, g c) := by
  rw [tbPairUp]
  rfl

/-- **The gauge family `Φ`**: the `S`-coordinates of a plane vector of `tbMap x` are sent to the two
complex coefficients of its blocks along `uVec i x` and `uVec j x`, realified. -/
def tbPhi (S : ChartIdx 4 16) (t : Fin 5 × Fin 5) (x : CP 4) : Amb 4 →L[ℝ] Amb 4 :=
  ContinuousLinearMap.comp
    (Work.Whitney.sumFibreR 2 2 : (Amb 2 × Amb 2) →L[ℝ] EuclideanSpace ℝ (Fin (2 + 2)))
    (tbPairUp (tbCoefL S t.1 x) (tbCoefR S t.2 x))

theorem tbPhi_apply (S : ChartIdx 4 16) (t : Fin 5 × Fin 5) (x : CP 4) (c : Amb 4) :
    tbPhi S t x c = (Work.Whitney.sumFibreR 2 2)
      (tbCoefL S t.1 x c, tbCoefR S t.2 x c) := by
  rw [tbPhi, ContinuousLinearMap.comp_apply, tbPairUp_apply]
  rfl

/-! ## 6. The inverse gauge -/

/-- The plane vector whose first block is `(tbZExp d) • uVec i x`: the `i`-th half of the
reconstruction of a plane vector from its two block coefficients. -/
def tbGeoHalfCore (i : Fin 5) (x : CP 4) : Amb 2 →L[ℝ] Amb 10 :=
  ContinuousLinearMap.comp tbReal
    (ContinuousLinearMap.smulRight tbZExp (tbOfLpC (Work.Gen.uVec i x)))

theorem tbGeoHalfCore_apply (i : Fin 5) (x : CP 4) (d : Amb 2) :
    tbGeoHalfCore i x d = tbReal (tbOfLpC ((tbZExp d) • Work.Gen.uVec i x)) := by
  rw [tbGeoHalfCore, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ← tbOfLpC_smul]

/-- The first block of the reconstructed plane vector. -/
def tbGeoHalfL (i : Fin 5) (x : CP 4) : Amb 2 →L[ℝ] Amb 20 :=
  (tbBlkL : Amb 10 →L[ℝ] Amb 20).comp (tbGeoHalfCore i x)

theorem tbGeoHalfL_apply (i : Fin 5) (x : CP 4) (d : Amb 2) :
    tbGeoHalfL i x d = tbBlkL (tbReal (tbOfLpC ((tbZExp d) • Work.Gen.uVec i x))) := by
  rw [tbGeoHalfL, ContinuousLinearMap.comp_apply, tbGeoHalfCore_apply]

/-- The second block of the reconstructed plane vector. -/
def tbGeoHalfR (i : Fin 5) (x : CP 4) : Amb 2 →L[ℝ] Amb 20 :=
  (tbBlkR : Amb 10 →L[ℝ] Amb 20).comp (tbGeoHalfCore i x)

theorem tbGeoHalfR_apply (i : Fin 5) (x : CP 4) (d : Amb 2) :
    tbGeoHalfR i x d = tbBlkR (tbReal (tbOfLpC ((tbZExp d) • Work.Gen.uVec i x))) := by
  rw [tbGeoHalfR, ContinuousLinearMap.comp_apply, tbGeoHalfCore_apply]

/-- **The plane vector with the two block coefficients `d₁`, `d₂`**: its `i`-block is the
realification of `(tbZExp d₁) • uVec i x`. -/
def tbGeo (t : Fin 5 × Fin 5) (x : CP 4) : Amb 4 →L[ℝ] Amb 20 :=
  (tbGeoHalfL t.1 x).comp ((ContinuousLinearMap.fst ℝ (Amb 2) (Amb 2)).comp
      ((Work.Whitney.sumFibreR 2 2).symm : EuclideanSpace ℝ (Fin (2 + 2)) →L[ℝ]
        (Amb 2 × Amb 2)))
    + (tbGeoHalfR t.2 x).comp ((ContinuousLinearMap.snd ℝ (Amb 2) (Amb 2)).comp
      ((Work.Whitney.sumFibreR 2 2).symm : EuclideanSpace ℝ (Fin (2 + 2)) →L[ℝ]
        (Amb 2 × Amb 2)))

theorem tbGeo_apply_aux (t : Fin 5 × Fin 5) (x : CP 4) (d : Amb 4) :
    tbGeo t x d = tbGeoHalfL t.1 x (((Work.Whitney.sumFibreR 2 2).symm d).1)
      + tbGeoHalfR t.2 x (((Work.Whitney.sumFibreR 2 2).symm d).2) := rfl

theorem tbGeo_apply (t : Fin 5 × Fin 5) (x : CP 4) (d : Amb 4) :
    tbGeo t x d = tbBlkL (tbReal (tbOfLpC ((tbZExp (((Work.Whitney.sumFibreR 2 2).symm d).1))
        • Work.Gen.uVec t.1 x)))
      + tbBlkR (tbReal (tbOfLpC ((tbZExp (((Work.Whitney.sumFibreR 2 2).symm d).2))
        • Work.Gen.uVec t.2 x))) := by
  rw [tbGeo_apply_aux, tbGeoHalfL_apply, tbGeoHalfR_apply]

/-- The `S`-coordinates of a plane vector of `tbMap x`, as a continuous linear map. -/
def tbToECoordAtCLM (S : ChartIdx 4 16) (P : OG 4 16) : Amb 20 →L[ℝ] Amb 4 :=
  ContinuousLinearMap.comp (matLin (orientMat S P))
    (ContinuousLinearMap.comp (tbToLp 4)
      (ContinuousLinearMap.comp
        (((coordProj S : (Fin (4 + 16) → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)).toContinuousLinearMap :
            (Fin (4 + 16) → ℝ) →L[ℝ] (Fin 4 → ℝ))) (tbOfLp 20)))

theorem tbToECoordAtCLM_apply (S : ChartIdx 4 16) (P : OG 4 16) (w : Amb 20) :
    tbToECoordAtCLM S P w = toECoordAt S P w := by
  rw [tbToECoordAtCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, toECoordAt, tbToLp_apply, tbOfLp_apply]
  rfl

/-- **The inverse gauge `Φ⁻¹`**: rebuild the plane vector of `tbMap x` from the two block
coefficients and read its `S`-coordinates. -/
def tbPhiInv (S : ChartIdx 4 16) (t : Fin 5 × Fin 5) (x : CP 4) : Amb 4 →L[ℝ] Amb 4 :=
  ContinuousLinearMap.comp (tbToECoordAtCLM S (tbMap x)) (tbGeo t x)

theorem tbPhiInv_apply (S : ChartIdx 4 16) (t : Fin 5 × Fin 5) (x : CP 4) (d : Amb 4) :
    tbPhiInv S t x d = toECoordAt S (tbMap x) (tbGeo t x d) := by
  rw [tbPhiInv, ContinuousLinearMap.comp_apply, tbToECoordAtCLM_apply]

end

end Work.ThomBordism.Grassmann.TBG
