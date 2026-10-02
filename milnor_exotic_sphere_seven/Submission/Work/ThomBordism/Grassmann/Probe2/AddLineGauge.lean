import Mathlib
import Submission.Work.ThomBordism.Grassmann.Probe2.AddLineDefs
import Submission.Work.ThomBordism.Grassmann.InclGauge
import Submission.Work.Gen.EulerToolkit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

/-!
# The gauge identifying `Ω^*γ_{k+1,m}` with `γ_{k,m} ⊕ ε`

For the "add a line" map `Ω : OG k m → OG (k+1) m` of
`Submission/Work/ThomBordism/Grassmann/AddLineDefs.lean` this module builds the bundle isomorphism
between the pullback `Ω^*γ_{k+1,m}` and `sumEpsR ι₀ γ_{k,m}` (= `γ_{k,m} ⊕ ε¹` in the
`sumEpsR`-presentation).

The gauge is the geometric identification of the two trivialisations: the chart `i` of the big
Grassmannian corresponds to the chart `dnChart i` of `OG k m` (obtained by dropping the last
coordinate, possible exactly when `Ω b ∈ baseSet i`), the two enumerations differ by the permutation
`alPerm`, and the frame computation `frameMatrix_alFrame` shows that the transition functions are
conjugated by

`T i b = matLin (blockMat (orientMat (dnChart i) b) * ((alQ i h)⁻¹ * orientMat i (Ω b)))`.

The conjugation identity `alT_comp_coordChangeO` is its frame-theoretic content; all six hypotheses
of `Work.Thom.nonempty_bundleIso_of_gauge` then follow formally.
-/

namespace Work.ThomBordism.Grassmann.Probe2

open scoped Topology
open Work.TangentClasses

noncomputable section

variable {k m : ℕ} {ι₀ : Type} [Inhabited ι₀]

/-- A chosen index of the trivial summand's cover. -/
abbrev alUnit (ι₀ : Type) [Inhabited ι₀] : ι₀ := default

/-- The pullback of the tautological bundle along `Ω`. -/
abbrev alP (k m : ℕ) : RealBundle (OG k m) (Amb (k + 1)) (ChartIdx (k + 1) m) :=
  Work.Thom.bundleComap (tautologicalBundle (k + 1) m) (alOmegaCM k m)

/-- The target `γ_{k,m} ⊕ ε¹` in the `sumEpsR`-presentation. -/
abbrev alW (k m : ℕ) (ι₀ : Type) [Inhabited ι₀] :
    RealBundle (OG k m) (Amb (k + 1)) (ChartIdx k m × ι₀) :=
  Work.Thom.sumEpsR ι₀ (tautologicalBundle k m)

@[simp] theorem alP_baseSet (i : ChartIdx (k + 1) m) :
    (alP k m).baseSet i = (alOmega k m) ⁻¹' baseSet i :=
  Work.Thom.bundleComap_baseSet _ _ i

theorem mem_alP_baseSet {i : ChartIdx (k + 1) m} {b : OG k m} (hb : b ∈ (alP k m).baseSet i) :
    alOmega k m b ∈ baseSet i := hb

theorem mem_alP_baseSet_of_mem {i : ChartIdx (k + 1) m} {b : OG k m}
    (hb : alOmega k m b ∈ baseSet i) : b ∈ (alP k m).baseSet i := hb

theorem nonempty_chartIdx' (k m : ℕ) : Nonempty (ChartIdx k m) :=
  ⟨⟨(Finset.univ : Finset (Fin k)).map (Fin.castLEEmb (Nat.le_add_right k m)), by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]⟩⟩

@[simp] theorem alW_baseSet (u : ChartIdx k m × ι₀) :
    (alW k m ι₀).baseSet u = baseSet u.1 := by
  show (Work.Thom.sumEpsR ι₀ (tautologicalBundle k m)).baseSet u = baseSet u.1
  rw [Work.Thom.sumEpsR_baseSet, Work.Thom.bundleSum_baseSet]
  exact Set.inter_univ _

/-! ## The corresponding chart and permutation, made total -/

/-- The chart of `OG k m` corresponding to a chart of `OG (k+1) m` (junk value when the chart does
not contain the last coordinate, in which case the pullback's chart is empty). -/
def dnChart (i : ChartIdx (k + 1) m) : ChartIdx k m :=
  if h : alLast k m ∈ i.1 then downChart i h else Classical.choice (nonempty_chartIdx' k m)

/-- The permutation matrix of `alPerm`, made total. -/
def dnQ (i : ChartIdx (k + 1) m) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  if h : alLast k m ∈ i.1 then alQ i h else 1

/-- The inverse permutation matrix. -/
def dnQinv (i : ChartIdx (k + 1) m) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  if h : alLast k m ∈ i.1 then (alQ i h)⁻¹ else 1

theorem dnChart_eq (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) :
    dnChart i = downChart i h := dif_pos h

theorem dnQ_eq (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) : dnQ i = alQ i h := dif_pos h

theorem dnQinv_eq (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) :
    dnQinv i = (alQ i h)⁻¹ := dif_pos h

theorem dnQ_mul_dnQinv (i : ChartIdx (k + 1) m) : dnQ i * dnQinv i = 1 := by
  by_cases h : alLast k m ∈ i.1
  · rw [dnQ_eq i h, dnQinv_eq i h]
    exact Matrix.mul_nonsing_inv (alQ i h) (isUnit_iff_ne_zero.mpr (alQ_det_ne_zero i h))
  · rw [dnQ, dif_neg h, dnQinv, dif_neg h, Matrix.one_mul]

theorem dnQinv_mul_dnQ (i : ChartIdx (k + 1) m) : dnQinv i * dnQ i = 1 := by
  by_cases h : alLast k m ∈ i.1
  · rw [dnQ_eq i h, dnQinv_eq i h]
    exact Matrix.nonsing_inv_mul (alQ i h) (isUnit_iff_ne_zero.mpr (alQ_det_ne_zero i h))
  · rw [dnQ, dif_neg h, dnQinv, dif_neg h, Matrix.one_mul]

theorem dnQ_det_ne_zero (i : ChartIdx (k + 1) m) : (dnQ i).det ≠ 0 := by
  by_cases h : alLast k m ∈ i.1
  · rw [dnQ_eq i h]; exact alQ_det_ne_zero i h
  · rw [dnQ, dif_neg h, Matrix.det_one]; norm_num

/-! ## The inner factor of the gauge -/

/-- The matrix of the inner factor of the gauge. -/
def alTmat (i : ChartIdx (k + 1) m) (b : OG k m) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  blockMat (k + 1) (orientMat (dnChart i) b) * (dnQinv i * orientMat i (alOmega k m b))

/-- The matrix of the inverse inner factor. -/
def alTinvmat (i : ChartIdx (k + 1) m) (b : OG k m) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  orientMat i (alOmega k m b) * (dnQ i * blockMat (k + 1) (orientMat (dnChart i) b))

/-- The inner factor of the gauge. -/
def alT (i : ChartIdx (k + 1) m) (b : OG k m) : Amb (k + 1) →L[ℝ] Amb (k + 1) :=
  matLin (alTmat i b)

/-- The inverse of the inner factor of the gauge. -/
def alTinv (i : ChartIdx (k + 1) m) (b : OG k m) : Amb (k + 1) →L[ℝ] Amb (k + 1) :=
  matLin (alTinvmat i b)

theorem alTinv_comp_alT (i : ChartIdx (k + 1) m) (b : OG k m)
    (h1 : alOmega k m b ∈ baseSet i) (h2 : b ∈ baseSet (dnChart i)) :
    (alTinv i b).comp (alT i b) = 1 := by
  have hD : orientMat i (alOmega k m b) * orientMat i (alOmega k m b) = 1 :=
    orientMat_mul_self (alOmega k m b) h1
  have hDd : orientMat (dnChart i) b * orientMat (dnChart i) b = 1 :=
    orientMat_mul_self b h2
  have hDdB : blockMat (k + 1) (orientMat (dnChart i) b)
      * blockMat (k + 1) (orientMat (dnChart i) b) = 1 := by
    rw [← blockMat_mul, hDd, blockMat_one]
  have hQ : dnQ i * dnQinv i = 1 := dnQ_mul_dnQinv i
  rw [alT, alTinv, ← matLin_mul,
    show alTinvmat i b * alTmat i b = 1 from by
      simp only [alTinvmat, alTmat]
      calc (orientMat i (alOmega k m b)
              * (dnQ i * blockMat (k + 1) (orientMat (dnChart i) b)))
            * (blockMat (k + 1) (orientMat (dnChart i) b)
              * (dnQinv i * orientMat i (alOmega k m b)))
          = orientMat i (alOmega k m b)
              * (dnQ i * ((blockMat (k + 1) (orientMat (dnChart i) b)
                * blockMat (k + 1) (orientMat (dnChart i) b))
                * (dnQinv i * orientMat i (alOmega k m b)))) := by noncomm_ring
        _ = orientMat i (alOmega k m b)
              * (dnQ i * ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
                * (dnQinv i * orientMat i (alOmega k m b)))) := by rw [hDdB]
        _ = orientMat i (alOmega k m b) * (dnQ i * (dnQinv i * orientMat i (alOmega k m b))) := by
              rw [Matrix.one_mul]
        _ = orientMat i (alOmega k m b)
              * ((dnQ i * dnQinv i) * orientMat i (alOmega k m b)) := by noncomm_ring
        _ = orientMat i (alOmega k m b) * (1 * orientMat i (alOmega k m b)) := by rw [hQ]
        _ = orientMat i (alOmega k m b) * orientMat i (alOmega k m b) := by rw [Matrix.one_mul]
        _ = 1 := hD,
    matLin_one]

theorem alT_comp_alTinv (i : ChartIdx (k + 1) m) (b : OG k m)
    (h1 : alOmega k m b ∈ baseSet i) (h2 : b ∈ baseSet (dnChart i)) :
    (alT i b).comp (alTinv i b) = 1 := by
  have hD : orientMat i (alOmega k m b) * orientMat i (alOmega k m b) = 1 :=
    orientMat_mul_self (alOmega k m b) h1
  have hDd : orientMat (dnChart i) b * orientMat (dnChart i) b = 1 :=
    orientMat_mul_self b h2
  have hDdB : blockMat (k + 1) (orientMat (dnChart i) b)
      * blockMat (k + 1) (orientMat (dnChart i) b) = 1 := by
    rw [← blockMat_mul, hDd, blockMat_one]
  have hQ : dnQinv i * dnQ i = 1 := dnQinv_mul_dnQ i
  rw [alT, alTinv, ← matLin_mul,
    show alTmat i b * alTinvmat i b = 1 from by
      simp only [alTinvmat, alTmat]
      calc (blockMat (k + 1) (orientMat (dnChart i) b)
              * (dnQinv i * orientMat i (alOmega k m b)))
            * (orientMat i (alOmega k m b)
              * (dnQ i * blockMat (k + 1) (orientMat (dnChart i) b)))
          = blockMat (k + 1) (orientMat (dnChart i) b)
              * (dnQinv i * ((orientMat i (alOmega k m b) * orientMat i (alOmega k m b))
                * (dnQ i * blockMat (k + 1) (orientMat (dnChart i) b)))) := by noncomm_ring
        _ = blockMat (k + 1) (orientMat (dnChart i) b)
              * (dnQinv i * ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
                * (dnQ i * blockMat (k + 1) (orientMat (dnChart i) b)))) := by rw [hD]
        _ = blockMat (k + 1) (orientMat (dnChart i) b)
              * (dnQinv i * (dnQ i * blockMat (k + 1) (orientMat (dnChart i) b))) := by
              rw [Matrix.one_mul]
        _ = blockMat (k + 1) (orientMat (dnChart i) b)
              * ((dnQinv i * dnQ i) * blockMat (k + 1) (orientMat (dnChart i) b)) := by
              noncomm_ring
        _ = blockMat (k + 1) (orientMat (dnChart i) b)
              * (1 * blockMat (k + 1) (orientMat (dnChart i) b)) := by rw [hQ]
        _ = blockMat (k + 1) (orientMat (dnChart i) b)
              * blockMat (k + 1) (orientMat (dnChart i) b) := by rw [Matrix.one_mul]
        _ = 1 := hDdB,
    matLin_one]

/-! ## The conjugation identity -/

theorem alT_apply (i : ChartIdx (k + 1) m) (b : OG k m) :
    alT i b = (matLin (blockMat (k + 1) (orientMat (dnChart i) b))).comp
      ((matLin (dnQinv i)).comp (matLin (orientMat i (alOmega k m b)))) := by
  rw [alT, alTmat, matLin_mul, matLin_mul]

theorem alTinv_apply (i : ChartIdx (k + 1) m) (b : OG k m) :
    alTinv i b = (matLin (orientMat i (alOmega k m b))).comp
      ((matLin (dnQ i)).comp (matLin (blockMat (k + 1) (orientMat (dnChart i) b)))) := by
  rw [alTinv, alTinvmat, matLin_mul, matLin_mul]

/-- The transitions of the `sumEpsR`-presentation of `Z ⊕ ε`: the `rhoR`-conjugate of the
block diagonal `T × 1`. -/
theorem alP_coordChange (i i' : ChartIdx (k + 1) m) (b : OG k m) :
    (alP k m).coordChange i i' b = coordChangeO i i' (alOmega k m b) := by
  show (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) (alOmegaCM k m)).coordChange i i' b = _
  rw [Work.Thom.bundleComap_coordChange]
  rfl

theorem alOmegaMk_eq (f : Stiefel k m) :
    alOmegaMk k m f = Quotient.mk'' (alFrameStiefel k m f) := rfl

theorem sumEpsR_coordChange_eq (S T : ChartIdx k m) (i₀ i₀' : ι₀) (b : OG k m) :
    (alW k m ι₀).coordChange (S, i₀) (T, i₀') b
      = ((Work.Thom.rhoR k : (Amb k × Amb 1) →L[ℝ] Amb (k + 1)).comp
          (((coordChangeO S T b).prodMap (ContinuousLinearMap.id ℝ (Amb 1))).comp
            ((Work.Thom.rhoR k).symm : Amb (k + 1) →L[ℝ] (Amb k × Amb 1)))) := by
  rw [Work.Thom.sumEpsR_coordChange, Work.Thom.bundleSum_coordChange]
  rfl

/-- **The conjugation identity**: the inner factor of the gauge intertwines the transition functions
of the pulled-back big bundle with those of `γ_{k,m} ⊕ ε¹`.  This is the frame computation
`frameMatrix_alFrame` transported to the transition functions. -/
theorem alT_comp_comap (i i' : ChartIdx (k + 1) m) (b : OG k m)
    (hi : alOmega k m b ∈ baseSet i) (hi' : alOmega k m b ∈ baseSet i') :
    (alT i b).comp ((alP k m).coordChange i' i b)
      = ((alW k m ι₀).coordChange (dnChart i', alUnit ι₀) (dnChart i, alUnit ι₀) b).comp
          (alT i' b) := by
  obtain ⟨f, rfl⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = b := Quotient.exists_rep b
  have hi1 := hi; rw [alOmega_mk] at hi1
  have hi1' := hi'; rw [alOmega_mk] at hi1'
  have hli : alLast k m ∈ i.1 := not_mem_last_of_mem_alOmega i hi
  have hli' : alLast k m ∈ i'.1 := not_mem_last_of_mem_alOmega i' hi'
  have hbi : Quotient.mk'' f ∈ baseSet (downChart i hli) :=
    mem_baseSet_downChart_of_mem_alOmega i hli hi
  have hbi' : Quotient.mk'' f ∈ baseSet (downChart i' hli') :=
    mem_baseSet_downChart_of_mem_alOmega i' hli' hi'
  have hci : alFrameStiefel k m f ∈ chartSet i := (mem_baseSet_iff i _).mp hi1
  have hci' : alFrameStiefel k m f ∈ chartSet i' := (mem_baseSet_iff i' _).mp hi1'
  have hfi : f ∈ chartSet (downChart i hli) := (mem_baseSet_iff (downChart i hli) f).mp hbi
  have hfi' : f ∈ chartSet (downChart i' hli') := (mem_baseSet_iff (downChart i' hli') f).mp hbi'
  have hdeti' : (frameMatrix (downChart i' hli') f.1).det ≠ 0 := hfi'
  simp only [alT, alTmat]
  rw [dnChart_eq i hli, dnChart_eq i' hli', alP_coordChange i' i (Quotient.mk'' f),
    alOmega_mk, alOmegaMk_eq,
    sumEpsR_coordChange_eq (downChart i' hli') (downChart i hli) default default (Quotient.mk'' f),
    coordChangeO_mk i' i (alFrameStiefel k m f) hci',
    coordChangeO_mk (downChart i' hli') (downChart i hli) f hfi',
    ← matLin_blockMat (orientMat (downChart i hli) (Quotient.mk'' f)
      * ((frameMatrix (downChart i hli) f.1 * (frameMatrix (downChart i' hli') f.1)⁻¹)
        * orientMat (downChart i' hli') (Quotient.mk'' f))),
    ← matLin_mul, ← matLin_mul]
  congr 1
  -- the matrix identity
  set Di := orientMat i (Quotient.mk'' (alFrameStiefel k m f)) with hDi_def
  set Di' := orientMat i' (Quotient.mk'' (alFrameStiefel k m f)) with hDi'_def
  set Ddi := orientMat (downChart i hli) (Quotient.mk'' f) with hDdi_def
  set Ddi' := orientMat (downChart i' hli') (Quotient.mk'' f) with hDdi'_def
  have hDi2 : Di * Di = 1 := by
    rw [hDi_def]; exact orientMat_mul_self _ hi
  have hBDdi'2 : blockMat (k + 1) Ddi' * blockMat (k + 1) Ddi' = 1 := by
    rw [← blockMat_mul, hDdi'_def, orientMat_mul_self _ hbi', blockMat_one]
  have hQinvi : (alQ i hli)⁻¹ * alQ i hli = 1 :=
    Matrix.nonsing_inv_mul (alQ i hli) (isUnit_iff_ne_zero.mpr (alQ_det_ne_zero i hli))
  have hunitQi' : IsUnit (alQ i' hli').det := isUnit_iff_ne_zero.mpr (alQ_det_ne_zero i' hli')
  have hunitBAi' : IsUnit (blockMat (k + 1) (frameMatrix (downChart i' hli') f.1)).det := by
    rw [det_blockMat]; exact isUnit_iff_ne_zero.mpr hdeti'
  rw [dnQinv_eq i hli, dnQinv_eq i' hli',
    frameMatrix_alFrameStiefel_mul i hli f, frameMatrix_alFrameStiefel_mul i' hli' f,
    matrix_mul_inv_eq (alQ i' hli') (blockMat (k + 1) (frameMatrix (downChart i' hli') f.1))
      hunitQi' hunitBAi',
    blockMat_inv_eq (frameMatrix (downChart i' hli') f.1) (isUnit_iff_ne_zero.mpr hdeti')]
  simp only [blockMat_mul]
  -- now the algebra
  set BBdi := blockMat (k + 1) Ddi with hBBdi_def
  set BBdi' := blockMat (k + 1) Ddi' with hBBdi'_def
  set Pi := alQ i hli with hPi_def
  set Pi' := alQ i' hli' with hPi'_def
  set Qi := blockMat (k + 1) (frameMatrix (downChart i hli) f.1) with hQi_def
  set Qi' := blockMat (k + 1) ((frameMatrix (downChart i' hli') f.1)⁻¹) with hQi'_def
  have hL : (BBdi * (Pi⁻¹ * Di)) * (Di * ((Pi * Qi * (Qi' * Pi'⁻¹)) * Di'))
      = BBdi * Qi * Qi' * Pi'⁻¹ * Di' := by
    rw [show (BBdi * (Pi⁻¹ * Di)) * (Di * ((Pi * Qi * (Qi' * Pi'⁻¹)) * Di'))
          = BBdi * (Pi⁻¹ * (Di * Di)) * (Pi * (Qi * (Qi' * Pi'⁻¹))) * Di' from by
        noncomm_ring,
      hDi2, Matrix.mul_one]
    rw [show BBdi * Pi⁻¹ * (Pi * (Qi * (Qi' * Pi'⁻¹))) * Di'
          = BBdi * ((Pi⁻¹ * Pi) * (Qi * (Qi' * Pi'⁻¹))) * Di' from by noncomm_ring,
      hQinvi, Matrix.one_mul]
    rw [show BBdi * (Qi * (Qi' * Pi'⁻¹)) * Di' = BBdi * Qi * Qi' * Pi'⁻¹ * Di' from by
      noncomm_ring]
  have hR : (BBdi * ((Qi * Qi') * BBdi')) * (BBdi' * (Pi'⁻¹ * Di'))
      = BBdi * Qi * Qi' * Pi'⁻¹ * Di' := by
    rw [show (BBdi * ((Qi * Qi') * BBdi')) * (BBdi' * (Pi'⁻¹ * Di'))
          = BBdi * (Qi * Qi') * (BBdi' * (BBdi' * (Pi'⁻¹ * Di'))) from by noncomm_ring]
    rw [show BBdi * (Qi * Qi') * (BBdi' * (BBdi' * (Pi'⁻¹ * Di')))
          = BBdi * (Qi * Qi') * ((BBdi' * BBdi') * (Pi'⁻¹ * Di')) from by noncomm_ring,
      hBDdi'2, Matrix.one_mul]
    rw [show BBdi * (Qi * Qi') * (Pi'⁻¹ * Di') = BBdi * Qi * Qi' * Pi'⁻¹ * Di' from by
      noncomm_ring]
  rw [hL, hR]

/-! ## The gauge family and the six hypotheses -/

/-- The gauge family: the fibrewise isomorphism between the pullback of `γ_{k+1,m}` and
`γ_{k,m} ⊕ ε¹` in the charts `(i, u)`. -/
def alPhi (i : ChartIdx (k + 1) m) (u : ChartIdx k m × ι₀) (b : OG k m) :
    Amb (k + 1) →L[ℝ] Amb (k + 1) :=
  (((alW k m ι₀).coordChange (dnChart i, alUnit ι₀) u b)).comp (alT i b)

/-- Its inverse. -/
def alPhiInv (i : ChartIdx (k + 1) m) (u : ChartIdx k m × ι₀) (b : OG k m) :
    Amb (k + 1) →L[ℝ] Amb (k + 1) :=
  (alTinv i b).comp (((alW k m ι₀).coordChange u (dnChart i, alUnit ι₀) b))

/-! ## Continuity -/

theorem mem_dnChart_of_mem_alP {i : ChartIdx (k + 1) m} {b : OG k m}
    (hb : b ∈ (alP k m).baseSet i) : b ∈ baseSet (dnChart i) := by
  rw [dnChart_eq i (not_mem_last_of_mem_alOmega i hb)]
  exact mem_baseSet_downChart_of_mem_alOmega i _ hb

theorem mem_alW_dnChart {i : ChartIdx (k + 1) m} {b : OG k m} (hb : b ∈ (alP k m).baseSet i) :
    b ∈ (alW k m ι₀).baseSet (dnChart i, alUnit ι₀) := by
  rw [alW_baseSet]
  exact mem_dnChart_of_mem_alP hb

theorem continuousOn_alT (i : ChartIdx (k + 1) m) :
    ContinuousOn (fun b : OG k m => alT i b) ((alP k m).baseSet i) := by
  have hA : ContinuousOn (fun b : OG k m => matLin (blockMat (k + 1) (orientMat (dnChart i) b)))
      ((alP k m).baseSet i) :=
    continuous_matLin.comp_continuousOn ((continuous_blockMat k).comp_continuousOn
      ((continuousOn_orientMat (dnChart i)).mono (fun b hb => mem_dnChart_of_mem_alP hb)))
  have hQ : ContinuousOn (fun _ : OG k m => matLin (dnQinv i)) ((alP k m).baseSet i) :=
    continuousOn_const
  have hB : ContinuousOn (fun b : OG k m => matLin (orientMat i (alOmega k m b)))
      ((alP k m).baseSet i) :=
    continuous_matLin.comp_continuousOn
      ((continuousOn_orientMat i).comp (continuous_alOmega k m).continuousOn
        (fun b hb => hb))
  refine (hA.clm_comp (hQ.clm_comp hB)).congr (fun b hb => ?_)
  rw [alT_apply]

theorem continuousOn_alTinv (i : ChartIdx (k + 1) m) :
    ContinuousOn (fun b : OG k m => alTinv i b) ((alP k m).baseSet i) := by
  have hA : ContinuousOn (fun b : OG k m => matLin (orientMat i (alOmega k m b)))
      ((alP k m).baseSet i) :=
    continuous_matLin.comp_continuousOn
      ((continuousOn_orientMat i).comp (continuous_alOmega k m).continuousOn
        (fun b hb => hb))
  have hQ : ContinuousOn (fun _ : OG k m => matLin (dnQ i)) ((alP k m).baseSet i) :=
    continuousOn_const
  have hB : ContinuousOn (fun b : OG k m => matLin (blockMat (k + 1) (orientMat (dnChart i) b)))
      ((alP k m).baseSet i) :=
    continuous_matLin.comp_continuousOn ((continuous_blockMat k).comp_continuousOn
      ((continuousOn_orientMat (dnChart i)).mono (fun b hb => mem_dnChart_of_mem_alP hb)))
  refine (hA.clm_comp (hQ.clm_comp hB)).congr (fun b hb => ?_)
  rw [alTinv_apply]

theorem continuousOn_alPhi (i : ChartIdx (k + 1) m) (u : ChartIdx k m × ι₀) :
    ContinuousOn (fun b : OG k m => alPhi i u b)
      ((alP k m).baseSet i ∩ (alW k m ι₀).baseSet u) := by
  have h1 : ContinuousOn
      (fun b : OG k m => (alW k m ι₀).coordChange (dnChart i, alUnit ι₀) u b)
      ((alP k m).baseSet i ∩ (alW k m ι₀).baseSet u) :=
    (((alW k m ι₀).continuousOn_coordChange (dnChart i, alUnit ι₀) u)).mono
      (fun b hb => ⟨mem_alW_dnChart (ι₀ := ι₀) hb.1, hb.2⟩)
  have h2 : ContinuousOn (fun b : OG k m => alT i b)
      ((alP k m).baseSet i ∩ (alW k m ι₀).baseSet u) :=
    (continuousOn_alT i).mono Set.inter_subset_left
  refine (h1.clm_comp h2).congr (fun b hb => ?_)
  rw [alPhi]

theorem continuousOn_alPhiInv (i : ChartIdx (k + 1) m) (u : ChartIdx k m × ι₀) :
    ContinuousOn (fun b : OG k m => alPhiInv i u b)
      ((alP k m).baseSet i ∩ (alW k m ι₀).baseSet u) := by
  have h1 : ContinuousOn (fun b : OG k m => alTinv i b)
      ((alP k m).baseSet i ∩ (alW k m ι₀).baseSet u) :=
    (continuousOn_alTinv i).mono Set.inter_subset_left
  have h2 : ContinuousOn
      (fun b : OG k m => (alW k m ι₀).coordChange u (dnChart i, alUnit ι₀) b)
      ((alP k m).baseSet i ∩ (alW k m ι₀).baseSet u) :=
    (((alW k m ι₀).continuousOn_coordChange u (dnChart i, alUnit ι₀))).mono
      (fun b hb => ⟨hb.2, mem_alW_dnChart (ι₀ := ι₀) hb.1⟩)
  refine (h1.clm_comp h2).congr (fun b hb => ?_)
  rw [alPhiInv]

/-! ## The six hypotheses -/

theorem alW_coordChange_mul_self_apply (u u' : ChartIdx k m × ι₀) (b : OG k m)
    (hb : b ∈ (alW k m ι₀).baseSet u ∩ (alW k m ι₀).baseSet u') (v : Amb (k + 1)) :
    ((alW k m ι₀).coordChange u u' b) (((alW k m ι₀).coordChange u' u b) v) = v := by
  rw [(alW k m ι₀).coordChange_comp u' u u' b ⟨⟨hb.2, hb.1⟩, hb.2⟩ v,
    (alW k m ι₀).coordChange_self u' b hb.2 v]

theorem alTinv_comp_alT_apply (i : ChartIdx (k + 1) m) (b : OG k m)
    (h1 : alOmega k m b ∈ baseSet i) (h2 : b ∈ baseSet (dnChart i)) (v : Amb (k + 1)) :
    (alTinv i b) ((alT i b) v) = v := by
  have h := congrArg (fun (L : Amb (k + 1) →L[ℝ] Amb (k + 1)) => L v) (alTinv_comp_alT i b h1 h2)
  rwa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h

theorem alT_comp_alTinv_apply (i : ChartIdx (k + 1) m) (b : OG k m)
    (h1 : alOmega k m b ∈ baseSet i) (h2 : b ∈ baseSet (dnChart i)) (v : Amb (k + 1)) :
    (alT i b) ((alTinv i b) v) = v := by
  have h := congrArg (fun (L : Amb (k + 1) →L[ℝ] Amb (k + 1)) => L v) (alT_comp_alTinv i b h1 h2)
  rwa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h

/-- The conjugation identity for the inverse inner factor (the inverse of `alT_comp_comap`). -/
theorem alTinv_comp_comap (i i' : ChartIdx (k + 1) m) (b : OG k m)
    (hi : alOmega k m b ∈ baseSet i) (hi' : alOmega k m b ∈ baseSet i') :
    ((alP k m).coordChange i i' b).comp (alTinv i b)
      = (alTinv i' b).comp ((alW k m ι₀).coordChange (dnChart i, alUnit ι₀)
          (dnChart i', alUnit ι₀) b) := by
  have hbi : b ∈ baseSet (dnChart i) := mem_dnChart_of_mem_alP hi
  have hbi' : b ∈ baseSet (dnChart i') := mem_dnChart_of_mem_alP hi'
  apply ContinuousLinearMap.ext
  intro v
  have hL : (alT i' b) (((alP k m).coordChange i i' b) ((alTinv i b) v))
      = ((alW k m ι₀).coordChange (dnChart i, alUnit ι₀) (dnChart i', alUnit ι₀) b) v := by
    have h := congrArg (fun (L : Amb (k + 1) →L[ℝ] Amb (k + 1)) => L ((alTinv i b) v))
      (alT_comp_comap (ι₀ := ι₀) i' i b hi' hi)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h
    rw [h, alT_comp_alTinv_apply i b hi hbi v]
  have h2 := congrArg (fun w => (alTinv i' b) w) hL
  rw [alTinv_comp_alT_apply i' b hi' hbi'] at h2
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact h2

theorem alPhi_htgt (i : ChartIdx (k + 1) m) (u u' : ChartIdx k m × ι₀) (b : OG k m)
    (hb1 : b ∈ (alP k m).baseSet i) (hb2 : b ∈ (alW k m ι₀).baseSet u)
    (hb3 : b ∈ (alW k m ι₀).baseSet u') :
    ((alW k m ι₀).coordChange u u' b).comp (alPhi i u b) = alPhi i u' b := by
  have hbi : b ∈ (alW k m ι₀).baseSet (dnChart i, alUnit ι₀) := mem_alW_dnChart (ι₀ := ι₀) hb1
  apply ContinuousLinearMap.ext
  intro v
  simp only [alPhi, ContinuousLinearMap.comp_apply]
  exact (alW k m ι₀).coordChange_comp (dnChart i, alUnit ι₀) u u' b
    ⟨⟨hbi, hb2⟩, hb3⟩ ((alT i b) v)

theorem alPhi_hsrc (i i' : ChartIdx (k + 1) m) (u : ChartIdx k m × ι₀) (b : OG k m)
    (hb1 : b ∈ (alP k m).baseSet i) (hb2 : b ∈ (alP k m).baseSet i')
    (hb3 : b ∈ (alW k m ι₀).baseSet u) :
    (alPhi i u b).comp ((alP k m).coordChange i' i b) = alPhi i' u b := by
  have hi : alOmega k m b ∈ baseSet i := hb1
  have hi' : alOmega k m b ∈ baseSet i' := hb2
  have hbi : b ∈ (alW k m ι₀).baseSet (dnChart i, alUnit ι₀) := mem_alW_dnChart (ι₀ := ι₀) hb1
  have hbi' : b ∈ (alW k m ι₀).baseSet (dnChart i', alUnit ι₀) := mem_alW_dnChart (ι₀ := ι₀) hb2
  apply ContinuousLinearMap.ext
  intro v
  simp only [alPhi, ContinuousLinearMap.comp_apply]
  have hconj := congrArg (fun (L : Amb (k + 1) →L[ℝ] Amb (k + 1)) => L v)
    (alT_comp_comap (ι₀ := ι₀) i i' b hi hi')
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hconj
  rw [hconj]
  exact (alW k m ι₀).coordChange_comp (dnChart i', alUnit ι₀) (dnChart i, alUnit ι₀) u b
    ⟨⟨hbi', hbi⟩, hb3⟩ ((alT i' b) v)

theorem alPhi_htgtinv (i : ChartIdx (k + 1) m) (u u' : ChartIdx k m × ι₀) (b : OG k m)
    (hb1 : b ∈ (alP k m).baseSet i) (hb2 : b ∈ (alW k m ι₀).baseSet u)
    (hb3 : b ∈ (alW k m ι₀).baseSet u') :
    (alPhiInv i u b).comp ((alW k m ι₀).coordChange u' u b) = alPhiInv i u' b := by
  have hbi : b ∈ (alW k m ι₀).baseSet (dnChart i, alUnit ι₀) := mem_alW_dnChart (ι₀ := ι₀) hb1
  apply ContinuousLinearMap.ext
  intro v
  simp only [alPhiInv, ContinuousLinearMap.comp_apply]
  congr 1
  exact (alW k m ι₀).coordChange_comp u' u (dnChart i, alUnit ι₀) b
    ⟨⟨hb3, hb2⟩, hbi⟩ v

theorem alPhi_hsrcinv (i i' : ChartIdx (k + 1) m) (u : ChartIdx k m × ι₀) (b : OG k m)
    (hb1 : b ∈ (alP k m).baseSet i) (hb2 : b ∈ (alP k m).baseSet i')
    (hb3 : b ∈ (alW k m ι₀).baseSet u) :
    ((alP k m).coordChange i i' b).comp (alPhiInv i u b) = alPhiInv i' u b := by
  have hi : alOmega k m b ∈ baseSet i := hb1
  have hi' : alOmega k m b ∈ baseSet i' := hb2
  have hbi : b ∈ (alW k m ι₀).baseSet (dnChart i, alUnit ι₀) := mem_alW_dnChart (ι₀ := ι₀) hb1
  have hbi' : b ∈ (alW k m ι₀).baseSet (dnChart i', alUnit ι₀) := mem_alW_dnChart (ι₀ := ι₀) hb2
  apply ContinuousLinearMap.ext
  intro v
  simp only [alPhiInv, ContinuousLinearMap.comp_apply]
  have hconj := congrArg (fun (L : Amb (k + 1) →L[ℝ] Amb (k + 1)) => L
    (((alW k m ι₀).coordChange u (dnChart i, alUnit ι₀) b) v))
    (alTinv_comp_comap (ι₀ := ι₀) i i' b hi hi')
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hconj
  rw [hconj]
  congr 1
  exact (alW k m ι₀).coordChange_comp u (dnChart i, alUnit ι₀) (dnChart i', alUnit ι₀) b
    ⟨⟨hb3, hbi⟩, hbi'⟩ v

theorem alPhi_hleft (i : ChartIdx (k + 1) m) (u : ChartIdx k m × ι₀) (b : OG k m)
    (hb : b ∈ (alP k m).baseSet i ∩ (alW k m ι₀).baseSet u) (x : Amb (k + 1)) :
    alPhiInv i u b (alPhi i u b x) = x := by
  have hi : alOmega k m b ∈ baseSet i := hb.1
  have hbi : b ∈ (alW k m ι₀).baseSet (dnChart i, alUnit ι₀) := mem_alW_dnChart (ι₀ := ι₀) hb.1
  simp only [alPhi, alPhiInv, ContinuousLinearMap.comp_apply]
  rw [alW_coordChange_mul_self_apply u (dnChart i, alUnit ι₀) b ⟨hb.2, hbi⟩]
  exact alTinv_comp_alT_apply i b hi (mem_dnChart_of_mem_alP hb.1) x

theorem alPhi_hright (i : ChartIdx (k + 1) m) (u : ChartIdx k m × ι₀) (b : OG k m)
    (hb : b ∈ (alP k m).baseSet i ∩ (alW k m ι₀).baseSet u) (y : Amb (k + 1)) :
    alPhi i u b (alPhiInv i u b y) = y := by
  have hi : alOmega k m b ∈ baseSet i := hb.1
  have hbi : b ∈ (alW k m ι₀).baseSet (dnChart i, alUnit ι₀) := mem_alW_dnChart (ι₀ := ι₀) hb.1
  simp only [alPhi, alPhiInv, ContinuousLinearMap.comp_apply]
  rw [alT_comp_alTinv_apply i b hi (mem_dnChart_of_mem_alP hb.1)]
  exact alW_coordChange_mul_self_apply (dnChart i, alUnit ι₀) u b ⟨hbi, hb.2⟩ y

/-! ## The bundle isomorphism -/

theorem addLineBundleIso (k m : ℕ) (ι₀ : Type) [Inhabited ι₀] :
    ∃ φ : C(OG k m, OG (k + 1) m),
      Nonempty (Work.Thom.BundleIso
        (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ)
        (Work.Thom.sumEpsR ι₀ (tautologicalBundle k m))) := by
  refine ⟨alOmegaCM k m, ?_⟩
  refine Work.Thom.nonempty_bundleIso_of_gauge (alP k m) (alW k m ι₀)
    (alPhi (k := k) (m := m) (ι₀ := ι₀)) (alPhiInv (k := k) (m := m) (ι₀ := ι₀))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i u
    exact continuousOn_alPhi i u
  · intro i u
    exact continuousOn_alPhiInv i u
  · intro i u u' b h1 h2 h3
    exact alPhi_htgt i u u' b h1 h2 h3
  · intro i u i' b h1 h2 h3
    exact alPhi_hsrc i i' u b h1 h2 h3
  · intro i u u' b h1 h2 h3
    exact alPhi_htgtinv i u u' b h1 h2 h3
  · intro i u i' b h1 h2 h3
    exact alPhi_hsrcinv i i' u b h1 h2 h3
  · intro i u b x hb
    exact alPhi_hleft i u b hb x
  · intro i u b y hb
    exact alPhi_hright i u b hb y

end

end Work.ThomBordism.Grassmann.Probe2
