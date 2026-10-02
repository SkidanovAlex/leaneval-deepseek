import Submission.Work.ThomBordism.Grassmann.InclDefs
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.Iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-!
# The gauge identifying `φ^*(γ_{k,m+1})` with `γ_{k,m}`

For the stabilisation inclusion `ogIncl : OG k m → OG k (m+1)` (appending a zero coordinate) this
module builds the **bundle isomorphism** between the pullback `φ^*(γ_{k,m+1})` and `γ_{k,m}`.

The gauge is the geometric identification of the two trivialisations: on the chart
`i : ChartIdx k (m+1)` of the big Grassmannian (with `Fin.last (k+m) ∉ i.1`) the corresponding
chart of `OG k m` is `chartDown k m i h`, and the two chart enumerations differ by the permutation
`chartPerm k m i h`.  Hence the fibrewise identification in the charts `(i,t)` is

`Φ i t b = coordChangeO (chartDown i h) t b ∘ matLin (orientMat (chartDown i h) b · (chartQ i h)⁻¹
   · orientMat i (ogIncl b))`,

whose "inner" factor `T i b := matLin D_{i^ρ} ∘ matLin Q_i⁻¹ ∘ matLin D_i` satisfies the
conjugation identity

`T i b ∘ coordChangeO j i (ogIncl b) = coordChangeO (j^ρ) (i^ρ) b ∘ T j b`

(`inclT_comp_coordChangeO`), which is the frame computation `frameMatrix_inclFrame` transported to
the transition functions.  All six hypotheses of `Work.Thom.nonempty_bundleIso_of_gauge` are proved
here.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology
open Work.TangentClasses

noncomputable section

variable {k m : ℕ}

/-! ## A chart of every index type -/

theorem nonempty_chartIdx (k m : ℕ) : Nonempty (ChartIdx k m) :=
  ⟨⟨(Finset.univ : Finset (Fin k)).map (Fin.castLEEmb (Nat.le_add_right k m)), by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]⟩⟩

/-! ## The chart correspondence, made total -/

/-- The chart of `OG k m` corresponding to a chart of `OG k (m+1)` (junk value when the chart
contains the last coordinate, in which case the pullback's chart is empty anyway). -/
def cd (k m : ℕ) (i : ChartIdx k (m + 1)) : ChartIdx k m :=
  if h : Fin.last (k + m) ∉ i.1 then chartDown k m i h
  else Classical.choice (nonempty_chartIdx k m)

/-- The permutation matrix of `chartPerm`, made total. -/
def cdQ (k m : ℕ) (i : ChartIdx k (m + 1)) : Matrix (Fin k) (Fin k) ℝ :=
  if h : Fin.last (k + m) ∉ i.1 then chartQ k m i h else 1

/-- The inverse permutation matrix of `chartPerm`, made total. -/
def cdQinv (k m : ℕ) (i : ChartIdx k (m + 1)) : Matrix (Fin k) (Fin k) ℝ :=
  if h : Fin.last (k + m) ∉ i.1 then chartQinv k m i h else 1

theorem cd_eq (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    cd k m i = chartDown k m i h := dif_pos h

theorem cdQ_eq (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    cdQ k m i = chartQ k m i h := dif_pos h

theorem cdQinv_eq (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    cdQinv k m i = chartQinv k m i h := dif_pos h

theorem cdQ_mul_cdQinv (i : ChartIdx k (m + 1)) : cdQ k m i * cdQinv k m i = 1 := by
  by_cases h : Fin.last (k + m) ∉ i.1
  · rw [cdQ_eq i h, cdQinv_eq i h, chartQ_mul_chartQinv]
  · rw [cdQ, dif_neg h, cdQinv, dif_neg h, Matrix.one_mul]

theorem cdQinv_mul_cdQ (i : ChartIdx k (m + 1)) : cdQinv k m i * cdQ k m i = 1 := by
  by_cases h : Fin.last (k + m) ∉ i.1
  · rw [cdQ_eq i h, cdQinv_eq i h, chartQinv_mul_chartQ]
  · rw [cdQ, dif_neg h, cdQinv, dif_neg h, Matrix.one_mul]

theorem chartQ_det_ne_zero (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    (chartQ k m i h).det ≠ 0 := by
  rw [chartQ, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (chartPerm k m i h)) with h1 | h1
  · rw [h1]; norm_num
  · rw [h1]; norm_num

theorem cdQ_det_ne_zero (i : ChartIdx k (m + 1)) : (cdQ k m i).det ≠ 0 := by
  by_cases h : Fin.last (k + m) ∉ i.1
  · rw [cdQ_eq i h]; exact chartQ_det_ne_zero i h
  · rw [cdQ, dif_neg h, Matrix.det_one]; norm_num

/-! ## The product form of the frame-matrix computation -/

/-- The frame matrix in the big chart, as the permutation matrix times the small frame matrix. -/
theorem frameMatrix_inclFrame_mul (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1)
    (f : Stiefel k m) :
    frameMatrix i (inclFrame k m f).1
      = chartQ k m i h * frameMatrix (chartDown k m i h) f.1 := by
  rw [frameMatrix_inclFrame i h f, chartQ]
  exact (PEquiv.toMatrix_toPEquiv_mul (chartPerm k m i h)
    (frameMatrix (chartDown k m i h) f.1)).symm

/-! ## The transition functions at a frame -/

/-- The transition function `coordChangeO S T` at a point given by a frame, in matrix form. -/
theorem coordChangeO_mk (S T : ChartIdx k m) (f : Stiefel k m) (hf : f ∈ chartSet S) :
    coordChangeO S T (Quotient.mk'' f)
      = matLin (orientMat T (Quotient.mk'' f)
          * ((frameMatrix T f.1 * (frameMatrix S f.1)⁻¹) * orientMat S (Quotient.mk'' f))) := by
  have hcc : coordChange S T (Quotient.mk'' f) = matLin (frameMatrix T f.1 * (frameMatrix S f.1)⁻¹) := by
    rw [coordChange_mk, coordChangeAux, dif_pos (show (frameMatrix S f.1).det ≠ 0 from hf)]
  simp only [coordChangeO]
  rw [hcc, ← matLin_mul, ← matLin_mul, Matrix.mul_assoc]

/-! ## The base sets -/

/-- Membership in the pullback's chart `i` propagates to the corresponding chart of `OG k m`. -/
theorem mem_baseSet_chartDown_of_mem_ogIncl (i : ChartIdx k (m + 1))
    (h : Fin.last (k + m) ∉ i.1) {b : OG k m}
    (hb : ogIncl k m b ∈ baseSet i) :
    b ∈ baseSet (chartDown k m i h) := by
  obtain ⟨f, rfl⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = b := Quotient.exists_rep b
  have hb' : (inclFrame k m f) ∈ chartSet i :=
    (mem_baseSet_iff i (inclFrame k m f)).mp (by
      show ogIncl k m (Quotient.mk'' f) ∈ baseSet i
      exact hb)
  refine (mem_baseSet_iff (chartDown k m i h) f).mpr ?_
  intro hdet
  exact hb' (by rw [frameMatrix_inclFrame_mul i h f, Matrix.det_mul, hdet, mul_zero])

/-- The chart `i` of `OG k (m+1)` meets the image of `ogIncl` exactly where the corresponding
chart of `OG k m` does. -/
theorem mem_baseSet_chartDown_iff_ogIncl (i : ChartIdx k (m + 1))
    (h : Fin.last (k + m) ∉ i.1) {b : OG k m} :
    ogIncl k m b ∈ baseSet i ↔ b ∈ baseSet (chartDown k m i h) := by
  refine ⟨fun hb => mem_baseSet_chartDown_of_mem_ogIncl i h hb, fun hb => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = b := Quotient.exists_rep b
  have hb' : (frameMatrix (chartDown k m i h) f.1).det ≠ 0 :=
    (mem_baseSet_iff (chartDown k m i h) f).mp hb
  refine (mem_baseSet_iff i (inclFrame k m f)).mpr ?_
  intro hdet
  exact hb' (by
    have h2 : (frameMatrix i (inclFrame k m f).1).det
        = (chartQ k m i h).det * (frameMatrix (chartDown k m i h) f.1).det := by
      rw [frameMatrix_inclFrame_mul i h f, Matrix.det_mul]
    rw [h2] at hdet
    rcases mul_eq_zero.mp hdet with h0 | h0
    · exact absurd h0 (chartQ_det_ne_zero i h)
    · exact h0)

/-- The chart `i` of the pullback has empty base set when `i` contains the last coordinate. -/
theorem mem_ogIncl_baseSet_eq_empty (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∈ i.1) :
    ∀ b : OG k m, ogIncl k m b ∉ baseSet i := by
  intro b hb
  obtain ⟨f, rfl⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = b := Quotient.exists_rep b
  have hb' : (frameMatrix i (inclFrame k m f).1).det ≠ 0 :=
    (mem_baseSet_iff i (inclFrame k m f)).mp (by
      show ogIncl k m (Quotient.mk'' f) ∈ baseSet i
      exact hb)
  refine hb' (Matrix.det_eq_zero_of_row_eq_zero
    ((i.1.equivFinOfCardEq i.2) ⟨Fin.last (k + m), h⟩) (fun mm => ?_))
  have hjj : chartVal k m i ((i.1.equivFinOfCardEq i.2) ⟨Fin.last (k + m), h⟩)
      = Fin.last (k + m) := by
    rw [chartVal, Equiv.symm_apply_apply]
  rw [frameMatrix_apply,
    show (((i.1.equivFinOfCardEq i.2).symm
        ((i.1.equivFinOfCardEq i.2) ⟨Fin.last (k + m), h⟩)) : Fin (k + m + 1))
      = chartVal k m i ((i.1.equivFinOfCardEq i.2) ⟨Fin.last (k + m), h⟩) from rfl,
    hjj]
  show ((inclFrame k m f).1 mm).ofLp (Fin.last (k + m)) = 0
  rw [inclFrame_val]
  exact snoc0_ofLp_last (k + m) (f.1 mm)

/-- The last coordinate is excluded from every chart that meets the image of `ogIncl`. -/
theorem not_mem_last_of_mem_ogIncl (i : ChartIdx k (m + 1)) {b : OG k m}
    (hb : ogIncl k m b ∈ baseSet i) :
    Fin.last (k + m) ∉ i.1 :=
  fun h => mem_ogIncl_baseSet_eq_empty i h b hb

/-- The pullback's chart `i` is the chart `cd i` of `OG k m`. -/
theorem mem_baseSet_cd_of_mem_ogIncl (i : ChartIdx k (m + 1)) {b : OG k m}
    (hb : ogIncl k m b ∈ baseSet i) :
    b ∈ baseSet (cd k m i) := by
  have h := not_mem_last_of_mem_ogIncl i hb
  rw [cd_eq i h]
  exact mem_baseSet_chartDown_of_mem_ogIncl i h hb

theorem comap_baseSet_eq_chartDown (i : ChartIdx k (m + 1)) (h : Fin.last (k + m) ∉ i.1) :
    (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i
      = baseSet (chartDown k m i h) := by
  ext b
  rw [Work.Thom.bundleComap_baseSet]
  change ogIncl k m b ∈ baseSet i ↔ b ∈ baseSet (chartDown k m i h)
  exact mem_baseSet_chartDown_iff_ogIncl i h

theorem comap_baseSet_eq_empty_of_mem_last (i : ChartIdx k (m + 1))
    (h : Fin.last (k + m) ∈ i.1) :
    (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr (fun b hb => ?_)
  rw [Work.Thom.bundleComap_baseSet] at hb
  change ogIncl k m b ∈ baseSet i at hb
  exact mem_ogIncl_baseSet_eq_empty i h b hb


/-! ## The inverse of a matrix product -/

theorem matrix_mul_inv_eq (A B : Matrix (Fin k) (Fin k) ℝ) (hA : IsUnit A.det)
    (hB : IsUnit B.det) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  calc B⁻¹ * A⁻¹ * (A * B) = B⁻¹ * (A⁻¹ * A) * B := by noncomm_ring
    _ = 1 := by rw [Matrix.nonsing_inv_mul A hA, Matrix.mul_one, Matrix.nonsing_inv_mul B hB]

/-! ## The transition functions at a frame, as continuous linear maps -/

theorem coordChangeO_compCLM (a b c : ChartIdx k m) (x : OG k m)
    (hx : x ∈ baseSet a ∩ baseSet b ∩ baseSet c) :
    (coordChangeO b c x).comp (coordChangeO a b x) = coordChangeO a c x :=
  ContinuousLinearMap.ext fun v => coordChangeO_comp a b c x hx v

theorem coordChangeO_mul_self (S T : ChartIdx k m) (x : OG k m)
    (hx : x ∈ baseSet S ∩ baseSet T) :
    (coordChangeO S T x).comp (coordChangeO T S x) = 1 := by
  ext v
  rw [ContinuousLinearMap.comp_apply, coordChangeO_comp T S T x ⟨⟨hx.2, hx.1⟩, hx.2⟩ v,
    coordChangeO_self T x hx.2 v]
  rfl

/-! ## The middle factor of the gauge -/

/-- The matrix of the "inner factor" of the gauge: `D_{i^ρ} · Q_i⁻¹ · D_i`. -/
def inclTmat (k m : ℕ) (i : ChartIdx k (m + 1)) (b : OG k m) : Matrix (Fin k) (Fin k) ℝ :=
  orientMat (cd k m i) b * (cdQinv k m i * orientMat i (ogIncl k m b))

/-- The matrix of the inverse inner factor: `D_i · Q_i · D_{i^ρ}`. -/
def inclTinvMat (k m : ℕ) (i : ChartIdx k (m + 1)) (b : OG k m) : Matrix (Fin k) (Fin k) ℝ :=
  orientMat i (ogIncl k m b) * (cdQ k m i * orientMat (cd k m i) b)

/-- The inner factor of the gauge. -/
def inclT (k m : ℕ) (i : ChartIdx k (m + 1)) (b : OG k m) : Amb k →L[ℝ] Amb k :=
  matLin (inclTmat k m i b)

/-- The inverse of the inner factor of the gauge. -/
def inclTinv (k m : ℕ) (i : ChartIdx k (m + 1)) (b : OG k m) : Amb k →L[ℝ] Amb k :=
  matLin (inclTinvMat k m i b)

theorem inclT_apply (i : ChartIdx k (m + 1)) (b : OG k m) :
    inclT k m i b = (matLin (orientMat (cd k m i) b)).comp
      ((matLin (cdQinv k m i)).comp (matLin (orientMat i (ogIncl k m b)))) := by
  rw [inclT, inclTmat, matLin_mul, matLin_mul]

theorem inclTinv_apply (i : ChartIdx k (m + 1)) (b : OG k m) :
    inclTinv k m i b = (matLin (orientMat i (ogIncl k m b))).comp
      ((matLin (cdQ k m i)).comp (matLin (orientMat (cd k m i) b))) := by
  rw [inclTinv, inclTinvMat, matLin_mul, matLin_mul]

/-- The inner factor is invertible, with `inclTinv` as inverse. -/
theorem inclTinv_comp_inclT (i : ChartIdx k (m + 1)) (b : OG k m)
    (h1 : ogIncl k m b ∈ baseSet i) (h2 : b ∈ baseSet (cd k m i)) :
    (inclTinv k m i b).comp (inclT k m i b) = 1 := by
  have hDi : orientMat i (ogIncl k m b) * orientMat i (ogIncl k m b) = 1 :=
    orientMat_mul_self (ogIncl k m b) h1
  have hDd : orientMat (cd k m i) b * orientMat (cd k m i) b = 1 :=
    orientMat_mul_self b h2
  have hQ : cdQ k m i * cdQinv k m i = 1 := cdQ_mul_cdQinv i
  rw [inclT, inclTinv, ← matLin_mul,
    show inclTinvMat k m i b * inclTmat k m i b = 1 from by
      simp only [inclTmat, inclTinvMat]
      rw [show (orientMat i (ogIncl k m b) * (cdQ k m i * orientMat (cd k m i) b))
            * (orientMat (cd k m i) b * (cdQinv k m i * orientMat i (ogIncl k m b)))
          = orientMat i (ogIncl k m b) * (cdQ k m i * (orientMat (cd k m i) b
              * (orientMat (cd k m i) b * (cdQinv k m i * orientMat i (ogIncl k m b)))))
          from by simp only [Matrix.mul_assoc]]
      rw [← Matrix.mul_assoc (orientMat (cd k m i) b) (orientMat (cd k m i) b)
          (cdQinv k m i * orientMat i (ogIncl k m b)), hDd, Matrix.one_mul,
        ← Matrix.mul_assoc (cdQ k m i) (cdQinv k m i) (orientMat i (ogIncl k m b)), hQ,
        Matrix.one_mul, hDi],
    matLin_one]

/-- The two-sided inverse property, in the other order. -/
theorem inclT_comp_inclTinv (i : ChartIdx k (m + 1)) (b : OG k m)
    (h1 : ogIncl k m b ∈ baseSet i) (h2 : b ∈ baseSet (cd k m i)) :
    (inclT k m i b).comp (inclTinv k m i b) = 1 := by
  have hDi : orientMat i (ogIncl k m b) * orientMat i (ogIncl k m b) = 1 :=
    orientMat_mul_self (ogIncl k m b) h1
  have hDd : orientMat (cd k m i) b * orientMat (cd k m i) b = 1 :=
    orientMat_mul_self b h2
  have hQ : cdQinv k m i * cdQ k m i = 1 := cdQinv_mul_cdQ i
  rw [inclT, inclTinv, ← matLin_mul,
    show inclTmat k m i b * inclTinvMat k m i b = 1 from by
      simp only [inclTmat, inclTinvMat]
      rw [show (orientMat (cd k m i) b * (cdQinv k m i * orientMat i (ogIncl k m b)))
            * (orientMat i (ogIncl k m b) * (cdQ k m i * orientMat (cd k m i) b))
          = orientMat (cd k m i) b * (cdQinv k m i * (orientMat i (ogIncl k m b)
              * (orientMat i (ogIncl k m b) * (cdQ k m i * orientMat (cd k m i) b))))
          from by simp only [Matrix.mul_assoc]]
      rw [← Matrix.mul_assoc (orientMat i (ogIncl k m b)) (orientMat i (ogIncl k m b))
          (cdQ k m i * orientMat (cd k m i) b), hDi, Matrix.one_mul,
        ← Matrix.mul_assoc (cdQinv k m i) (cdQ k m i) (orientMat (cd k m i) b), hQ,
        Matrix.one_mul, hDd],
    matLin_one]

/-! ## The conjugation identity (the crux) -/

/-- **The conjugation identity, at the level of matrices.**  This is the algebraic content of the
frame computation `frameMatrix_inclFrame`: the `D`-factors cancel modulo the involution
`D · D = 1`. -/
theorem inclTmat_conj (Qinvi Qinvj Ai Aj Bi Bj Di Dj Ddi Ddj : Matrix (Fin k) (Fin k) ℝ)
    (hDi : Di * Di = 1) (hDdj : Ddj * Ddj = 1)
    (hBi : Qinvi * Bi = Ai) (hBj : Bj⁻¹ = Aj⁻¹ * Qinvj) :
    (Ddi * (Qinvi * Di)) * (Di * ((Bi * Bj⁻¹) * Dj))
      = (Ddi * ((Ai * Aj⁻¹) * Ddj)) * (Ddj * (Qinvj * Dj)) := by
  rw [← hBi, hBj]
  calc (Ddi * (Qinvi * Di)) * (Di * ((Bi * (Aj⁻¹ * Qinvj)) * Dj))
      = Ddi * (Qinvi * (Di * (Di * ((Bi * (Aj⁻¹ * Qinvj)) * Dj)))) := by noncomm_ring
    _ = Ddi * (Qinvi * ((Bi * (Aj⁻¹ * Qinvj)) * Dj)) := by
          rw [← Matrix.mul_assoc Di Di ((Bi * (Aj⁻¹ * Qinvj)) * Dj), hDi, Matrix.one_mul]
    _ = Ddi * (Qinvi * (Bi * (Aj⁻¹ * (Qinvj * Dj)))) := by noncomm_ring
    _ = (Ddi * ((Qinvi * Bi) * Aj⁻¹ * Ddj)) * (Ddj * (Qinvj * Dj)) := by
          have e : (Ddi * ((Qinvi * Bi) * Aj⁻¹ * Ddj)) * (Ddj * (Qinvj * Dj))
              = Ddi * (Qinvi * (Bi * (Aj⁻¹ * (Ddj * (Ddj * (Qinvj * Dj)))))) := by
            noncomm_ring
          rw [e, ← Matrix.mul_assoc Ddj Ddj (Qinvj * Dj), hDdj, Matrix.one_mul]

/-- **The conjugation identity**: the inner factor of the gauge intertwines the transition
functions of the pulled-back big bundle with those of the small bundle. -/
theorem inclT_comp_coordChangeO (i j : ChartIdx k (m + 1)) (b : OG k m)
    (hi : ogIncl k m b ∈ baseSet i) (hj : ogIncl k m b ∈ baseSet j) :
    (inclT k m i b).comp (coordChangeO j i (ogIncl k m b))
      = (coordChangeO (cd k m j) (cd k m i) b).comp (inclT k m j b) := by
  obtain ⟨f, rfl⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = b := Quotient.exists_rep b
  have hi' := hi
  rw [ogIncl_mk] at hi'
  have hj' := hj
  rw [ogIncl_mk] at hj'
  have hli : Fin.last (k + m) ∉ i.1 := not_mem_last_of_mem_ogIncl i hi
  have hlj : Fin.last (k + m) ∉ j.1 := not_mem_last_of_mem_ogIncl j hj
  have hci : (inclFrame k m f) ∈ chartSet i := (mem_baseSet_iff i (inclFrame k m f)).mp hi'
  have hcj : (inclFrame k m f) ∈ chartSet j := (mem_baseSet_iff j (inclFrame k m f)).mp hj'
  have hfdj : Quotient.mk'' f ∈ baseSet (cd k m j) := mem_baseSet_cd_of_mem_ogIncl j hj
  have hfj : f ∈ chartSet (cd k m j) := (mem_baseSet_iff (cd k m j) f).mp hfdj
  have hcZ := coordChangeO_mk j i (inclFrame k m f) hcj
  have hcZ' := coordChangeO_mk (cd k m j) (cd k m i) f hfj
  rw [ogIncl_mk]
  simp only [inclT, inclTmat]
  rw [hcZ, hcZ', ← matLin_mul, ← matLin_mul]
  congr 1
  simp only [cd_eq i hli, cd_eq j hlj, cdQinv_eq i hli, cdQinv_eq j hlj]
  refine inclTmat_conj _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · exact orientMat_mul_self (Quotient.mk'' (inclFrame k m f)) hi'
  · rw [← cd_eq j hlj]; exact orientMat_mul_self (Quotient.mk'' f) hfdj
  · rw [frameMatrix_inclFrame_mul i hli f, ← Matrix.mul_assoc, chartQinv_mul_chartQ i hli,
      Matrix.one_mul]
  · rw [frameMatrix_inclFrame_mul j hlj f,
      matrix_mul_inv_eq (chartQ k m j hlj) (frameMatrix (chartDown k m j hlj) f.1)
        (isUnit_iff_ne_zero.mpr (chartQ_det_ne_zero j hlj))
        (isUnit_iff_ne_zero.mpr (show (frameMatrix (chartDown k m j hlj) f.1).det ≠ 0 from by
          rw [← cd_eq j hlj]; exact hfj)),
      Matrix.inv_eq_left_inv (chartQinv_mul_chartQ j hlj)]

/-! ## The inverse inner factor and the second conjugation identity -/

theorem inclT_injective (i : ChartIdx k (m + 1)) (b : OG k m) (h1 : ogIncl k m b ∈ baseSet i)
    (h2 : b ∈ baseSet (cd k m i)) : Function.Injective (inclT k m i b) := by
  intro x y hxy
  have hx : (inclTinv k m i b) ((inclT k m i b) x) = x := by
    have h := congrArg (fun (L : Amb k →L[ℝ] Amb k) => L x) (inclTinv_comp_inclT i b h1 h2)
    rwa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h
  have hy : (inclTinv k m i b) ((inclT k m i b) y) = y := by
    have h := congrArg (fun (L : Amb k →L[ℝ] Amb k) => L y) (inclTinv_comp_inclT i b h1 h2)
    rwa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h
  calc x = (inclTinv k m i b) ((inclT k m i b) x) := hx.symm
    _ = (inclTinv k m i b) ((inclT k m i b) y) := by rw [hxy]
    _ = y := hy

theorem inclT_comp_inclTinv_apply (i : ChartIdx k (m + 1)) (b : OG k m)
    (h1 : ogIncl k m b ∈ baseSet i) (h2 : b ∈ baseSet (cd k m i)) (v : Amb k) :
    (inclT k m i b) ((inclTinv k m i b) v) = v := by
  have h := congrArg (fun (L : Amb k →L[ℝ] Amb k) => L v) (inclT_comp_inclTinv i b h1 h2)
  rwa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h

/-- The conjugation identity for the inverse inner factor (the inverse of
`inclT_comp_coordChangeO`). -/
theorem coordChangeO_comp_inclTinv (i j : ChartIdx k (m + 1)) (b : OG k m)
    (hi : ogIncl k m b ∈ baseSet i) (hj : ogIncl k m b ∈ baseSet j) :
    (coordChangeO i j (ogIncl k m b)).comp (inclTinv k m i b)
      = (inclTinv k m j b).comp (coordChangeO (cd k m i) (cd k m j) b) := by
  have hTj : Function.Injective (inclT k m j b) :=
    inclT_injective j b hj (mem_baseSet_cd_of_mem_ogIncl j hj)
  apply ContinuousLinearMap.ext
  intro v
  apply hTj
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have e1 : (inclT k m j b) ((coordChangeO i j (ogIncl k m b)) ((inclTinv k m i b) v))
      = (coordChangeO (cd k m i) (cd k m j) b) v := by
    have h := congrArg (fun (L : Amb k →L[ℝ] Amb k) => L ((inclTinv k m i b) v))
      (inclT_comp_coordChangeO (k := k) (m := m) j i b hj hi)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h
    rw [h, inclT_comp_inclTinv_apply i b hi (mem_baseSet_cd_of_mem_ogIncl i hi) v]
  have e2 : (inclT k m j b) ((inclTinv k m j b) ((coordChangeO (cd k m i) (cd k m j) b) v))
      = (coordChangeO (cd k m i) (cd k m j) b) v :=
    inclT_comp_inclTinv_apply j b hj (mem_baseSet_cd_of_mem_ogIncl j hj)
      ((coordChangeO (cd k m i) (cd k m j) b) v)
  rw [e1, e2]

/-! ## The gauge families -/

/-- The gauge family: the fibrewise isomorphism between the pullback of `γ_{k,m+1}` and `γ_{k,m}`
in the charts `(i,t)`. -/
def inclPhi (k m : ℕ) (i : ChartIdx k (m + 1)) (t : ChartIdx k m) (b : OG k m) :
    Amb k →L[ℝ] Amb k :=
  (coordChangeO (cd k m i) t b).comp (inclT k m i b)

/-- Its inverse. -/
def inclPhiInv (k m : ℕ) (i : ChartIdx k (m + 1)) (t : ChartIdx k m) (b : OG k m) :
    Amb k →L[ℝ] Amb k :=
  (inclTinv k m i b).comp (coordChangeO t (cd k m i) b)

/-! ## Continuity -/

/-- The membership of the pullback's chart `i`, in terms of `ogIncl`. -/
theorem mem_comap_baseSet {i : ChartIdx k (m + 1)} {b : OG k m}
    (hb : b ∈ (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i) :
    ogIncl k m b ∈ baseSet i := by
  rw [Work.Thom.bundleComap_baseSet] at hb
  change ogIncl k m b ∈ baseSet i at hb
  exact hb

theorem continuousOn_inclT (i : ChartIdx k (m + 1)) :
    ContinuousOn (fun b : OG k m => inclT k m i b)
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i) := by
  have hA : ContinuousOn (fun b : OG k m => matLin (orientMat (cd k m i) b))
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i) :=
    continuous_matLin.comp_continuousOn ((continuousOn_orientMat (cd k m i)).mono
      (fun b hb => mem_baseSet_cd_of_mem_ogIncl i (mem_comap_baseSet hb)))
  have hQ : ContinuousOn (fun _ : OG k m => matLin (cdQinv k m i))
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i) :=
    continuousOn_const
  have hB : ContinuousOn (fun b : OG k m => matLin (orientMat i (ogIncl k m b)))
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i) :=
    continuous_matLin.comp_continuousOn ((continuousOn_orientMat i).comp
      (continuous_ogIncl k m).continuousOn (fun b hb => mem_comap_baseSet hb))
  refine (hA.clm_comp (hQ.clm_comp hB)).congr (fun b hb => ?_)
  rw [inclT_apply]

theorem continuousOn_inclTinv (i : ChartIdx k (m + 1)) :
    ContinuousOn (fun b : OG k m => inclTinv k m i b)
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i) := by
  have hA : ContinuousOn (fun b : OG k m => matLin (orientMat i (ogIncl k m b)))
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i) :=
    continuous_matLin.comp_continuousOn ((continuousOn_orientMat i).comp
      (continuous_ogIncl k m).continuousOn (fun b hb => mem_comap_baseSet hb))
  have hQ : ContinuousOn (fun _ : OG k m => matLin (cdQ k m i))
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i) :=
    continuousOn_const
  have hB : ContinuousOn (fun b : OG k m => matLin (orientMat (cd k m i) b))
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i) :=
    continuous_matLin.comp_continuousOn ((continuousOn_orientMat (cd k m i)).mono
      (fun b hb => mem_baseSet_cd_of_mem_ogIncl i (mem_comap_baseSet hb)))
  refine (hA.clm_comp (hQ.clm_comp hB)).congr (fun b hb => ?_)
  rw [inclTinv_apply]

theorem continuousOn_inclPhi (i : ChartIdx k (m + 1)) (t : ChartIdx k m) :
    ContinuousOn (fun b : OG k m => inclPhi k m i t b)
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i
        ∩ (tautologicalBundle k m).baseSet t) := by
  have h1 : ContinuousOn (fun b : OG k m => coordChangeO (cd k m i) t b)
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i
        ∩ (tautologicalBundle k m).baseSet t) :=
    (continuousOn_coordChangeO (cd k m i) t).mono (fun b hb =>
      ⟨mem_baseSet_cd_of_mem_ogIncl i (mem_comap_baseSet hb.1), by
        show b ∈ baseSet t
        exact hb.2⟩)
  have h2 : ContinuousOn (fun b : OG k m => inclT k m i b)
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i
        ∩ (tautologicalBundle k m).baseSet t) :=
    (continuousOn_inclT i).mono Set.inter_subset_left
  refine (h1.clm_comp h2).congr (fun b hb => ?_)
  rw [inclPhi]

theorem continuousOn_inclPhiInv (i : ChartIdx k (m + 1)) (t : ChartIdx k m) :
    ContinuousOn (fun b : OG k m => inclPhiInv k m i t b)
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i
        ∩ (tautologicalBundle k m).baseSet t) := by
  have h1 : ContinuousOn (fun b : OG k m => coordChangeO t (cd k m i) b)
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i
        ∩ (tautologicalBundle k m).baseSet t) :=
    (continuousOn_coordChangeO t (cd k m i)).mono (fun b hb =>
      ⟨by show b ∈ baseSet t
          exact hb.2,
        mem_baseSet_cd_of_mem_ogIncl i (mem_comap_baseSet hb.1)⟩)
  have h2 : ContinuousOn (fun b : OG k m => inclTinv k m i b)
      ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i
        ∩ (tautologicalBundle k m).baseSet t) :=
    (continuousOn_inclTinv i).mono Set.inter_subset_left
  refine (h2.clm_comp h1).congr (fun b hb => ?_)
  rw [inclPhiInv]

/-! ## The six hypotheses of the gauge construction -/

theorem coordChange_eq_coordChangeO (S T : ChartIdx k m) (x : OG k m) :
    (tautologicalBundle k m).coordChange S T x = coordChangeO S T x := rfl

theorem comap_coordChange_eq (i j : ChartIdx k (m + 1)) (b : OG k m) :
    (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).coordChange i j b
      = coordChangeO i j (ogIncl k m b) := by
  rw [Work.Thom.bundleComap_coordChange]
  rfl

theorem inclTinv_comp_inclT_apply (i : ChartIdx k (m + 1)) (b : OG k m)
    (h1 : ogIncl k m b ∈ baseSet i) (h2 : b ∈ baseSet (cd k m i)) (v : Amb k) :
    (inclTinv k m i b) ((inclT k m i b) v) = v := by
  have h := congrArg (fun (L : Amb k →L[ℝ] Amb k) => L v) (inclTinv_comp_inclT i b h1 h2)
  rwa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h

theorem coordChangeO_mul_self_apply (S T : ChartIdx k m) (x : OG k m)
    (hx : x ∈ baseSet S ∩ baseSet T) (v : Amb k) :
    (coordChangeO S T x) ((coordChangeO T S x) v) = v := by
  rw [coordChangeO_comp T S T x ⟨⟨hx.2, hx.1⟩, hx.2⟩ v, coordChangeO_self T x hx.2 v]

theorem inclPhi_htgt (i : ChartIdx k (m + 1)) (t t' : ChartIdx k m) (b : OG k m)
    (hb1 : b ∈ (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i)
    (hb2 : b ∈ (tautologicalBundle k m).baseSet t)
    (hb3 : b ∈ (tautologicalBundle k m).baseSet t') :
    ((tautologicalBundle k m).coordChange t t' b).comp (inclPhi k m i t b)
      = inclPhi k m i t' b := by
  have hb1' : ogIncl k m b ∈ baseSet i := mem_comap_baseSet hb1
  have hb2' : b ∈ baseSet t := hb2
  have hb3' : b ∈ baseSet t' := hb3
  apply ContinuousLinearMap.ext
  intro v
  simp only [coordChange_eq_coordChangeO, inclPhi, ContinuousLinearMap.comp_apply]
  exact coordChangeO_comp (cd k m i) t t' b
    ⟨⟨mem_baseSet_cd_of_mem_ogIncl i hb1', hb2'⟩, hb3'⟩ _

theorem inclPhi_hsrc (i i' : ChartIdx k (m + 1)) (t : ChartIdx k m) (b : OG k m)
    (hb1 : b ∈ (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i)
    (hb2 : b ∈ (Work.Thom.bundleComap (tautologicalBundle k (m + 1))
      (ogInclCM k m)).baseSet i')
    (hb3 : b ∈ (tautologicalBundle k m).baseSet t) :
    (inclPhi k m i t b).comp
        ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).coordChange i' i b)
      = inclPhi k m i' t b := by
  have hb1' : ogIncl k m b ∈ baseSet i := mem_comap_baseSet hb1
  have hb2' : ogIncl k m b ∈ baseSet i' := mem_comap_baseSet hb2
  have hb3' : b ∈ baseSet t := hb3
  apply ContinuousLinearMap.ext
  intro v
  simp only [comap_coordChange_eq, inclPhi, ContinuousLinearMap.comp_apply]
  have hconj := congrArg (fun (L : Amb k →L[ℝ] Amb k) => L v)
    (inclT_comp_coordChangeO i i' b hb1' hb2')
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hconj
  rw [hconj]
  exact coordChangeO_comp (cd k m i') (cd k m i) t b
    ⟨⟨mem_baseSet_cd_of_mem_ogIncl i' hb2', mem_baseSet_cd_of_mem_ogIncl i hb1'⟩, hb3'⟩ _

theorem inclPhi_hleft (i : ChartIdx k (m + 1)) (t : ChartIdx k m) (b : OG k m)
    (hb : b ∈ (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i
      ∩ (tautologicalBundle k m).baseSet t) (x : Amb k) :
    inclPhiInv k m i t b (inclPhi k m i t b x) = x := by
  have hb1' : ogIncl k m b ∈ baseSet i := mem_comap_baseSet hb.1
  have hb2' : b ∈ baseSet t := hb.2
  simp only [inclPhi, inclPhiInv, ContinuousLinearMap.comp_apply]
  rw [coordChangeO_mul_self_apply t (cd k m i) b
    ⟨hb2', mem_baseSet_cd_of_mem_ogIncl i hb1'⟩]
  exact inclTinv_comp_inclT_apply i b hb1' (mem_baseSet_cd_of_mem_ogIncl i hb1') x

theorem inclPhi_hright (i : ChartIdx k (m + 1)) (t : ChartIdx k m) (b : OG k m)
    (hb : b ∈ (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i
      ∩ (tautologicalBundle k m).baseSet t) (y : Amb k) :
    inclPhi k m i t b (inclPhiInv k m i t b y) = y := by
  have hb1' : ogIncl k m b ∈ baseSet i := mem_comap_baseSet hb.1
  have hb2' : b ∈ baseSet t := hb.2
  simp only [inclPhi, inclPhiInv, ContinuousLinearMap.comp_apply]
  rw [inclT_comp_inclTinv_apply i b hb1' (mem_baseSet_cd_of_mem_ogIncl i hb1')]
  exact coordChangeO_mul_self_apply (cd k m i) t b
    ⟨mem_baseSet_cd_of_mem_ogIncl i hb1', hb2'⟩ y

theorem inclPhi_htgtinv (i : ChartIdx k (m + 1)) (t t' : ChartIdx k m) (b : OG k m)
    (hb1 : b ∈ (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i)
    (hb2 : b ∈ (tautologicalBundle k m).baseSet t)
    (hb3 : b ∈ (tautologicalBundle k m).baseSet t') :
    (inclPhiInv k m i t b).comp ((tautologicalBundle k m).coordChange t' t b)
      = inclPhiInv k m i t' b := by
  have hb1' : ogIncl k m b ∈ baseSet i := mem_comap_baseSet hb1
  have hb2' : b ∈ baseSet t := hb2
  have hb3' : b ∈ baseSet t' := hb3
  apply ContinuousLinearMap.ext
  intro v
  simp only [coordChange_eq_coordChangeO, inclPhiInv, ContinuousLinearMap.comp_apply]
  congr 1
  exact coordChangeO_comp t' t (cd k m i) b
    ⟨⟨hb3', hb2'⟩, mem_baseSet_cd_of_mem_ogIncl i hb1'⟩ _

theorem inclPhi_hsrcinv (i i' : ChartIdx k (m + 1)) (t : ChartIdx k m) (b : OG k m)
    (hb1 : b ∈ (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).baseSet i)
    (hb2 : b ∈ (Work.Thom.bundleComap (tautologicalBundle k (m + 1))
      (ogInclCM k m)).baseSet i')
    (hb3 : b ∈ (tautologicalBundle k m).baseSet t) :
    ((Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m)).coordChange i i' b).comp
        (inclPhiInv k m i t b)
      = inclPhiInv k m i' t b := by
  have hb1' : ogIncl k m b ∈ baseSet i := mem_comap_baseSet hb1
  have hb2' : ogIncl k m b ∈ baseSet i' := mem_comap_baseSet hb2
  have hb3' : b ∈ baseSet t := hb3
  apply ContinuousLinearMap.ext
  intro v
  simp only [comap_coordChange_eq, inclPhiInv, ContinuousLinearMap.comp_apply]
  have hconj := congrArg (fun (L : Amb k →L[ℝ] Amb k) =>
      L ((coordChangeO t (cd k m i) b) v)) (coordChangeO_comp_inclTinv i i' b hb1' hb2')
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hconj
  rw [hconj]
  congr 1
  exact coordChangeO_comp t (cd k m i) (cd k m i') b
    ⟨⟨hb3', mem_baseSet_cd_of_mem_ogIncl i hb1'⟩,
      mem_baseSet_cd_of_mem_ogIncl i' hb2'⟩ _

end

end Work.ThomBordism.Grassmann

