import Mathlib
import Submission.Work.ThomBordism.Grassmann.zStdSetup
import Submission.Work.ThomBordism.Grassmann.ZStdURSupport
import Submission.Work.ThomBordism.Grassmann.zStd_VR_cohomology
import Submission.Work.ThomBordism.Grassmann.p1RatPuncture

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The overlap `UR ∩ VR`: the ratio coordinates

This module sets up the vocabulary for the proof that `H³(UR ∩ VR) = 0`
(`Work.ThomBordism.Grassmann.zStd_UV_cohomology`).  Recall (`zStdSetup`) that

* `W = realification (complexificationCore zStd)` is the rank-`4` real bundle over `ℂP²` whose top
  Chern class is the Euler class of the canonical Thom class,
* `UR = {Re ≠ 0}`, `VR = {Im ≠ 0}` are the two pieces of `zeroComplement W`,

so `UR ∩ VR` is the locus where the real part `U = cxRePart w` and the imaginary part
`V = cxImPart w` of the fibre vector `w ∈ ℂ²` are both nonzero.

## The ratio

`zStd = mapFibre equivC1R2 (realification (tautDual 2))` is the realification of a *complex* line
bundle, so its transition functions, read in the coordinates `ccoord` induced by `equivC1R2`, are
multiplication by a complex number (`ccoord_zStd_coordChange`).  Hence the ratio
`uvRatio p = v/u` of the two components of the fibre vector is invariant under a change of chart and
gives a well defined function `uvRatio : ↥(UR ∩ VR) → ℂ` with values in `ℂ ∖ {0}`
(`uvRatio_ne_zero`); every region `Reg ⊆ ℂ` pulls back to a subset `uvPiece Reg` of `UR ∩ VR`.

## The pieces

* `uvA = {ratio ∉ ℝ_{≥0}}` and `uvB = {ratio ∉ ℝ_{≤0}}` cover `UR ∩ VR` (`uvA_union_uvB`), since
  only `0` lies in both rays and the ratio never vanishes;
* `uvA ∩ uvB = {ratio ∉ ℝ} = uvP ∪ uvQ` with `uvP = {Im ratio > 0}` and `uvQ = {Im ratio < 0}`
  (`uvA_inter_uvB`, `uvP_inter_uvQ`).

Each of the four pieces is homotopy equivalent to `zeroComplement zStd` (the retraction
`p ↦ (base, u)`, the section whose ratio is a fixed `κ ∈ Reg`, and the straight line homotopy
`r_t = (1-t) r + t κ` in the ratio); see `uvPieceHomotopyEquiv`.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

/-! ## The complex coordinate of the model fibres -/

/-- The `0`-th coordinate of a vector of `ℂ¹ = EuclideanSpace ℂ (Fin 1)`, as a complex number. -/
def zcoord (z : EuclideanSpace ℂ (Fin 1)) : ℂ := z 0

/-- The canonical generator `1` of `ℂ¹`. -/
def oneCx : EuclideanSpace ℂ (Fin 1) := WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℂ))

/-- The complex coordinate of a vector of the standard fibre `ℝ²` of `zStd`, via `equivC1R2`. -/
def ccoord (x : EuclideanSpace ℝ (Fin 2)) : ℂ := zcoord (equivC1R2.symm x)

@[simp] theorem zcoord_zero : zcoord (0 : EuclideanSpace ℂ (Fin 1)) = 0 := rfl

@[simp] theorem oneCx_ne_zero : oneCx ≠ 0 := by
  intro h
  have h1 : zcoord oneCx = zcoord (0 : EuclideanSpace ℂ (Fin 1)) := by rw [h]
  rw [zcoord_zero] at h1
  simp [oneCx, zcoord] at h1

@[simp] theorem ccoord_zero : ccoord (0 : EuclideanSpace ℝ (Fin 2)) = 0 := by
  simp [ccoord, zcoord]

@[simp] theorem ccoord_equivC1R2 (z : EuclideanSpace ℂ (Fin 1)) :
    ccoord (equivC1R2 z) = zcoord z := by
  simp [ccoord]

theorem zcoord_smul (c : ℂ) (z : EuclideanSpace ℂ (Fin 1)) :
    zcoord (c • z) = c * zcoord z := rfl

theorem zcoord_eq_zero_iff (z : EuclideanSpace ℂ (Fin 1)) : zcoord z = 0 ↔ z = 0 := by
  constructor
  · intro h
    ext t
    fin_cases t
    simpa [zcoord] using h
  · intro h; rw [h]; rfl

theorem ccoord_eq_zero_iff (x : EuclideanSpace ℝ (Fin 2)) : ccoord x = 0 ↔ x = 0 := by
  rw [ccoord, zcoord_eq_zero_iff, ContinuousLinearEquiv.map_eq_zero_iff]

theorem ccoord_ne_zero_iff (x : EuclideanSpace ℝ (Fin 2)) : ccoord x ≠ 0 ↔ x ≠ 0 :=
  not_congr (ccoord_eq_zero_iff x)

/-- The complex structure `J` on the standard fibre `ℝ²` of `zStd`: multiplication by `i` on `ℂ`,
transported along `equivC1R2`. -/
def Jz : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
    ((LinearMap.toContinuousLinearMap (Work.Thom.cxMulI (k := 1))).comp
      (equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1)))

@[simp] theorem Jz_apply (x : EuclideanSpace ℝ (Fin 2)) :
    Jz x = equivC1R2 (Work.Thom.cxMulI (equivC1R2.symm x)) := rfl

/-- `J` acts as multiplication by `i` on the `ccoord`-coordinates. -/
theorem ccoord_Jz (x : EuclideanSpace ℝ (Fin 2)) : ccoord (Jz x) = Complex.I * ccoord x := by
  simp [ccoord, Jz, zcoord, Work.Thom.cxMulI]

theorem Jz_Jz (x : EuclideanSpace ℝ (Fin 2)) : Jz (Jz x) = -x := by
  simp only [Jz_apply, ContinuousLinearEquiv.symm_apply_apply, Work.Thom.cxMulI_cxMulI, map_neg,
    ContinuousLinearEquiv.apply_symm_apply]

theorem Jz_eq_zero_iff (x : EuclideanSpace ℝ (Fin 2)) : Jz x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h2 : Jz (Jz x) = Jz 0 := by rw [h]
    rw [Jz_Jz, map_zero] at h2
    simpa using h2
  · intro h; rw [h, map_zero]

theorem Jz_ne_zero_iff (x : EuclideanSpace ℝ (Fin 2)) : Jz x ≠ 0 ↔ x ≠ 0 :=
  not_congr (Jz_eq_zero_iff x)

theorem Jz_injective : Function.Injective (Jz : EuclideanSpace ℝ (Fin 2) → _) := by
  intro x y h
  have h2 := congrArg Jz h
  rw [Jz_Jz, Jz_Jz, neg_inj] at h2
  exact h2

/-! ## The transition functions of `zStd` are complex multiplications -/

theorem mapFibre_coordChange_fun (i j : Fin 3) (b : Work.Projective.CP 2) :
    ⇑(zStd.coordChange i j b)
      = ⇑(equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)) ∘
        ⇑((Work.Thom.realification (Work.Gen.tautDual 2)).coordChange i j b) ∘
        ⇑(equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1)) := by
  rw [show zStd = RealBundle.mapFibre equivC1R2
      (Work.Thom.realification (Work.Gen.tautDual 2)) from rfl]
  rw [RealBundle.mapFibre_coordChange equivC1R2
    (Work.Thom.realification (Work.Gen.tautDual 2)) i j b]
  rfl

/-- **The transition functions of `zStd` commute with the complex structure `J`.** -/
theorem zStd_coordChange_Jz (i j : Fin 3) (b : Work.Projective.CP 2)
    (x : EuclideanSpace ℝ (Fin 2)) :
    zStd.coordChange i j b (Jz x) = Jz (zStd.coordChange i j b x) := by
  have hg := mapFibre_coordChange_fun i j b
  have hG : ⇑((Work.Thom.realification (Work.Gen.tautDual 2)).coordChange i j b)
      = ⇑((Work.Gen.tautDual 2).coordChange i j b) :=
    Work.Thom.realification_coordChange (Work.Gen.tautDual 2) i j b
  rw [show zStd.coordChange i j b (Jz x)
      = equivC1R2 ((Work.Thom.realification (Work.Gen.tautDual 2)).coordChange i j b
          (equivC1R2.symm (Jz x))) from congrFun hg (Jz x)]
  rw [show (equivC1R2.symm (Jz x)) = Work.Thom.cxMulI (equivC1R2.symm x) from by
    simp only [Jz_apply, ContinuousLinearEquiv.symm_apply_apply]]
  rw [hG]
  rw [show Work.Thom.cxMulI (equivC1R2.symm x) = Complex.I • (equivC1R2.symm x) from rfl]
  rw [map_smul]
  rw [show zStd.coordChange i j b x
      = equivC1R2 ((Work.Thom.realification (Work.Gen.tautDual 2)).coordChange i j b
          (equivC1R2.symm x)) from congrFun hg x]
  rw [hG, Jz_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- **In a chart, the transition function is a complex multiplication.** -/
theorem zcoord_tautDual_coordChange (i j : Fin 3) (b : Work.Projective.CP 2)
    (z : EuclideanSpace ℂ (Fin 1)) :
    zcoord ((Work.Gen.tautDual 2).coordChange i j b z)
      = zcoord ((Work.Gen.tautDual 2).coordChange i j b oneCx) * zcoord z := by
  have hz : z = zcoord z • oneCx := by
    ext t
    fin_cases t
    simp [zcoord, oneCx]
  calc zcoord ((Work.Gen.tautDual 2).coordChange i j b z)
      = zcoord ((Work.Gen.tautDual 2).coordChange i j b (zcoord z • oneCx)) := by rw [← hz]
    _ = zcoord ((zcoord z) • (Work.Gen.tautDual 2).coordChange i j b oneCx) := by rw [map_smul]
    _ = zcoord z * zcoord ((Work.Gen.tautDual 2).coordChange i j b oneCx) := rfl
    _ = zcoord ((Work.Gen.tautDual 2).coordChange i j b oneCx) * zcoord z := by ring

/-- **The transition functions of `zStd` act, in the `ccoord`-coordinates, by multiplication by a
complex number.** -/
theorem ccoord_zStd_coordChange (i j : Fin 3) (b : Work.Projective.CP 2)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ccoord (zStd.coordChange i j b x)
      = zcoord ((Work.Gen.tautDual 2).coordChange i j b oneCx) * ccoord x := by
  have hg := mapFibre_coordChange_fun i j b
  have hG : ⇑((Work.Thom.realification (Work.Gen.tautDual 2)).coordChange i j b)
      = ⇑((Work.Gen.tautDual 2).coordChange i j b) :=
    Work.Thom.realification_coordChange (Work.Gen.tautDual 2) i j b
  rw [show zStd.coordChange i j b x
      = equivC1R2 ((Work.Thom.realification (Work.Gen.tautDual 2)).coordChange i j b
          (equivC1R2.symm x)) from congrFun hg x]
  rw [ccoord_equivC1R2, hG]
  exact zcoord_tautDual_coordChange i j b _

/-- `zStd` and `tautDual 2` have the same charts. -/
theorem zStd_baseSet_tautDual (i : Fin 3) :
    zStd.baseSet i = (Work.Gen.tautDual 2).baseSet i := by
  rw [show zStd = RealBundle.mapFibre equivC1R2
      (Work.Thom.realification (Work.Gen.tautDual 2)) from rfl,
    RealBundle.mapFibre_baseSet, Work.Thom.realification_baseSet]

/-- The complex number of a transition function is nonzero when the transition is honest. -/
theorem zcoord_tautDual_coordChange_oneCx_ne_zero (i j : Fin 3) (b : Work.Projective.CP 2)
    (hb : b ∈ zStd.baseSet i ∩ zStd.baseSet j) :
    zcoord ((Work.Gen.tautDual 2).coordChange i j b oneCx) ≠ 0 := by
  have hbi : b ∈ (Work.Gen.tautDual 2).baseSet i := by rw [← zStd_baseSet_tautDual i]; exact hb.1
  have hbj : b ∈ (Work.Gen.tautDual 2).baseSet j := by rw [← zStd_baseSet_tautDual j]; exact hb.2
  intro h0
  have hzall : ∀ z : EuclideanSpace ℂ (Fin 1),
      (Work.Gen.tautDual 2).coordChange i j b z = 0 := by
    intro z
    apply (zcoord_eq_zero_iff _).mp
    rw [zcoord_tautDual_coordChange, h0, zero_mul]
  have hcomp := VectorBundleCore.coordChange_comp (Work.Gen.tautDual 2) j i j b
    ⟨⟨hbj, hbi⟩, hbj⟩ oneCx
  rw [VectorBundleCore.coordChange_self (Work.Gen.tautDual 2) j b hbj oneCx] at hcomp
  simp only [hzall, map_zero] at hcomp
  exact oneCx_ne_zero hcomp.symm

/-! ## The ratio coordinates on `UR ∩ VR` -/

/-- The complex coordinate of the real part of the fibre vector. -/
def uvU (p : ↥(UR ∩ VR)) : ℂ := ccoord (Work.Thom.cxRePart p.1.1.2)

/-- The complex coordinate of the imaginary part of the fibre vector. -/
def uvV (p : ↥(UR ∩ VR)) : ℂ := ccoord (Work.Thom.cxImPart p.1.1.2)

/-- **The ratio coordinate** `v/u` on the overlap. -/
def uvRatio (p : ↥(UR ∩ VR)) : ℂ := uvV p / uvU p

theorem uvU_ne_zero (p : ↥(UR ∩ VR)) : uvU p ≠ 0 :=
  (ccoord_ne_zero_iff _).mpr p.2.1

theorem uvV_ne_zero (p : ↥(UR ∩ VR)) : uvV p ≠ 0 :=
  (ccoord_ne_zero_iff _).mpr p.2.2

theorem uvRatio_ne_zero (p : ↥(UR ∩ VR)) : uvRatio p ≠ 0 := by
  rw [uvRatio, div_ne_zero_iff]
  exact ⟨uvV_ne_zero p, uvU_ne_zero p⟩

/-- The piece of the overlap cut out by a region of the ratio space. -/
def uvPiece (Reg : Set ℂ) : Set ↥(UR ∩ VR) := {p | uvRatio p ∈ Reg}

@[simp] theorem mem_uvPiece {Reg : Set ℂ} {p : ↥(UR ∩ VR)} :
    p ∈ uvPiece Reg ↔ uvRatio p ∈ Reg := Iff.rfl

/-! ## The complex number of the transition to a chart -/

/-- The complex number by which the transition from the preferred chart to the chart `i`
multiplies the `ccoord`-coordinates. -/
def uvLam (i : Fin 3) (p : ↥(UR ∩ VR)) : ℂ :=
  zcoord ((Work.Gen.tautDual 2).coordChange (zStd.indexAt p.1.1.1) i p.1.1.1 oneCx)

/-- The chart coordinate of the real part, read in the `ccoord`-coordinates. -/
def uvUi (i : Fin 3) (p : ↥(UR ∩ VR)) : ℂ :=
  ccoord (Work.Thom.cxRePart ((W.localTriv i p.1.1).2))

/-- The chart coordinate of the imaginary part, read in the `ccoord`-coordinates. -/
def uvVi (i : Fin 3) (p : ↥(UR ∩ VR)) : ℂ :=
  ccoord (Work.Thom.cxImPart ((W.localTriv i p.1.1).2))

theorem uvLam_mul_uvU (i : Fin 3) (p : ↥(UR ∩ VR)) : uvUi i p = uvLam i p * uvU p := by
  rw [uvUi, uvU, uvLam]
  rw [show Work.Thom.cxRePart ((W.localTriv i p.1.1).2)
      = zStd.coordChange (W.indexAt p.1.1.1) i p.1.1.1 (Work.Thom.cxRePart p.1.1.2) from by
    rw [VectorBundleCore.localTriv_apply]
    exact Work.ThomBordism.Grassmann.cxRePart_W_coordChange _ _ _ _]
  rw [show W.indexAt p.1.1.1 = zStd.indexAt p.1.1.1 from (zStdUR_W_indexAt p.1.1.1).symm]
  exact ccoord_zStd_coordChange _ _ _ _

theorem uvLam_mul_uvV (i : Fin 3) (p : ↥(UR ∩ VR)) : uvVi i p = uvLam i p * uvV p := by
  rw [uvVi, uvV, uvLam]
  rw [show Work.Thom.cxImPart ((W.localTriv i p.1.1).2)
      = zStd.coordChange (W.indexAt p.1.1.1) i p.1.1.1 (Work.Thom.cxImPart p.1.1.2) from by
    rw [VectorBundleCore.localTriv_apply]
    exact cxImPart_W_coordChange _ _ _ _]
  rw [show W.indexAt p.1.1.1 = zStd.indexAt p.1.1.1 from (zStdUR_W_indexAt p.1.1.1).symm]
  exact ccoord_zStd_coordChange _ _ _ _

theorem uvLam_ne_zero (i : Fin 3) (p : ↥(UR ∩ VR)) (hb : p.1.1.1 ∈ W.baseSet i) :
    uvLam i p ≠ 0 := by
  have hb2 : p.1.1.1 ∈ zStd.baseSet i := by
    rw [zStdUR_W_baseSet i]; exact hb
  have hb' : p.1.1.1 ∈ zStd.baseSet (zStd.indexAt p.1.1.1) ∩ zStd.baseSet i :=
    ⟨VectorBundleCore.mem_baseSet_at zStd p.1.1.1, hb2⟩
  exact zcoord_tautDual_coordChange_oneCx_ne_zero _ i p.1.1.1 hb'

theorem uvUi_ne_zero (i : Fin 3) (p : ↥(UR ∩ VR)) (hb : p.1.1.1 ∈ W.baseSet i) :
    uvUi i p ≠ 0 := by
  rw [uvLam_mul_uvU]
  exact mul_ne_zero (uvLam_ne_zero i p hb) (uvU_ne_zero p)

theorem uvVi_ne_zero (i : Fin 3) (p : ↥(UR ∩ VR)) (hb : p.1.1.1 ∈ W.baseSet i) :
    uvVi i p ≠ 0 := by
  rw [uvLam_mul_uvV]
  exact mul_ne_zero (uvLam_ne_zero i p hb) (uvV_ne_zero p)

/-- **The ratio agrees with the ratio of the chart coordinates**, in cross-multiplied form. -/
theorem uvRatio_chart (i : Fin 3) (p : ↥(UR ∩ VR)) :
    uvVi i p * uvU p = uvUi i p * uvV p := by
  rw [uvLam_mul_uvV, uvLam_mul_uvU]
  ring

/-- **The ratio agrees with the ratio of the chart coordinates.** -/
theorem uvRatio_eq_chart_div (i : Fin 3) (p : ↥(UR ∩ VR)) (hb : p.1.1.1 ∈ W.baseSet i) :
    uvRatio p = uvVi i p / uvUi i p := by
  rw [uvRatio, div_eq_div_iff (uvU_ne_zero p) (uvUi_ne_zero i p hb)]
  rw [mul_comm (uvV p) (uvUi i p)]
  exact (uvRatio_chart i p).symm

/-! ## Linearity of the complex coordinate, and the section with prescribed ratio -/

theorem ccoord_add (x y : EuclideanSpace ℝ (Fin 2)) : ccoord (x + y) = ccoord x + ccoord y := by
  simp [ccoord, zcoord]

theorem ccoord_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    ccoord (c • x) = (c : ℂ) * ccoord x := by
  simp [ccoord, zcoord]

theorem ccoord_sub (x y : EuclideanSpace ℝ (Fin 2)) : ccoord (x - y) = ccoord x - ccoord y := by
  simp [ccoord, zcoord]

/-- The `ccoord` of a real combination of `x` and `J x`. -/
theorem ccoord_smul_add_Jz (a b : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    ccoord (a • x + b • Jz x) = ((a : ℂ) + (b : ℂ) * Complex.I) * ccoord x := by
  rw [ccoord_add, ccoord_smul, ccoord_smul, ccoord_Jz]
  ring

/-- The fibre coordinate of a point of `zeroComplement zStd`, as an element of the model fibre. -/
def zcFib (x : ↥(Work.Thom.zeroComplement zStd)) : EuclideanSpace ℝ (Fin 2) := x.1.2

/-- The base point of a point of `zeroComplement zStd`. -/
def zcBase (x : ↥(Work.Thom.zeroComplement zStd)) : Work.Projective.CP 2 := x.1.1

/-- **The section with prescribed ratio `κ`**: the point of `W` over `b` whose real part is `u`
and whose imaginary part is `κ u`. -/
def uvSigFun (κ : ℂ) (x : ↥(Work.Thom.zeroComplement zStd)) : W.TotalSpace :=
  ⟨zcBase x, Work.Thom.cxOfReal (zcFib x)
    + Work.Thom.cxMulI (Work.Thom.cxOfReal (κ.re • zcFib x + κ.im • Jz (zcFib x)))⟩

@[simp] theorem uvSigFun_fst (κ : ℂ) (x : ↥(Work.Thom.zeroComplement zStd)) :
    (uvSigFun κ x).1 = zcBase x := rfl

/-- The imaginary part of the section is `κ` times its real part, in `ccoord`-coordinates. -/
theorem ccoord_uvSigFun (κ : ℂ) (x : ↥(Work.Thom.zeroComplement zStd)) :
    ccoord (κ.re • zcFib x + κ.im • Jz (zcFib x)) = κ * ccoord (zcFib x) := by
  rw [ccoord_smul_add_Jz, Complex.re_add_im]

/-! ## The rays and the four pieces -/

/-- The nonnegative real ray in `ℂ`. -/
def rayNN : Set ℂ := {r | ∃ a : ℝ, 0 ≤ a ∧ r = (a : ℂ)}

/-- The nonpositive real ray in `ℂ`. -/
def rayNP : Set ℂ := {r | ∃ a : ℝ, 0 ≤ a ∧ r = -(a : ℂ)}

/-- The upper half plane. -/
def upperHalf : Set ℂ := {r | 0 < r.im}

/-- The lower half plane. -/
def lowerHalf : Set ℂ := {r | r.im < 0}

theorem rayNN_inter_rayNP : rayNN ∩ rayNP = {0} := by
  ext r
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, ⟨a', ha', h'⟩⟩
    have h2 : ((a : ℂ)) = -(a' : ℂ) := h'
    have h3 : a = -a' := by exact_mod_cast h2
    have ha0 : a = 0 := by linarith
    simp [ha0]
  · rintro rfl
    exact ⟨⟨0, le_refl 0, by simp⟩, ⟨0, le_refl 0, by simp⟩⟩

theorem rayNN_union_rayNP : rayNN ∪ rayNP = {r : ℂ | r.im = 0} := by
  ext r
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) <;> simp
  · intro hr
    have hre : r = ((r.re : ℝ) : ℂ) := by
      rw [Complex.ext_iff]
      exact ⟨by simp, by simpa using hr⟩
    rcases le_total r.re 0 with h | h
    · right
      refine ⟨-r.re, by linarith, ?_⟩
      rw [hre]
      push_cast
      simp
    · left
      exact ⟨r.re, h, by simpa using hre⟩

theorem upperHalf_union_lowerHalf : upperHalf ∪ lowerHalf = {r : ℂ | r.im ≠ 0} := by
  ext r
  constructor
  · rintro (h | h)
    · exact ne_of_gt h
    · exact ne_of_lt h
  · intro h
    rcases lt_or_gt_of_ne h with h' | h'
    · right; exact h'
    · left; exact h'

theorem upperHalf_inter_lowerHalf : upperHalf ∩ lowerHalf = ∅ := by
  ext r
  constructor
  · rintro ⟨h1, h2⟩
    exact absurd (show (0 : ℝ) < r.im from h1)
      (not_lt.mpr (le_of_lt (show r.im < 0 from h2)))
  · intro h; exact absurd h (Set.notMem_empty r)

theorem compl_im_eq_zero : ({r : ℂ | r.im = 0} : Set ℂ)ᶜ = {r : ℂ | r.im ≠ 0} := by
  ext r; simp

/-- `uvA = {ratio ∉ ℝ_{≥0}}`. -/
def uvA : Set ↥(UR ∩ VR) := uvPiece rayNNᶜ

/-- `uvB = {ratio ∉ ℝ_{≤0}}`. -/
def uvB : Set ↥(UR ∩ VR) := uvPiece rayNPᶜ

/-- `uvP = {Im ratio > 0}`. -/
def uvP : Set ↥(UR ∩ VR) := uvPiece upperHalf

/-- `uvQ = {Im ratio < 0}`. -/
def uvQ : Set ↥(UR ∩ VR) := uvPiece lowerHalf

theorem uvPiece_union (Reg Reg' : Set ℂ) : uvPiece (Reg ∪ Reg') = uvPiece Reg ∪ uvPiece Reg' :=
  rfl

theorem uvPiece_inter (Reg Reg' : Set ℂ) : uvPiece (Reg ∩ Reg') = uvPiece Reg ∩ uvPiece Reg' :=
  rfl

/-- **The two pieces `uvA`, `uvB` cover the overlap.** -/
theorem uvA_union_uvB : uvA ∪ uvB = Set.univ := by
  rw [uvA, uvB, ← uvPiece_union, ← Set.compl_inter, rayNN_inter_rayNP]
  ext p
  simp only [mem_uvPiece, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact uvRatio_ne_zero p

/-- **The intersection of the two pieces is the union of `uvP` and `uvQ`.** -/
theorem uvA_inter_uvB : uvA ∩ uvB = uvP ∪ uvQ := by
  rw [uvA, uvB, ← uvPiece_inter, ← Set.compl_union, rayNN_union_rayNP, compl_im_eq_zero,
    uvP, uvQ, ← uvPiece_union, upperHalf_union_lowerHalf]

/-- **`uvP` and `uvQ` are disjoint.** -/
theorem uvP_inter_uvQ : uvP ∩ uvQ = ∅ := by
  rw [uvP, uvQ, ← uvPiece_inter, upperHalf_inter_lowerHalf]
  ext p
  simp [uvPiece]

/-- **`H³` of the punctured total space of `zStd` vanishes.** -/
theorem uvC_three_zero :
    CategoryTheory.Limits.IsZero (Work.Thom.Coh ℤ 3 ↥(Work.Thom.zeroComplement zStd)) := by
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    punctHomeoTautDualTwoR.toHomotopyEquiv 3
  exact CategoryTheory.Limits.IsZero.of_iso
    (puncturedTautDualTwoHZero 3 (by norm_num) (by norm_num)) iso.symm

end

end Work.ThomBordism.Grassmann
