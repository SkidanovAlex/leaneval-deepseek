import Mathlib
import Submission.Work.ThomBordism.Grassmann.ZStdURSupport

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `H⁴` of the piece `VR = {Im ≠ 0}` of the punctured total space of `W`

This is the mirror of `Submission/Work/ThomBordism/Grassmann/zStd_UR_cohomology.lean`, with the
roles of the real and the imaginary part exchanged: the retraction is `(b,u,v) ↦ (b,v)`, the
section is `(b,v) ↦ (b, i·v)` (`i` = `Work.Thom.cxMulI`), and the deformation is the straight-line
homotopy `(t,p) ↦ (1-t)·v + t·(i·Im v)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

/-! ## The imaginary-part coordinate lemmas -/

/-- The imaginary part of a transition function of `W` is the transition function of `zStd` applied
to the imaginary part. -/
theorem cxImPart_W_coordChange (i j : Fin 3) (b : Work.Projective.CP 2)
    (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Thom.cxImPart (W.coordChange i j b v) = zStd.coordChange i j b (Work.Thom.cxImPart v) := by
  rw [show W.coordChange i j b v
      = (Work.Thom.complexificationCore zStd).coordChange i j b v from
    congrFun (Work.Thom.realification_coordChange (Work.Thom.complexificationCore zStd) i j b) v]
  exact Work.Thom.complexificationCore_coordChange_cxImPart zStd i j b v

/-- The inclusion `zStd → W` as the *imaginary* part, `u ↦ i·u`, is a bundle morphism. -/
theorem cxMulI_cxOfReal_zStd_coordChange (i j : Fin 3) (b : Work.Projective.CP 2)
    (u : EuclideanSpace ℝ (Fin 2)) :
    Work.Thom.cxMulI (Work.Thom.cxOfReal (zStd.coordChange i j b u))
      = W.coordChange i j b (Work.Thom.cxMulI (Work.Thom.cxOfReal u)) := by
  rw [show W.coordChange i j b (Work.Thom.cxMulI (Work.Thom.cxOfReal u))
      = (Work.Thom.complexificationCore zStd).coordChange i j b
          (Work.Thom.cxMulI (Work.Thom.cxOfReal u)) from
    congrFun (Work.Thom.realification_coordChange (Work.Thom.complexificationCore zStd) i j b)
      (Work.Thom.cxMulI (Work.Thom.cxOfReal u))]
  rw [Work.Thom.complexificationCore_coordChange, Work.Thom.cxTrans_apply]
  simp

/-! ## The maps of total spaces -/

noncomputable def cxImPartCLM : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap Work.Thom.cxImPart

noncomputable def iotaCLM : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2) :=
  (LinearMap.toContinuousLinearMap (Work.Thom.cxMulI (k := 2))).comp
    (LinearMap.toContinuousLinearMap (Work.Thom.cxOfReal (k := 2)))

@[simp] theorem iotaCLM_apply (u : EuclideanSpace ℝ (Fin 2)) :
    iotaCLM u = Work.Thom.cxMulI (Work.Thom.cxOfReal u) := rfl

/-- The imaginary-part projection `W → zStd`. -/
abbrev imPartTotal (p : W.TotalSpace) : zStd.TotalSpace :=
  ⟨p.1, Work.Thom.cxImPart p.2⟩

/-- The inclusion of `zStd` as the imaginary part of `W`. -/
abbrev iotaTotal (p : zStd.TotalSpace) : W.TotalSpace :=
  ⟨p.1, Work.Thom.cxMulI (Work.Thom.cxOfReal p.2)⟩

/-- The fibrewise imaginary-part projection of `W` onto itself. -/
abbrev Qtot (p : W.TotalSpace) : W.TotalSpace :=
  ⟨p.1, Work.Thom.cxMulI (Work.Thom.cxOfReal (Work.Thom.cxImPart p.2))⟩

theorem continuous_imPartTotal : Continuous imPartTotal :=
  continuous_totalSpaceMap_intertwine W zStd cxImPartCLM
    (fun i => zStdUR_W_baseSet i) (fun b => zStdUR_W_indexAt b)
    (fun i j b v _ => cxImPart_W_coordChange i j b v)

theorem continuous_iotaTotal : Continuous iotaTotal :=
  continuous_totalSpaceMap_intertwine zStd W iotaCLM
    (fun i => (zStdUR_W_baseSet i).symm) (fun b => (zStdUR_W_indexAt b).symm)
    (fun i j b v _ => cxMulI_cxOfReal_zStd_coordChange i j b v)

theorem continuous_Qtot : Continuous Qtot := continuous_iotaTotal.comp continuous_imPartTotal

/-! ## Reading the coordinates in the model fibre -/

/-- The base point of a point of `VR`. -/
def vrBase (p : ↥VR) : Work.Projective.CP 2 := p.1.1.1

/-- The fibre coordinate of a point of `VR`, read in the model fibre `ℂ²`. -/
def vrFibre (p : ↥VR) : EuclideanSpace ℂ (Fin 2) := p.1.1.2

/-- The base point of a point of `zStd∖0`. -/
def zdBaseV (q : ↥(Work.Thom.zeroComplement zStd)) : Work.Projective.CP 2 := q.1.1

/-- The fibre coordinate of a point of `zStd∖0`, read in the model fibre `ℝ²`. -/
def zdFibreV (q : ↥(Work.Thom.zeroComplement zStd)) : EuclideanSpace ℝ (Fin 2) := q.1.2

/-! ## The retraction onto `zStd∖0` and its section -/

/-- **The retraction of `VR` onto `zStd∖0`**: read the imaginary part, forget the real part. -/
noncomputable def rhoMapV : C(↥VR, ↥(Work.Thom.zeroComplement zStd)) where
  toFun p := ⟨⟨vrBase p, Work.Thom.cxImPart (vrFibre p)⟩, p.2⟩
  continuous_toFun := by
    have h1 : Continuous (fun p : ↥VR => (p.1.1 : W.TotalSpace)) :=
      (continuous_subtype_val (p := fun q : W.TotalSpace =>
          q ∈ Work.Thom.zeroComplement W)).comp
        (continuous_subtype_val (p := fun p : ↥(Work.Thom.zeroComplement W) => p ∈ VR))
    exact Continuous.subtype_mk (continuous_imPartTotal.comp h1) (fun p => p.2)

/-- A point of `zStd∖0`, included as the imaginary part of `W`, lies in `zeroComplement W`. -/
theorem etaFunV_wmem (q : ↥(Work.Thom.zeroComplement zStd)) :
    (⟨zdBaseV q, Work.Thom.cxMulI (Work.Thom.cxOfReal (zdFibreV q))⟩ : W.TotalSpace)
        ∈ Work.Thom.zeroComplement W := fun h => q.2 (by
    have h1 : Work.Thom.cxMulI (Work.Thom.cxOfReal (zdFibreV q)) = 0 := h
    have h2 := congrArg Work.Thom.cxImPart h1
    rw [Work.Thom.cxImPart_cxMulI, Work.Thom.cxRePart_cxOfReal, map_zero] at h2
    exact h2)

/-- The imaginary part of an included point of `zStd∖0` does not vanish. -/
theorem etaFunV_memVR (q : ↥(Work.Thom.zeroComplement zStd)) :
    Work.Thom.cxImPart (Work.Thom.cxMulI (Work.Thom.cxOfReal (zdFibreV q))) ≠ 0 := by
  rw [Work.Thom.cxImPart_cxMulI, Work.Thom.cxRePart_cxOfReal]
  exact q.2

/-- **The section of `rhoMapV`**: include `zStd` as the imaginary part of `W`. -/
noncomputable def etaMapV : C(↥(Work.Thom.zeroComplement zStd), ↥VR) where
  toFun q := ⟨⟨⟨zdBaseV q, Work.Thom.cxMulI (Work.Thom.cxOfReal (zdFibreV q))⟩,
      etaFunV_wmem q⟩, etaFunV_memVR q⟩
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_iotaTotal.comp continuous_subtype_val)
      (fun q => etaFunV_wmem q))
    (fun q => etaFunV_memVR q)

/-! ## The straight-line homotopy -/

/-- The fibre component of the straight-line homotopy at time `t`:
`(1-t)·v + t·(i·Im v)`. -/
noncomputable def homotopyFibreV (x : ↑unitInterval × ↥VR) : EuclideanSpace ℂ (Fin 2) :=
  (1 - (x.1 : ℝ)) • vrFibre x.2
    + (x.1 : ℝ) • Work.Thom.cxMulI (Work.Thom.cxOfReal (Work.Thom.cxImPart (vrFibre x.2)))

/-- The imaginary part of the interpolated vector is the imaginary part of the original vector. -/
theorem cxImPart_homotopyFibreV (x : ↑unitInterval × ↥VR) :
    Work.Thom.cxImPart (homotopyFibreV x) = Work.Thom.cxImPart (vrFibre x.2) := by
  rw [homotopyFibreV, map_add, map_smul, map_smul, Work.Thom.cxImPart_cxMulI,
    Work.Thom.cxRePart_cxOfReal, ← add_smul, sub_add_cancel, one_smul]

/-- The interpolated vector never vanishes. -/
theorem homotopyFibreV_ne_zero (x : ↑unitInterval × ↥VR) : homotopyFibreV x ≠ 0 := by
  intro h
  refine x.2.2 ?_
  have h2 : Work.Thom.cxImPart (homotopyFibreV x) = Work.Thom.cxImPart (vrFibre x.2) :=
    cxImPart_homotopyFibreV x
  rw [h, map_zero] at h2
  exact h2.symm

/-- The interpolated vector has non-vanishing imaginary part (the homotopy stays inside `VR`). -/
theorem cxImPart_homotopyFibreV_ne_zero (x : ↑unitInterval × ↥VR) :
    Work.Thom.cxImPart (homotopyFibreV x) ≠ 0 := by
  rw [cxImPart_homotopyFibreV]
  exact x.2.2

/-- The straight-line homotopy, as a map into the total space of `W`. -/
noncomputable def homotopyTotalV : C(↑unitInterval × ↥VR, W.TotalSpace) where
  toFun x := ⟨vrBase x.2, homotopyFibreV x⟩
  continuous_toFun := by
    have hσ₀ : Continuous (fun x : ↑unitInterval × ↥VR => (x.2.1.1 : W.TotalSpace)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    have hc₁ : Continuous (fun x : ↑unitInterval × ↥VR => 1 - (x.1 : ℝ)) :=
      continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    have hc₂ : Continuous (fun x : ↑unitInterval × ↥VR => (x.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hP : Continuous (fun x : ↑unitInterval × ↥VR =>
        (⟨vrBase x.2, Work.Thom.cxMulI (Work.Thom.cxOfReal
          (Work.Thom.cxImPart (vrFibre x.2)))⟩ : W.TotalSpace)) :=
      continuous_Qtot.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
    have hσ : Continuous (fun x : ↑unitInterval × ↥VR =>
        (⟨vrBase x.2, (1 - (x.1 : ℝ)) • vrFibre x.2⟩ : W.TotalSpace)) :=
      Work.Thom.continuous_smul_section W
        ⟨fun x : ↑unitInterval × ↥VR => x.2.1.1, hσ₀⟩
        ⟨fun x : ↑unitInterval × ↥VR => 1 - (x.1 : ℝ), hc₁⟩
    have hτ : Continuous (fun x : ↑unitInterval × ↥VR =>
        (⟨vrBase x.2, (x.1 : ℝ) • Work.Thom.cxMulI (Work.Thom.cxOfReal
          (Work.Thom.cxImPart (vrFibre x.2)))⟩ : W.TotalSpace)) :=
      Work.Thom.continuous_smul_section W
        ⟨fun x : ↑unitInterval × ↥VR => (⟨vrBase x.2, Work.Thom.cxMulI (Work.Thom.cxOfReal
          (Work.Thom.cxImPart (vrFibre x.2)))⟩ : W.TotalSpace), hP⟩
        ⟨fun x : ↑unitInterval × ↥VR => (x.1 : ℝ), hc₂⟩
    exact Work.Thom.continuous_add_section W
      ⟨fun x : ↑unitInterval × ↥VR => (⟨vrBase x.2,
        (1 - (x.1 : ℝ)) • vrFibre x.2⟩ : W.TotalSpace), hσ⟩
      ⟨fun x : ↑unitInterval × ↥VR => (⟨vrBase x.2, (x.1 : ℝ) • Work.Thom.cxMulI
        (Work.Thom.cxOfReal (Work.Thom.cxImPart (vrFibre x.2)))⟩ : W.TotalSpace), hτ⟩
      (fun _ => rfl)

/-- The straight-line homotopy, as a map into `VR`. -/
noncomputable def homotopyFunV (x : ↑unitInterval × ↥VR) : ↥VR :=
  ⟨⟨⟨vrBase x.2, homotopyFibreV x⟩, homotopyFibreV_ne_zero x⟩,
    cxImPart_homotopyFibreV_ne_zero x⟩

/-- The straight-line homotopy, as a continuous map into `VR`. -/
noncomputable def homotopyMapV : C(↑unitInterval × ↥VR, ↥VR) where
  toFun := homotopyFunV
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk homotopyTotalV.continuous (fun x => homotopyFibreV_ne_zero x))
    (fun x => cxImPart_homotopyFibreV_ne_zero x)

/-- **The straight-line homotopy from the identity of `VR` to the retraction followed by its
section.** -/
noncomputable def VRHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id ↥VR) (etaMapV.comp rhoMapV) :=
  ContinuousMap.Homotopy.mk homotopyMapV
    (by
      intro p
      apply Subtype.ext
      apply Subtype.ext
      show (⟨vrBase p, homotopyFibreV ((0 : ↑unitInterval), p)⟩ : W.TotalSpace) = p.1.1
      rw [homotopyFibreV, Set.Icc.coe_zero]
      simp only [sub_zero, one_smul, zero_smul, add_zero]
      rfl)
    (by
      intro p
      apply Subtype.ext
      apply Subtype.ext
      change (⟨vrBase p, homotopyFibreV ((1 : ↑unitInterval), p)⟩ : W.TotalSpace) =
        ↑↑((etaMapV.comp rhoMapV) p)
      rw [homotopyFibreV, Set.Icc.coe_one]
      simp only [sub_self, zero_smul, one_smul, zero_add]
      rfl)

/-! ## The homotopy equivalence and the vanishing of `H⁴` -/

/-- **`VR` is homotopy equivalent to the punctured total space of `zStd`.** -/
noncomputable def VRHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↥VR ↥(Work.Thom.zeroComplement zStd) where
  toFun := rhoMapV
  invFun := etaMapV
  left_inv := ⟨VRHomotopy.symm⟩
  right_inv := by
    have h : rhoMapV.comp etaMapV = ContinuousMap.id ↥(Work.Thom.zeroComplement zStd) := by
      apply ContinuousMap.ext
      intro q
      apply Subtype.ext
      change (⟨q.1.1, Work.Thom.cxImPart
        (Work.Thom.cxMulI (Work.Thom.cxOfReal q.1.2))⟩ : zStd.TotalSpace) = ↑q
      rw [Work.Thom.cxImPart_cxMulI, Work.Thom.cxRePart_cxOfReal]
    exact h ▸ ContinuousMap.Homotopic.refl _

/-- **`H⁴` of the piece `VR = {Im ≠ 0}` of the punctured total space of `W` vanishes.** -/
theorem zStd_VR_cohomology :
    Subsingleton (Work.Thom.Coh ℤ 4 ↥VR) := by
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv VRHomotopyEquiv 4
  exact ModuleCat.subsingleton_of_isZero
    (CategoryTheory.Limits.IsZero.of_iso isZero_cohomology_four_zStd iso)

end

end Work.ThomBordism.Grassmann
