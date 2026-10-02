import Mathlib
import Submission.Work.ThomBordism.Grassmann.UVOverlap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-!
# The piece `{ratio ∈ Reg}` is homotopy equivalent to `zeroComplement zStd`

For a region `Reg ⊆ ℂ ∖ {0}` which is star-shaped with respect to a point `κ ∈ Reg`, the piece
`uvPiece Reg = {p ∈ UR ∩ VR | uvRatio p ∈ Reg}` (see `UVOverlap.lean`) is homotopy equivalent to the
punctured total space `zeroComplement zStd` of `zStd`:

* the retraction is `p ↦ (base p, uvU p)` (the real part, which never vanishes on `UR`);
* the section sends `x = (b,u)` to the point of `W` with real part `u` and imaginary part `κ u`
  (`uvSigFun`), whose ratio is `κ`;
* the homotopy interpolates the ratio linearly, `r ↦ (1-t) r + t κ`, and keeps the real part fixed.

The membership of the interpolated points uses only `hstar` (the region is star-shaped) and
`0 ∉ Reg` (so the ratio never vanishes and the points stay in `VR`).
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

/-! ## The real and imaginary parts of a point, and of the fibre of `W` -/

/-- The real part of the fibre vector of a point of the overlap. -/
def ovUVec (p : ↥(UR ∩ VR)) : EuclideanSpace ℝ (Fin 2) := Work.Thom.cxRePart p.1.1.2

/-- The imaginary part of the fibre vector of a point of the overlap. -/
def ovVVec (p : ↥(UR ∩ VR)) : EuclideanSpace ℝ (Fin 2) := Work.Thom.cxImPart p.1.1.2

theorem uvU_eq_ccoord (p : ↥(UR ∩ VR)) : uvU p = ccoord (ovUVec p) := rfl

theorem uvV_eq_ccoord (p : ↥(UR ∩ VR)) : uvV p = ccoord (ovVVec p) := rfl

theorem ccoord_ovUVec_ne_zero (p : ↥(UR ∩ VR)) : ccoord (ovUVec p) ≠ 0 := uvU_ne_zero p

theorem ccoord_ovVVec_ne_zero (p : ↥(UR ∩ VR)) : ccoord (ovVVec p) ≠ 0 := uvV_ne_zero p

/-- The fibre coordinate of a point of `zeroComplement zStd` is nonzero. -/
theorem zcFib_ne_zero (x : ↥(Work.Thom.zeroComplement zStd)) : zcFib x ≠ 0 := x.2

/-! ## The two projections of a sum `x + i y` -/

theorem cxRePart_add_cxMulI (u w : EuclideanSpace ℝ (Fin 2)) :
    Work.Thom.cxRePart (Work.Thom.cxOfReal u + Work.Thom.cxMulI (Work.Thom.cxOfReal w)) = u := by
  rw [map_add, Work.Thom.cxRePart_cxOfReal, Work.Thom.cxRePart_cxMulI,
    Work.Thom.cxImPart_cxOfReal, neg_zero, add_zero]

theorem cxImPart_add_cxMulI (u w : EuclideanSpace ℝ (Fin 2)) :
    Work.Thom.cxImPart (Work.Thom.cxOfReal u + Work.Thom.cxMulI (Work.Thom.cxOfReal w)) = w := by
  rw [map_add, Work.Thom.cxImPart_cxOfReal, Work.Thom.cxImPart_cxMulI,
    Work.Thom.cxRePart_cxOfReal, zero_add]

/-- The fibre vector of `uvSigFun`. -/
theorem uvSigFun_snd (κ : ℂ) (x : ↥(Work.Thom.zeroComplement zStd)) :
    (uvSigFun κ x).2
      = Work.Thom.cxOfReal (zcFib x) + Work.Thom.cxMulI (Work.Thom.cxOfReal
          (κ.re • zcFib x + κ.im • Jz (zcFib x))) := rfl

/-! ## Continuity of the section at the level of total spaces -/

/-- **The section `κ` is continuous as a map into the total space of `W`.** -/
theorem continuous_uvSigFun (κ : ℂ) : Continuous (uvSigFun κ) := by
  have hcoe : Continuous (fun x : ↥(Work.Thom.zeroComplement zStd) =>
      (x.1 : zStd.TotalSpace)) := continuous_subtype_val
  -- the real part (the `η`-inclusion)
  have heta : Continuous (fun x : ↥(Work.Thom.zeroComplement zStd) =>
      (⟨zcBase x, Work.Thom.cxOfReal (zcFib x)⟩ : W.TotalSpace)) :=
    continuous_etaTotal.comp hcoe
  -- the `J`-section of `zStd`
  have hJz : Continuous (fun x : ↥(Work.Thom.zeroComplement zStd) =>
      (⟨zcBase x, Jz (zcFib x)⟩ : zStd.TotalSpace)) :=
    (continuous_totalSpaceMap_intertwine zStd zStd Jz
      (fun _ => rfl) (fun _ => rfl)
      (fun i j b v _ => (zStd_coordChange_Jz i j b v).symm)).comp hcoe
  -- the scaled identity section of `zStd`
  have hid : Continuous (fun x : ↥(Work.Thom.zeroComplement zStd) =>
      (⟨zcBase x, κ.re • zcFib x⟩ : zStd.TotalSpace)) :=
    Work.Thom.continuous_smul_section zStd
      ⟨fun x : ↥(Work.Thom.zeroComplement zStd) => (x.1 : zStd.TotalSpace),
        hcoe⟩ ⟨fun _ => κ.re, continuous_const⟩
  -- the scaled `J`-section
  have hJzs : Continuous (fun x : ↥(Work.Thom.zeroComplement zStd) =>
      (⟨zcBase x, κ.im • Jz (zcFib x)⟩ : zStd.TotalSpace)) :=
    Work.Thom.continuous_smul_section zStd
      ⟨fun x : ↥(Work.Thom.zeroComplement zStd) =>
        (⟨zcBase x, Jz (zcFib x)⟩ : zStd.TotalSpace), hJz⟩
      ⟨fun _ => κ.im, continuous_const⟩
  -- their sum
  have hsum : Continuous (fun x : ↥(Work.Thom.zeroComplement zStd) =>
      (⟨zcBase x, κ.re • zcFib x + κ.im • Jz (zcFib x)⟩ : zStd.TotalSpace)) :=
    Work.Thom.continuous_add_section zStd
      ⟨_, hid⟩ ⟨_, hJzs⟩ (fun _ => rfl)
  -- the imaginary part of the point of `W`
  have him : Continuous (fun x : ↥(Work.Thom.zeroComplement zStd) =>
      (⟨zcBase x, Work.Thom.cxMulI (Work.Thom.cxOfReal
        (κ.re • zcFib x + κ.im • Jz (zcFib x)))⟩ : W.TotalSpace)) :=
    continuous_iotaTotal.comp hsum
  refine (Work.Thom.continuous_add_section W ⟨_, heta⟩ ⟨_, him⟩ (fun _ => rfl)).congr ?_
  intro x
  apply Bundle.TotalSpace.ext
  · rfl
  · exact heq_of_eq rfl

/-! ## The section lands in the piece -/

theorem uvSig_snd_eq (κ : ℂ) (x : ↥(Work.Thom.zeroComplement zStd)) :
    (uvSigFun κ x).2 = Work.Thom.cxOfReal (zcFib x) + Work.Thom.cxMulI
      (Work.Thom.cxOfReal (κ.re • zcFib x + κ.im • Jz (zcFib x))) := rfl

theorem uvSigFun_mem_zeroComplement (κ : ℂ) (x : ↥(Work.Thom.zeroComplement zStd)) :
    uvSigFun κ x ∈ Work.Thom.zeroComplement W := by
  change (⟨zcBase x, Work.Thom.cxOfReal (zcFib x) + Work.Thom.cxMulI
    (Work.Thom.cxOfReal (κ.re • zcFib x + κ.im • Jz (zcFib x)))⟩ : W.TotalSpace)
      ∈ Work.Thom.zeroComplement W
  intro h
  have h2 : Work.Thom.cxOfReal (zcFib x) + Work.Thom.cxMulI
      (Work.Thom.cxOfReal (κ.re • zcFib x + κ.im • Jz (zcFib x))) = 0 := h
  have h1 : Work.Thom.cxRePart (Work.Thom.cxOfReal (zcFib x) + Work.Thom.cxMulI
      (Work.Thom.cxOfReal (κ.re • zcFib x + κ.im • Jz (zcFib x)))) = 0 := by
    rw [h2, map_zero]
  rw [cxRePart_add_cxMulI] at h1
  exact zcFib_ne_zero x h1

theorem uvSig_re_ne_zero (κ : ℂ) (x : ↥(Work.Thom.zeroComplement zStd)) :
    Work.Thom.cxRePart (uvSigFun κ x).2 ≠ 0 := by
  change Work.Thom.cxRePart (Work.Thom.cxOfReal (zcFib x) + Work.Thom.cxMulI
      (Work.Thom.cxOfReal (κ.re • zcFib x + κ.im • Jz (zcFib x)))) ≠ 0
  rw [cxRePart_add_cxMulI]
  exact zcFib_ne_zero x

theorem uvSig_im_ne_zero (κ : ℂ) (hκ0 : κ ≠ 0) (x : ↥(Work.Thom.zeroComplement zStd)) :
    Work.Thom.cxImPart (uvSigFun κ x).2 ≠ 0 := by
  change Work.Thom.cxImPart (Work.Thom.cxOfReal (zcFib x) + Work.Thom.cxMulI
      (Work.Thom.cxOfReal (κ.re • zcFib x + κ.im • Jz (zcFib x)))) ≠ 0
  rw [cxImPart_add_cxMulI]
  rw [← ccoord_ne_zero_iff, ccoord_uvSigFun]
  exact mul_ne_zero hκ0 ((ccoord_ne_zero_iff _).mpr (zcFib_ne_zero x))

/-- The section as a point of the overlap. -/
def uvSigPt (κ : ℂ) (hκ0 : κ ≠ 0) (x : ↥(Work.Thom.zeroComplement zStd)) : ↥(UR ∩ VR) :=
  ⟨⟨uvSigFun κ x, uvSigFun_mem_zeroComplement κ x⟩,
    ⟨uvSig_re_ne_zero κ x, uvSig_im_ne_zero κ hκ0 x⟩⟩

/-- The ratio of the section is `κ`. -/
theorem uvRatio_uvSigPt (κ : ℂ) (hκ0 : κ ≠ 0) (x : ↥(Work.Thom.zeroComplement zStd)) :
    uvRatio (uvSigPt κ hκ0 x) = κ := by
  have h3 : uvV (uvSigPt κ hκ0 x) = κ * ccoord (zcFib x) := by
    change ccoord (Work.Thom.cxImPart (⟨zcBase x, Work.Thom.cxOfReal (zcFib x)
      + Work.Thom.cxMulI (Work.Thom.cxOfReal (κ.re • zcFib x + κ.im • Jz (zcFib x)))⟩
        : W.TotalSpace).2) = κ * ccoord (zcFib x)
    rw [cxImPart_add_cxMulI, ccoord_uvSigFun]
  have h4 : uvU (uvSigPt κ hκ0 x) = ccoord (zcFib x) := by
    change ccoord (Work.Thom.cxRePart (⟨zcBase x, Work.Thom.cxOfReal (zcFib x)
      + Work.Thom.cxMulI (Work.Thom.cxOfReal (κ.re • zcFib x + κ.im • Jz (zcFib x)))⟩
        : W.TotalSpace).2) = ccoord (zcFib x)
    rw [cxRePart_add_cxMulI]
  rw [uvRatio, h3, h4]
  exact mul_div_cancel_right₀ κ ((ccoord_ne_zero_iff _).mpr (zcFib_ne_zero x))

/-! ## The retraction and the section -/

/-- The W-point of a point of the overlap. -/
def ovW (p : ↥(UR ∩ VR)) : W.TotalSpace := p.1.1

/-- The base point of a point of the overlap. -/
def ovBase (p : ↥(UR ∩ VR)) : Work.Projective.CP 2 := p.1.1.1

/-- The model-fibre vector of a point of the overlap. -/
def ovUW (p : ↥(UR ∩ VR)) : EuclideanSpace ℂ (Fin 2) := p.1.1.2

theorem ovUR (p : ↥(UR ∩ VR)) : Work.Thom.cxRePart p.1.1.2 ≠ 0 := p.2.1

/-- **The retraction** of a piece of the overlap onto `zeroComplement zStd`, `p ↦ (base, Re p)`. -/
noncomputable def uvRetract (Reg : Set ℂ) :
    C(↥(uvPiece Reg), ↥(Work.Thom.zeroComplement zStd)) where
  toFun p := ⟨rhoTotal (ovW p.1), ovUR p.1⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_rhoTotal.comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_subtype_val))) (fun p => ovUR p.1)

/-- **The section** whose ratio is `κ`. -/
noncomputable def uvSection (Reg : Set ℂ) (κ : ℂ) (hκ0 : κ ≠ 0) (hκ : κ ∈ Reg) :
    C(↥(Work.Thom.zeroComplement zStd), ↥(uvPiece Reg)) where
  toFun x := ⟨uvSigPt κ hκ0 x, by
    change uvRatio (uvSigPt κ hκ0 x) ∈ Reg
    rw [uvRatio_uvSigPt κ hκ0 x]
    exact hκ⟩
  continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_uvSigFun κ)
      (fun x => uvSigFun_mem_zeroComplement κ x))
      (fun x => ⟨uvSig_re_ne_zero κ x, uvSig_im_ne_zero κ hκ0 x⟩))
    (fun x => by
      change uvRatio (uvSigPt κ hκ0 x) ∈ Reg
      rw [uvRatio_uvSigPt κ hκ0 x]
      exact hκ)

theorem uvSig_cxRePart (κ : ℂ) (x : ↥(Work.Thom.zeroComplement zStd)) :
    Work.Thom.cxRePart (uvSigFun κ x).2 = zcFib x := by
  change Work.Thom.cxRePart (Work.Thom.cxOfReal (zcFib x) + Work.Thom.cxMulI
      (Work.Thom.cxOfReal (κ.re • zcFib x + κ.im • Jz (zcFib x)))) = zcFib x
  exact cxRePart_add_cxMulI _ _

theorem uvRetract_uvSection (Reg : Set ℂ) (κ : ℂ) (hκ0 : κ ≠ 0) (hκ : κ ∈ Reg)
    (x : ↥(Work.Thom.zeroComplement zStd)) :
    uvRetract Reg (uvSection Reg κ hκ0 hκ x) = x := by
  apply Subtype.ext
  apply Bundle.TotalSpace.ext
  · rfl
  · exact heq_of_eq (uvSig_cxRePart κ x)

/-! ## The straight-line homotopy in the ratio -/

/-- The fibre vector of the homotopy at time `t`. -/
def uvHomVec (Reg : Set ℂ) (κ : ℂ) (z : ↑unitInterval × ↥(uvPiece Reg)) :
    EuclideanSpace ℂ (Fin 2) :=
  Work.Thom.cxOfReal (ovUVec z.2.1) + Work.Thom.cxMulI (Work.Thom.cxOfReal
    ((1 - (z.1 : ℝ)) • ovVVec z.2.1 + (z.1 : ℝ) •
      (κ.re • ovUVec z.2.1 + κ.im • Jz (ovUVec z.2.1))))

/-- The imaginary part of the homotopy fibre. -/
def uvHomImVec (Reg : Set ℂ) (κ : ℂ) (z : ↑unitInterval × ↥(uvPiece Reg)) :
    EuclideanSpace ℝ (Fin 2) :=
  (1 - (z.1 : ℝ)) • ovVVec z.2.1 + (z.1 : ℝ) •
    (κ.re • ovUVec z.2.1 + κ.im • Jz (ovUVec z.2.1))

theorem uvHomVec_re (Reg : Set ℂ) (κ : ℂ) (z : ↑unitInterval × ↥(uvPiece Reg)) :
    Work.Thom.cxRePart (uvHomVec Reg κ z) = ovUVec z.2.1 :=
  cxRePart_add_cxMulI _ _

theorem uvHomVec_im (Reg : Set ℂ) (κ : ℂ) (z : ↑unitInterval × ↥(uvPiece Reg)) :
    Work.Thom.cxImPart (uvHomVec Reg κ z) = uvHomImVec Reg κ z :=
  cxImPart_add_cxMulI _ _

/-- The ratio of the interpolated point is the linear interpolation of the ratios. -/
theorem ccoord_uvHomImVec (Reg : Set ℂ) (κ : ℂ) (z : ↑unitInterval × ↥(uvPiece Reg)) :
    ccoord (uvHomImVec Reg κ z) = ccoord (ovUVec z.2.1) *
      ((1 - (z.1 : ℝ)) * uvRatio z.2.1 + (z.1 : ℝ) * κ) := by
  have hJz : ccoord (κ.re • ovUVec z.2.1 + κ.im • Jz (ovUVec z.2.1))
      = κ * ccoord (ovUVec z.2.1) := by
    rw [ccoord_smul_add_Jz, Complex.re_add_im]
  have hne : ccoord (ovUVec z.2.1) ≠ 0 := ccoord_ovUVec_ne_zero z.2.1
  rw [uvHomImVec, ccoord_add, ccoord_smul, ccoord_smul, hJz]
  rw [uvRatio, uvV_eq_ccoord, uvU_eq_ccoord]
  field_simp
  push_cast
  ring

theorem uvHomImVec_ne_zero (Reg : Set ℂ) (κ : ℂ) (h0 : (0 : ℂ) ∉ Reg)
    (hstar : ∀ r ∈ Reg, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) * r + t * κ ∈ Reg)
    (z : ↑unitInterval × ↥(uvPiece Reg)) : uvHomImVec Reg κ z ≠ 0 := by
  intro h
  have h1 := ccoord_uvHomImVec Reg κ z
  rw [h, ccoord_zero] at h1
  rcases mul_eq_zero.mp h1.symm with h2 | h2
  · exact ccoord_ovUVec_ne_zero z.2.1 h2
  · exact h0 (h2 ▸ hstar (uvRatio z.2.1) (mem_uvPiece.mp z.2.2) (z.1 : ℝ)
      z.1.2.1 z.1.2.2)

theorem uvHomVec_ne_zero (Reg : Set ℂ) (κ : ℂ) (z : ↑unitInterval × ↥(uvPiece Reg)) :
    uvHomVec Reg κ z ≠ 0 := by
  intro h
  have h1 : Work.Thom.cxRePart (uvHomVec Reg κ z) = 0 := by rw [h, map_zero]
  rw [uvHomVec_re] at h1
  exact ccoord_ovUVec_ne_zero z.2.1 (by rw [h1, ccoord_zero])

/-- The interpolated point of the overlap. -/
def uvHomPt (Reg : Set ℂ) (κ : ℂ) (h0 : (0 : ℂ) ∉ Reg)
    (hstar : ∀ r ∈ Reg, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) * r + t * κ ∈ Reg)
    (z : ↑unitInterval × ↥(uvPiece Reg)) : ↥(UR ∩ VR) :=
  ⟨⟨⟨ovBase z.2.1, uvHomVec Reg κ z⟩, uvHomVec_ne_zero Reg κ z⟩,
    ⟨by
      change Work.Thom.cxRePart (uvHomVec Reg κ z) ≠ 0
      rw [uvHomVec_re]
      exact fun hc => ccoord_ovUVec_ne_zero z.2.1 (by rw [hc, ccoord_zero]),
     by
      change Work.Thom.cxImPart (uvHomVec Reg κ z) ≠ 0
      rw [uvHomVec_im]
      exact uvHomImVec_ne_zero Reg κ h0 hstar z⟩⟩

theorem uvHomPt_ratio (Reg : Set ℂ) (κ : ℂ) (h0 : (0 : ℂ) ∉ Reg)
    (hstar : ∀ r ∈ Reg, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) * r + t * κ ∈ Reg)
    (z : ↑unitInterval × ↥(uvPiece Reg)) :
    uvRatio (uvHomPt Reg κ h0 hstar z)
      = (1 - (z.1 : ℝ)) * uvRatio z.2.1 + (z.1 : ℝ) * κ := by
  have hnum : uvV (uvHomPt Reg κ h0 hstar z) = ccoord (uvHomImVec Reg κ z) := by
    change ccoord (Work.Thom.cxImPart (uvHomVec Reg κ z)) = _
    rw [uvHomVec_im]
  have hden : uvU (uvHomPt Reg κ h0 hstar z) = ccoord (ovUVec z.2.1) := by
    change ccoord (Work.Thom.cxRePart (uvHomVec Reg κ z)) = _
    rw [uvHomVec_re]
  rw [uvRatio, hnum, hden, ccoord_uvHomImVec]
  rw [mul_comm (ccoord (ovUVec z.2.1))]
  exact mul_div_cancel_right₀ _ (ccoord_ovUVec_ne_zero z.2.1)

theorem uvHomPt_mem (Reg : Set ℂ) (κ : ℂ) (h0 : (0 : ℂ) ∉ Reg)
    (hstar : ∀ r ∈ Reg, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) * r + t * κ ∈ Reg)
    (z : ↑unitInterval × ↥(uvPiece Reg)) :
    uvRatio (uvHomPt Reg κ h0 hstar z) ∈ Reg := by
  rw [uvHomPt_ratio]
  exact hstar _ z.2.2 _ z.1.2.1 z.1.2.2

/-! ## Continuity and the homotopy -/

theorem continuous_ovW (Reg : Set ℂ) :
    Continuous (fun z : ↑unitInterval × ↥(uvPiece Reg) => (ovW z.2.1 : W.TotalSpace)) :=
  continuous_subtype_val.comp (continuous_subtype_val.comp
    (continuous_subtype_val.comp continuous_snd))

/-- The real-part contribution to the homotopy. -/
noncomputable def uvHomU (Reg : Set ℂ) :
    C(↑unitInterval × ↥(uvPiece Reg), W.TotalSpace) where
  toFun z := ⟨(ovW z.2.1).1, Work.Thom.cxOfReal (ovUVec z.2.1)⟩
  continuous_toFun := continuous_etaTotal.comp (continuous_rhoTotal.comp (continuous_ovW Reg))

/-- The imaginary-part contribution to the homotopy. -/
noncomputable def uvHomV (Reg : Set ℂ) :
    C(↑unitInterval × ↥(uvPiece Reg), W.TotalSpace) where
  toFun z := ⟨(ovW z.2.1).1, Work.Thom.cxMulI (Work.Thom.cxOfReal (ovVVec z.2.1))⟩
  continuous_toFun := continuous_iotaTotal.comp (continuous_imPartTotal.comp (continuous_ovW Reg))

/-- The rescaled imaginary-part contribution. -/
noncomputable def uvHomVs (Reg : Set ℂ) :
    C(↑unitInterval × ↥(uvPiece Reg), W.TotalSpace) where
  toFun z := ⟨(ovW z.2.1).1, (1 - (z.1 : ℝ)) • Work.Thom.cxMulI
    (Work.Thom.cxOfReal (ovVVec z.2.1))⟩
  continuous_toFun := Work.Thom.continuous_smul_section W (uvHomV Reg)
    ⟨fun z => 1 - (z.1 : ℝ),
      continuous_const.sub (continuous_subtype_val.comp continuous_fst)⟩

/-- The `κ`-contribution to the homotopy. -/
noncomputable def uvHomK (Reg : Set ℂ) (κ : ℂ) :
    C(↑unitInterval × ↥(uvPiece Reg), W.TotalSpace) where
  toFun z := ⟨(ovW z.2.1).1, (z.1 : ℝ) • Work.Thom.cxMulI (Work.Thom.cxOfReal
    (κ.re • ovUVec z.2.1 + κ.im • Jz (ovUVec z.2.1)))⟩
  continuous_toFun := by
    have hproj : Continuous (fun z : ↑unitInterval × ↥(uvPiece Reg) =>
        (ovW z.2.1 : W.TotalSpace)) := continuous_ovW Reg
    have hJzmap : Continuous (fun z : ↑unitInterval × ↥(uvPiece Reg) =>
        (⟨(ovW z.2.1).1, Jz (ovUVec z.2.1)⟩ : zStd.TotalSpace)) :=
      (continuous_totalSpaceMap_intertwine zStd zStd Jz (fun _ => rfl) (fun _ => rfl)
        (fun i j b v _ => (zStd_coordChange_Jz i j b v).symm)).comp
          (continuous_rhoTotal.comp hproj)
    have hkz : Continuous (fun z : ↑unitInterval × ↥(uvPiece Reg) =>
        (⟨(ovW z.2.1).1, κ.re • ovUVec z.2.1 + κ.im • Jz (ovUVec z.2.1)⟩ : zStd.TotalSpace)) :=
      Work.Thom.continuous_add_section zStd
        ⟨_, Work.Thom.continuous_smul_section zStd
          ⟨fun z => rhoTotal (ovW z.2.1), continuous_rhoTotal.comp hproj⟩
          ⟨fun _ => κ.re, continuous_const⟩⟩
        ⟨_, Work.Thom.continuous_smul_section zStd ⟨_, hJzmap⟩
          ⟨fun _ => κ.im, continuous_const⟩⟩
        (fun _ => rfl)
    exact Work.Thom.continuous_smul_section W ⟨_, continuous_iotaTotal.comp hkz⟩
      ⟨fun z => (z.1 : ℝ), continuous_subtype_val.comp continuous_fst⟩

/-- **The pointwise sum of two continuous points of `W` over the same base map**, in the
explicit form in which the two fibre vectors are given by elements of the model fibre. -/
theorem continuous_addPoint {Y : Type} [TopologicalSpace Y] {b : Y → Work.Projective.CP 2}
    (f g : Y → EuclideanSpace ℂ (Fin 2))
    (hf : Continuous (fun y => (⟨b y, f y⟩ : W.TotalSpace)))
    (hg : Continuous (fun y => (⟨b y, g y⟩ : W.TotalSpace))) :
    Continuous (fun y => (⟨b y, f y + g y⟩ : W.TotalSpace)) := by
  have h : Continuous (fun y => (⟨(⟨b y, f y⟩ : W.TotalSpace).1,
      (show EuclideanSpace ℂ (Fin 2) from (⟨b y, f y⟩ : W.TotalSpace).2)
        + (show EuclideanSpace ℂ (Fin 2) from (⟨b y, g y⟩ : W.TotalSpace).2)⟩
      : W.TotalSpace)) :=
    Work.Thom.continuous_add_section (Y := Y) (F := EuclideanSpace ℂ (Fin 2)) (ι := Fin 3) W
      ⟨fun y => (⟨b y, f y⟩ : W.TotalSpace), hf⟩
      ⟨fun y => (⟨b y, g y⟩ : W.TotalSpace), hg⟩ (fun y => rfl)
  refine h.congr ?_
  intro y
  exact rfl

/-- **The total space map of the homotopy** (with the fibre vector `uvHomVec`). -/
theorem continuous_uvHomTotal (Reg : Set ℂ) (κ : ℂ) :
    Continuous (fun z : ↑unitInterval × ↥(uvPiece Reg) =>
      (⟨(ovW z.2.1).1, uvHomVec Reg κ z⟩ : W.TotalSpace)) := by
  have hVsC : Continuous (fun z : ↑unitInterval × ↥(uvPiece Reg) =>
      (⟨(ovW z.2.1).1, (1 - (z.1 : ℝ)) • Work.Thom.cxMulI (Work.Thom.cxOfReal (ovVVec z.2.1))⟩
        : W.TotalSpace)) := (uvHomVs Reg).continuous
  have hKC : Continuous (fun z : ↑unitInterval × ↥(uvPiece Reg) =>
      (⟨(ovW z.2.1).1, (z.1 : ℝ) • Work.Thom.cxMulI (Work.Thom.cxOfReal
        (κ.re • ovUVec z.2.1 + κ.im • Jz (ovUVec z.2.1)))⟩ : W.TotalSpace)) :=
    (uvHomK Reg κ).continuous
  have hUC : Continuous (fun z : ↑unitInterval × ↥(uvPiece Reg) =>
      (⟨(ovW z.2.1).1, Work.Thom.cxOfReal (ovUVec z.2.1)⟩ : W.TotalSpace)) :=
    (uvHomU Reg).continuous
  have hinner := continuous_addPoint (b := fun z : ↑unitInterval × ↥(uvPiece Reg) => (ovW z.2.1).1)
    (f := fun z => (1 - (z.1 : ℝ)) • Work.Thom.cxMulI (Work.Thom.cxOfReal (ovVVec z.2.1)))
    (g := fun z => (z.1 : ℝ) • Work.Thom.cxMulI (Work.Thom.cxOfReal
      (κ.re • ovUVec z.2.1 + κ.im • Jz (ovUVec z.2.1)))) hVsC hKC
  have htot := continuous_addPoint (b := fun z : ↑unitInterval × ↥(uvPiece Reg) => (ovW z.2.1).1)
    (f := fun z => Work.Thom.cxOfReal (ovUVec z.2.1))
    (g := fun z => (1 - (z.1 : ℝ)) • Work.Thom.cxMulI (Work.Thom.cxOfReal (ovVVec z.2.1))
      + (z.1 : ℝ) • Work.Thom.cxMulI (Work.Thom.cxOfReal
        (κ.re • ovUVec z.2.1 + κ.im • Jz (ovUVec z.2.1)))) hUC hinner
  refine htot.congr ?_
  intro z
  apply Bundle.TotalSpace.ext
  · rfl
  · refine heq_of_eq ?_
    simp only [uvHomVec, map_add, map_smul]

/-- The homotopy, as a map of total spaces. -/
noncomputable def uvHomTotal (Reg : Set ℂ) (κ : ℂ) :
    C(↑unitInterval × ↥(uvPiece Reg), W.TotalSpace) where
  toFun z := ⟨(ovW z.2.1).1, uvHomVec Reg κ z⟩
  continuous_toFun := continuous_uvHomTotal Reg κ

/-- The homotopy, as a map into the piece. -/
noncomputable def uvHomPtFun (Reg : Set ℂ) (κ : ℂ) (h0 : (0 : ℂ) ∉ Reg)
    (hstar : ∀ r ∈ Reg, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) * r + t * κ ∈ Reg) :
    C(↑unitInterval × ↥(uvPiece Reg), ↥(uvPiece Reg)) where
  toFun z := ⟨uvHomPt Reg κ h0 hstar z, uvHomPt_mem Reg κ h0 hstar z⟩
  continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk (Continuous.subtype_mk
    (continuous_uvHomTotal Reg κ) (fun z => uvHomVec_ne_zero Reg κ z))
    (fun z => ⟨by
        change Work.Thom.cxRePart (uvHomVec Reg κ z) ≠ 0
        rw [uvHomVec_re]
        exact fun hc => ccoord_ovUVec_ne_zero z.2.1 (by rw [hc, ccoord_zero]),
      by
        change Work.Thom.cxImPart (uvHomVec Reg κ z) ≠ 0
        rw [uvHomVec_im]
        exact uvHomImVec_ne_zero Reg κ h0 hstar z⟩))
    (fun z => uvHomPt_mem Reg κ h0 hstar z)

theorem uvHomPtFun_zero (Reg : Set ℂ) (κ : ℂ) (h0 : (0 : ℂ) ∉ Reg)
    (hstar : ∀ r ∈ Reg, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) * r + t * κ ∈ Reg)
    (p : ↥(uvPiece Reg)) : uvHomPtFun Reg κ h0 hstar (0, p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Bundle.TotalSpace.ext
  · rfl
  · refine heq_of_eq ?_
    show Work.Thom.cxOfReal (ovUVec p.1) + Work.Thom.cxMulI
        (Work.Thom.cxOfReal ((1 - ((0 : ↑unitInterval) : ℝ)) • ovVVec p.1
          + ((0 : ↑unitInterval) : ℝ) • (κ.re • ovUVec p.1 + κ.im • Jz (ovUVec p.1))))
      = (ovW p.1).2
    rw [show ((0 : ↑unitInterval) : ℝ) = 0 from rfl, sub_zero, one_smul, zero_smul, add_zero]
    rw [← Work.Thom.cxOfReal_cxRePart_add_cxMulI_cxImPart (ovW p.1).2]
    rfl

theorem uvHomPtFun_one (Reg : Set ℂ) (κ : ℂ) (hκ0 : κ ≠ 0) (hκ : κ ∈ Reg)
    (h0 : (0 : ℂ) ∉ Reg)
    (hstar : ∀ r ∈ Reg, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) * r + t * κ ∈ Reg)
    (p : ↥(uvPiece Reg)) :
    uvHomPtFun Reg κ h0 hstar (1, p) = uvSection Reg κ hκ0 hκ (uvRetract Reg p) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Bundle.TotalSpace.ext
  · rfl
  · refine heq_of_eq ?_
    show Work.Thom.cxOfReal (ovUVec p.1) + Work.Thom.cxMulI
        (Work.Thom.cxOfReal ((1 - ((1 : ↑unitInterval) : ℝ)) • ovVVec p.1
          + ((1 : ↑unitInterval) : ℝ) • (κ.re • ovUVec p.1 + κ.im • Jz (ovUVec p.1))))
      = Work.Thom.cxOfReal (ovUVec p.1) + Work.Thom.cxMulI
          (Work.Thom.cxOfReal (κ.re • ovUVec p.1 + κ.im • Jz (ovUVec p.1)))
    rw [show ((1 : ↑unitInterval) : ℝ) = 1 from rfl, sub_self, zero_smul, one_smul, zero_add]

/-- **The piece `{ratio ∈ Reg}` is homotopy equivalent to `zeroComplement zStd`.** -/
theorem uvPieceHomotopyEquiv (Reg : Set ℂ) (κ : ℂ) (hκ : κ ∈ Reg) (h0 : (0 : ℂ) ∉ Reg)
    (hstar : ∀ r ∈ Reg, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) * r + t * κ ∈ Reg) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(uvPiece Reg) ↥(Work.Thom.zeroComplement zStd)) := by
  have hκ0 : κ ≠ 0 := fun hc => h0 (hc ▸ hκ)
  refine ⟨{ toFun := uvRetract Reg
            invFun := uvSection Reg κ hκ0 hκ
            left_inv := ⟨?_⟩
            right_inv := ?_ }⟩
  · exact (ContinuousMap.Homotopy.mk (uvHomPtFun Reg κ h0 hstar)
      (fun p => uvHomPtFun_zero Reg κ h0 hstar p)
      (fun p => uvHomPtFun_one Reg κ hκ0 hκ h0 hstar p)).symm
  · have h : (uvRetract Reg).comp (uvSection Reg κ hκ0 hκ)
        = ContinuousMap.id ↥(Work.Thom.zeroComplement zStd) := by
      apply ContinuousMap.ext
      intro x
      exact uvRetract_uvSection Reg κ hκ0 hκ x
    exact h ▸ ContinuousMap.Homotopic.refl _

end

end Work.ThomBordism.Grassmann
