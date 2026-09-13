import Submission.Grassmann.HybridLift
import Submission.Grassmann.Assembly4
import Submission.Commons.LinearAlgebra.Matrix.plLE_mul_mul_iff_of_inj_surj
import Submission.Commons.LinearAlgebra.Matrix.exists_mul_of_ker_eq
import Submission.Commons.LinearAlgebra.Matrix.exists_mul_of_range_eq_inj

/-!
# §8 of arXiv:2209.04243: the role-space form of the switching-roles multiplier

The switching-roles summand of `Assembly3`/`Assembly4` carries the multiplier
`PComb t p.1 p.2 Z = PTranspA t p.1 p.2 (charMat t.1 t.2.1 Z) ∧ PInA t p.1 p.2 Z`, i.e. the
`plLE`-condition between the *compressions* of the big-space maps to the `(p.1,p.2)`-coordinates.

The paper's right-hand side of `prop:switching the roles between the derivatives` instead uses
`D_{X(W₃,V/V₃)}`, an `X`-derivative of the **role space** `L(V/V₃, W₃)`.  This file shows that the
two agree: the `plLE`-condition of `PTranspA` is, up to an injective left factor and a surjective
right factor (both supplied by the change of coordinates `(Qp p.1 * Qp t.1)` vs `Qp (liftV t.1 p.1)`
and `Ip t.2.1 * Ip p.2` vs `Ip (liftW t.2.1 p.2)`), the `plLE`-condition
`plLE X' (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) Z)` in the role space, where
`X' = charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X?` and `X?` is any big-space matrix realising the
coordinate matrix `XtOf t.1 t.2.1 t.2.2` of the triple's map.

The existence of `X?` is `exists_bigMat`/`bigMat` below (a lift of the linear map `t.2.2` through
the quotient map `mkQ t.1` on the subspace `W₂`); the change of coordinates is
`exists_mul_of_ker_eq` / `exists_mul_of_range_eq_inj` (commons).
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 200000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## The lifted pair of the switching-roles summand -/

/-- `liftV (VrOf t) (pV t p) = p.1 ⊔ VrOf t`. -/
theorem liftV_pV (t : Triple m n) (p : QPair m n t) :
    liftV (VrOf t) (pV t p) = p.1 ⊔ VrOf t := by
  rw [pV, liftV_Vco, sup_assoc, sup_idem]

/-- `liftW (WrOf t) (pW t p) = p.2 ⊓ WrOf t`. -/
theorem liftW_pW (t : Triple m n) (p : QPair m n t) :
    liftW (WrOf t) (pW t p) = p.2 ⊓ WrOf t := by
  rw [pW, liftW_Wco, inf_assoc, inf_idem]

/-! ## The big-space lift of the triple's coordinate matrix -/

/-- **The big-space matrix realising the triple's coordinate matrix.**  For every triple
`t = (V₂,W₂,X)` there is a linear map `X? : W → V` whose compression to `W₂` followed by the
quotient map onto `V/V₂` is precisely `t.2.2`. -/
theorem exists_bigMat (t : Triple m n) :
    ∃ X : Matrix (Fin n) (Fin m) 𝔽₂, charMat t.1 t.2.1 X = XtOf t.1 t.2.1 t.2.2 := by
  classical
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective (Qp t.1).mulVecLin (range_Qp t.1)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective t.2.1.subtype
    (Submodule.ker_subtype t.2.1)
  set cr : (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂) →ₗ[𝔽₂] ↥t.2.1 :=
    LinearMap.codRestrict t.2.1 (Ip t.2.1).mulVecLin (fun x => Ip_mem t.2.1 x) with hcrdef
  set Xraw : (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂) →ₗ[𝔽₂]
      (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂) :=
    (Qe t.1).toLinearMap.comp (t.2.2.comp cr) with hXrawdef
  set Xlin : (Fin m → 𝔽₂) →ₗ[𝔽₂] (Fin n → 𝔽₂) :=
    σ.comp ((Qe t.1).toLinearMap.comp (t.2.2.comp π)) with hXlindef
  refine ⟨LinearMap.toMatrix' Xlin, ?_⟩
  have hIp : ∀ x, (Ip t.2.1).mulVecLin x = t.2.1.subtype (cr x) := fun x => rfl
  have hπsub : ∀ x : ↥t.2.1, π (t.2.1.subtype x) = x := fun x => by
    have := congrArg (fun (g : ↥t.2.1 →ₗ[𝔽₂] ↥t.2.1) => g x) hπ
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using this
  have hπcr : ∀ y, π ((Ip t.2.1).mulVecLin y) = cr y := fun y => by
    rw [hIp y]; exact hπsub _
  have hσ' : ∀ z, (Qp t.1).mulVecLin (σ z) = z := fun z => by
    have := congrArg (fun (g : (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂) →ₗ[𝔽₂]
      (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂)) => g z) hσ
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using this
  have hXtOf : XtOf t.1 t.2.1 t.2.2 = LinearMap.toMatrix' Xraw := rfl
  have htm : (LinearMap.toMatrix' Xlin).mulVecLin = Xlin := by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  have hXt : (XtOf t.1 t.2.1 t.2.2).mulVecLin = Xraw := by
    rw [hXtOf, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  have hkey : (Qp t.1).mulVecLin.comp (Xlin.comp (Ip t.2.1).mulVecLin) = Xraw := by
    apply LinearMap.ext
    intro y
    simp only [Xlin, Xraw, LinearMap.comp_apply]
    rw [hπcr y, hσ']
  have hlin : (charMat t.1 t.2.1 (LinearMap.toMatrix' Xlin)).mulVecLin
      = (XtOf t.1 t.2.1 t.2.2).mulVecLin := by
    rw [charMat, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.comp_assoc, htm, hkey, hXt]
  have h1 : charMat t.1 t.2.1 (LinearMap.toMatrix' Xlin)
      = LinearMap.toMatrix' ((charMat t.1 t.2.1 (LinearMap.toMatrix' Xlin)).mulVecLin) :=
    (LinearMap.toMatrix'_toLin' _).symm
  have h2 : LinearMap.toMatrix' ((XtOf t.1 t.2.1 t.2.2).mulVecLin) = XtOf t.1 t.2.1 t.2.2 :=
    LinearMap.toMatrix'_toLin' _
  rw [h1, hlin, h2]

/-- A choice of the big-space matrix realising the triple's coordinate matrix. -/
noncomputable def bigMat (t : Triple m n) : Matrix (Fin n) (Fin m) 𝔽₂ :=
  Classical.choose (exists_bigMat t)

/-- The defining property of `bigMat`. -/
theorem charMat_bigMat (t : Triple m n) :
    charMat t.1 t.2.1 (bigMat t) = XtOf t.1 t.2.1 t.2.2 :=
  Classical.choose_spec (exists_bigMat t)

/-! ## The two changes of coordinates of the switching-roles summand -/

/-- The `V`-side change of coordinates: `Qp p.1 * Qp t.1` and `Qp (liftV t.1 p.1)` are surjective
maps with the same kernel, so they differ by an injective left factor. -/
theorem ker_Qp_mul_Qp (t : Triple m n) (p : QPair m n t) :
    LinearMap.ker ((Qp p.1 * Qp t.1)).mulVecLin = liftV t.1 p.1 := by
  rw [Matrix.mulVecLin_mul, LinearMap.ker_comp, ker_Qp]

/-- The `W`-side change of coordinates: `Ip t.2.1 * Ip p.2` and `Ip (liftW t.2.1 p.2)` are
injective maps with the same range, so they differ by a surjective right factor. -/
theorem range_Ip_mul_Ip (t : Triple m n) (p : QPair m n t) :
    LinearMap.range ((Ip t.2.1 * Ip p.2)).mulVecLin = liftW t.2.1 p.2 := by
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp, range_Ip, liftW]

/-! ## The role-space form of `PTranspA` -/

/-- **The coordinate change of the switching-roles summand.**  The compression of the triple's map
to the `(p.1,p.2)`-coordinates is the conjugate (by the injective `M` and the surjective `S`) of the
role-space matrix `charMat V₃ W₃ X`. -/
theorem charMat_comp_eq (t : Triple m n) (p : QPair m n t) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hX : charMat t.1 t.2.1 X = XtOf t.1 t.2.1 t.2.2)
    (M : Matrix (Fin ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ p.1))
      (Fin (n - Module.finrank 𝔽₂ (liftV t.1 p.1))) 𝔽₂)
    (S : Matrix (Fin (Module.finrank 𝔽₂ (liftW t.2.1 p.2)))
      (Fin (Module.finrank 𝔽₂ p.2)) 𝔽₂)
    (hMA : Qp p.1 * Qp t.1 = M * Qp (liftV t.1 p.1))
    (hSB : Ip t.2.1 * Ip p.2 = Ip (liftW t.2.1 p.2) * S) :
    charMat p.1 p.2 (XtOf t.1 t.2.1 t.2.2)
      = M * charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X * S := by
  have hasso : ∀ A : Matrix (Fin n) (Fin m) 𝔽₂,
      (Qp p.1 * Qp t.1) * A * (Ip t.2.1 * Ip p.2)
        = M * (Qp (liftV t.1 p.1) * A * Ip (liftW t.2.1 p.2)) * S := by
    intro A
    rw [hMA, hSB]
    simp only [Matrix.mul_assoc]
  rw [← hX]
  rw [show charMat p.1 p.2 (charMat t.1 t.2.1 X)
      = (Qp p.1 * Qp t.1) * X * (Ip t.2.1 * Ip p.2) from by
    simp only [charMat, Matrix.mul_assoc]]
  rw [hasso X]
  rfl

/-- **The `plLE`-condition of `PTranspA`, transferred to the role space.**  With
`A = Qp p.1 * Qp t.1 = M * Qp (liftV t.1 p.1)` and `B = Ip t.2.1 * Ip p.2 = Ip (liftW t.2.1 p.2) * S`
(`M` injective, `S` surjective), the `plLE`-condition between the `(p.1,p.2)`-compressions is
equivalent to the role-space `plLE`-condition `plLE X' (charMat V₃ W₃ Z)`, where
`X' = charMat V₃ W₃ X` for any big-space matrix `X` whose compression is the triple's coordinate
matrix. -/
theorem PTranspA_iff_plLE_role
    (t : Triple m n) (p : QPair m n t) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hX : charMat t.1 t.2.1 X = XtOf t.1 t.2.1 t.2.2)
    (M : Matrix (Fin ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ p.1))
      (Fin (n - Module.finrank 𝔽₂ (liftV t.1 p.1))) 𝔽₂)
    (S : Matrix (Fin (Module.finrank 𝔽₂ (liftW t.2.1 p.2)))
      (Fin (Module.finrank 𝔽₂ p.2)) 𝔽₂)
    (hM : Function.Injective M.mulVecLin) (hS : Function.Surjective S.mulVecLin)
    (hMA : Qp p.1 * Qp t.1 = M * Qp (liftV t.1 p.1))
    (hSB : Ip t.2.1 * Ip p.2 = Ip (liftW t.2.1 p.2) * S)
    (Z : Matrix (Fin n) (Fin m) 𝔽₂) :
    PTranspA t p.1 p.2 (charMat t.1 t.2.1 Z) ↔
      plLE (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X)
        (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) Z) := by
  have hasso : ∀ A : Matrix (Fin n) (Fin m) 𝔽₂,
      (Qp p.1 * Qp t.1) * A * (Ip t.2.1 * Ip p.2)
        = M * (Qp (liftV t.1 p.1) * A * Ip (liftW t.2.1 p.2)) * S := by
    intro A
    rw [hMA, hSB]
    simp only [Matrix.mul_assoc]
  have hZeq : charMat p.1 p.2 (charMat t.1 t.2.1 Z)
      = (Qp p.1 * Qp t.1) * Z * (Ip t.2.1 * Ip p.2) := by
    simp only [charMat, Matrix.mul_assoc]
  have hZ : charMat p.1 p.2 (charMat t.1 t.2.1 Z)
      = M * charMat (liftV t.1 p.1) (liftW t.2.1 p.2) Z * S := by
    rw [hZeq, hasso Z]
    rfl
  have hX' := charMat_comp_eq t p X hX M S hMA hSB
  have hsub : charMat p.1 p.2 (charMat t.1 t.2.1 Z)
        - charMat p.1 p.2 (XtOf t.1 t.2.1 t.2.2)
      = M * (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) Z
          - charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X) * S := by
    rw [hZ, hX', ← Matrix.sub_mul, ← Matrix.mul_sub]
  show plLE (charMat p.1 p.2 (XtOf t.1 t.2.1 t.2.2))
        (charMat p.1 p.2 (charMat t.1 t.2.1 Z)) ↔
      plLE (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X)
        (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) Z)
  rw [plLE, hsub, hZ, hX']
  rw [show M * (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) Z
        - charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X) * S
      = M * charMat (liftV t.1 p.1) (liftW t.2.1 p.2) Z * S
        - M * charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X * S from by
    rw [Matrix.mul_sub, Matrix.sub_mul]]
  exact Commons.LinearAlgebra.Matrix.plLE_mul_mul_iff_of_inj_surj M S
    (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X)
    (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) Z) hM hS

/-! ## The restriction data of the switching-roles summand -/

open Classical in
/-- **The `V`-side restriction data of the switching-roles summand.**  The kernel of the composite
restriction `Qp (range X') * Qp V₃` is `Vc = liftV t.1 (p.1 ⊔ VrOf t)`. -/
theorem comap_range_charMat (t : Triple m n) (p : QPair m n t) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hX : charMat t.1 t.2.1 X = XtOf t.1 t.2.1 t.2.2)
    (M : Matrix (Fin ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ p.1))
      (Fin (n - Module.finrank 𝔽₂ (liftV t.1 p.1))) 𝔽₂)
    (S : Matrix (Fin (Module.finrank 𝔽₂ (liftW t.2.1 p.2)))
      (Fin (Module.finrank 𝔽₂ p.2)) 𝔽₂)
    (hM : Function.Injective M.mulVecLin) (hS : Function.Surjective S.mulVecLin)
    (hMA : Qp p.1 * Qp t.1 = M * Qp (liftV t.1 p.1))
    (hSB : Ip t.2.1 * Ip p.2 = Ip (liftW t.2.1 p.2) * S)
    (hW : p.2 ⊔ WrOf t = ⊤) :
    Submodule.comap (Qp (liftV t.1 p.1)).mulVecLin
        (LinearMap.range (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X).mulVecLin)
      = Submodule.comap (Qp t.1).mulVecLin (p.1 ⊔ VrOf t) := by
  have hrange := range_charMat_XtOf t p hW
  have h1 : LinearMap.range (charMat p.1 p.2 (XtOf t.1 t.2.1 t.2.2)).mulVecLin
      = Submodule.map M.mulVecLin
          (LinearMap.range (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X).mulVecLin) := by
    rw [charMat_comp_eq t p X hX M S hMA hSB]
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
    rw [Matrix.mulVecLin_mul, Submodule.map_comp]
    rw [LinearMap.range_eq_top.mpr hS, Submodule.map_top]
  have h2 : Submodule.comap M.mulVecLin (Submodule.map M.mulVecLin
      (LinearMap.range (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X).mulVecLin))
      = LinearMap.range (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X).mulVecLin := by
    rw [Submodule.comap_map_eq, LinearMap.ker_eq_bot.mpr hM, sup_bot_eq]
  calc Submodule.comap (Qp (liftV t.1 p.1)).mulVecLin
        (LinearMap.range (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X).mulVecLin)
      = Submodule.comap (Qp (liftV t.1 p.1)).mulVecLin
          (Submodule.comap M.mulVecLin (Submodule.map M.mulVecLin
            (LinearMap.range (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X).mulVecLin))) := by
          rw [h2]
    _ = Submodule.comap (Qp (liftV t.1 p.1)).mulVecLin
          (Submodule.comap M.mulVecLin
            (LinearMap.range (charMat p.1 p.2 (XtOf t.1 t.2.1 t.2.2)).mulVecLin)) := by
          rw [h1]
    _ = Submodule.comap (Qp (liftV t.1 p.1)).mulVecLin
          (Submodule.comap M.mulVecLin (Submodule.map (Qp p.1).mulVecLin (VrOf t))) := by
          rw [hrange]
    _ = Submodule.comap ((Qp p.1 * Qp t.1)).mulVecLin
          (Submodule.map (Qp p.1).mulVecLin (VrOf t)) := by
          rw [← Submodule.comap_comp]
          congr 1
          rw [hMA, Matrix.mulVecLin_mul]
    _ = Submodule.comap (Qp t.1).mulVecLin
          (Submodule.comap (Qp p.1).mulVecLin (Submodule.map (Qp p.1).mulVecLin (VrOf t))) := by
          rw [Matrix.mulVecLin_mul, Submodule.comap_comp]
    _ = Submodule.comap (Qp t.1).mulVecLin (VrOf t ⊔ p.1) := by
          rw [Submodule.comap_map_eq, ker_Qp]
    _ = Submodule.comap (Qp t.1).mulVecLin (p.1 ⊔ VrOf t) := by rw [sup_comm]

lemma map_Ip_WrOf_inf (t : Triple m n) (p : QPair m n t) :
    Submodule.map (Ip p.2).mulVecLin
        (Submodule.comap (Ip p.2).mulVecLin (WrOf t)) = p.2 ⊓ WrOf t := by
  rw [Submodule.map_comap_eq, range_Ip, inf_comm]

open Classical in
/-- **The `W`-side restriction data of the switching-roles summand.**  The image of the kernel of
`X'` under `Ip W₃` is `Wc = liftW t.2.1 (p.2 ⊓ WrOf t)`. -/
theorem map_Ip_ker_charMat (t : Triple m n) (p : QPair m n t) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hX : charMat t.1 t.2.1 X = XtOf t.1 t.2.1 t.2.2)
    (M : Matrix (Fin ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ p.1))
      (Fin (n - Module.finrank 𝔽₂ (liftV t.1 p.1))) 𝔽₂)
    (S : Matrix (Fin (Module.finrank 𝔽₂ (liftW t.2.1 p.2)))
      (Fin (Module.finrank 𝔽₂ p.2)) 𝔽₂)
    (hM : Function.Injective M.mulVecLin) (hS : Function.Surjective S.mulVecLin)
    (hMA : Qp p.1 * Qp t.1 = M * Qp (liftV t.1 p.1))
    (hSB : Ip t.2.1 * Ip p.2 = Ip (liftW t.2.1 p.2) * S)
    (hV : p.1 ⊓ VrOf t = ⊥) :
    Submodule.map (Ip (liftW t.2.1 p.2)).mulVecLin
        (LinearMap.ker (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X).mulVecLin)
      = Submodule.map (Ip t.2.1).mulVecLin (p.2 ⊓ WrOf t) := by
  have hker1 : LinearMap.ker ((charMat p.1 p.2 (XtOf t.1 t.2.1 t.2.2)).mulVecLin)
      = Submodule.comap S.mulVecLin
          (LinearMap.ker ((charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X)).mulVecLin) := by
    rw [charMat_comp_eq t p X hX M S hMA hSB]
    rw [Matrix.mulVecLin_mul, LinearMap.ker_comp]
    rw [Matrix.mulVecLin_mul, LinearMap.ker_comp]
    rw [LinearMap.ker_eq_bot.mpr hM, Submodule.comap_bot]
  have hker2 := ker_charMat_XtOf t p hV
  calc Submodule.map (Ip (liftW t.2.1 p.2)).mulVecLin
        (LinearMap.ker (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X).mulVecLin)
      = Submodule.map (Ip (liftW t.2.1 p.2)).mulVecLin
          (Submodule.map S.mulVecLin (Submodule.comap S.mulVecLin
            (LinearMap.ker (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X).mulVecLin))) := by
          rw [Submodule.map_comap_eq, LinearMap.range_eq_top.mpr hS, top_inf_eq]
    _ = Submodule.map ((Ip (liftW t.2.1 p.2) * S)).mulVecLin
          (Submodule.comap S.mulVecLin
            (LinearMap.ker (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) X).mulVecLin)) := by
          rw [Matrix.mulVecLin_mul, Submodule.map_comp]
    _ = Submodule.map ((Ip t.2.1 * Ip p.2)).mulVecLin
          (LinearMap.ker (charMat p.1 p.2 (XtOf t.1 t.2.1 t.2.2)).mulVecLin) := by
          rw [← hSB, ← hker1]
    _ = Submodule.map (Ip t.2.1).mulVecLin (p.2 ⊓ WrOf t) := by
          rw [hker2, Matrix.mulVecLin_mul, Submodule.map_comp, map_Ip_WrOf_inf t p]


/-! ## The unconditional form of the role-space transfer -/

/-- The restriction pair of a switching-roles summand, on the `V`-side. -/
abbrev VcOf {m n : ℕ} (t : Triple m n) (p : QPair m n t) : Submodule 𝔽₂ (Fin n → 𝔽₂) :=
  liftV t.1 (p.1 ⊔ VrOf t)

/-- The restriction pair of a switching-roles summand, on the `W`-side. -/
abbrev WcOf {m n : ℕ} (t : Triple m n) (p : QPair m n t) : Submodule 𝔽₂ (Fin m → 𝔽₂) :=
  liftW t.2.1 (p.2 ⊓ WrOf t)

/-- The role-space matrix of a switching-roles summand. -/
noncomputable def XsOf {m n : ℕ} (t : Triple m n) (p : QPair m n t) :
    Matrix (Fin (n - Module.finrank 𝔽₂ (liftV t.1 p.1)))
      (Fin (Module.finrank 𝔽₂ (liftW t.2.1 p.2))) 𝔽₂ :=
  charMat (liftV t.1 p.1) (liftW t.2.1 p.2) (bigMat t)

/-- The defining equation of `XsOf`. -/
theorem XsOf_eq (t : Triple m n) (p : QPair m n t) :
    XsOf t p = charMat (liftV t.1 p.1) (liftW t.2.1 p.2) (bigMat t) := rfl

/-- **The multiplier predicate of the switching-roles summand, in the role space** (canonical lift
`bigMat t`). -/
theorem PTranspA_iff_plLE_role_bigMat (t : Triple m n) (p : QPair m n t)
    (Z : Matrix (Fin n) (Fin m) 𝔽₂) :
    PTranspA t p.1 p.2 (charMat t.1 t.2.1 Z) ↔
      plLE (XsOf t p) (charMat (liftV t.1 p.1) (liftW t.2.1 p.2) Z) := by
  rw [XsOf_eq]
  have hker : LinearMap.ker ((Qp p.1 * Qp t.1)).mulVecLin
      = LinearMap.ker (Qp (liftV t.1 p.1)).mulVecLin := by
    rw [ker_Qp_mul_Qp, ker_Qp]
  have hA : LinearMap.range ((Qp p.1 * Qp t.1)).mulVecLin = ⊤ := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp, range_Qp, Submodule.map_top, range_Qp]
  obtain ⟨M, hM, hMA⟩ := Commons.LinearAlgebra.Matrix.exists_mul_of_ker_eq
    (Qp p.1 * Qp t.1) (Qp (liftV t.1 p.1)) hker hA (range_Qp _)
  have hrange : LinearMap.range (Ip (liftW t.2.1 p.2)).mulVecLin
      = LinearMap.range ((Ip t.2.1 * Ip p.2)).mulVecLin := by
    rw [range_Ip_mul_Ip, range_Ip]
  obtain ⟨S, hS, hSB⟩ := Commons.LinearAlgebra.Matrix.exists_mul_of_range_eq_inj
    (Ip (liftW t.2.1 p.2)) (Ip t.2.1 * Ip p.2) hrange (ker_Ip _) (by
      rw [Matrix.mulVecLin_mul, LinearMap.ker_comp, ker_Ip, Submodule.comap_bot, ker_Ip])
  exact PTranspA_iff_plLE_role t p (bigMat t) (charMat_bigMat t) M S hM hS hMA hSB Z

/-- **The switching-roles multiplier in role-space form.** -/
theorem lapMulN_PComb_eq_role (t : Triple m n) (p : QPair m n t)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f)
      = lapMulN (fun Z => plLE (XsOf t p)
            (Qp (liftV t.1 p.1) * Z * Ip (liftW t.2.1 p.2)))
          (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f) := by
  rw [lapMulN_PComb_apply_Lsub]
  exact (lapMulN_congr (fun Z => PTranspA_iff_plLE_role_bigMat t p Z) _).trans
    (lapMulN_congr (fun _ => Iff.rfl) _)

noncomputable def XrR {m n : ℕ} (t : Triple m n) (p : QPair m n t) :
    Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ (liftV t.1 p.1)) → 𝔽₂) :=
  LinearMap.range (XsOf t p).mulVecLin

noncomputable def XrK {m n : ℕ} (t : Triple m n) (p : QPair m n t) :
    Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (liftW t.2.1 p.2)) → 𝔽₂) :=
  LinearMap.ker (XsOf t p).mulVecLin

theorem XrR_eq (t : Triple m n) (p : QPair m n t) :
    XrR t p = LinearMap.range (XsOf t p).mulVecLin := rfl

theorem XrK_eq (t : Triple m n) (p : QPair m n t) :
    XrK t p = LinearMap.ker (XsOf t p).mulVecLin := rfl

theorem comap_XrR (t : Triple m n) (p : QPair m n t) (hW : p.2 ⊔ WrOf t = ⊤)
    (M : Matrix (Fin ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ p.1))
      (Fin (n - Module.finrank 𝔽₂ (liftV t.1 p.1))) 𝔽₂)
    (S : Matrix (Fin (Module.finrank 𝔽₂ (liftW t.2.1 p.2)))
      (Fin (Module.finrank 𝔽₂ p.2)) 𝔽₂)
    (hM : Function.Injective M.mulVecLin) (hS : Function.Surjective S.mulVecLin)
    (hMA : Qp p.1 * Qp t.1 = M * Qp (liftV t.1 p.1))
    (hSB : Ip t.2.1 * Ip p.2 = Ip (liftW t.2.1 p.2) * S) :
    Submodule.comap (Qp (liftV t.1 p.1)).mulVecLin (XrR t p) = VcOf t p := by
  rw [XrR_eq, XsOf_eq]
  exact comap_range_charMat t p (bigMat t) (charMat_bigMat t) M S hM hS hMA hSB hW

theorem map_Ip_XrK (t : Triple m n) (p : QPair m n t) (hV : p.1 ⊓ VrOf t = ⊥)
    (M : Matrix (Fin ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ p.1))
      (Fin (n - Module.finrank 𝔽₂ (liftV t.1 p.1))) 𝔽₂)
    (S : Matrix (Fin (Module.finrank 𝔽₂ (liftW t.2.1 p.2)))
      (Fin (Module.finrank 𝔽₂ p.2)) 𝔽₂)
    (hM : Function.Injective M.mulVecLin) (hS : Function.Surjective S.mulVecLin)
    (hMA : Qp p.1 * Qp t.1 = M * Qp (liftV t.1 p.1))
    (hSB : Ip t.2.1 * Ip p.2 = Ip (liftW t.2.1 p.2) * S) :
    Submodule.map (Ip (liftW t.2.1 p.2)).mulVecLin (XrK t p) = WcOf t p := by
  rw [XrK_eq, XsOf_eq]
  exact map_Ip_ker_charMat t p (bigMat t) (charMat_bigMat t) M S hM hS hMA hSB hV



/-- **The switching-roles summand is a role-space `X`-derivative applied to `D_{V₃,W₃,T}`.**
This is the `D`-form of the paper's `D_{X(W₃,V/V₃)} ∘ D_{V₃,W₃,T}`. -/
theorem l2sq_restr_eq_DopRole (t : Triple m n) (p : QPair m n t)
    (hV : p.1 ⊓ VrOf t = ⊥) (hW : p.2 ⊔ WrOf t = ⊤)
    (T' : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (restr (Qp (VcOf t p)) (Ip (WcOf t p))
        (shift T' (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))
      = l2sq (restr (Qp (XrR t p)) (Ip (XrK t p))
          (lapMulN (plLE (XsOf t p))
            (Dop0S (liftV t.1 p.1) (liftW t.2.1 p.2) T' f))) := by
  have hker : LinearMap.ker ((Qp p.1 * Qp t.1)).mulVecLin
      = LinearMap.ker (Qp (liftV t.1 p.1)).mulVecLin := by
    rw [ker_Qp_mul_Qp, ker_Qp]
  have hA : LinearMap.range ((Qp p.1 * Qp t.1)).mulVecLin = ⊤ := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp, range_Qp, Submodule.map_top, range_Qp]
  obtain ⟨M, hM, hMA⟩ := Commons.LinearAlgebra.Matrix.exists_mul_of_ker_eq
    (Qp p.1 * Qp t.1) (Qp (liftV t.1 p.1)) hker hA (range_Qp _)
  have hrange : LinearMap.range (Ip (liftW t.2.1 p.2)).mulVecLin
      = LinearMap.range ((Ip t.2.1 * Ip p.2)).mulVecLin := by
    rw [range_Ip_mul_Ip, range_Ip]
  obtain ⟨S, hS, hSB⟩ := Commons.LinearAlgebra.Matrix.exists_mul_of_range_eq_inj
    (Ip (liftW t.2.1 p.2)) (Ip t.2.1 * Ip p.2) hrange (ker_Ip _) (by
      rw [Matrix.mulVecLin_mul, LinearMap.ker_comp, ker_Ip, Submodule.comap_bot, ker_Ip])
  have hstep1 : restr (Qp (liftV t.1 p.1)) (Ip (liftW t.2.1 p.2))
      (lapMulN (fun Z => plLE (XsOf t p)
        (Qp (liftV t.1 p.1) * Z * Ip (liftW t.2.1 p.2)))
        (shift T' (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f)))
      = lapMulN (plLE (XsOf t p))
          (restr (Qp (liftV t.1 p.1)) (Ip (liftW t.2.1 p.2))
            (shift T' (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f))) :=
    restr_lapMulN_comp (Qp (liftV t.1 p.1)) (Ip (liftW t.2.1 p.2))
      (plLE (XsOf t p)) (shift T' (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f))
  have hQ₂ : LinearMap.ker ((Qp (XrR t p) * Qp (liftV t.1 p.1))).mulVecLin = VcOf t p := by
    rw [Matrix.mulVecLin_mul, LinearMap.ker_comp, ker_Qp]
    exact comap_XrR t p hW M S hM hS hMA hSB
  have hQ₂r : LinearMap.range ((Qp (XrR t p) * Qp (liftV t.1 p.1))).mulVecLin = ⊤ := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp, range_Qp, Submodule.map_top, range_Qp]
  have hι₂ : LinearMap.range ((Ip (liftW t.2.1 p.2) * Ip (XrK t p))).mulVecLin = WcOf t p := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp, range_Ip]
    exact map_Ip_XrK t p hV M S hM hS hMA hSB
  have hι₂k : LinearMap.ker ((Ip (liftW t.2.1 p.2) * Ip (XrK t p))).mulVecLin = ⊥ := by
    rw [Matrix.mulVecLin_mul, LinearMap.ker_comp, ker_Ip, Submodule.comap_bot, ker_Ip]
  have hL : l2sq (restr (Qp (VcOf t p)) (Ip (WcOf t p))
        (shift T' (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))
      = l2sq (restr (Qp (VcOf t p)) (Ip (WcOf t p))
          (lapMulN (fun Z => plLE (XsOf t p)
              (Qp (liftV t.1 p.1) * Z * Ip (liftW t.2.1 p.2)))
            (shift T' (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f)))) := by
    rw [lapMulN_PComb_eq_role t p f, lapMulN_shift]
  have hcongr : l2sq (restr (Qp (VcOf t p)) (Ip (WcOf t p))
        (lapMulN (fun Z => plLE (XsOf t p)
            (Qp (liftV t.1 p.1) * Z * Ip (liftW t.2.1 p.2)))
          (shift T' (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f))))
      = l2sq (restr (Qp (XrR t p) * Qp (liftV t.1 p.1))
          (Ip (liftW t.2.1 p.2) * Ip (XrK t p))
          (lapMulN (fun Z => plLE (XsOf t p)
              (Qp (liftV t.1 p.1) * Z * Ip (liftW t.2.1 p.2)))
            (shift T' (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f)))) :=
    l2sq_restr_congr (VcOf t p) (WcOf t p) (Qp (VcOf t p)) (Ip (WcOf t p)) _ _
      (ker_Qp _) (range_Qp _) (range_Ip _) (ker_Ip _) hQ₂ hQ₂r hι₂ hι₂k _
  have hR : l2sq (restr (Qp (XrR t p)) (Ip (XrK t p))
        (lapMulN (plLE (XsOf t p)) (Dop0S (liftV t.1 p.1) (liftW t.2.1 p.2) T' f)))
      = l2sq (restr (Qp (XrR t p) * Qp (liftV t.1 p.1))
          (Ip (liftW t.2.1 p.2) * Ip (XrK t p))
          (lapMulN (fun Z => plLE (XsOf t p)
              (Qp (liftV t.1 p.1) * Z * Ip (liftW t.2.1 p.2)))
            (shift T' (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f)))) := by
    rw [Dop0S, ← hstep1, restr_restr]
  rw [hL, hcongr, hR]

end

end Submission.Grassmann

