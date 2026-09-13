import Submission.Grassmann.RestrictionTriple

/-!
# Canonical coordinates for the quotients `V/V₁` and the subspaces `W₁`

For Proposition "taking restrictions of Laplacians" of arXiv:2209.04243 (§8) one has to compare
functions living on different spaces `L(V/V₂, W₂)` and `L(V/V₁, W₁)`.  This file fixes, once and
for all, canonical linear coordinates:

* `Qp V₁ : Matrix (Fin (n - dim V₁)) (Fin n) 𝔽₂` — the projection `𝔽₂ⁿ ↠ 𝔽₂ⁿ/V₁`
  (`ker = V₁`, onto);
* `Ip W₁ : Matrix (Fin m) (Fin (dim W₁)) 𝔽₂` — an inclusion `𝔽₂^{dim W₁} ↪ 𝔽₂ᵐ`
  (`range = W₁`, injective);
* `coeffEquiv V₁ W₁ : Matrix (Fin (dim W₁)) (Fin (n - dim V₁)) ≃ homSub V₁ W₁`,
  `A ↦ Ip W₁ * A * Qp V₁`.

Since `homSub V₁ W₁` is a subtype of the *fixed* matrix space `Matrix (Fin m) (Fin n) 𝔽₂`, the
"lift" of an element of `Hom(V/V₁,W₁)` to `Hom(V/V₂,W₂)` (for `V₂ ≤ V₁`, `W₁ ≤ W₂`) is the
identity: no transport of types is ever needed.  The character identity `mchar_coeff` is the
bridge between the abstract Fourier analysis on `Hom(V/V₁,W₁)` and the coordinate model.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-- The dimension of the quotient `𝔽₂ⁿ / V₁`. -/
theorem finrank_quotient_eq (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    Module.finrank 𝔽₂ ((Fin n → 𝔽₂) ⧸ V₁) = n - Module.finrank 𝔽₂ V₁ := by
  have h := Submodule.finrank_quotient_add_finrank V₁
  rw [Module.finrank_fin_fun (R := 𝔽₂)] at h
  omega

/-- The canonical linear equivalence `𝔽₂ⁿ/V₁ ≃ₗ 𝔽₂^{n - dim V₁}`. -/
noncomputable def Qe (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    ((Fin n → 𝔽₂) ⧸ V₁) ≃ₗ[𝔽₂] (Fin (n - Module.finrank 𝔽₂ V₁) → 𝔽₂) :=
  (LinearEquiv.ofFinrankEq ((Fin (n - Module.finrank 𝔽₂ V₁)) → 𝔽₂) ((Fin n → 𝔽₂) ⧸ V₁) (by
    rw [Module.finrank_fin_fun (R := 𝔽₂), finrank_quotient_eq])).symm

/-- The canonical projection `𝔽₂ⁿ ↠ 𝔽₂ⁿ/V₁`, presented as a matrix. -/
noncomputable def Qp (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    Matrix (Fin (n - Module.finrank 𝔽₂ V₁)) (Fin n) 𝔽₂ :=
  LinearMap.toMatrix' ((Qe V₁).toLinearMap.comp (Submodule.mkQ V₁))

/-- The canonical inclusion `𝔽₂^{dim V₁} ↪ 𝔽₂ⁿ` with image `V₁`, presented as a matrix. -/
noncomputable def Ip (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    Matrix (Fin n) (Fin (Module.finrank 𝔽₂ V₁)) 𝔽₂ :=
  LinearMap.toMatrix' (V₁.subtype.comp
    ((Module.finBasis 𝔽₂ ↥V₁).equivFun.symm.toLinearMap))

lemma Qp_mulVecLin (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    (Qp V₁).mulVecLin = (Qe V₁).toLinearMap.comp (Submodule.mkQ V₁) :=
  Commons.LinearAlgebra.Submodule.mulVecLin_toMatrix' _

lemma Ip_mulVecLin (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    (Ip V₁).mulVecLin = V₁.subtype.comp
      ((Module.finBasis 𝔽₂ ↥V₁).equivFun.symm.toLinearMap) :=
  Commons.LinearAlgebra.Submodule.mulVecLin_toMatrix' _

lemma ker_Qp (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    LinearMap.ker (Qp V₁).mulVecLin = V₁ := by
  rw [Qp_mulVecLin, LinearMap.ker_comp_of_ker_eq_bot _ (LinearEquiv.ker _), Submodule.ker_mkQ]

lemma range_Qp (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    LinearMap.range (Qp V₁).mulVecLin = ⊤ := by
  rw [Qp_mulVecLin, LinearMap.range_comp_of_range_eq_top _ (Submodule.range_mkQ V₁),
    LinearEquiv.range]

lemma range_Ip (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    LinearMap.range (Ip V₁).mulVecLin = V₁ := by
  rw [Ip_mulVecLin, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.range_subtype]

lemma ker_Ip (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    LinearMap.ker (Ip V₁).mulVecLin = ⊥ := by
  rw [Ip_mulVecLin, LinearMap.ker_comp_of_ker_eq_bot _ (Submodule.ker_subtype V₁),
    LinearEquiv.ker]

lemma Ip_mem (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (x : Fin (Module.finrank 𝔽₂ V₁) → 𝔽₂) :
    (Ip V₁).mulVecLin x ∈ V₁ :=
  le_of_eq (range_Ip V₁) (LinearMap.mem_range.mpr ⟨x, rfl⟩)

/-- **`coeffEquiv V₁ W₁`**: the canonical identification
`Matrix (Fin (dim W₁)) (Fin (n - dim V₁)) ≃ Hom(V/V₁, W₁)`, `A ↦ Ip W₁ * A * Qp V₁`. -/
noncomputable def coeffEquiv (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) :
    Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ ≃ homSub V₁ W₁ :=
  Equiv.ofBijective
    (fun A => ⟨Ip W₁ * A * Qp V₁, (Commons.LinearAlgebra.Submodule.mul_mul_bijOn_hom_subtype
      V₁ W₁ (Qp V₁) (Ip W₁) (ker_Qp V₁) (range_Qp V₁) (range_Ip W₁) (ker_Ip W₁)).1
        (Set.mem_univ A)⟩)
    ⟨fun A A' h => (Commons.LinearAlgebra.Submodule.mul_mul_bijOn_hom_subtype
        V₁ W₁ (Qp V₁) (Ip W₁) (ker_Qp V₁) (range_Qp V₁) (range_Ip W₁) (ker_Ip W₁)).2.1
          (Set.mem_univ A) (Set.mem_univ A') (Subtype.ext_iff.mp h),
     fun B => by
      obtain ⟨A, -, hA⟩ := (Commons.LinearAlgebra.Submodule.mul_mul_bijOn_hom_subtype
        V₁ W₁ (Qp V₁) (Ip W₁) (ker_Qp V₁) (range_Qp V₁) (range_Ip W₁) (ker_Ip W₁)).2.2
          B.2
      exact ⟨A, Subtype.ext hA⟩⟩

/-- The inverse of `coeffEquiv`: the coordinate matrix of an element of `Hom(V/V₁, W₁)`. -/
noncomputable def coeff (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) :
    homSub V₁ W₁ → Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ :=
  (coeffEquiv V₁ W₁).symm

@[simp] lemma coeffEquiv_val (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (A : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂) :
    (coeffEquiv V₁ W₁ A).1 = Ip W₁ * A * Qp V₁ := rfl

@[simp] lemma coeff_coeffEquiv (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (A : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂) :
    coeff V₁ W₁ (coeffEquiv V₁ W₁ A) = A :=
  Equiv.symm_apply_apply _ _

@[simp] lemma coeffEquiv_coeff (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (B : homSub V₁ W₁) :
    coeffEquiv V₁ W₁ (coeff V₁ W₁ B) = B :=
  Equiv.apply_symm_apply _ _

lemma coeff_apply (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (B : homSub V₁ W₁) :
    Ip W₁ * coeff V₁ W₁ B * Qp V₁ = B.1 := by
  have h := congrArg Subtype.val (coeffEquiv_coeff V₁ W₁ B)
  rw [coeffEquiv_val] at h
  exact h

lemma coeffEquiv_add (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (A A' : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂) :
    (coeffEquiv V₁ W₁ (A + A')).1 = (coeffEquiv V₁ W₁ A).1 + (coeffEquiv V₁ W₁ A').1 := by
  rw [coeffEquiv_val, coeffEquiv_val, coeffEquiv_val, Matrix.mul_add, Matrix.add_mul]

lemma coeffEquiv_smul (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (c : 𝔽₂) (A : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂) :
    (coeffEquiv V₁ W₁ (c • A)).1 = c • (coeffEquiv V₁ W₁ A).1 := by
  rw [coeffEquiv_val, coeffEquiv_val, Matrix.mul_smul, Matrix.smul_mul]

/-- **The character identity**: the character of `Hom(V/V₁,W₁)` attached to `Y` evaluated at
`B` equals the character of the coordinate model attached to `Qp V₁ * Y * Ip W₁` evaluated at
`coeff V₁ W₁ B`. -/
theorem mchar_coeff (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) (B : homSub V₁ W₁) :
    mchar Y B.1 = mchar (Qp V₁ * Y * Ip W₁) (coeff V₁ W₁ B) := by
  rw [mchar_eq_trace, mchar_eq_trace]
  congr 1
  have h := coeff_apply V₁ W₁ B
  calc Matrix.trace (Y * B.1)
      = Matrix.trace (Y * (Ip W₁ * coeff V₁ W₁ B * Qp V₁)) := by rw [h]
    _ = Matrix.trace (Qp V₁ * Y * Ip W₁ * coeff V₁ W₁ B) := by
        rw [show Y * (Ip W₁ * coeff V₁ W₁ B * Qp V₁) = Y * Ip W₁ * (coeff V₁ W₁ B * Qp V₁)
          from by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_cycle Y (Ip W₁) (coeff V₁ W₁ B * Qp V₁),
          show (coeff V₁ W₁ B * Qp V₁) * Y * Ip W₁ = coeff V₁ W₁ B * (Qp V₁ * Y * Ip W₁)
            from by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm (coeff V₁ W₁ B) (Qp V₁ * Y * Ip W₁)]

/-! ## Transfer of character indices to the coordinate model -/

/-- The coordinate matrix of a linear map `X : ↥W₂ → V/V₂` in the model
`Hom(W₂, V/V₂) ≅ Matrix (Fin (n - dim V₂)) (Fin (dim W₂))`. -/
noncomputable def XtOf (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) :
    Matrix (Fin (n - Module.finrank 𝔽₂ V₂)) (Fin (Module.finrank 𝔽₂ W₂)) 𝔽₂ :=
  LinearMap.toMatrix' ((Qe V₂).toLinearMap.comp (X.comp
    (LinearMap.codRestrict W₂ (Ip W₂).mulVecLin (fun x => Ip_mem W₂ x))))

/-- The coordinate matrix of `Y|_{W₂}^{V/V₂}`. -/
noncomputable def charMat (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    Matrix (Fin (n - Module.finrank 𝔽₂ V₂)) (Fin (Module.finrank 𝔽₂ W₂)) 𝔽₂ :=
  Qp V₂ * Y * Ip W₂

/-- `Y` restricted to `W₂`, with values in `V/V₂`. -/
noncomputable def YlinOf (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂) :=
  (Submodule.mkQ V₂).comp (Y.mulVecLin.comp W₂.subtype)

/-- The coordinate matrix of a linear map has the same rank. -/
lemma rank_XtOf (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) :
    (XtOf V₂ W₂ X).rank = Module.finrank 𝔽₂ (LinearMap.range X) := by
  have hι : (LinearMap.codRestrict W₂ (Ip W₂).mulVecLin
      (fun x => Ip_mem W₂ x)).range = ⊤ := by
    rw [LinearMap.range_codRestrict, range_Ip W₂, Submodule.comap_subtype_self]
  rw [Matrix.rank, XtOf, Commons.LinearAlgebra.Submodule.mulVecLin_toMatrix',
    LinearMap.range_comp, LinearMap.range_comp, hι, Submodule.map_top]
  exact LinearEquiv.finrank_map_eq (Qe V₂) _

/-- `charMat` is the coordinate matrix of the linear map `Y|_{W₂}^{V/V₂}`. -/
lemma charMat_eq_XtOf (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    charMat V₂ W₂ Y = XtOf V₂ W₂ (YlinOf V₂ W₂ Y) := by
  have hsub : W₂.subtype.comp (LinearMap.codRestrict W₂ (Ip W₂).mulVecLin
      (fun x => Ip_mem W₂ x)) = (Ip W₂).mulVecLin := by
    ext a
    rfl
  have hc : charMat V₂ W₂ Y = LinearMap.toMatrix'
      ((Qp V₂).mulVecLin.comp (Y.mulVecLin.comp (Ip W₂).mulVecLin)) := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply',
      Commons.LinearAlgebra.Submodule.mulVecLin_toMatrix',
      charMat, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.comp_assoc]
  have hd : XtOf V₂ W₂ (YlinOf V₂ W₂ Y) = LinearMap.toMatrix'
      ((Qp V₂).mulVecLin.comp (Y.mulVecLin.comp (Ip W₂).mulVecLin)) := by
    rw [XtOf, YlinOf, Qp_mulVecLin]
    congr 1
  rw [hc, hd]

/-! ## The relation `X ≤ Y₂` -/

/-- The partial order on linear maps (the `plLE` of the matrices `X ≤ Y`): `X ≤ Y` iff the
ranks add. -/
def lmLE {M M' : Type*} [AddCommGroup M] [Module 𝔽₂ M] [AddCommGroup M']
    [Module 𝔽₂ M'] (X Y : M →ₗ[𝔽₂] M') : Prop :=
  Module.finrank 𝔽₂ (LinearMap.range Y) =
    Module.finrank 𝔽₂ (LinearMap.range X) + Module.finrank 𝔽₂ (LinearMap.range (Y - X))

/-- **The range/agreement characterisation of `lmLE`** (the linear-map analogue of
`Commons.LinearAlgebra.Matrix.rank_poset_iff`): `X ≤ Y` in the rank partial order iff
`range X ⊆ range Y` and `X`, `Y` agree on `Y⁻¹(range X)`. -/
theorem lmLE_iff {M M' : Type*} [AddCommGroup M] [Module 𝔽₂ M] [FiniteDimensional 𝔽₂ M]
    [AddCommGroup M'] [Module 𝔽₂ M'] (X Y : M →ₗ[𝔽₂] M') :
    lmLE X Y ↔ LinearMap.range X ≤ LinearMap.range Y ∧
      ∀ w, Y w ∈ LinearMap.range X → Y w = X w := by
  have hsub : ∀ w : M, (Y - X) w = Y w - X w := fun w => rfl
  constructor
  · intro h
    have hsum : Y = X + (Y - X) := by ext w; simp
    have hle : LinearMap.range Y ≤ LinearMap.range X ⊔ LinearMap.range (Y - X) := by
      rw [congrArg LinearMap.range hsum]; exact LinearMap.range_add_le _ _
    have hfin : Module.finrank 𝔽₂ ↥(LinearMap.range X ⊔ LinearMap.range (Y - X)) ≤
        Module.finrank 𝔽₂ ↥(LinearMap.range X) +
          Module.finrank 𝔽₂ ↥(LinearMap.range (Y - X)) :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    have h1 : Module.finrank 𝔽₂ ↥(LinearMap.range Y) ≤
        Module.finrank 𝔽₂ ↥(LinearMap.range X ⊔ LinearMap.range (Y - X)) :=
      Submodule.finrank_mono hle
    have h2 : Module.finrank 𝔽₂ ↥(LinearMap.range X ⊔ LinearMap.range (Y - X)) =
        Module.finrank 𝔽₂ ↥(LinearMap.range X) +
          Module.finrank 𝔽₂ ↥(LinearMap.range (Y - X)) :=
      le_antisymm hfin (h ▸ h1)
    have heq : LinearMap.range Y = LinearMap.range X ⊔ LinearMap.range (Y - X) :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [h2, ← h])
    have hinf : LinearMap.range X ⊓ LinearMap.range (Y - X) = ⊥ := by
      have hsd := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range X)
        (LinearMap.range (Y - X))
      have hz : Module.finrank 𝔽₂ ↥(LinearMap.range X ⊓ LinearMap.range (Y - X)) = 0 := by
        rw [h2] at hsd; omega
      exact Submodule.finrank_eq_zero.mp hz
    refine ⟨?_, ?_⟩
    · rw [heq]; exact le_sup_left
    · intro w hw
      have hmem1 : (Y - X) w ∈ LinearMap.range X := by
        rw [hsub]
        exact Submodule.sub_mem (LinearMap.range X) hw (LinearMap.mem_range.mpr ⟨w, rfl⟩)
      have hmem2 : (Y - X) w ∈ LinearMap.range (Y - X) :=
        LinearMap.mem_range.mpr ⟨w, rfl⟩
      have hzero : (Y - X) w = 0 := by
        have : (Y - X) w ∈ (⊥ : Submodule 𝔽₂ M') := by rw [← hinf]; exact ⟨hmem1, hmem2⟩
        simpa using this
      rw [hsub, sub_eq_zero] at hzero
      exact hzero
  · rintro ⟨hle, hagree⟩
    have hsum : Y = X + (Y - X) := by ext w; simp
    have hle' : LinearMap.range Y ≤ LinearMap.range X ⊔ LinearMap.range (Y - X) := by
      rw [congrArg LinearMap.range hsum]; exact LinearMap.range_add_le _ _
    have hZle : LinearMap.range (Y - X) ≤ LinearMap.range Y := by
      rintro v hv
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hv
      rw [← hw, hsub]
      exact Submodule.sub_mem (LinearMap.range Y) (LinearMap.mem_range.mpr ⟨w, rfl⟩)
        (hle (LinearMap.mem_range.mpr ⟨w, rfl⟩))
    have heq : LinearMap.range Y = LinearMap.range X ⊔ LinearMap.range (Y - X) :=
      le_antisymm hle' (sup_le hle hZle)
    have hinf : LinearMap.range X ⊓ LinearMap.range (Y - X) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro v ⟨hv1, hv2⟩
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hv2
      obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hv1
      have hYw : Y w ∈ LinearMap.range X := by
        have hYw' : Y w = X (w + u) := by
          rw [map_add, hu, ← hw, hsub]
          abel
        rw [hYw']; exact LinearMap.mem_range.mpr ⟨w + u, rfl⟩
      have := hagree w hYw
      have hz : (Y - X) w = 0 := by rw [hsub, this, sub_self]
      rw [← hw, hz]
    rw [lmLE, heq]
    have hsd := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range X)
      (LinearMap.range (Y - X))
    rw [hinf, finrank_bot, add_zero] at hsd
    exact hsd

lemma XtOf_sub (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X Y : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) :
    XtOf V₂ W₂ (Y - X) = XtOf V₂ W₂ Y - XtOf V₂ W₂ X := by
  rw [XtOf, XtOf, XtOf]
  have h : (Qe V₂).toLinearMap.comp ((Y - X).comp (LinearMap.codRestrict W₂ (Ip W₂).mulVecLin
        (fun x => Ip_mem W₂ x)))
      = (Qe V₂).toLinearMap.comp (Y.comp (LinearMap.codRestrict W₂ (Ip W₂).mulVecLin
          (fun x => Ip_mem W₂ x)))
        - (Qe V₂).toLinearMap.comp (X.comp (LinearMap.codRestrict W₂ (Ip W₂).mulVecLin
          (fun x => Ip_mem W₂ x))) := by
    ext a
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub]
  rw [h, map_sub]

/-- **The transfer of the order `X ≤ Y₂` to coordinates**: `X ≤ Y₂` holds iff the coordinate
matrices satisfy `plLE`. -/
lemma plLE_XtOf_iff (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X Y : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) :
    ((XtOf V₂ W₂ Y).rank = (XtOf V₂ W₂ X).rank + (XtOf V₂ W₂ Y - XtOf V₂ W₂ X).rank) ↔
      lmLE X Y := by
  rw [lmLE, ← XtOf_sub, rank_XtOf, rank_XtOf, rank_XtOf]

/-! ## The canonical `X` satisfies the conditions of the sum -/

/-- **`Xlin` is in the index set of Proposition "taking restrictions of Laplacians"**: its
kernel is `W₁` and its range is `V₁/V₂` (given `V₁ ≤ Im Y` and `ker Y ≤ W₁`). -/
theorem Xlin_mem (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    {Y : Matrix (Fin n) (Fin m) 𝔽₂} (hV : V₁ ≤ LinearMap.range Y.mulVecLin)
    (hW : LinearMap.ker Y.mulVecLin ≤ W₁) :
    LinearMap.ker (Xlin V₁ W₁ Y) = Submodule.comap (W2sub V₁ W₁ Y).subtype W₁ ∧
      LinearMap.range (Xlin V₁ W₁ Y) =
        Submodule.map (Submodule.mkQ (V2sub V₁ W₁ Y)) V₁ :=
  ⟨ker_Xlin hW, range_Xlin hV⟩

/-- **The canonical `X` satisfies `X ≤ Y₂`** (`Xlin_le_Ylin`, rephrased as `lmLE`). -/
theorem lmLE_Xlin (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    {Y : Matrix (Fin n) (Fin m) 𝔽₂} (hV : V₁ ≤ LinearMap.range Y.mulVecLin)
    (hW : LinearMap.ker Y.mulVecLin ≤ W₁) :
    lmLE (Xlin V₁ W₁ Y) (YlinOf (V2sub V₁ W₁ Y) (W2sub V₁ W₁ Y) Y) :=
  (lmLE_iff _ _).mpr (Xlin_le_Ylin hV hW)

/-- Membership in `(V₁ + V₂)/V₂` unwinds to membership in `V₁` (for `V₂ ≤ V₁`). -/
lemma mkQ_mem_map_iff {V₂ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)} (h : V₂ ≤ V₁) (x : Fin n → 𝔽₂) :
    Submodule.mkQ V₂ x ∈ Submodule.map (Submodule.mkQ V₂) V₁ ↔ x ∈ V₁ := by
  constructor
  · intro hx
    rw [Submodule.mem_map] at hx
    obtain ⟨v, hv, hvw⟩ := hx
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hvw
    have : x - v ∈ V₁ := h (by simpa using V₂.neg_mem hvw)
    have := V₁.add_mem this hv
    simpa using this
  · intro hx
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

/-- `Y₂⁻¹(V₁/V₂) = Y⁻¹(V₁)`: the preimage of `V₁/V₂` under the restriction `Y₂`. -/
lemma mem_YlinOf_preimage_iff {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)} {Y : Matrix (Fin n) (Fin m) 𝔽₂}
    (w : ↥(W2sub V₁ W₁ Y)) :
    YlinOf (V2sub V₁ W₁ Y) (W2sub V₁ W₁ Y) Y w ∈
        Submodule.map (Submodule.mkQ (V2sub V₁ W₁ Y)) V₁ ↔ Y.mulVecLin w.1 ∈ V₁ :=
  mkQ_mem_map_iff (V2sub_le V₁ W₁ Y) _

/-- **Uniqueness of the contributing `X`**: any `X` with `ker X = W₁`, `range X = V₁/V₂` and
`X ≤ Y₂` equals the canonical `Xlin`. -/
theorem eq_Xlin_of_lmLE (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    {Y : Matrix (Fin n) (Fin m) 𝔽₂} (hV : V₁ ≤ LinearMap.range Y.mulVecLin)
    (hW : LinearMap.ker Y.mulVecLin ≤ W₁)
    (X : ↥(W2sub V₁ W₁ Y) →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V2sub V₁ W₁ Y))
    (hker : LinearMap.ker X = Submodule.comap (W2sub V₁ W₁ Y).subtype W₁)
    (hrange : LinearMap.range X = Submodule.map (Submodule.mkQ (V2sub V₁ W₁ Y)) V₁)
    (hXle : lmLE X (YlinOf (V2sub V₁ W₁ Y) (W2sub V₁ W₁ Y) Y)) :
    X = Xlin V₁ W₁ Y := by
  have h1 := (lmLE_iff X (YlinOf (V2sub V₁ W₁ Y) (W2sub V₁ W₁ Y) Y)).mp hXle
  have h2 := (lmLE_iff (Xlin V₁ W₁ Y)
    (YlinOf (V2sub V₁ W₁ Y) (W2sub V₁ W₁ Y) Y)).mp (lmLE_Xlin V₁ W₁ hV hW)
  -- `X` and `Xlin` agree on `Y⁻¹(V₁) ⊆ W₂`
  have hagree : ∀ b : ↥(ASub V₁ Y),
      X ⟨b.1, (le_sup_left : ASub V₁ Y ≤ W2sub V₁ W₁ Y) b.2⟩ =
        Xlin V₁ W₁ Y ⟨b.1, (le_sup_left : ASub V₁ Y ≤ W2sub V₁ W₁ Y) b.2⟩ := by
    intro b
    have hb : YlinOf (V2sub V₁ W₁ Y) (W2sub V₁ W₁ Y) Y
        ⟨b.1, (le_sup_left : ASub V₁ Y ≤ W2sub V₁ W₁ Y) b.2⟩ ∈
        Submodule.map (Submodule.mkQ (V2sub V₁ W₁ Y)) V₁ :=
      (mem_YlinOf_preimage_iff _).mpr b.2
    rw [← h1.2 _ (by rw [hrange]; exact hb), ← h2.2 _ (by rw [range_Xlin hV]; exact hb)]
  -- extend to all of `W₂` using `W₂ = W₁ ⊔ Y⁻¹(V₁)`
  ext w
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp w.2
  have haW : a ∈ W2sub V₁ W₁ Y := (le_sup_left : ASub V₁ Y ≤ W2sub V₁ W₁ Y) ha
  have hbW : b ∈ W2sub V₁ W₁ Y := (le_sup_right : W₁ ≤ W2sub V₁ W₁ Y) hb
  have hw : w = (⟨a, haW⟩ : ↥(W2sub V₁ W₁ Y)) + ⟨b, hbW⟩ :=
    Subtype.ext (by simpa using hab.symm)
  have hA : X ⟨a, haW⟩ = Xlin V₁ W₁ Y ⟨a, haW⟩ := hagree ⟨a, ha⟩
  have hB : X ⟨b, hbW⟩ = 0 := by
    rw [← LinearMap.mem_ker, hker]
    exact hb
  have hB' : Xlin V₁ W₁ Y ⟨b, hbW⟩ = 0 := Xlin_eq_zero_of_mem hW hb
  rw [hw, map_add, map_add, hA, hB, hB', add_zero]

end

end Submission.Grassmann
