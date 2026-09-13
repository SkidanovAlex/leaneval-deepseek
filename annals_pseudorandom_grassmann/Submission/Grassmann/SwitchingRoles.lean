import Submission.Grassmann.RestrictProp
import Submission.Commons.LinearAlgebra.Submodule.swapping_places
import Submission.Commons.LinearAlgebra.Submodule.exists_complement_pair_of_le_rank
import Submission.Commons.LinearAlgebra.Submodule.range_le_range_iff_restrict_quotient

/-!
# Proposition "switching the roles between the derivatives" (arXiv:2209.04243 §8)

For `V₁ ≤ V₂ ≤ V`, `W₂ ≤ W₁ ≤ W` and `X ∈ L(W,V)` with `ker X = W₁` and `Im X = V₁`:

  `D_{V₂/V₁,W₂} ∘ D_X = Σ_{V₃ ∈ 𝓕₁, W₃ ∈ 𝓕₂} D_{X(W₃,V/V₃)} ∘ D_{V₃,W₃}`

where `𝓕₁ = {V₃ ≤ V₂ : V₃ ⊕ V₁ = V₂}` and `𝓕₂ = {W₃ ≥ W₂ : (W₃/W₂) ⊕ (W₁/W₂) = W/W₂}`.

Here `D_{U₁,U₂,T}` is the *hybrid* derivative of arXiv:2209.04243 (a restriction of
`L_{U₁,U₂} = Lsub U₁ U₂`), while `D_{X,T}` (indexed by a *map*) is the restriction of the
`X`-Laplacian `L_X` (the multiplier `plLE X`).

The two index families are described by
`𝓕₁ = {V₃ : V₃ ⊓ V₁ = ⊥ ∧ V₃ ⊔ V₁ = V₂}` and
`𝓕₂ = {W₃ : W₂ ≤ W₃ ∧ W₃ ⊓ W₁ = W₂ ∧ W₃ ⊔ W₁ = ⊤}`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## The coordinate subspaces `V₂/V₁` and `W₂ ≤ W₁` -/

/-- The coordinate isomorphism `𝔽₂^{dim W₁} ≃ₗ ↥W₁` (the inverse of the one used for `Ip`). -/
noncomputable abbrev ecW (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) :
    (Fin (Module.finrank 𝔽₂ W₁) → 𝔽₂) ≃ₗ[𝔽₂] ↥W₁ :=
  (Module.finBasis 𝔽₂ ↥W₁).equivFun.symm

/-- The image of `V₂/V₁` in the coordinates `𝔽₂^{n - dim V₁} ≅ V/V₁` of the quotient. -/
def Vco (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ V₁) → 𝔽₂) :=
  Submodule.map (Qe V₁).toLinearMap (Submodule.map (Submodule.mkQ V₁) V₂)

/-- The coordinates of `W₂` inside `𝔽₂^{dim W₁} ≅ W₁`. -/
def Wco (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) :
    Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₁) → 𝔽₂) :=
  Submodule.map (ecW W₁).symm.toLinearMap (Submodule.comap W₁.subtype W₂)

/-! ## The derivatives -/

/-- The `X`-derivative (the restriction of the `X`-Laplacian `L_X = lapMulN (plLE X)`), as an
operator from functions on `L(V,W)` to functions on `L(V/V₁,W₁)` in canonical coordinates. -/
noncomputable def DopUp (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ :=
  restr (Qp V₁) (Ip W₁) (lapMulN (plLE X) f)

/-- The hybrid derivative `D_{V₁,W₁}` at position `0`. -/
noncomputable def Dop0 (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ :=
  restr (Qp V₁) (Ip W₁) (Lsub V₁ W₁ f)

/-- The hybrid derivative `D_{V₂/V₁,W₂}` acting on functions on `L(V/V₁,W₁)`. -/
noncomputable def DopDown (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁)
    (g : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ :=
  restr (Qsup V₂ V₁ hV) (Isub W₂ W₁ hW)
    (lapMulN (hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂)) g)

/-- The left-hand side `D_{V₂/V₁,W₂} ∘ D_X` of Prop "switching the roles between the
derivatives". -/
noncomputable def SwitchLHS (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ :=
  DopDown V₁ W₁ V₂ W₂ hV hW (DopUp V₁ W₁ X f)

/-- The condition `V₃ ∈ 𝓕₁` and `W₃ ∈ 𝓕₂` on the pair `(V₃,W₃)`. -/
abbrev Fr (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂)) : Prop :=
  V₃ ⊓ V₁ = ⊥ ∧ V₃ ⊔ V₁ = V₂ ∧ W₂ ≤ W₃ ∧ W₃ ⊓ W₁ = W₂ ∧ W₃ ⊔ W₁ = ⊤

/-- The bare summand `D_{X(W₃,V/V₃)} ∘ D_{V₃,W₃}` (without the index condition). -/
noncomputable def Bare (_V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (_W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ :=
  restr (QsupT V₂ V₃) (IsubT W₂ W₃) (lapMulN (plLE (charMat V₃ W₃ X)) (Dop0 V₃ W₃ f))

/-- One summand of the right-hand side of Prop "switching the roles between the derivatives":
`D_{X(W₃,V/V₃)} ∘ D_{V₃,W₃}`, zero unless `V₃ ∈ 𝓕₁` and `W₃ ∈ 𝓕₂`. -/
noncomputable def SwitchSummand (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ :=
  if Fr V₁ W₁ V₂ W₂ V₃ W₃ then Bare V₁ W₁ V₂ W₂ V₃ W₃ X f else 0

/-- The right-hand side `Σ_{V₃ ∈ 𝓕₁, W₃ ∈ 𝓕₂} D_{X(W₃,V/V₃)} ∘ D_{V₃,W₃}` of Prop "switching the
roles between the derivatives" (indexed by the product of the two families of subspaces so that
it is a single `Fintype` sum). -/
noncomputable def SwitchRHS (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ :=
  ∑ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
    SwitchSummand V₁ W₁ V₂ W₂ p.1 p.2 X f

/-! ## The characters of the derivatives -/

/-- A Fourier multiplier restricted to a character. -/
theorem restr_lapMulN_mchar {m n m' n' : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (Q : Matrix (Fin n') (Fin n) (ZMod 2)) (ι : Matrix (Fin m) (Fin m') (ZMod 2))
    (Y : Matrix (Fin n) (Fin m) (ZMod 2)) :
    restr Q ι (lapMulN P (mchar Y)) =
      (if P Y then (1 : ℂ) else 0) •
        (mchar (Q * Y * ι) : Matrix (Fin m') (Fin n') (ZMod 2) → ℂ) := by
  rw [lapMulN_mchar, restr_smul, restr_mchar]

/-- The `X`-derivative on a character. -/
theorem DopUp_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    DopUp V₁ W₁ X (mchar Y) =
      (if plLE X Y then (1 : ℂ) else 0) •
        (mchar (charMat V₁ W₁ Y) :
          Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ) := by
  rw [DopUp, restr_lapMulN_mchar, charMat]

/-- The hybrid derivative `D_{V₁,W₁}` on a character. -/
theorem Dop0_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    Dop0 V₁ W₁ (mchar Y) =
      (if hybridPredSub V₁ W₁ Y then (1 : ℂ) else 0) •
        (mchar (charMat V₁ W₁ Y) :
          Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ) := by
  rw [Dop0, Lsub, restr_lapMulN_mchar, charMat]

/-- The hybrid derivative `D_{V₂/V₁,W₂}` on a character. -/
theorem DopDown_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁)
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₁)) (Fin (Module.finrank 𝔽₂ W₁)) 𝔽₂) :
    DopDown V₁ W₁ V₂ W₂ hV hW (mchar Z) =
      (if hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂) Z then (1 : ℂ) else 0) •
        (mchar (Qsup V₂ V₁ hV * Z * Isub W₂ W₁ hW) :
          Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ) := by
  rw [DopDown, restr_lapMulN_mchar]

/-- The key computation: the left-hand side of Prop "switching the roles between the
derivatives" on a character `mchar Y`. -/
theorem SwitchLHS_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁) {X : Matrix (Fin n) (Fin m) 𝔽₂}
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    SwitchLHS V₁ W₁ V₂ W₂ hV hW X (mchar Y) =
      ((if plLE X Y then (1 : ℂ) else 0) *
        (if hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂) (charMat V₁ W₁ Y) then (1 : ℂ) else 0)) •
        (mchar (charMat V₂ W₂ Y) :
          Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ) := by
  have hkey : Qsup V₂ V₁ hV * (charMat V₁ W₁ Y) * Isub W₂ W₁ hW = charMat V₂ W₂ Y := by
    rw [show Qsup V₂ V₁ hV * (charMat V₁ W₁ Y) * Isub W₂ W₁ hW =
        (Qsup V₂ V₁ hV * Qp V₁) * Y * (Ip W₁ * Isub W₂ W₁ hW) from by
          simp only [Matrix.mul_assoc, charMat],
      Qsup_mul_Qp, Ip_mul_Isub]
    rfl
  rw [SwitchLHS, DopUp_mchar, DopDown]
  rw [lapMulN_smul, restr_smul]
  rw [restr_lapMulN_mchar, hkey]
  simp only [smul_smul]

/-- The summand of the right-hand side of Prop "switching the roles between the derivatives" on a
character. -/
theorem SwitchSummand_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    SwitchSummand V₁ W₁ V₂ W₂ V₃ W₃ X (mchar Y) =
      ((if V₃ ⊓ V₁ = ⊥ ∧ V₃ ⊔ V₁ = V₂ ∧ W₂ ≤ W₃ ∧ W₃ ⊓ W₁ = W₂ ∧ W₃ ⊔ W₁ = ⊤ then
          (if hybridPredSub V₃ W₃ Y then (1 : ℂ) else 0) *
          (if plLE (charMat V₃ W₃ X) (charMat V₃ W₃ Y) then (1 : ℂ) else 0)
        else 0)) •
        (mchar (charMat V₂ W₂ Y) :
          Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ) := by
  rw [SwitchSummand, Bare]
  by_cases h : V₃ ⊓ V₁ = ⊥ ∧ V₃ ⊔ V₁ = V₂ ∧ W₂ ≤ W₃ ∧ W₃ ⊓ W₁ = W₂ ∧ W₃ ⊔ W₁ = ⊤
  · have hV : V₃ ≤ V₂ := le_sup_left.trans_eq h.2.1
    have hW : W₂ ≤ W₃ := h.2.2.1
    have hkey : Qsup V₂ V₃ hV * (charMat V₃ W₃ Y) * Isub W₂ W₃ hW = charMat V₂ W₂ Y := by
      rw [show Qsup V₂ V₃ hV * (charMat V₃ W₃ Y) * Isub W₂ W₃ hW =
          (Qsup V₂ V₃ hV * Qp V₃) * Y * (Ip W₃ * Isub W₂ W₃ hW) from by
            simp only [Matrix.mul_assoc, charMat],
        Qsup_mul_Qp, Ip_mul_Isub]
      rfl
    rw [if_pos h, if_pos h, Dop0_mchar, lapMulN_smul, restr_smul,
      QsupT_eq V₂ V₃ hV, IsubT_eq W₂ W₃ hW, restr_lapMulN_mchar, hkey, smul_smul]
  · rw [if_neg h, if_neg h, zero_smul]

/-- The right-hand side of Prop "switching the roles between the derivatives" on a character. -/
theorem SwitchRHS_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    SwitchRHS V₁ W₁ V₂ W₂ X (mchar Y) =
      (∑ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if p.1 ⊓ V₁ = ⊥ ∧ p.1 ⊔ V₁ = V₂ ∧ W₂ ≤ p.2 ∧ p.2 ⊓ W₁ = W₂ ∧ p.2 ⊔ W₁ = ⊤ then
          (if hybridPredSub p.1 p.2 Y then (1 : ℂ) else 0) *
          (if plLE (charMat p.1 p.2 X) (charMat p.1 p.2 Y) then (1 : ℂ) else 0)
        else 0)) •
        (mchar (charMat V₂ W₂ Y) :
          Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ) := by
  rw [SwitchRHS, Finset.sum_smul]
  exact Finset.sum_congr rfl fun p _ => SwitchSummand_mchar V₁ W₁ V₂ W₂ p.1 p.2 X Y

/-! ## Translating the hybrid predicate to coordinates -/

/-- The hybrid predicate, as a range/comap condition. -/
theorem hybridPredSub_iff {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    hybridPredSub V₁ W₁ X ↔
      V₁ ≤ LinearMap.range X.mulVecLin ∧ Submodule.comap X.mulVecLin V₁ ≤ W₁ :=
  Iff.rfl

/-- The rank order on matrices is the rank order on the associated linear maps. -/
theorem plLE_iff_lmLE {m n : ℕ} (X Y : Matrix (Fin n) (Fin m) (ZMod 2)) :
    plLE X Y ↔ lmLE X.mulVecLin Y.mulVecLin := by
  have hsub : (Y - X).mulVecLin = Y.mulVecLin - X.mulVecLin := by
    apply LinearMap.ext
    intro v
    rw [Matrix.mulVecLin_apply, LinearMap.sub_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.sub_mulVec]
  have h1 : (Y - X).rank = Module.finrank (ZMod 2) ↥((Y - X).mulVecLin.range) := rfl
  rw [plLE, lmLE, h1, hsub]
  exact Iff.rfl

/-- The coordinate model of `W₁`: the `codRestrict` used in `XtOf` is the isomorphism `ecW`. -/
theorem codRestrict_Ip_eq_ecW (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) :
    LinearMap.codRestrict W₁ (Ip W₁).mulVecLin (fun x => Ip_mem W₁ x) = (ecW W₁).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [LinearMap.codRestrict_apply, Ip_mulVecLin]
  rfl

/-- The range of the coordinate model of a map `W₁ → V/V₁`. -/
theorem range_XtOf (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : ↥W₁ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₁)) :
    LinearMap.range (XtOf V₁ W₁ Z).mulVecLin =
      Submodule.map (Qe V₁).toLinearMap (LinearMap.range Z) := by
  have hC : (LinearMap.codRestrict W₁ (Ip W₁).mulVecLin
      (fun x => Ip_mem W₁ x)).range = ⊤ := by
    rw [LinearMap.range_codRestrict, range_Ip, Submodule.comap_subtype_self]
  rw [XtOf, Commons.LinearAlgebra.Submodule.mulVecLin_toMatrix']
  rw [show ((Qe V₁).toLinearMap.comp (Z.comp (LinearMap.codRestrict W₁ (Ip W₁).mulVecLin
      (fun x => Ip_mem W₁ x)))) = ((Qe V₁).toLinearMap.comp Z).comp (LinearMap.codRestrict W₁
      (Ip W₁).mulVecLin (fun x => Ip_mem W₁ x)) from by
        rw [LinearMap.comp_assoc]]
  rw [LinearMap.range_comp, Submodule.map_comp, hC, Submodule.map_top]

/-- The preimage of a coordinate subspace under the coordinate model of a map `W₁ → V/V₁`. -/
theorem comap_XtOf (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : ↥W₁ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₁))
    (S : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ V₁) → 𝔽₂)) :
    Submodule.comap (XtOf V₁ W₁ Z).mulVecLin S =
      Submodule.map (ecW W₁).symm.toLinearMap
        (Submodule.comap Z (Submodule.comap (Qe V₁).toLinearMap S)) := by
  rw [XtOf, Commons.LinearAlgebra.Submodule.mulVecLin_toMatrix']
  rw [show ((Qe V₁).toLinearMap.comp (Z.comp (LinearMap.codRestrict W₁ (Ip W₁).mulVecLin
      (fun x => Ip_mem W₁ x)))) = ((Qe V₁).toLinearMap.comp Z).comp (LinearMap.codRestrict W₁
      (Ip W₁).mulVecLin (fun x => Ip_mem W₁ x)) from by
        rw [LinearMap.comp_assoc]]
  rw [Submodule.comap_comp, Submodule.comap_comp, codRestrict_Ip_eq_ecW,
    Submodule.comap_equiv_eq_map_symm]

/-- **The hybrid predicate on the coordinate model**: it is exactly the hybrid predicate of the
quotient space `V/V₁` at the pair `(V₂/V₁, W₂)`. -/
theorem hybridPredSub_Vco_Wco_XtOf (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Z : ↥W₁ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₁)) :
    hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂) (XtOf V₁ W₁ Z) ↔
      (Submodule.map (Submodule.mkQ V₁) V₂ ≤ LinearMap.range Z ∧
        Submodule.comap Z (Submodule.map (Submodule.mkQ V₁) V₂) ≤
          Submodule.comap W₁.subtype W₂) := by
  have hcomap : Submodule.comap (XtOf V₁ W₁ Z).mulVecLin (Vco V₁ V₂) =
      Submodule.map (ecW W₁).symm.toLinearMap
        (Submodule.comap Z (Submodule.map (Submodule.mkQ V₁) V₂)) := by
    rw [comap_XtOf, Vco, Submodule.comap_map_eq_of_injective (Qe V₁).injective]
  rw [hybridPredSub_iff, range_XtOf, hcomap, Wco]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(Submodule.map_le_map_iff_of_injective (Qe V₁).injective _ _).mp h1,
      (Submodule.map_le_map_iff_of_injective (ecW W₁).symm.injective _ _).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(Submodule.map_le_map_iff_of_injective (Qe V₁).injective _ _).mpr h1,
      (Submodule.map_le_map_iff_of_injective (ecW W₁).symm.injective _ _).mpr h2⟩

/-- The hybrid predicate on `charMat V₁ W₁ Y`, in terms of `Y`. -/
theorem hybridPredSub_Vco_Wco_charMat (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂) (charMat V₁ W₁ Y) ↔
      (Submodule.map (Submodule.mkQ V₁) V₂ ≤ LinearMap.range (YlinOf V₁ W₁ Y) ∧
        Submodule.comap (YlinOf V₁ W₁ Y) (Submodule.map (Submodule.mkQ V₁) V₂) ≤
          Submodule.comap W₁.subtype W₂) := by
  rw [charMat_eq_XtOf]
  exact hybridPredSub_Vco_Wco_XtOf V₁ W₁ V₂ W₂ (YlinOf V₁ W₁ Y)

/-- The rank order on the coordinate models of `X` and `Y`. -/
theorem plLE_charMat_iff (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    plLE (charMat V₃ W₃ X) (charMat V₃ W₃ Y) ↔ lmLE (YlinOf V₃ W₃ X) (YlinOf V₃ W₃ Y) := by
  rw [charMat_eq_XtOf, charMat_eq_XtOf, plLE, plLE_XtOf_iff]

theorem SwitchSummand_eq (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwitchSummand V₁ W₁ V₂ W₂ V₃ W₃ X f =
      (if Fr V₁ W₁ V₂ W₂ V₃ W₃ then Bare V₁ W₁ V₂ W₂ V₃ W₃ X f else 0) := rfl

theorem SwitchRHS_eq (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwitchRHS V₁ W₁ V₂ W₂ X f =
      ∑ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Fr V₁ W₁ V₂ W₂ p.1 p.2 then Bare V₁ W₁ V₂ W₂ p.1 p.2 X f else 0) := by
  rw [SwitchRHS]
  exact Finset.sum_congr rfl fun p _ => rfl

/-! ## Linearity in the function argument -/

/-- The hybrid derivative at position `0` is linear. -/
theorem Dop0_sum_smul {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (s : Finset ι) (c : ι → ℂ)
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Dop0 V₁ W₁ (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • Dop0 V₁ W₁ (g i) := by
  simp only [Dop0, Lsub, lapMulN_sum, lapMulN_smul, restr_sum, restr_smul]

/-- The `X`-derivative is linear. -/
theorem DopUp_sum_smul {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : Matrix (Fin n) (Fin m) 𝔽₂) (s : Finset ι)
    (c : ι → ℂ) (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DopUp V₁ W₁ X (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • DopUp V₁ W₁ X (g i) := by
  simp only [DopUp, lapMulN_sum, lapMulN_smul, restr_sum, restr_smul]

/-- The bare summand is linear. -/
theorem Bare_sum_smul {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : Matrix (Fin n) (Fin m) 𝔽₂) (s : Finset ι)
    (c : ι → ℂ) (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Bare V₁ W₁ V₂ W₂ V₃ W₃ X (∑ i ∈ s, c i • g i) =
      ∑ i ∈ s, c i • Bare V₁ W₁ V₂ W₂ V₃ W₃ X (g i) := by
  simp only [Bare, Dop0_sum_smul, lapMulN_sum, lapMulN_smul, restr_sum, restr_smul]

/-- The summand of the right-hand side is linear. -/
theorem SwitchSummand_sum_smul {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : Matrix (Fin n) (Fin m) 𝔽₂) (s : Finset ι)
    (c : ι → ℂ) (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwitchSummand V₁ W₁ V₂ W₂ V₃ W₃ X (∑ i ∈ s, c i • g i) =
      ∑ i ∈ s, c i • SwitchSummand V₁ W₁ V₂ W₂ V₃ W₃ X (g i) := by
  rw [SwitchSummand_eq]
  by_cases h : Fr V₁ W₁ V₂ W₂ V₃ W₃
  · rw [if_pos h, Bare_sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SwitchSummand_eq, if_pos h]
  · rw [if_neg h]
    exact (Finset.sum_eq_zero fun i _ => by rw [SwitchSummand_eq, if_neg h, smul_zero]).symm

/-- **Linearity of the right-hand side.** -/
theorem SwitchRHS_sum_smul {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : Matrix (Fin n) (Fin m) 𝔽₂) (s : Finset ι)
    (c : ι → ℂ) (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwitchRHS V₁ W₁ V₂ W₂ X (∑ i ∈ s, c i • g i) =
      ∑ i ∈ s, c i • SwitchRHS V₁ W₁ V₂ W₂ X (g i) := by
  rw [SwitchRHS_eq]
  have hstep : (∑ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Fr V₁ W₁ V₂ W₂ p.1 p.2 then
          Bare V₁ W₁ V₂ W₂ p.1 p.2 X (∑ i ∈ s, c i • g i) else 0)) =
      ∑ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Fr V₁ W₁ V₂ W₂ p.1 p.2 then
          ∑ i ∈ s, c i • Bare V₁ W₁ V₂ W₂ p.1 p.2 X (g i) else 0) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : Fr V₁ W₁ V₂ W₂ p.1 p.2
    · rw [if_pos h, if_pos h, Bare_sum_smul]
    · rw [if_neg h, if_neg h]
  rw [hstep, sum_ite_sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun z => c i • z) (SwitchRHS_eq V₁ W₁ V₂ W₂ X (g i)).symm

/-- **Linearity of the left-hand side.** -/
theorem SwitchLHS_sum_smul {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (s : Finset ι) (c : ι → ℂ)
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwitchLHS V₁ W₁ V₂ W₂ hV hW X (∑ i ∈ s, c i • g i) =
      ∑ i ∈ s, c i • SwitchLHS V₁ W₁ V₂ W₂ hV hW X (g i) := by
  simp only [SwitchLHS, DopDown, DopUp_sum_smul, lapMulN_sum, lapMulN_smul, restr_sum,
    restr_smul]

/-! ## The counting identity and the proposition -/

theorem switch_sum_eq (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    {X : Matrix (Fin n) (Fin m) 𝔽₂}
    (hXker : LinearMap.ker X.mulVecLin = W₁) (hXrange : LinearMap.range X.mulVecLin = V₁)
    (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁) (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    (if plLE X Y then (1 : ℂ) else 0) *
      (if hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂) (charMat V₁ W₁ Y) then (1 : ℂ) else 0) =
      ∑ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Fr V₁ W₁ V₂ W₂ p.1 p.2 then
          (if hybridPredSub p.1 p.2 Y then (1 : ℂ) else 0) *
          (if plLE (charMat p.1 p.2 X) (charMat p.1 p.2 Y) then (1 : ℂ) else 0)
        else 0) := by
  classical
  have hcomap : ∀ (p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂)),
      hybridPredSub p.1 p.2 Y → Submodule.comap Y.mulVecLin p.1 ≤ p.2 := by
    intro p hp w hw
    rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at hw
    exact hp.2 w hw
  have hzero : ∀ (p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂)),
      Fr V₁ W₁ V₂ W₂ p.1 p.2 → hybridPredSub p.1 p.2 Y →
      plLE (charMat p.1 p.2 X) (charMat p.1 p.2 Y) →
      plLE X Y ∧ hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂) (charMat V₁ W₁ Y) := by
    intro p hR hS hpl
    have hsw := Commons.LinearAlgebra.Submodule.swapping_places X.mulVecLin Y.mulVecLin V₁ V₂ p.1 W₁ W₂ p.2 hXker hXrange
      hR.2.1 hR.1 hR.2.2.2.2 hR.2.2.2.1 hS.1 (hcomap p hS) ((plLE_charMat_iff p.1 p.2 X Y).mp hpl)
    refine ⟨(plLE_iff_lmLE X Y).mpr hsw.1, ?_⟩
    exact (hybridPredSub_Vco_Wco_charMat V₁ W₁ V₂ W₂ Y).mpr ⟨hsw.2.1, hsw.2.2.1⟩
  have huniq : ∀ (p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂)),
      Fr V₁ W₁ V₂ W₂ p.1 p.2 → hybridPredSub p.1 p.2 Y →
      plLE (charMat p.1 p.2 X) (charMat p.1 p.2 Y) →
      p = (LinearMap.range (Y.mulVecLin - X.mulVecLin) ⊓ V₂,
           LinearMap.ker (Y.mulVecLin - X.mulVecLin) ⊔ W₂) := by
    intro p hR hS hpl
    have hsw := Commons.LinearAlgebra.Submodule.swapping_places X.mulVecLin Y.mulVecLin V₁ V₂ p.1 W₁ W₂ p.2 hXker hXrange
      hR.2.1 hR.1 hR.2.2.2.2 hR.2.2.2.1 hS.1 (hcomap p hS) ((plLE_charMat_iff p.1 p.2 X Y).mp hpl)
    exact Prod.ext (hsw.2.2.2.1.symm) (hsw.2.2.2.2.symm)
  have hex : plLE X Y → hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂) (charMat V₁ W₁ Y) →
      Fr V₁ W₁ V₂ W₂ (LinearMap.range (Y.mulVecLin - X.mulVecLin) ⊓ V₂)
        (LinearMap.ker (Y.mulVecLin - X.mulVecLin) ⊔ W₂) ∧
      hybridPredSub (LinearMap.range (Y.mulVecLin - X.mulVecLin) ⊓ V₂)
        (LinearMap.ker (Y.mulVecLin - X.mulVecLin) ⊔ W₂) Y ∧
      plLE (charMat (LinearMap.range (Y.mulVecLin - X.mulVecLin) ⊓ V₂)
        (LinearMap.ker (Y.mulVecLin - X.mulVecLin) ⊔ W₂) X)
        (charMat (LinearMap.range (Y.mulVecLin - X.mulVecLin) ⊓ V₂)
        (LinearMap.ker (Y.mulVecLin - X.mulVecLin) ⊔ W₂) Y) := by
    intro h1 h2
    have hQ := (hybridPredSub_Vco_Wco_charMat V₁ W₁ V₂ W₂ Y).mp h2
    have hXY := (plLE_iff_lmLE X Y).mp h1
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ :=
      Commons.LinearAlgebra.Submodule.exists_complement_pair_of_le_rank X.mulVecLin Y.mulVecLin
        V₁ V₂ W₁ W₂ hXker hXrange hV hW hXY hQ.1 hQ.2
    exact ⟨⟨h₂, h₁, le_sup_right, h₄, h₃⟩, ⟨h₅, h₆⟩,
      (plLE_charMat_iff _ _ X Y).mpr h₇⟩
  have hlhs : (if plLE X Y then (1 : ℂ) else 0) *
      (if hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂) (charMat V₁ W₁ Y) then (1 : ℂ) else 0) =
      (if plLE X Y ∧ hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂) (charMat V₁ W₁ Y)
        then (1 : ℂ) else 0) := by
    by_cases h1 : plLE X Y <;> by_cases h2 : hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂)
      (charMat V₁ W₁ Y) <;> simp [h1, h2]
  rw [hlhs]
  by_cases h : plLE X Y ∧ hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂) (charMat V₁ W₁ Y)
  · rw [if_pos h]
    obtain ⟨hR₀, hS₀, hpl₀⟩ := hex h.1 h.2
    rw [Finset.sum_eq_single (LinearMap.range (Y.mulVecLin - X.mulVecLin) ⊓ V₂,
      LinearMap.ker (Y.mulVecLin - X.mulVecLin) ⊔ W₂)]
    · rw [if_pos hR₀, if_pos hS₀, if_pos hpl₀, mul_one]
    · intro p _ hp
      by_cases hpR : Fr V₁ W₁ V₂ W₂ p.1 p.2
      · by_cases hpS : hybridPredSub p.1 p.2 Y
        · by_cases hp2 : plLE (charMat p.1 p.2 X) (charMat p.1 p.2 Y)
          · exact absurd (huniq p hpR hpS hp2) hp
          · rw [if_pos hpR, if_pos hpS, if_neg hp2, mul_zero]
        · rw [if_pos hpR, if_neg hpS, zero_mul]
      · rw [if_neg hpR]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun p _ => ?_).symm
    by_cases hpR : Fr V₁ W₁ V₂ W₂ p.1 p.2
    · by_cases hpS : hybridPredSub p.1 p.2 Y
      · by_cases hp2 : plLE (charMat p.1 p.2 X) (charMat p.1 p.2 Y)
        · exact absurd (hzero p hpR hpS hp2) h
        · rw [if_pos hpR, if_pos hpS, if_neg hp2, mul_zero]
      · rw [if_pos hpR, if_neg hpS, zero_mul]
    · rw [if_neg hpR]

/-- **Prop "switching the roles between the derivatives"** (arXiv:2209.04243 §8). -/
theorem switching_roles (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    {X : Matrix (Fin n) (Fin m) 𝔽₂}
    (hXker : LinearMap.ker X.mulVecLin = W₁) (hXrange : LinearMap.range X.mulVecLin = V₁)
    (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwitchLHS V₁ W₁ V₂ W₂ hV hW X f = SwitchRHS V₁ W₁ V₂ W₂ X f := by
  conv_lhs => rw [eq_sum_fcoeff_mchar f]
  rw [SwitchLHS_sum_smul]
  conv_rhs => rw [eq_sum_fcoeff_mchar f]
  rw [SwitchRHS_sum_smul]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [SwitchLHS_mchar, SwitchRHS_mchar, switch_sum_eq V₁ W₁ V₂ W₂ hXker hXrange hV hW Y]

/-! ## Prop (2): the shifted version -/

/-- The shifted `X`-derivative. -/
noncomputable def DopUpS (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (S : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ :=
  restr (Qp V₁) (Ip W₁) (shift S (lapMulN (plLE X) f))

/-- The shifted hybrid derivative at position `0`. -/
noncomputable def Dop0S (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (S : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ :=
  restr (Qp V₁) (Ip W₁) (shift S (Lsub V₁ W₁ f))

/-- The shifted hybrid derivative `D_{V₂/V₁,W₂,T}`. -/
noncomputable def DopDownS (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (T : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂)
    (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁)
    (g : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ :=
  restr (Qsup V₂ V₁ hV) (Isub W₂ W₁ hW)
    (shift T (lapMulN (hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂)) g))

/-- The left-hand side `D_{V₂/V₁,W₂,T} ∘ D_{X,S}` of Prop (2). -/
noncomputable def SwitchLHSS (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (S : Matrix (Fin m) (Fin n) 𝔽₂)
    (T : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ :=
  DopDownS V₁ W₁ V₂ W₂ T hV hW (DopUpS V₁ W₁ X S f)

/-- The bare shifted summand `D_{X(W₃,V/V₃)} ∘ D_{V₃,W₃,S'}`. -/
noncomputable def BareS (_V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (_W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (S : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ :=
  restr (QsupT V₂ V₃) (IsubT W₂ W₃)
    (lapMulN (plLE (charMat V₃ W₃ X)) (Dop0S V₃ W₃ S f))

noncomputable def SwitchSummandS (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (S : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ :=
  if Fr V₁ W₁ V₂ W₂ V₃ W₃ then BareS V₁ W₁ V₂ W₂ V₃ W₃ X S f else 0

/-- The right-hand side `Σ D_{X(W₃,V/V₃)} ∘ D_{V₃,W₃,S'}` of Prop (2). -/
noncomputable def SwitchRHSS (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (S : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ :=
  ∑ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
    SwitchSummandS V₁ W₁ V₂ W₂ p.1 p.2 X S f

theorem DopUp_smul (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (c : ℂ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DopUp V₁ W₁ X (c • f) = c • DopUp V₁ W₁ X f := by
  simp only [DopUp, lapMulN_smul, restr_smul]

theorem Dop0S_smul (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (S : Matrix (Fin m) (Fin n) 𝔽₂) (c : ℂ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Dop0S V₁ W₁ S (c • f) = c • Dop0S V₁ W₁ S f := by
  simp only [Dop0S, Lsub, lapMulN_smul, shift_smul, restr_smul]

theorem DopDownS_smul (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (T : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂)
    (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁) (c : ℂ)
    (g : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ) :
    DopDownS V₁ W₁ V₂ W₂ T hV hW (c • g) = c • DopDownS V₁ W₁ V₂ W₂ T hV hW g := by
  simp only [DopDownS, lapMulN_smul, shift_smul, restr_smul]

theorem DopUpS_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X Y : Matrix (Fin n) (Fin m) 𝔽₂) (S : Matrix (Fin m) (Fin n) 𝔽₂) :
    DopUpS V₁ W₁ X S (mchar Y) =
      ((mchar Y S) * (if plLE X Y then (1 : ℂ) else 0)) •
        (mchar (charMat V₁ W₁ Y) :
          Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ) := by
  rw [DopUpS, lapMulN_mchar, shift_smul, shift_mchar, restr_smul, restr_smul, restr_mchar,
    smul_smul, charMat, mul_comm]

theorem Dop0S_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (S : Matrix (Fin m) (Fin n) 𝔽₂) (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    Dop0S V₁ W₁ S (mchar Y) =
      ((mchar Y S) * (if hybridPredSub V₁ W₁ Y then (1 : ℂ) else 0)) •
        (mchar (charMat V₁ W₁ Y) :
          Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ) := by
  rw [Dop0S, Lsub, lapMulN_mchar, shift_smul, shift_mchar, restr_smul, restr_smul, restr_mchar,
    smul_smul, charMat, mul_comm]

theorem DopDownS_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (T : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂)
    (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁)
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₁)) (Fin (Module.finrank 𝔽₂ W₁)) 𝔽₂) :
    DopDownS V₁ W₁ V₂ W₂ T hV hW (mchar Z) =
      ((mchar Z T) * (if hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂) Z then (1 : ℂ) else 0)) •
        (mchar (Qsup V₂ V₁ hV * Z * Isub W₂ W₁ hW) :
          Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ) := by
  rw [DopDownS, lapMulN_mchar, shift_smul, shift_mchar, restr_smul, restr_smul, restr_mchar,
    smul_smul, mul_comm]

theorem SwitchSummandS_eq (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (S : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwitchSummandS V₁ W₁ V₂ W₂ V₃ W₃ X S f =
      (if Fr V₁ W₁ V₂ W₂ V₃ W₃ then BareS V₁ W₁ V₂ W₂ V₃ W₃ X S f else 0) := rfl

theorem SwitchRHSS_eq (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (S : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwitchRHSS V₁ W₁ V₂ W₂ X S f =
      ∑ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Fr V₁ W₁ V₂ W₂ p.1 p.2 then BareS V₁ W₁ V₂ W₂ p.1 p.2 X S f else 0) := by
  rw [SwitchRHSS]
  exact Finset.sum_congr rfl fun p _ => rfl

theorem SwitchSummandS_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X Y : Matrix (Fin n) (Fin m) 𝔽₂) (S : Matrix (Fin m) (Fin n) 𝔽₂) :
    SwitchSummandS V₁ W₁ V₂ W₂ V₃ W₃ X S (mchar Y) =
      ((mchar Y S) * (if Fr V₁ W₁ V₂ W₂ V₃ W₃ then
          (if hybridPredSub V₃ W₃ Y then (1 : ℂ) else 0) *
          (if plLE (charMat V₃ W₃ X) (charMat V₃ W₃ Y) then (1 : ℂ) else 0)
        else 0)) •
        (mchar (charMat V₂ W₂ Y) :
          Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ) := by
  rw [SwitchSummandS_eq, BareS]
  by_cases h : Fr V₁ W₁ V₂ W₂ V₃ W₃
  · have hV : V₃ ≤ V₂ := le_sup_left.trans_eq h.2.1
    have hW : W₂ ≤ W₃ := h.2.2.1
    have hkey : Qsup V₂ V₃ hV * (charMat V₃ W₃ Y) * Isub W₂ W₃ hW = charMat V₂ W₂ Y := by
      rw [show Qsup V₂ V₃ hV * (charMat V₃ W₃ Y) * Isub W₂ W₃ hW =
          (Qsup V₂ V₃ hV * Qp V₃) * Y * (Ip W₃ * Isub W₂ W₃ hW) from by
            simp only [Matrix.mul_assoc, charMat],
        Qsup_mul_Qp, Ip_mul_Isub]
      rfl
    rw [if_pos h, if_pos h, Dop0S_mchar, lapMulN_smul, restr_smul, QsupT_eq V₂ V₃ hV,
      IsubT_eq W₂ W₃ hW, restr_lapMulN_mchar, hkey]
    simp only [smul_smul]
    congr 1
    ring
  · rw [if_neg h, if_neg h, mul_zero, zero_smul]

theorem SwitchRHSS_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X Y : Matrix (Fin n) (Fin m) 𝔽₂) (S : Matrix (Fin m) (Fin n) 𝔽₂) :
    SwitchRHSS V₁ W₁ V₂ W₂ X S (mchar Y) =
      ((mchar Y S) * (∑ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Fr V₁ W₁ V₂ W₂ p.1 p.2 then
          (if hybridPredSub p.1 p.2 Y then (1 : ℂ) else 0) *
          (if plLE (charMat p.1 p.2 X) (charMat p.1 p.2 Y) then (1 : ℂ) else 0)
        else 0))) •
        (mchar (charMat V₂ W₂ Y) :
          Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ) := by
  rw [SwitchRHSS, Finset.sum_congr rfl (fun p _ => SwitchSummandS_mchar V₁ W₁ V₂ W₂ p.1 p.2 X Y S),
    ← Finset.sum_smul]
  congr 1
  exact (Finset.mul_sum Finset.univ (fun p : Submodule 𝔽₂ (Fin n → 𝔽₂) ×
      Submodule 𝔽₂ (Fin m → 𝔽₂) =>
      (if Fr V₁ W₁ V₂ W₂ p.1 p.2 then
        (if hybridPredSub p.1 p.2 Y then (1 : ℂ) else 0) *
        (if plLE (charMat p.1 p.2 X) (charMat p.1 p.2 Y) then (1 : ℂ) else 0)
      else 0)) (mchar Y S)).symm

theorem SwitchLHSS_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁) (X Y : Matrix (Fin n) (Fin m) 𝔽₂)
    (S : Matrix (Fin m) (Fin n) 𝔽₂)
    (T : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂) :
    SwitchLHSS V₁ W₁ V₂ W₂ hV hW X S T (mchar Y) =
      ((mchar Y S) * (mchar (charMat V₁ W₁ Y) T) * (if plLE X Y then (1 : ℂ) else 0) *
        (if hybridPredSub (Vco V₁ V₂) (Wco W₁ W₂) (charMat V₁ W₁ Y)
          then (1 : ℂ) else 0)) •
        (mchar (charMat V₂ W₂ Y) :
          Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ) := by
  have hkey : Qsup V₂ V₁ hV * (charMat V₁ W₁ Y) * Isub W₂ W₁ hW = charMat V₂ W₂ Y := by
    rw [show Qsup V₂ V₁ hV * (charMat V₁ W₁ Y) * Isub W₂ W₁ hW =
        (Qsup V₂ V₁ hV * Qp V₁) * Y * (Ip W₁ * Isub W₂ W₁ hW) from by
          simp only [Matrix.mul_assoc, charMat],
      Qsup_mul_Qp, Ip_mul_Isub]
    rfl
  rw [SwitchLHSS, DopUpS_mchar, DopDownS_smul, DopDownS_mchar, hkey]
  simp only [smul_smul]
  congr 1
  ring

/-- The scalar cyclicity identity `mchar Y (Ip W₁ * T * Qp V₁) = mchar (charMat V₁ W₁ Y) T`. -/
theorem mchar_Ip_mul_mul_Qp (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂)
    (T : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂) :
    mchar Y (Ip W₁ * T * Qp V₁) = mchar (charMat V₁ W₁ Y) T := by
  rw [mchar_eq_trace, mchar_eq_trace, charMat]
  congr 1
  rw [show Y * (Ip W₁ * T * Qp V₁) = (Y * Ip W₁ * T) * Qp V₁ from by simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_cycle (Y * Ip W₁) T (Qp V₁)]
  rw [show (Qp V₁ * (Y * Ip W₁) * T) = Qp V₁ * Y * Ip W₁ * T from by simp only [Matrix.mul_assoc]]

theorem DopUpS_smul (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (S : Matrix (Fin m) (Fin n) 𝔽₂) (c : ℂ)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DopUpS V₁ W₁ X S (c • f) = c • DopUpS V₁ W₁ X S f := by
  simp only [DopUpS, lapMulN_smul, shift_smul, restr_smul]

theorem DopUpS_sum_smul {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (S : Matrix (Fin m) (Fin n) 𝔽₂) (s : Finset ι) (c : ι → ℂ)
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DopUpS V₁ W₁ X S (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • DopUpS V₁ W₁ X S (g i) := by
  simp only [DopUpS, lapMulN_sum, lapMulN_smul, shift_sum, shift_smul, restr_sum, restr_smul]

theorem Dop0S_sum_smul {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (S : Matrix (Fin m) (Fin n) 𝔽₂) (s : Finset ι)
    (c : ι → ℂ) (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Dop0S V₁ W₁ S (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • Dop0S V₁ W₁ S (g i) := by
  simp only [Dop0S, Lsub, lapMulN_sum, lapMulN_smul, shift_sum, shift_smul, restr_sum, restr_smul]

theorem BareS_sum_smul {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (S : Matrix (Fin m) (Fin n) 𝔽₂) (s : Finset ι) (c : ι → ℂ)
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    BareS V₁ W₁ V₂ W₂ V₃ W₃ X S (∑ i ∈ s, c i • g i) =
      ∑ i ∈ s, c i • BareS V₁ W₁ V₂ W₂ V₃ W₃ X S (g i) := by
  simp only [BareS, Dop0S_sum_smul, lapMulN_sum, lapMulN_smul, restr_sum, restr_smul]

theorem SwitchSummandS_sum_smul {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₃ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (S : Matrix (Fin m) (Fin n) 𝔽₂) (s : Finset ι) (c : ι → ℂ)
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwitchSummandS V₁ W₁ V₂ W₂ V₃ W₃ X S (∑ i ∈ s, c i • g i) =
      ∑ i ∈ s, c i • SwitchSummandS V₁ W₁ V₂ W₂ V₃ W₃ X S (g i) := by
  rw [SwitchSummandS_eq]
  by_cases h : Fr V₁ W₁ V₂ W₂ V₃ W₃
  · rw [if_pos h, BareS_sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SwitchSummandS_eq, if_pos h]
  · rw [if_neg h]
    exact (Finset.sum_eq_zero fun i _ => by rw [SwitchSummandS_eq, if_neg h, smul_zero]).symm

theorem DopDownS_sum_smul {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (T : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂)
    (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁) (s : Finset ι) (c : ι → ℂ)
    (g : ι → Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ) :
    DopDownS V₁ W₁ V₂ W₂ T hV hW (∑ i ∈ s, c i • g i) =
      ∑ i ∈ s, c i • DopDownS V₁ W₁ V₂ W₂ T hV hW (g i) := by
  simp only [DopDownS, lapMulN_sum, lapMulN_smul, shift_sum, shift_smul, restr_sum, restr_smul]

theorem SwitchRHSS_sum_smul {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (S : Matrix (Fin m) (Fin n) 𝔽₂) (s : Finset ι) (c : ι → ℂ)
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwitchRHSS V₁ W₁ V₂ W₂ X S (∑ i ∈ s, c i • g i) =
      ∑ i ∈ s, c i • SwitchRHSS V₁ W₁ V₂ W₂ X S (g i) := by
  rw [SwitchRHSS_eq]
  have hstep : (∑ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Fr V₁ W₁ V₂ W₂ p.1 p.2 then
          BareS V₁ W₁ V₂ W₂ p.1 p.2 X S (∑ i ∈ s, c i • g i) else 0)) =
      ∑ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Fr V₁ W₁ V₂ W₂ p.1 p.2 then
          ∑ i ∈ s, c i • BareS V₁ W₁ V₂ W₂ p.1 p.2 X S (g i) else 0) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : Fr V₁ W₁ V₂ W₂ p.1 p.2
    · rw [if_pos h, if_pos h, BareS_sum_smul]
    · rw [if_neg h, if_neg h]
  rw [hstep, sum_ite_sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun z => c i • z) (SwitchRHSS_eq V₁ W₁ V₂ W₂ X S (g i)).symm

theorem SwitchLHSS_sum_smul {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (S : Matrix (Fin m) (Fin n) 𝔽₂)
    (T : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂)
    (s : Finset ι) (c : ι → ℂ) (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwitchLHSS V₁ W₁ V₂ W₂ hV hW X S T (∑ i ∈ s, c i • g i) =
      ∑ i ∈ s, c i • SwitchLHSS V₁ W₁ V₂ W₂ hV hW X S T (g i) := by
  rw [SwitchLHSS]
  simp only [DopUpS_sum_smul, DopDownS_sum_smul]
  rfl

/-- **Prop "switching the roles between the derivatives", part (2)** (arXiv:2209.04243 §8):

  `D_{V₂/V₁,W₂,T} ∘ D_{X,S} = Σ_{V₃ ∈ 𝓕₁, W₃ ∈ 𝓕₂} D_{X(W₃,V/V₃)} ∘ D_{V₃,W₃,S+T(W,V)}`

where the shift `T(W,V)` on the `W`-side is the lift `Ip W₁ * T * Qp V₁` of `T` to `L(V,W)`. -/
theorem switching_roles_shift (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    {X : Matrix (Fin n) (Fin m) 𝔽₂}
    (hXker : LinearMap.ker X.mulVecLin = W₁) (hXrange : LinearMap.range X.mulVecLin = V₁)
    (hV : V₁ ≤ V₂) (hW : W₂ ≤ W₁) (S : Matrix (Fin m) (Fin n) 𝔽₂)
    (T : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwitchLHSS V₁ W₁ V₂ W₂ hV hW X S T f =
      SwitchRHSS V₁ W₁ V₂ W₂ X (S + Ip W₁ * T * Qp V₁) f := by
  conv_lhs => rw [eq_sum_fcoeff_mchar f]
  rw [SwitchLHSS_sum_smul]
  conv_rhs => rw [eq_sum_fcoeff_mchar f]
  rw [SwitchRHSS_sum_smul]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [SwitchLHSS_mchar, SwitchRHSS_mchar]
  congr 1
  rw [mchar_add_right, mchar_Ip_mul_mul_Qp, ← switch_sum_eq V₁ W₁ V₂ W₂ hXker hXrange hV hW Y]
  congr 1
  simp only [mul_assoc]

/-! ## `prop:composition of derivatives` -/

/-- **Prop "composition of derivatives"** (arXiv:2209.04243 §8): for `V₂ ≤ V₁ ≤ V`,
`W₁ ≤ W₂ ≤ W`, `T ∈ L(V,W)` and `S ∈ L(V/V₂,W₂)`,
`D_{V₁/V₂,W₁,S} ∘ D_{V₂,W₂,T} = D_{V₁,W₁,T+S(V,W)}`. -/
theorem composition_of_derivatives (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂)
    (S : Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂)
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DopDownS V₂ W₂ V₁ W₁ S hV hW (Dop0S V₂ W₂ T f) =
      Dop0S V₁ W₁ (T + Ip W₂ * S * Qp V₂) f := by
  conv_lhs => rw [eq_sum_fcoeff_mchar f]
  rw [Dop0S_sum_smul, DopDownS_sum_smul]
  conv_rhs => rw [eq_sum_fcoeff_mchar f]
  rw [Dop0S_sum_smul]
  refine Finset.sum_congr rfl fun Y _ => ?_
  have hkey : Qsup V₁ V₂ hV * (charMat V₂ W₂ Y) * Isub W₁ W₂ hW = charMat V₁ W₁ Y := by
    rw [show Qsup V₁ V₂ hV * (charMat V₂ W₂ Y) * Isub W₁ W₂ hW =
        (Qsup V₁ V₂ hV * Qp V₂) * Y * (Ip W₂ * Isub W₁ W₂ hW) from by
          simp only [Matrix.mul_assoc, charMat],
      Qsup_mul_Qp, Ip_mul_Isub]
    rfl
  have hcyc : mchar (charMat V₂ W₂ Y) S = mchar Y (Ip W₂ * S * Qp V₂) :=
    (mchar_Ip_mul_mul_Qp V₂ W₂ Y S).symm
  have hiff : hybridPredSub (Vco V₂ V₁) (Wco W₂ W₁) (charMat V₂ W₂ Y) ↔
      (Submodule.map (Submodule.mkQ V₂) V₁ ≤ LinearMap.range (YlinOf V₂ W₂ Y) ∧
        Submodule.comap (YlinOf V₂ W₂ Y) (Submodule.map (Submodule.mkQ V₂) V₁) ≤
          Submodule.comap W₂.subtype W₁) := hybridPredSub_Vco_Wco_charMat V₂ W₂ V₁ W₁ Y
  have hiff2 : hybridPredSub V₁ W₁ Y ↔ (hybridPredSub V₂ W₂ Y ∧
      (Submodule.map (Submodule.mkQ V₂) V₁ ≤ LinearMap.range (YlinOf V₂ W₂ Y) ∧
        Submodule.comap (YlinOf V₂ W₂ Y) (Submodule.map (Submodule.mkQ V₂) V₁) ≤
          Submodule.comap W₂.subtype W₁)) := by
    have h := Commons.LinearAlgebra.Submodule.range_le_range_iff_restrict_quotient Y.mulVecLin
      V₁ V₂ W₁ W₂ hV hW
    constructor
    · intro hx
      exact ⟨⟨(h.mp hx).1, (h.mp hx).2.1⟩, (h.mp hx).2.2⟩
    · intro hx
      exact h.mpr ⟨hx.1.1, hx.1.2, hx.2.1, hx.2.2⟩
  have hscal : (if hybridPredSub V₁ W₁ Y then (1 : ℂ) else 0) =
      (if hybridPredSub V₂ W₂ Y then (1 : ℂ) else 0) *
        (if hybridPredSub (Vco V₂ V₁) (Wco W₂ W₁) (charMat V₂ W₂ Y)
          then (1 : ℂ) else 0) := by
    by_cases h2 : hybridPredSub V₂ W₂ Y
    · by_cases h3 : hybridPredSub (Vco V₂ V₁) (Wco W₂ W₁) (charMat V₂ W₂ Y)
      · have h1 : hybridPredSub V₁ W₁ Y := hiff2.mpr ⟨h2, (hiff.mp h3).1, (hiff.mp h3).2⟩
        rw [if_pos h1, if_pos h2, if_pos h3]; ring
      · have h1 : ¬ hybridPredSub V₁ W₁ Y := by
          intro h
          exact h3 (hiff.mpr ⟨(hiff2.mp h).2.1, (hiff2.mp h).2.2⟩)
        rw [if_neg h1, if_pos h2, if_neg h3]; ring
    · have h1 : ¬ hybridPredSub V₁ W₁ Y := fun h => h2 (hiff2.mp h).1
      rw [if_neg h1, if_neg h2]; ring
  rw [Dop0S_mchar, DopDownS_smul, DopDownS_mchar, hkey, hcyc, Dop0S_mchar]
  simp only [smul_smul]
  congr 1
  rw [mchar_add_right, hscal]
  ring

end

end Submission.Grassmann
