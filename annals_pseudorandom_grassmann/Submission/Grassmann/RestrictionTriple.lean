import Submission.Grassmann.HypHyperUC

/-!
# The triple `(W₂, V₂, X)` of `lem:restrictiond of compositions of Laplacians`

The hard identity behind `lem:bounds on composition` of arXiv:2209.04243 is
Proposition "taking restrictions of Laplacians":

  `(L_{V₁}∘L_{W₁}[f])_{(V₁,W₁)→T} = Σ_{V₂ ⊆ V₁, W₂ ⊇ W₁} Σ_{X̃ : W₂/W₁ ≅ V₁/V₂} D_X ∘ D_{V₂,W₂,T} f`.

Its linear-algebraic core is the paper's `lem:restrictiond of compositions of Laplacians`: for
every character index `Y` with `V₁ ⊆ Im Y` and `ker Y ⊆ W₁` there is a **unique** triple
`(W₂, V₂, X)` with

  `W₂ = W₁ + Y⁻¹(V₁)`,  `V₂ = Y(W₁) ∩ V₁`,  `X : W₂ → V₁/V₂` the map induced by `Y`

and `X ≤ Y|_{W₂}^{V/V₂}`.

This file carries out the linear algebra:

* `W2sub V₁ W₁ Y = Y⁻¹(V₁) ⊔ W₁` and `V2sub V₁ W₁ Y = Y(W₁) ⊓ V₁`;
* `comap_V2sub_eq` — `Y⁻¹(V₂) = W₁ ⊓ Y⁻¹(V₁)` (in particular `Y⁻¹(V₂) ⊆ W₂`);
* `finrank_W2sub_sub_W1` — the dimension identity
  `dim W₂ - dim W₁ = dim V₁ - dim V₂`;
* `Xlin` — the induced linear map `W₂ → V/V₂`, with
  `ker_Xlin` (`ker X = W₁`) and `range_Xlin` (`Im X = V₁/V₂`);
* `Ylin` — the map `Y₂ = Y|_{W₂}^{V/V₂}`, with `Xlin ≤ Ylin` (`Xlin_le_Ylin`, the paper's
  `X ≤ Y₂` condition);
* the uniqueness statements `W2sub_unique`, `V2sub_unique`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-- `w + w = 0` for vectors over `𝔽₂` (there is no global `CharP` instance for function types). -/
lemma vec_add_self {m : ℕ} (w : Fin m → 𝔽₂) : w + w = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (w i)

/-- `A = Y⁻¹(V₁)`: the preimage of `V₁` under the character `Y`. -/
abbrev ASub (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    Submodule 𝔽₂ (Fin m → 𝔽₂) :=
  Submodule.comap Y.mulVecLin V₁

/-- `W₂ = W₁ + Y⁻¹(V₁)`: the subspace of the domain appearing in the paper's
`lem:restrictiond of compositions of Laplacians`. -/
abbrev W2sub (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) : Submodule 𝔽₂ (Fin m → 𝔽₂) :=
  ASub V₁ Y ⊔ W₁

/-- `V₂ = Y(W₁) ∩ V₁`: the subspace of the codomain appearing in the paper's
`lem:restrictiond of compositions of Laplacians`. -/
abbrev V2sub (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) : Submodule 𝔽₂ (Fin n → 𝔽₂) :=
  Submodule.map Y.mulVecLin W₁ ⊓ V₁

lemma le_W2sub (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) : W₁ ≤ W2sub V₁ W₁ Y := le_sup_right

lemma V2sub_le (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) : V2sub V₁ W₁ Y ≤ V₁ := inf_le_right

lemma V2sub_le_map (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    V2sub V₁ W₁ Y ≤ Submodule.map Y.mulVecLin W₁ := inf_le_left

/-- `Y⁻¹(V₁) ⊆ W₂` is built into the definition of `W₂`. -/
lemma comap_V1_le_W2sub (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) : ASub V₁ Y ≤ W2sub V₁ W₁ Y := le_sup_left

/-- **`Y⁻¹(V₂) = W₁ ⊓ Y⁻¹(V₁)`**: the crucial computation in the paper's construction.  It uses
`ker Y ⊆ W₁` (which holds whenever `Y` is kept by `L_{V₁,W₁}`).  In particular `Y⁻¹(V₂) ⊆ W₂`. -/
theorem comap_V2sub_eq {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Y : Matrix (Fin n) (Fin m) 𝔽₂} (hW : LinearMap.ker Y.mulVecLin ≤ W₁) :
    Submodule.comap Y.mulVecLin (V2sub V₁ W₁ Y) = W₁ ⊓ ASub V₁ Y := by
  rw [V2sub, Submodule.comap_inf, Submodule.comap_map_eq_self hW]

/-- `Y⁻¹(V₂) ⊆ W₂`. -/
theorem comap_V2sub_le_W2sub {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Y : Matrix (Fin n) (Fin m) 𝔽₂} (hW : LinearMap.ker Y.mulVecLin ≤ W₁) :
    Submodule.comap Y.mulVecLin (V2sub V₁ W₁ Y) ≤ W2sub V₁ W₁ Y := by
  rw [comap_V2sub_eq hW]
  exact le_trans inf_le_right le_sup_left

/-- **`Y(W₂) = Y(W₁) ⊔ V₁`**, i.e. `V₁ ⊆ Y(W₂)` whenever `V₁ ⊆ Y(W)`. -/
theorem map_W2sub_eq {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Y : Matrix (Fin n) (Fin m) 𝔽₂} (hV : V₁ ≤ LinearMap.range Y.mulVecLin) :
    Submodule.map Y.mulVecLin (W2sub V₁ W₁ Y) = Submodule.map Y.mulVecLin W₁ ⊔ V₁ := by
  rw [W2sub, ASub, Submodule.map_sup, Submodule.map_comap_eq, inf_eq_right.mpr hV]
  exact sup_comm _ _

/-- `V₁ ⊆ Y(W₂)`. -/
theorem V1_le_map_W2sub {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Y : Matrix (Fin n) (Fin m) 𝔽₂} (hV : V₁ ≤ LinearMap.range Y.mulVecLin) :
    V₁ ≤ Submodule.map Y.mulVecLin (W2sub V₁ W₁ Y) := by
  rw [map_W2sub_eq hV]
  exact le_sup_right

/-- `Y(W₁ ⊓ Y⁻¹(V₁)) ⊆ V₂`. -/
theorem map_inf_le_V2sub (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    Submodule.map Y.mulVecLin (W₁ ⊓ ASub V₁ Y) ≤ V2sub V₁ W₁ Y := by
  rintro v ⟨w, hw, rfl⟩
  exact ⟨Submodule.mem_map.mpr ⟨w, hw.1, rfl⟩, hw.2⟩

/-! ## The dimension identity -/

/-- **`dim W₂ - dim W₁ = dim V₁ - dim V₂`**: this is what makes the induced map `X : W₂/W₁ → V₁/V₂`
an isomorphism. -/
theorem finrank_W2sub_sub_finrank_W1 {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)} {Y : Matrix (Fin n) (Fin m) 𝔽₂}
    (hV : V₁ ≤ LinearMap.range Y.mulVecLin) (hW : LinearMap.ker Y.mulVecLin ≤ W₁) :
    Module.finrank 𝔽₂ ↥(W2sub V₁ W₁ Y) - Module.finrank 𝔽₂ ↥W₁ =
      Module.finrank 𝔽₂ ↥V₁ - Module.finrank 𝔽₂ ↥(V2sub V₁ W₁ Y) := by
  have hleW : W₁ ≤ W2sub V₁ W₁ Y := le_W2sub V₁ W₁ Y
  have hker₂ : W2sub V₁ W₁ Y ⊓ LinearMap.ker Y.mulVecLin = LinearMap.ker Y.mulVecLin :=
    inf_eq_right.mpr (le_trans hW hleW)
  have hker₁ : W₁ ⊓ LinearMap.ker Y.mulVecLin = LinearMap.ker Y.mulVecLin :=
    inf_eq_right.mpr hW
  have hm₂ : Module.finrank 𝔽₂ ↥(Submodule.map Y.mulVecLin (W2sub V₁ W₁ Y)) =
      Module.finrank 𝔽₂ ↥(W2sub V₁ W₁ Y) - Module.finrank 𝔽₂ ↥(LinearMap.ker Y.mulVecLin) := by
    rw [Commons.LinearAlgebra.finrank_map_eq Y.mulVecLin (W2sub V₁ W₁ Y), hker₂]
  have hm₁ : Module.finrank 𝔽₂ ↥(Submodule.map Y.mulVecLin W₁) =
      Module.finrank 𝔽₂ ↥W₁ - Module.finrank 𝔽₂ ↥(LinearMap.ker Y.mulVecLin) := by
    rw [Commons.LinearAlgebra.finrank_map_eq Y.mulVecLin W₁, hker₁]
  have hmap : Submodule.map Y.mulVecLin (W2sub V₁ W₁ Y) =
      Submodule.map Y.mulVecLin W₁ ⊔ V₁ := map_W2sub_eq hV
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.map Y.mulVecLin W₁) V₁
  have hV₂ : V2sub V₁ W₁ Y = Submodule.map Y.mulVecLin W₁ ⊓ V₁ := rfl
  have hfin : Module.finrank 𝔽₂ ↥(LinearMap.ker Y.mulVecLin) ≤ Module.finrank 𝔽₂ ↥W₁ :=
    Submodule.finrank_mono hW
  have hfin' : Module.finrank 𝔽₂ ↥W₁ ≤ Module.finrank 𝔽₂ ↥(W2sub V₁ W₁ Y) :=
    Submodule.finrank_mono hleW
  rw [hmap] at hm₂
  rw [hV₂]
  omega

/-! ## The induced map `X : W₂ → V/V₂`

For `z ∈ A = Y⁻¹(V₁)` the vector `Y z` is in `V₁`; this gives a linear map `φ : A → V/V₂` whose
kernel contains `W₁ ⊓ A`.  Descending to `A/(W₁ ⊓ A)` and using the second isomorphism theorem
`A/(W₁ ⊓ A) ≅ (W₁ + A)/W₁ = W₂/W₁`, we get the map `X` of the paper. -/

/-- The map `φ : A → V/V₂`, `z ↦ Y z`. -/
def phiLin (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) : ↥(ASub V₁ Y) →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V2sub V₁ W₁ Y) :=
  (Submodule.mkQ (V2sub V₁ W₁ Y)).comp (Y.mulVecLin.comp (ASub V₁ Y).subtype)

lemma phiLin_apply (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) (z : ↥(ASub V₁ Y)) :
    phiLin V₁ W₁ Y z = Submodule.mkQ (V2sub V₁ W₁ Y) (Y.mulVecLin z.1) := rfl

/-- `W₁ ⊓ A` is contained in the kernel of `φ`: if `z ∈ W₁` then `Y z ∈ V₂`. -/
theorem inf_le_ker_phiLin (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    Submodule.comap (ASub V₁ Y).subtype W₁ ≤ LinearMap.ker (phiLin V₁ W₁ Y) := by
  intro z hz
  have hz' : (z : Fin m → 𝔽₂) ∈ W₁ := hz
  rw [LinearMap.mem_ker, phiLin_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨Submodule.mem_map.mpr ⟨z.1, hz', rfl⟩, z.2⟩

/-- The kernel of `φ` is exactly `Y⁻¹(V₂) ⊆ A`. -/
theorem ker_phiLin (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    LinearMap.ker (phiLin V₁ W₁ Y) =
      Submodule.comap (ASub V₁ Y).subtype (Submodule.comap Y.mulVecLin (V2sub V₁ W₁ Y)) := by
  rw [phiLin, LinearMap.ker_comp, Submodule.ker_mkQ]
  rfl

/-- The kernel of `φ`, in the form used below. -/
theorem ker_phiLin' {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Y : Matrix (Fin n) (Fin m) 𝔽₂} (hW : LinearMap.ker Y.mulVecLin ≤ W₁) :
    LinearMap.ker (phiLin V₁ W₁ Y) =
      Submodule.comap (ASub V₁ Y).subtype (ASub V₁ Y ⊓ W₁) := by
  rw [ker_phiLin, comap_V2sub_eq hW, inf_comm]

/-- The kernel of `φ` equals `W₁ ↾ A` (given `ker Y ⊆ W₁`). -/
theorem ker_phiLin_eq {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Y : Matrix (Fin n) (Fin m) 𝔽₂} (hW : LinearMap.ker Y.mulVecLin ≤ W₁) :
    LinearMap.ker (phiLin V₁ W₁ Y) = Submodule.comap (ASub V₁ Y).subtype W₁ := by
  rw [ker_phiLin' hW, Submodule.comap_inf, Submodule.comap_subtype_self]
  simp

/-- The second isomorphism theorem, in the direction and with the bookkeeping used below:
`W₂/W₁ ≃ A/(A ⊓ W₁)` where `W₂ = A ⊔ W₁`. -/
def eEquiv (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    (↥(W2sub V₁ W₁ Y) ⧸ Submodule.comap (W2sub V₁ W₁ Y).subtype W₁) ≃ₗ[𝔽₂]
      (↥(ASub V₁ Y) ⧸ Submodule.comap (ASub V₁ Y).subtype W₁) :=
  (LinearMap.quotientInfEquivSupQuotient (ASub V₁ Y) W₁).symm.trans
    (Submodule.quotEquivOfEq _ _ (by rw [Submodule.comap_subtype_self]; simp))

/-- The action of `eEquiv` on the class of an element of `A`. -/
theorem eEquiv_apply_inclusion (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Y : Matrix (Fin n) (Fin m) 𝔽₂)
    (z : ↥(ASub V₁ Y)) :
    eEquiv V₁ W₁ Y
        (Submodule.Quotient.mk (Submodule.inclusion (le_sup_left : ASub V₁ Y ≤ W2sub V₁ W₁ Y) z)) =
      Submodule.Quotient.mk z := by
  rw [eEquiv, LinearEquiv.trans_apply,
    LinearMap.quotientInfEquivSupQuotient_symm_apply_left (ASub V₁ Y) W₁
      (Submodule.inclusion le_sup_left z) z.2,
    Submodule.quotEquivOfEq_mk]
  rfl

/-- The map `X : W₂ → V/V₂` of arXiv:2209.04243, `lem:restrictiond of compositions of
Laplacians`.  On `A = Y⁻¹(V₁)` it is `Y`; on `W₁` it is `0`; and it descends to
`W₂/W₁ ≅ V₁/V₂` (see `ker_Xlin` and `range_Xlin`). -/
def Xlin (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    ↥(W2sub V₁ W₁ Y) →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V2sub V₁ W₁ Y) :=
  (Submodule.liftQ (Submodule.comap (ASub V₁ Y).subtype W₁) (phiLin V₁ W₁ Y)
      (inf_le_ker_phiLin V₁ W₁ Y)).comp
    ((eEquiv V₁ W₁ Y).toLinearMap.comp
      (Submodule.mkQ (Submodule.comap (W2sub V₁ W₁ Y).subtype W₁)))

/-- The defining formula for `Xlin`. -/
theorem Xlin_apply (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) (w : ↥(W2sub V₁ W₁ Y)) :
    Xlin V₁ W₁ Y w =
      (Submodule.liftQ (Submodule.comap (ASub V₁ Y).subtype W₁) (phiLin V₁ W₁ Y)
        (inf_le_ker_phiLin V₁ W₁ Y))
        (eEquiv V₁ W₁ Y (Submodule.mkQ (Submodule.comap (W2sub V₁ W₁ Y).subtype W₁) w)) := rfl

/-- **The value of `X` on `A = Y⁻¹(V₁)`**: `X z = Y z`. -/
theorem Xlin_inclusion (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) (z : ↥(ASub V₁ Y)) :
    Xlin V₁ W₁ Y (Submodule.inclusion (le_sup_left : ASub V₁ Y ≤ W2sub V₁ W₁ Y) z) =
      Submodule.mkQ (V2sub V₁ W₁ Y) (Y.mulVecLin z.1) := by
  rw [Xlin_apply, Submodule.mkQ_apply, eEquiv_apply_inclusion, Submodule.liftQ_apply,
    phiLin_apply]

/-- The kernel of `X` is `W₁` (given `ker Y ⊆ W₁`): `X` is the quotient map `W₂/W₁ → V₁/V₂`. -/
theorem ker_Xlin {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Y : Matrix (Fin n) (Fin m) 𝔽₂} (hW : LinearMap.ker Y.mulVecLin ≤ W₁) :
    LinearMap.ker (Xlin V₁ W₁ Y) = Submodule.comap (W2sub V₁ W₁ Y).subtype W₁ := by
  have hker : LinearMap.ker
      (Submodule.liftQ (Submodule.comap (ASub V₁ Y).subtype W₁) (phiLin V₁ W₁ Y)
        (inf_le_ker_phiLin V₁ W₁ Y)) = ⊥ := by
    rw [Submodule.ker_liftQ_eq_bot (Submodule.comap (ASub V₁ Y).subtype W₁) (phiLin V₁ W₁ Y)
      (inf_le_ker_phiLin V₁ W₁ Y) (by rw [ker_phiLin_eq hW])]
  rw [Xlin, LinearMap.ker_comp, hker, Submodule.comap_comp, Submodule.comap_bot,
    LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]

/-- `X` kills `W₁`. -/
theorem Xlin_eq_zero_of_mem {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)} {Y : Matrix (Fin n) (Fin m) 𝔽₂}
    (hW : LinearMap.ker Y.mulVecLin ≤ W₁) {w : ↥(W2sub V₁ W₁ Y)}
    (hw : (w : Fin m → 𝔽₂) ∈ W₁) : Xlin V₁ W₁ Y w = 0 := by
  rw [← LinearMap.mem_ker, ker_Xlin hW]
  exact hw

/-- `X` is surjective onto `V₁/V₂`: the image of `X` is `V₁/V₂`. -/
theorem range_Xlin {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Y : Matrix (Fin n) (Fin m) 𝔽₂} (hV : V₁ ≤ LinearMap.range Y.mulVecLin) :
    LinearMap.range (Xlin V₁ W₁ Y) = Submodule.map (Submodule.mkQ (V2sub V₁ W₁ Y)) V₁ := by
  have hsurj : LinearMap.range
      ((eEquiv V₁ W₁ Y).toLinearMap.comp
        (Submodule.mkQ (Submodule.comap (W2sub V₁ W₁ Y).subtype W₁))) = ⊤ := by
    rw [LinearMap.range_comp, Submodule.range_mkQ, Submodule.map_top, LinearEquiv.range]
  have hrangeφ : LinearMap.range (phiLin V₁ W₁ Y) =
      Submodule.map (Submodule.mkQ (V2sub V₁ W₁ Y)) V₁ := by
    have h1 : LinearMap.range ((Submodule.mkQ (V2sub V₁ W₁ Y)).comp
        (Y.mulVecLin.comp (ASub V₁ Y).subtype)) =
        Submodule.map (Submodule.mkQ (V2sub V₁ W₁ Y)) (Submodule.map Y.mulVecLin (ASub V₁ Y)) := by
      rw [LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
    rw [phiLin, h1, ASub, Submodule.map_comap_eq, inf_eq_right.mpr hV]
  rw [Xlin, LinearMap.range_comp, hsurj, Submodule.map_top, Submodule.range_liftQ, hrangeφ]

/-! ## The map `Y₂ = Y|_{W₂}^{V/V₂}` -/

/-- The restriction `Y₂ = Y|_{W₂}^{V/V₂}` of the character `Y`. -/
def Ylin (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    ↥(W2sub V₁ W₁ Y) →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V2sub V₁ W₁ Y) :=
  (Submodule.mkQ (V2sub V₁ W₁ Y)).comp (Y.mulVecLin.comp (W2sub V₁ W₁ Y).subtype)

lemma Ylin_apply (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) (w : ↥(W2sub V₁ W₁ Y)) :
    Ylin V₁ W₁ Y w = Submodule.mkQ (V2sub V₁ W₁ Y) (Y.mulVecLin w.1) := rfl

/-- `V₁ ⊆ Y(W₂)` rephrased. -/
theorem range_Ylin (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    LinearMap.range (Ylin V₁ W₁ Y) =
      Submodule.map (Submodule.mkQ (V2sub V₁ W₁ Y)) (Submodule.map Y.mulVecLin (W2sub V₁ W₁ Y)) := by
  rw [Ylin, LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]

/-! ## `X ≤ Y₂`: the paper's `X ≤ Y(W₂, V/V₂)` condition -/

/-- Membership in `(V₁ + V₂)/V₂` unwinds to membership in `V₁` (for `V₂ ≤ V₁`). -/
lemma mkQ_mem_map_mkQ {V₂ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)} (h : V₂ ≤ V₁)
    {x : Fin n → 𝔽₂} (hx : Submodule.mkQ V₂ x ∈ Submodule.map (Submodule.mkQ V₂) V₁) :
    x ∈ V₁ := by
  rw [Submodule.mem_map] at hx
  obtain ⟨v, hv, hvw⟩ := hx
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hvw
  have h2 : x - v ∈ V₁ := h (by simpa using V₂.neg_mem hvw)
  have := V₁.add_mem h2 hv
  simpa using this

/-- **`X ≤ Y₂`** (arXiv:2209.04243, `lem:restrictiond of compositions of Laplacians`): the
induced map `X : W₂ → V/V₂` has image `V₁/V₂ ⊆ Im Y₂` and agrees with `Y₂` on
`Y₂⁻¹(V₁/V₂)`.  By `Commons.LinearAlgebra.Matrix.rank_poset_iff` this is exactly the partial
order relation `rank Y₂ = rank X + rank (Y₂ - X)` used in the paper. -/
theorem Xlin_le_Ylin {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Y : Matrix (Fin n) (Fin m) 𝔽₂} (hV : V₁ ≤ LinearMap.range Y.mulVecLin)
    (hW : LinearMap.ker Y.mulVecLin ≤ W₁) :
    LinearMap.range (Xlin V₁ W₁ Y) ≤ LinearMap.range (Ylin V₁ W₁ Y) ∧
      ∀ w : ↥(W2sub V₁ W₁ Y), Ylin V₁ W₁ Y w ∈ LinearMap.range (Xlin V₁ W₁ Y) →
        Ylin V₁ W₁ Y w = Xlin V₁ W₁ Y w := by
  refine ⟨?_, ?_⟩
  · rw [range_Xlin hV, range_Ylin, map_W2sub_eq hV]
    exact Submodule.map_mono le_sup_right
  · intro w hw
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp w.2
    have hy2 : y ∈ W2sub V₁ W₁ Y := (le_sup_left : ASub V₁ Y ≤ W2sub V₁ W₁ Y) hy
    have hz2 : z ∈ W2sub V₁ W₁ Y := (le_sup_right : W₁ ≤ W2sub V₁ W₁ Y) hz
    -- `X w = Y y`
    have hXw : Xlin V₁ W₁ Y w = Submodule.mkQ (V2sub V₁ W₁ Y) (Y.mulVecLin y) := by
      have hsplit : (⟨y, hy2⟩ : ↥(W2sub V₁ W₁ Y)) + ⟨z, hz2⟩ = w :=
        Subtype.ext (by simpa using hyz)
      conv_lhs => rw [← hsplit]
      rw [map_add, show Xlin V₁ W₁ Y ⟨z, hz2⟩ = 0 from Xlin_eq_zero_of_mem hW hz, add_zero]
      exact Xlin_inclusion V₁ W₁ Y ⟨y, hy⟩
    -- `Y w ∈ V₁` from `Y₂ w ∈ V₁/V₂`
    have hYw : Y.mulVecLin w.1 ∈ V₁ := by
      rw [range_Xlin hV, Ylin_apply] at hw
      exact mkQ_mem_map_mkQ (V2sub_le V₁ W₁ Y) hw
    -- `Y z ∈ V₂`
    have hYz : Y.mulVecLin z ∈ V2sub V₁ W₁ Y := by
      refine ⟨Submodule.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
      have hy1 : Y.mulVecLin y ∈ V₁ := hy
      have hsum : Y.mulVecLin w.1 = Y.mulVecLin y + Y.mulVecLin z := by
        rw [← hyz, map_add]
      rw [hsum] at hYw
      simpa using V₁.sub_mem hYw hy1
    rw [Ylin_apply, hXw, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hdiff : Y.mulVecLin w.1 - Y.mulVecLin y = Y.mulVecLin z := by
      rw [← hyz, map_add, add_sub_cancel_left]
    rw [hdiff]
    exact hYz

/-! ## Uniqueness of the triple

The triple `(W₂, V₂, X)` of `lem:restrictiond of compositions of Laplacians` is *unique*: this
is what makes the sum in Proposition "taking restrictions of Laplacians" have exactly one
non-zero term for each character. -/

/-- If `map (mkQ p) A ≤ map (mkQ p) B` then `A ≤ B + p`. -/
lemma le_sup_of_map_mkQ_le {p A B : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    (h : Submodule.map (Submodule.mkQ p) A ≤ Submodule.map (Submodule.mkQ p) B) :
    A ≤ B ⊔ p := by
  intro a ha
  have ha' : Submodule.mkQ p a ∈ Submodule.map (Submodule.mkQ p) B :=
    h (Submodule.mem_map.mpr ⟨a, ha, rfl⟩)
  rw [Submodule.mem_map] at ha'
  obtain ⟨b, hb, hba⟩ := ha'
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hba
  have hab : a - b ∈ p := by simpa using p.neg_mem hba
  have : a = b + (a - b) := by abel
  rw [this]
  exact (B ⊔ p).add_mem (Submodule.mem_sup.mpr ⟨b, hb, 0, p.zero_mem, by simp⟩)
    (Submodule.mem_sup.mpr ⟨0, B.zero_mem, a - b, hab, by simp⟩)

/-- The dimension identity for an arbitrary pair `(V₂', W₂')` carrying a quotient isomorphism
`W₂'/W₁ ≅ V₁/V₂'`: `dim W₂' = dim W₁ + (dim V₁ - dim V₂')`. -/
theorem finrank_eq_of_quotient {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)} {W₂' : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {V₂' : Submodule 𝔽₂ (Fin n → 𝔽₂)} (hW'W : W₁ ≤ W₂') (hV'V : V₂' ≤ V₁)
    {X' : ↥W₂' →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂')}
    (hker : LinearMap.ker X' = Submodule.comap W₂'.subtype W₁)
    (hrange : LinearMap.range X' = Submodule.map (Submodule.mkQ V₂') V₁) :
    Module.finrank 𝔽₂ ↥W₂' =
      Module.finrank 𝔽₂ ↥W₁ + (Module.finrank 𝔽₂ ↥V₁ - Module.finrank 𝔽₂ ↥V₂') := by
  have hrn := LinearMap.finrank_range_add_finrank_ker X'
  rw [hker] at hrn
  have hk : Module.finrank 𝔽₂ ↥(Submodule.comap W₂'.subtype W₁) = Module.finrank 𝔽₂ ↥W₁ :=
    (Submodule.comapSubtypeEquivOfLe hW'W).finrank_eq
  have hr : Module.finrank 𝔽₂ ↥(LinearMap.range X') =
      Module.finrank 𝔽₂ ↥V₁ - Module.finrank 𝔽₂ ↥V₂' := by
    rw [hrange, Commons.LinearAlgebra.finrank_map_eq (Submodule.mkQ V₂') V₁,
      Submodule.ker_mkQ, inf_eq_right.mpr hV'V]
  rw [hk, hr] at hrn
  omega

/-- `Y(W₂' ⊓ Y⁻¹(V₁)) = Y(W₂') ⊓ V₁`. -/
lemma map_inf_comap_self (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂' : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    Submodule.map Y.mulVecLin (W₂' ⊓ ASub V₁ Y) = Submodule.map Y.mulVecLin W₂' ⊓ V₁ := by
  refine le_antisymm ?_ ?_
  · rintro v ⟨w, hw, rfl⟩
    exact ⟨Submodule.mem_map.mpr ⟨w, hw.1, rfl⟩, hw.2⟩
  · rintro v ⟨hv, hv1⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    exact Submodule.mem_map.mpr ⟨w, ⟨hw, hv1⟩, rfl⟩

/-- **Uniqueness of the triple** (arXiv:2209.04243, `lem:restrictiond of compositions of
Laplacians`): any pair `(V₂', W₂')` with `V₂' ≤ V₁`, `W₂' ≥ W₁`, `Y⁻¹(V₂') ≤ W₂'`, carrying a
quotient isomorphism `W₂'/W₁ ≅ V₁/V₂'` compatible with `Y`, equals `(W2sub, V2sub)`. -/
theorem W2sub_V2sub_unique {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)} {Y : Matrix (Fin n) (Fin m) 𝔽₂}
    (hV : V₁ ≤ LinearMap.range Y.mulVecLin)
    {W₂' : Submodule 𝔽₂ (Fin m → 𝔽₂)} {V₂' : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    (hW'W : W₁ ≤ W₂') (hV'V : V₂' ≤ V₁)
    (hcomap' : Submodule.comap Y.mulVecLin V₂' ≤ W₂')
    {X' : ↥W₂' →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂')}
    (hker : LinearMap.ker X' = Submodule.comap W₂'.subtype W₁)
    (hrange : LinearMap.range X' = Submodule.map (Submodule.mkQ V₂') V₁)
    (hle : LinearMap.range X' ≤
      LinearMap.range ((Submodule.mkQ V₂').comp (Y.mulVecLin.comp W₂'.subtype)))
    (hagree : ∀ w : ↥W₂', Y.mulVecLin w.1 ∈ V₁ →
      X' w = Submodule.mkQ V₂' (Y.mulVecLin w.1)) :
    W₂' = W2sub V₁ W₁ Y ∧ V₂' = V2sub V₁ W₁ Y := by
  have hrangeY : LinearMap.range ((Submodule.mkQ V₂').comp (Y.mulVecLin.comp W₂'.subtype)) =
      Submodule.map (Submodule.mkQ V₂') (Submodule.map Y.mulVecLin W₂') := by
    rw [LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
  -- (1) `V₁ ≤ Y(W₂') + V₂'`
  have hVle : V₁ ≤ Submodule.map Y.mulVecLin W₂' ⊔ V₂' := by
    refine le_sup_of_map_mkQ_le ?_
    rw [← hrangeY, ← hrange]
    exact hle
  -- (2) `Y⁻¹(V₁) ≤ W₂'`
  have hcomapV1 : Submodule.comap Y.mulVecLin V₁ ≤ W₂' := by
    intro w hw
    have hmem : Y.mulVecLin w ∈ Submodule.map Y.mulVecLin W₂' ⊔ V₂' := hVle hw
    rw [Submodule.mem_sup] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    rw [Submodule.mem_map] at ha
    obtain ⟨w', hw', hYw'⟩ := ha
    have h1 : Y.mulVecLin (w - w') ∈ V₂' := by
      have : Y.mulVecLin w - Y.mulVecLin w' = b := by
        rw [hYw', ← hab, add_sub_cancel_left]
      rw [map_sub, this]
      exact hb
    have h2 : w - w' ∈ W₂' := hcomap' h1
    have hthis : w = w' + (w - w') := by abel
    rw [hthis]
    exact W₂'.add_mem hw' h2
  -- (3) `Y⁻¹(V₂') = W₁ ⊓ Y⁻¹(V₁)`
  have hcomapV2 : Submodule.comap Y.mulVecLin V₂' ≤ W₁ := by
    intro w hw
    have hwV₁ : Y.mulVecLin w ∈ V₁ := hV'V hw
    have hX := hagree ⟨w, hcomap' hw⟩ hwV₁
    have h0 : X' ⟨w, hcomap' hw⟩ = 0 := by
      rw [hX, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hw
    rw [← LinearMap.mem_ker, hker] at h0
    exact h0
  have hcomapV2' : W₁ ⊓ ASub V₁ Y ≤ Submodule.comap Y.mulVecLin V₂' := by
    intro w hw
    rw [Submodule.mem_comap]
    have hX := hagree ⟨w, hW'W hw.1⟩ hw.2
    have h0 : X' ⟨w, hW'W hw.1⟩ = 0 := by
      rw [← LinearMap.mem_ker, hker]
      exact hw.1
    rw [hX, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  have hcomapEq : Submodule.comap Y.mulVecLin V₂' = W₁ ⊓ ASub V₁ Y :=
    le_antisymm (le_inf hcomapV2 (Submodule.comap_mono hV'V)) hcomapV2'
  -- (4) `V₂' = V2sub V₁ W₁ Y`
  have hV₂ : V₂' = V2sub V₁ W₁ Y := by
    refine le_antisymm ?_ ?_
    · intro v hv
      have hvV1 : v ∈ V₁ := hV'V hv
      have hvIm : v ∈ LinearMap.range Y.mulVecLin := hV hvV1
      obtain ⟨w, hYw⟩ := LinearMap.mem_range.mp hvIm
      have hwV2' : w ∈ Submodule.comap Y.mulVecLin V₂' :=
        Submodule.mem_comap.mpr (by rw [hYw]; exact hv)
      have hwW₁ : w ∈ W₁ := hcomapV2 hwV2'
      rw [V2sub, Submodule.mem_inf]
      exact ⟨Submodule.mem_map.mpr ⟨w, hwW₁, hYw⟩, hvV1⟩
    · rintro v ⟨hv, hvV1⟩
      obtain ⟨w₁, hw₁, hYw₁⟩ := Submodule.mem_map.mp hv
      have hw₁W₂' : w₁ ∈ W₂' := hW'W hw₁
      have hXw := hagree ⟨w₁, hw₁W₂'⟩ (by rw [hYw₁]; exact hvV1)
      have h0 : X' ⟨w₁, hw₁W₂'⟩ = 0 := by
        rw [← LinearMap.mem_ker, hker]
        exact hw₁
      rw [hXw, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
      rwa [← hYw₁]
  refine ⟨?_, hV₂⟩
  -- (5) `W₂' = W2sub V₁ W₁ Y`, where `W2sub V₁ W₁ Y = W₁ ⊔ Y⁻¹(V₁)`
  have hkerfin : Module.finrank 𝔽₂
      ↥(Submodule.comap (W₂' ⊓ ASub V₁ Y).subtype (Submodule.comap Y.mulVecLin V₂'))
      = Module.finrank 𝔽₂ ↥(Submodule.comap Y.mulVecLin V₂') :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe
      (le_inf hcomap' (Submodule.comap_mono hV'V)))
  have hrangeφ : LinearMap.range
      ((((Submodule.mkQ V₂').comp Y.mulVecLin)).comp (W₂' ⊓ ASub V₁ Y).subtype) =
      Submodule.map (Submodule.mkQ V₂') V₁ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    refine le_antisymm ?_ ?_
    · rintro v ⟨w, hw, rfl⟩
      exact Submodule.mem_map.mpr ⟨Y.mulVecLin w, hw.2, rfl⟩
    · rintro v hv
      obtain ⟨v', hv', rfl⟩ := Submodule.mem_map.mp hv
      have hmem : v' ∈ Submodule.map Y.mulVecLin W₂' ⊔ V₂' := hVle hv'
      rw [Submodule.mem_sup] at hmem
      obtain ⟨y, hy, z, hz, hyz⟩ := hmem
      obtain ⟨w, hw, hYw⟩ := Submodule.mem_map.mp hy
      refine Submodule.mem_map.mpr ⟨w, ⟨hw, ?_⟩, ?_⟩
      · refine Submodule.mem_comap.mpr ?_
        have hyvz : y = v' - z := by rw [← hyz, add_sub_cancel_right]
        rw [hYw, hyvz]
        exact V₁.sub_mem hv' (hV'V hz)
      · show Submodule.mkQ V₂' (Y.mulVecLin w) = Submodule.mkQ V₂' v'
        have hthis : Submodule.mkQ V₂' v' = Submodule.mkQ V₂' y := by
          rw [← hyz, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
            add_sub_cancel_left]
          exact hz
        rw [hYw, hthis]
  have hrn := LinearMap.finrank_range_add_finrank_ker
    ((((Submodule.mkQ V₂').comp Y.mulVecLin)).comp (W₂' ⊓ ASub V₁ Y).subtype)
  rw [LinearMap.ker_comp, LinearMap.ker_comp, Submodule.ker_mkQ] at hrn
  rw [hkerfin, hrangeφ, Commons.LinearAlgebra.finrank_map_eq (Submodule.mkQ V₂') V₁,
    Submodule.ker_mkQ, inf_eq_right.mpr hV'V] at hrn
  -- `hrn : (finrank V₁ - finrank V₂') + finrank (W₂' ⊓ Y⁻¹(V₁)) = finrank (W₂' ⊓ Y⁻¹(V₁))`
  have hdimM : Module.finrank 𝔽₂ ↥(W₂' ⊓ ASub V₁ Y) =
      (Module.finrank 𝔽₂ ↥V₁ - Module.finrank 𝔽₂ ↥V₂') +
        Module.finrank 𝔽₂ ↥(Submodule.comap Y.mulVecLin V₂') := hrn.symm
  have hdimW₂' := finrank_eq_of_quotient hW'W hV'V hker hrange
  rw [hV₂] at hdimW₂'
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq W₁ (W₂' ⊓ ASub V₁ Y)
  have hinfMW : W₁ ⊓ (W₂' ⊓ ASub V₁ Y) = W₁ ⊓ ASub V₁ Y := by
    rw [← inf_assoc, inf_eq_left.mpr hW'W]
  have hkerfin2 : Module.finrank 𝔽₂ ↥(Submodule.comap Y.mulVecLin V₂')
      = Module.finrank 𝔽₂ ↥(W₁ ⊓ ASub V₁ Y) := by rw [hcomapEq]
  have hgoal : Module.finrank 𝔽₂ ↥(W₁ ⊔ (W₂' ⊓ ASub V₁ Y)) = Module.finrank 𝔽₂ ↥W₂' := by
    rw [hinfMW] at hmod
    rw [hkerfin2] at hdimM
    rw [← hV₂] at hdimW₂'
    have h1 : Module.finrank 𝔽₂ ↥(W₁ ⊓ ASub V₁ Y) ≤
        Module.finrank 𝔽₂ ↥(W₂' ⊓ ASub V₁ Y) :=
      Submodule.finrank_mono (le_inf (le_trans inf_le_left hW'W) inf_le_right)
    have h2 : Module.finrank 𝔽₂ ↥V₂' ≤ Module.finrank 𝔽₂ ↥V₁ := Submodule.finrank_mono hV'V
    omega
  have heq : W₁ ⊔ (W₂' ⊓ ASub V₁ Y) = W₂' :=
    Submodule.eq_of_le_of_finrank_eq (sup_le hW'W inf_le_left) hgoal
  have hfinal : W₂' = W2sub V₁ W₁ Y := by
    rw [W2sub, ← heq, inf_eq_right.mpr hcomapV1, sup_comm]
  exact hfinal

end

end Submission.Grassmann