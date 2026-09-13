import Submission.Grassmann.CountingIdentity
import Submission.Grassmann.SpectralSSE

/-!
# Proposition "taking restrictions of Laplacians" (arXiv:2209.04243 §8)

The proposition states that for `V₁ ≤ V` and `W₁ ≤ W`

  `(L_{V₁} ∘ L_{W₁}[f])_{(V₁,W₁)→T}
      = Σ_{V₂ ⊆ V₁} Σ_{W₂ ⊇ W₁} Σ_{X̃ : W₂/W₁ ≅ V₁/V₂} D_X ∘ D_{V₂,W₂,T}`.

Both sides are functions on the quotient space `L(V/V₁, W₁)`, presented here in the canonical
coordinates `Matrix (Fin (dim W₁)) (Fin (n - dim V₁))` of `Coords.lean`.  The second restriction
(of a function on `L(V/V₂,W₂)` down to `L(V/V₁,W₁)`) needs the canonical maps `Qsup` and
`Isub`, defined and characterised in the first section below.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## The canonical maps for the second restriction -/

/-- The canonical map of coordinate spaces induced by an inclusion `V₂ ≤ V₁` of quotients:
`Qsup V₁ V₂ h : 𝔽₂^{n - dim V₁} → 𝔽₂^{n - dim V₂}`, characterised by
`Qsup * Qp V₂ = Qp V₁`. -/
noncomputable def Qsup (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (h : V₂ ≤ V₁) :
    Matrix (Fin (n - Module.finrank 𝔽₂ V₁)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ :=
  LinearMap.toMatrix' (((Qe V₁).toLinearMap).comp
    ((Submodule.liftQ V₂ (Submodule.mkQ V₁) (by rw [Submodule.ker_mkQ]; exact h)).comp
      ((Qe V₂).symm.toLinearMap)))

/-- **The defining equation of `Qsup`**: `Qsup * Qp V₂ = Qp V₁`. -/
theorem Qsup_mul_Qp (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (h : V₂ ≤ V₁) :
    Qsup V₁ V₂ h * Qp V₂ = Qp V₁ := by
  have hQ : Qp V₁ = LinearMap.toMatrix' (((Qe V₁).toLinearMap).comp (Submodule.mkQ V₁)) :=
    rfl
  have hQ' : Qp V₂ = LinearMap.toMatrix' (((Qe V₂).toLinearMap).comp (Submodule.mkQ V₂)) :=
    rfl
  have hQs : Qsup V₁ V₂ h = LinearMap.toMatrix' (((Qe V₁).toLinearMap).comp
    ((Submodule.liftQ V₂ (Submodule.mkQ V₁) (by rw [Submodule.ker_mkQ]; exact h)).comp
      ((Qe V₂).symm.toLinearMap))) := rfl
  rw [hQ, hQ', hQs, ← LinearMap.toMatrix'_comp]
  congr 1
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [LinearEquiv.symm_apply_apply]
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- The canonical map of coordinate spaces induced by an inclusion `W₁ ≤ W₂` of subspaces:
`Isub W₁ W₂ h : 𝔽₂^{dim W₁} → 𝔽₂^{dim W₂}`, characterised by `Ip W₂ * Isub = Ip W₁`. -/
noncomputable def Isub (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (h : W₁ ≤ W₂) :
    Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (Module.finrank 𝔽₂ W₁)) 𝔽₂ :=
  LinearMap.toMatrix' (((Module.finBasis 𝔽₂ ↥W₂).equivFun.toLinearMap).comp
    ((Submodule.inclusion h).comp ((Module.finBasis 𝔽₂ ↥W₁).equivFun.symm.toLinearMap)))

/-- **The defining equation of `Isub`**: `Ip W₂ * Isub W₁ W₂ h = Ip W₁`. -/
theorem Ip_mul_Isub (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (h : W₁ ≤ W₂) :
    Ip W₂ * Isub W₁ W₂ h = Ip W₁ := by
  have hI : Ip W₁ = LinearMap.toMatrix'
      (W₁.subtype.comp ((Module.finBasis 𝔽₂ ↥W₁).equivFun.symm.toLinearMap)) := rfl
  have hI' : Ip W₂ = LinearMap.toMatrix'
      (W₂.subtype.comp ((Module.finBasis 𝔽₂ ↥W₂).equivFun.symm.toLinearMap)) := rfl
  have hIs : Isub W₁ W₂ h = LinearMap.toMatrix'
      (((Module.finBasis 𝔽₂ ↥W₂).equivFun.toLinearMap).comp
        ((Submodule.inclusion h).comp
          ((Module.finBasis 𝔽₂ ↥W₁).equivFun.symm.toLinearMap))) := rfl
  rw [hI, hI', hIs, ← LinearMap.toMatrix'_comp]
  congr 1
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-! ## Characters and multipliers -/

/-- The hybrid Laplacian on a character. -/
theorem Lsub_mchar {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    Lsub V₁ W₁ (mchar Y) =
      (if hybridPredSub V₁ W₁ Y then (1 : ℂ) else 0) • (mchar Y : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) := by
  rw [Lsub, lapMulN_mchar]

/-- The basic `V`-Laplacian on a character. -/
theorem Lup_mchar {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    Lup V₁ (mchar Y) =
      (if V₁ ≤ LinearMap.range Y.mulVecLin then (1 : ℂ) else 0) •
        (mchar Y : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) := by
  rw [Lup, lapMulN_mchar]

/-- The basic `W`-Laplacian on a character. -/
theorem Ldown_mchar {m n : ℕ} (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    Ldown W₁ (mchar Y) =
      (if LinearMap.ker Y.mulVecLin ≤ W₁ then (1 : ℂ) else 0) •
        (mchar Y : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) := by
  rw [Ldown, lapMulN_mchar]

/-- **The restriction of the shifted hybrid Laplacian of a character**: it is the product of the
scalar `mchar Y T` and the restriction `mchar (Q * Y * ι)`, cut off by the hybrid predicate. -/
theorem restr_shift_Lsub_mchar {m n m' n' : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    restr Q ι (shift T (Lsub V₁ W₁ (mchar Y))) =
      (if hybridPredSub V₁ W₁ Y then (1 : ℂ) else 0) •
        ((mchar Y T) • (mchar (Q * Y * ι) : Matrix (Fin m') (Fin n') 𝔽₂ → ℂ)) := by
  rw [Lsub_mchar, shift_smul, restr_smul, restr_shift_mchar]

/-- **The restriction of the shifted basic Laplacians of a character.** -/
theorem restr_shift_Lup_Ldown_mchar {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    restr (Qp V₁) (Ip W₁) (shift T (Lup V₁ (Ldown W₁ (mchar Y)))) =
      (if LinearMap.ker Y.mulVecLin ≤ W₁ then (1 : ℂ) else 0) •
        ((if V₁ ≤ LinearMap.range Y.mulVecLin then (1 : ℂ) else 0) •
          ((mchar Y T) • (mchar (charMat V₁ W₁ Y) :
            Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ))) := by
  rw [Ldown_mchar, Lup, lapMulN_smul, lapMulN_mchar]
  simp only [shift_smul, restr_smul]
  rw [restr_shift_mchar, charMat]

/-! ## Total versions of the canonical maps -/

/-- The total version of `Qsup` (junk value when `V₂ ⊄ V₁`). -/
noncomputable def QsupT (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    Matrix (Fin (n - Module.finrank 𝔽₂ V₁)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ :=
  if h : V₂ ≤ V₁ then Qsup V₁ V₂ h else 0

theorem QsupT_eq (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (h : V₂ ≤ V₁) :
    QsupT V₁ V₂ = Qsup V₁ V₂ h := by
  rw [QsupT, dif_pos h]

/-- The total version of `Isub` (junk value when `W₁ ⊄ W₂`). -/
noncomputable def IsubT (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) :
    Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (Module.finrank 𝔽₂ W₁)) 𝔽₂ :=
  if h : W₁ ≤ W₂ then Isub W₁ W₂ h else 0

theorem IsubT_eq (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (h : W₁ ≤ W₂) :
    IsubT W₁ W₂ = Isub W₁ W₂ h := by
  rw [IsubT, dif_pos h]

/-! ## The summand `D_X ∘ D_{V₂,W₂,T}` -/

/-- The index set of the sum in Prop "taking restrictions of Laplacians": triples
`(V₂, W₂, X)` with `X : ↥W₂ → V/V₂`. -/
abbrev Triple (m n : ℕ) : Type :=
  Sigma (fun V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂) =>
    Sigma (fun W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂) =>
      ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)))

/-- The condition for a triple `(V₂,W₂,X)` to appear in Prop "taking restrictions of
Laplacians": `V₂ ≤ V₁`, `W₁ ≤ W₂`, `ker X = W₁` and `Im X = V₁/V₂`. -/
def TripleOK (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (t : Triple m n) : Prop :=
  t.1 ≤ V₁ ∧ W₁ ≤ t.2.1 ∧
    LinearMap.ker t.2.2 = Submodule.comap t.2.1.subtype W₁ ∧
    LinearMap.range t.2.2 = Submodule.map (Submodule.mkQ t.1) V₁

/-- The summand `D_X ∘ D_{V₂,W₂,T}` of Prop "taking restrictions of Laplacians", as a function
on `L(V/V₁,W₁)` in the coordinates of `Coords.lean`. -/
noncomputable def DopX (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ :=
  restr (QsupT V₁ V₂) (IsubT W₁ W₂)
    (lapMulN (plLE (XtOf V₂ W₂ X))
      (restr (Qp V₂) (Ip W₂) (shift T (Lsub V₂ W₂ f))))

/-- The right-hand side of Prop "taking restrictions of Laplacians". -/
noncomputable def DopSum (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ :=
  ∑ t : Triple m n, if TripleOK V₁ W₁ t then DopX V₁ W₁ t.1 t.2.1 t.2.2 T f else 0

/-- The left-hand side of Prop "taking restrictions of Laplacians". -/
noncomputable def DopLHS (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ :=
  restr (Qp V₁) (Ip W₁) (shift T (Lup V₁ (Ldown W₁ f)))

/-- **The value of the summand on a character.** -/
theorem DopX_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    {V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂)
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    DopX V₁ W₁ V₂ W₂ X T (mchar Y) =
      (if hybridPredSub V₂ W₂ Y then (1 : ℂ) else 0) •
        ((if plLE (XtOf V₂ W₂ X) (charMat V₂ W₂ Y) then (1 : ℂ) else 0) •
          ((mchar Y T) • (mchar (charMat V₁ W₁ Y) :
            Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ))) := by
  have hkey : Qsup V₁ V₂ hV * (Qp V₂ * Y * Ip W₂) * Isub W₁ W₂ hW
      = Qp V₁ * Y * Ip W₁ := by
    rw [show Qsup V₁ V₂ hV * (Qp V₂ * Y * Ip W₂) * Isub W₁ W₂ hW =
        (Qsup V₁ V₂ hV * Qp V₂) * Y * (Ip W₂ * Isub W₁ W₂ hW) from by
          simp only [Matrix.mul_assoc],
      Qsup_mul_Qp, Ip_mul_Isub]
  rw [DopX, QsupT_eq V₁ V₂ hV, IsubT_eq W₁ W₂ hW, restr_shift_Lsub_mchar]
  rw [lapMulN_smul, lapMulN_smul, lapMulN_mchar]
  simp only [restr_smul]
  rw [restr_mchar, hkey]
  simp only [smul_smul, mul_comm, charMat]
  rfl

/-! ## Linearity in `f` -/

/-- A `Fintype` sum of an `if`-weighted sum of scalar multiples can be swapped. -/
theorem sum_ite_sum_smul {ι κ M : Type*} [Fintype κ] [AddCommMonoid M] [Module ℂ M]
    (p : κ → Prop) [DecidablePred p] (s : Finset ι) (c : ι → ℂ) (h : κ → ι → M) :
    (∑ k : κ, (if p k then ∑ i ∈ s, c i • h k i else 0)) =
      ∑ i ∈ s, c i • ∑ k : κ, (if p k then h k i else 0) := by
  have h1 : (∑ k : κ, (if p k then ∑ i ∈ s, c i • h k i else 0)) =
      ∑ k : κ, ∑ i ∈ s, (if p k then c i • h k i else 0) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hp : p k
    · rw [if_pos hp]
      exact (Finset.sum_congr rfl (fun i _ => by rw [if_pos hp])).symm
    · rw [if_neg hp]
      exact (Finset.sum_eq_zero (fun i _ => by rw [if_neg hp])).symm
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hp : p k
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp, smul_zero]

/-- **Linearity of the left-hand side.** -/
theorem DopLHS_sum_smul {m n : ℕ} {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (s : Finset ι) (c : ι → ℂ) (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DopLHS V₁ W₁ T (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • DopLHS V₁ W₁ T (g i) := by
  simp only [DopLHS, Ldown, Lup, lapMulN_sum, lapMulN_smul, shift_sum, shift_smul, restr_sum,
    restr_smul]

/-- **Linearity of the right-hand side.** -/
theorem DopSum_sum_smul {m n : ℕ} {ι : Type*} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (s : Finset ι) (c : ι → ℂ) (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DopSum V₁ W₁ T (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • DopSum V₁ W₁ T (g i) := by
  simp only [DopSum, DopX, Lsub, lapMulN_sum, lapMulN_smul, shift_sum, shift_smul, restr_sum,
    restr_smul]
  exact sum_ite_sum_smul _ s c _

/-! ## The character case -/

/-- **The scalar counting identity in the index set of Prop "taking restrictions of
Laplacians"**: summing the indicators `[Y⁻¹(V₂) ⊆ W₂]·[X ≤ Y₂]` over all admissible triples
gives `[V₁ ⊆ Im Y]·[ker Y ⊆ W₁]`. -/
theorem sum_tripleOK (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    (∑ t : Triple m n, (if TripleOK V₁ W₁ t then
        ((if hybridPredSub t.1 t.2.1 Y then (1 : ℂ) else 0) *
         (if lmLE t.2.2 (YlinOf t.1 t.2.1 Y) then (1 : ℂ) else 0)) else 0)) =
      (if V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ then
        (1 : ℂ) else 0) := by
  have hinner : ∀ (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)),
      (∑ X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂),
          (if TripleOK V₁ W₁ (⟨V₂, ⟨W₂, X⟩⟩ : Triple m n) then
            ((if hybridPredSub V₂ W₂ Y then (1 : ℂ) else 0) *
             (if lmLE X (YlinOf V₂ W₂ Y) then (1 : ℂ) else 0)) else 0)) =
        (if V₂ ≤ V₁ ∧ W₁ ≤ W₂ ∧ hybridPredSub V₂ W₂ Y then
          (admCount V₁ V₂ W₁ W₂ Y : ℂ) else 0) := by
    intro V₂ W₂
    by_cases h : V₂ ≤ V₁ ∧ W₁ ≤ W₂ ∧ hybridPredSub V₂ W₂ Y
    · rw [if_pos h]
      have hstep : ∀ X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂),
          (if TripleOK V₁ W₁ (⟨V₂, ⟨W₂, X⟩⟩ : Triple m n) then
              ((if hybridPredSub V₂ W₂ Y then (1 : ℂ) else 0) *
               (if lmLE X (YlinOf V₂ W₂ Y) then (1 : ℂ) else 0)) else 0) =
            (if CondX V₁ V₂ W₁ W₂ Y X then (1 : ℂ) else 0) := by
        intro X
        by_cases hX : LinearMap.ker X = Submodule.comap W₂.subtype W₁ ∧
            LinearMap.range X = Submodule.map (Submodule.mkQ V₂) V₁
        · have hOK : TripleOK V₁ W₁ (⟨V₂, ⟨W₂, X⟩⟩ : Triple m n) := ⟨h.1, h.2.1, hX.1, hX.2⟩
          by_cases hm : lmLE X (YlinOf V₂ W₂ Y)
          · have hC : CondX V₁ V₂ W₁ W₂ Y X := ⟨hX.1, hX.2, hm⟩
            simp only [if_pos hOK, if_pos h.2.2, if_pos hm, if_pos hC, one_mul]
          · have hC : ¬ CondX V₁ V₂ W₁ W₂ Y X := fun hc => hm hc.2.2
            simp only [if_pos hOK, if_pos h.2.2, if_neg hm, if_neg hC, mul_zero]
        · have hOK : ¬ TripleOK V₁ W₁ (⟨V₂, ⟨W₂, X⟩⟩ : Triple m n) :=
            fun hc => hX ⟨hc.2.2.1, hc.2.2.2⟩
          have hC : ¬ CondX V₁ V₂ W₁ W₂ Y X := fun hc => hX ⟨hc.1, hc.2.1⟩
          simp only [if_neg hOK, if_neg hC]
      rw [Finset.sum_congr rfl (fun X _ => hstep X), ← admCount_eq_sum V₁ V₂ W₁ W₂ Y]
    · rw [if_neg h]
      refine Finset.sum_eq_zero (fun X _ => ?_)
      by_cases hhyb : hybridPredSub V₂ W₂ Y
      · have hOK : ¬ TripleOK V₁ W₁ (⟨V₂, ⟨W₂, X⟩⟩ : Triple m n) :=
          fun hc => h ⟨hc.1, hc.2.1, hhyb⟩
        simp only [if_neg hOK]
      · rw [if_neg hhyb]
        by_cases hOK : TripleOK V₁ W₁ (⟨V₂, ⟨W₂, X⟩⟩ : Triple m n)
        · rw [if_pos hOK, zero_mul]
        · rw [if_neg hOK]
  simp only [Fintype.sum_sigma]
  rw [← sum_admCount_nested V₁ W₁ Y]
  refine Finset.sum_congr rfl (fun V₂ _ => Finset.sum_congr rfl (fun W₂ _ => ?_))
  exact hinner V₂ W₂

/-- **The value of the right-hand side on a character.** -/
theorem DopSum_mchar (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    DopSum V₁ W₁ T (mchar Y) = DopLHS V₁ W₁ T (mchar Y) := by
  have hiff : ∀ t : Triple m n,
      (plLE (XtOf t.1 t.2.1 t.2.2) (charMat t.1 t.2.1 Y) ↔
        lmLE t.2.2 (YlinOf t.1 t.2.1 Y)) := by
    intro t
    rw [charMat_eq_XtOf]
    exact plLE_XtOf_iff t.1 t.2.1 t.2.2 (YlinOf t.1 t.2.1 Y)
  have hstep : (∑ t : Triple m n,
        if TripleOK V₁ W₁ t then DopX V₁ W₁ t.1 t.2.1 t.2.2 T (mchar Y) else 0) =
      (∑ t : Triple m n, (if TripleOK V₁ W₁ t then
          ((if hybridPredSub t.1 t.2.1 Y then (1 : ℂ) else 0) *
           (if lmLE t.2.2 (YlinOf t.1 t.2.1 Y) then (1 : ℂ) else 0)) else 0)) •
        ((mchar Y T) • (mchar (charMat V₁ W₁ Y) :
          Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ)) := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases hOK : TripleOK V₁ W₁ t
    · rw [if_pos hOK, if_pos hOK, DopX_mchar V₁ W₁ hOK.1 hOK.2.1 t.2.2 T Y]
      by_cases hc : plLE (XtOf t.1 t.2.1 t.2.2) (charMat t.1 t.2.1 Y)
      · rw [if_pos hc, if_pos ((hiff t).mp hc), smul_smul]
      · rw [if_neg hc, if_neg (fun h => hc ((hiff t).mpr h)), smul_smul]
    · rw [if_neg hOK, if_neg hOK, zero_smul]
  have hsc : (if V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ then
        (1 : ℂ) else 0) =
      (if LinearMap.ker Y.mulVecLin ≤ W₁ then (1 : ℂ) else 0) *
        (if V₁ ≤ LinearMap.range Y.mulVecLin then (1 : ℂ) else 0) := by
    by_cases hV : V₁ ≤ LinearMap.range Y.mulVecLin <;>
      by_cases hW : LinearMap.ker Y.mulVecLin ≤ W₁ <;> simp [hV, hW]
  rw [DopSum, hstep, sum_tripleOK, hsc, DopLHS, restr_shift_Lup_Ldown_mchar]
  simp only [smul_smul, mul_assoc]

/-! ## The proposition -/

/-- **Prop "taking restrictions of Laplacians"** (arXiv:2209.04243 §8). -/
theorem taking_restrictions (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DopLHS V₁ W₁ T f = DopSum V₁ W₁ T f := by
  conv_lhs => rw [eq_sum_fcoeff_mchar f]
  rw [DopLHS_sum_smul]
  conv_rhs => rw [eq_sum_fcoeff_mchar f]
  rw [DopSum_sum_smul]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  rw [DopSum_mchar]

end

end Submission.Grassmann
