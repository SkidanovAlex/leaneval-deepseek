import Submission.Grassmann.AfterRestricting
import Submission.Grassmann.SwitchingRoles
import Submission.Grassmann.Prop56

/-!
# The degree of the derivatives `D_X ∘ D_{V₂,W₂,T}`

`lem:derivatives`, `lem:derivatives-2` of arXiv:2209.04243: a derivative of order `i` lowers the
degree by (at least) `i`.  Concretely, for `f` of degree `≤ d` and a triple
`t = (V₂,W₂,X)` of total order `|t| = dim V₂ + codim W₂ + rank X`, the function
`D_X ∘ D_{V₂,W₂,T}[f]` has degree `≤ d - |t|`.

This is the hypothesis needed to apply the induction hypothesis to `D_X ∘ D_{V₂,W₂,T}[f]`
(`lem:upper bound on 4-norms of the derivatives given induction hypothesis`).
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## Kernel and range of the canonical maps `Qsup` and `Isub` -/

/-- The kernel of `Qsup V₁ V₂ h` is the coordinates of `V₁/V₂`. -/
theorem ker_Qsup (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (h : V₂ ≤ V₁) :
    LinearMap.ker (Qsup V₁ V₂ h).mulVecLin = Vco V₂ V₁ := by
  have hQ : (Qsup V₁ V₂ h).mulVecLin = ((Qe V₁).toLinearMap).comp
      (((Submodule.liftQ V₂ (Submodule.mkQ V₁) (by rw [Submodule.ker_mkQ]; exact h)).comp
        ((Qe V₂).symm.toLinearMap))) := by
    rw [Qsup, Commons.LinearAlgebra.Submodule.mulVecLin_toMatrix']
  rw [hQ, LinearMap.ker_comp_of_ker_eq_bot _ (LinearEquiv.ker (Qe V₁)), LinearMap.ker_comp,
    Submodule.ker_liftQ, Submodule.ker_mkQ, Vco, Submodule.comap_equiv_eq_map_symm]
  rfl

/-- The range of `Isub W₁ W₂ h` is the coordinates of `W₁` inside `W₂`. -/
theorem range_Isub (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (h : W₁ ≤ W₂) :
    LinearMap.range (Isub W₁ W₂ h).mulVecLin = Wco W₂ W₁ := by
  have hI : (Isub W₁ W₂ h).mulVecLin =
      ((Module.finBasis 𝔽₂ ↥W₂).equivFun.toLinearMap).comp
        ((Submodule.inclusion h).comp
          ((Module.finBasis 𝔽₂ ↥W₁).equivFun.symm.toLinearMap)) := by
    rw [Isub, Commons.LinearAlgebra.Submodule.mulVecLin_toMatrix']
  rw [hI, LinearMap.range_comp, LinearMap.range_comp, Wco, ecW]
  congr 1
  have h1 : ((Module.finBasis 𝔽₂ ↥W₁).equivFun.symm.toLinearMap).range = ⊤ :=
    LinearEquiv.range _
  rw [h1, Submodule.map_top, Submodule.range_inclusion]

/-- The kernel of `Isub W₁ W₂ h` is trivial. -/
theorem ker_Isub (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (h : W₁ ≤ W₂) :
    LinearMap.ker (Isub W₁ W₂ h).mulVecLin = ⊥ := by
  have hI : (Isub W₁ W₂ h).mulVecLin =
      ((Module.finBasis 𝔽₂ ↥W₂).equivFun.toLinearMap).comp
        ((Submodule.inclusion h).comp
          ((Module.finBasis 𝔽₂ ↥W₁).equivFun.symm.toLinearMap)) := by
    rw [Isub, Commons.LinearAlgebra.Submodule.mulVecLin_toMatrix']
  rw [hI, LinearMap.ker_comp_of_ker_eq_bot _ (LinearEquiv.ker _), LinearMap.ker_comp,
    Submodule.ker_inclusion, Submodule.comap_bot, LinearEquiv.ker]

/-! ## The degree reduction of `D_X ∘ D_{V₂,W₂,T}` -/

/-- `DegLe` in terms of the normalised Fourier coefficients. -/
theorem degLe_iff_fcoeff {m n d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} :
    DegLe d f ↔ ∀ X : Matrix (Fin n) (Fin m) 𝔽₂, d < X.rank → fcoeff f X = 0 := by
  constructor
  · intro h X hX
    rw [fcoeff_eq, h X hX, mul_zero]
  · intro h X hX
    have hh := h X hX
    rw [fcoeff_eq] at hh
    exact (mul_eq_zero.mp hh).resolve_left
      (inv_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)))

/-- **A `plLE`-multiplier followed by a restriction drops the degree by `rank Xt`.** -/
theorem degLe_restr_lapMulN_plLE {m n m' n' D : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (Xt : Matrix (Fin n) (Fin m) 𝔽₂)
    (hQ : LinearMap.ker Q.mulVecLin = LinearMap.range Xt.mulVecLin)
    (hιk : LinearMap.ker ι.mulVecLin = ⊥)
    (hι : LinearMap.range ι.mulVecLin = LinearMap.ker Xt.mulVecLin)
    {g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hg : DegLe D g) :
    DegLe (D - Xt.rank) (restr Q ι (lapMulN (plLE Xt) g)) := by
  rw [degLe_iff_fcoeff]
  intro Z' hZ'
  have hzero : fcoeff (restr Q ι (lapMulN (plLE Xt) g)) Z' = 0 := by
    rw [fcoeff_restr]
    refine Finset.sum_eq_zero fun Z hZ => ?_
    rw [Finset.mem_filter] at hZ
    obtain ⟨-, hZeq⟩ := hZ
    rw [fcoeff_lapMulN]
    by_cases hle : plLE Xt Z
    · rw [if_pos hle]
      have hpos := (Commons.LinearAlgebra.Matrix.rank_poset_iff Xt Z).mp hle
      have hZrank : (Q * Z * ι).rank = Z.rank - Xt.rank :=
        rank_mul_mul_eq_of_rank_le Q ι Xt Z hQ hιk hι hpos.1
          (fun w hw => (hpos.2 w hw).symm)
      rw [hZeq] at hZrank
      have hxle : Xt.rank ≤ Z.rank := plLE_rank_le hle
      rw [(degLe_iff_fcoeff (d := D) (f := g)).mp hg Z (by omega), mul_zero]
    · rw [if_neg hle, zero_mul]
  exact hzero

/-- The kernel of `XtOf V₂ W₂ X` is the coordinate image of `ker X`. -/
theorem ker_XtOf (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) :
    LinearMap.ker (XtOf V₂ W₂ X).mulVecLin =
      Submodule.map (ecW W₂).symm.toLinearMap (LinearMap.ker X) := by
  have hC : LinearMap.codRestrict W₂ (Ip W₂).mulVecLin (fun x => Ip_mem W₂ x) =
      (ecW W₂).toLinearMap := codRestrict_Ip_eq_ecW W₂
  rw [XtOf, Commons.LinearAlgebra.Submodule.mulVecLin_toMatrix', hC]
  rw [show ((Qe V₂).toLinearMap.comp (X.comp ((ecW W₂).toLinearMap))) =
      ((Qe V₂).toLinearMap.comp X).comp ((ecW W₂).toLinearMap) from by
        rw [LinearMap.comp_assoc]]
  rw [LinearMap.ker_comp, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot,
    Submodule.comap_equiv_eq_map_symm]

/-- The degree of `D_{V₂,W₂,T}[f]` is at most `d - |(V₂,W₂)|`. -/
theorem degLe_Dop0S {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f)
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) :
    DegLe (d - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂)))
      (Dop0S V₂ W₂ T f) := by
  have hP : ∀ Z : Matrix (Fin n) (Fin m) 𝔽₂, hybridPredSub V₂ W₂ Z →
      (Qp V₂ * Z * Ip W₂).rank ≤
        Z.rank - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂)) := by
    intro Z hZ
    have h1 : (charMat V₂ W₂ Z).rank =
        Module.finrank 𝔽₂ (LinearMap.range (YlinOf V₂ W₂ Z)) := by
      rw [charMat_eq_XtOf, rank_XtOf]
    change (charMat V₂ W₂ Z).rank ≤
      Z.rank - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂))
    rw [h1, finrank_range_YlinOf hZ]
  have hres : DegLe (d - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂)))
      (restr (Qp V₂) (Ip W₂) (shift T (lapMulN (hybridPredSub V₂ W₂) f))) :=
    degLe_restr_shift_lapMulN (Q := Qp V₂) (inj := Ip W₂) (T := T)
      (P := hybridPredSub V₂ W₂) (k := Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂)) hf hP
  rw [Dop0S, Lsub]
  exact hres

/-- **`lem:derivatives` for the composite `D_X ∘ D_{V₂,W₂,T}`**: the degree drops by the total
order `|(V₂,W₂,X)| = dim V₂ + codim W₂ + rank X`. -/
theorem degLe_DopX {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f)
    (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂)
    (hker : LinearMap.ker X = Submodule.comap W₂.subtype W₁)
    (hrange : LinearMap.range X = Submodule.map (Submodule.mkQ V₂) V₁) :
    DegLe (d - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂) +
      Module.finrank 𝔽₂ (LinearMap.range X))) (DopX V₁ W₁ V₂ W₂ X T f) := by
  have h1 := degLe_Dop0S (V₂ := V₂) (W₂ := W₂) (T := T) hf
  have h2 : DegLe ((d - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂))) -
      (XtOf V₂ W₂ X).rank)
      (restr (QsupT V₁ V₂) (IsubT W₁ W₂)
        (lapMulN (plLE (XtOf V₂ W₂ X))
          (restr (Qp V₂) (Ip W₂) (shift T (Lsub V₂ W₂ f))))) := by
    refine degLe_restr_lapMulN_plLE (QsupT V₁ V₂) (IsubT W₁ W₂) (XtOf V₂ W₂ X) ?_ ?_ ?_ h1
    · rw [QsupT_eq V₁ V₂ hV, ker_Qsup, Vco, ← hrange, ← range_XtOf]
    · rw [IsubT_eq W₁ W₂ hW, ker_Isub]
    · rw [IsubT_eq W₁ W₂ hW, range_Isub, ker_XtOf, hker, Wco]
  have harith : (d - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂))) -
      (XtOf V₂ W₂ X).rank =
      d - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂) +
        Module.finrank 𝔽₂ (LinearMap.range X)) := by
    rw [rank_XtOf]; omega
  rw [DopX, ← harith]
  exact h2

/-! ## Lifting coordinate subspaces -/

/-- **The lift of a coordinate subspace of `V/V₁`**: the coordinate image of the preimage of `U`
under `Qp V₁` is `U` again.  This is the translation needed to apply
`switching_roles`/`composition_of_derivatives` (which live on `L(V,W)`) to a subspace of the
quotient coordinates. -/
theorem Vco_comap_Qp (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (U : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ V₁) → 𝔽₂)) :
    Vco V₁ (Submodule.comap (Qp V₁).mulVecLin U) = U := by
  unfold Vco
  rw [Qp_mulVecLin, Submodule.comap_comp, Submodule.map_comap_eq, Submodule.range_mkQ,
    top_inf_eq, Submodule.map_comap_eq, LinearEquiv.range, top_inf_eq]

/-- **The lift of a coordinate subspace of `W₁`**: the coordinates of the image of `U` under
`Ip W₁` are `U` again. -/
theorem Wco_map_Ip (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (U : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₁) → 𝔽₂)) :
    Wco W₁ (Submodule.map (Ip W₁).mulVecLin U) = U := by
  have h2 : Submodule.map (ecW W₁).toLinearMap U = Submodule.comap (ecW W₁).symm.toLinearMap U :=
    Submodule.map_equiv_eq_comap_symm (ecW W₁) U
  unfold Wco
  rw [Ip_mulVecLin, Submodule.map_comp, Submodule.comap_map_eq_of_injective
    (Submodule.subtype_injective W₁), h2, Submodule.map_comap_eq, LinearEquiv.range, top_inf_eq]

end

end Submission.Grassmann
