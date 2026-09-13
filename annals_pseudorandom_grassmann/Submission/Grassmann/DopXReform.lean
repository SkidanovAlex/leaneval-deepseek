import Submission.Grassmann.Transport
import Submission.Grassmann.D4Rewrite
import Submission.Grassmann.Coords

/-!
# The `X`-derivative `D_X` in the big space

`DopX V₁ W₁ V₂ W₂ X T f` (arXiv:2209.04243 §8) is the `X`-derivative
`D_X ∘ D_{V₂,W₂,T}` for a map `X : ↥W₂ → V/V₂` with `ker X = W₁` and `Im X = V₁/V₂`.
Its definition applies `L_X` on the quotient coordinates `L(V/V₂,W₂)` and then restricts
down to `L(V/V₁,W₁)`.

Here we show that it can be written as an honest restriction of a Laplacian of the *big*
space `L(V,W)`:

* `DopX_eq_restr` : `DopX ... T f = (L_{P_X}[f])_{(V₁,W₁) → T}` where `L_{P_X}` is the
  multiplier with predicate `P_X Y := plLE (XtOf V₂ W₂ X) (charMat V₂ W₂ Y)`;
* `sum_l4q_DopX` : averaging over the shift `T` gives
  `Σ_T ‖DopX ... T f‖₄⁴ = q^{mn} ‖L_{P_X}[f]‖₄⁴`.

The second identity is the "expectation over `T`" step of the induction: it removes the shift
and exposes a single Laplacian of the big space, which is what one needs in order to apply the
switching-roles Proposition.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-- **`DopX` as a restriction of a Laplacian of the big space.** -/
theorem DopX_eq_restr (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂) :
    DopX V₁ W₁ V₂ W₂ X T f =
      restr (Qp V₁) (Ip W₁) (lapMulN (fun Y : Matrix (Fin n) (Fin m) 𝔽₂ =>
        plLE (XtOf V₂ W₂ X) (charMat V₂ W₂ Y)) (shift T (Lsub V₂ W₂ f))) := by
  have hQ : QsupT V₁ V₂ * Qp V₂ = Qp V₁ := by rw [QsupT_eq V₁ V₂ hV, Qsup_mul_Qp]
  have hI : Ip W₂ * IsubT W₁ W₂ = Ip W₁ := by rw [IsubT_eq W₁ W₂ hW, Ip_mul_Isub]
  have hstep : DopX V₁ W₁ V₂ W₂ X T f =
      restr (QsupT V₁ V₂) (IsubT W₁ W₂)
        (restr (Qp V₂) (Ip W₂)
          (lapMulN (fun Y : Matrix (Fin n) (Fin m) 𝔽₂ =>
            plLE (XtOf V₂ W₂ X) (charMat V₂ W₂ Y)) (shift T (Lsub V₂ W₂ f)))) := by
    rw [DopX]
    rw [← restr_lapMulN_comp (Qp V₂) (Ip W₂) (plLE (XtOf V₂ W₂ X))
      (shift T (Lsub V₂ W₂ f))]
    simp only [charMat]
  rw [hstep, restr_restr, hQ, hI]

/-- **The averaged `X`-derivative**: `Σ_T ‖D_X ∘ D_{V₂,W₂,T}[f]‖₄⁴ = q^{mn} ‖L_X[f]‖₄⁴`. -/
theorem sum_l4q_DopX (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂) :
    (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, l4q (DopX V₁ W₁ V₂ W₂ X T f)) =
      (2 : ℝ) ^ (m * n) *
        l4q (lapMulN (fun Y : Matrix (Fin n) (Fin m) 𝔽₂ =>
          plLE (XtOf V₂ W₂ X) (charMat V₂ W₂ Y)) (Lsub V₂ W₂ f)) := by
  set h₀ : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ :=
    lapMulN (fun Y : Matrix (Fin n) (Fin m) 𝔽₂ =>
      plLE (XtOf V₂ W₂ X) (charMat V₂ W₂ Y)) (Lsub V₂ W₂ f) with hh₀
  have hpt : ∀ T : Matrix (Fin m) (Fin n) 𝔽₂,
      DopX V₁ W₁ V₂ W₂ X T f = restr (Qp V₁) (Ip W₁) (shift T h₀) := by
    intro T
    rw [DopX_eq_restr V₁ W₁ V₂ W₂ X T f hV hW, lapMulN_shift]
  have h4 : ∀ T : Matrix (Fin m) (Fin n) 𝔽₂,
      l4q (restr (Qp V₁) (Ip W₁) (shift T h₀)) =
        ((Nat.card (homSub V₁ W₁) : ℝ))⁻¹ *
          ∑ B : homSub V₁ W₁, ‖h₀ (B.1 + T)‖ ^ 4 :=
    fun T => l4q_restr_shift_eq_homSub V₁ W₁ (Qp V₁) (Ip W₁) (ker_Qp V₁) (range_Qp V₁)
      (range_Ip W₁) (ker_Ip W₁) T h₀
  rw [Finset.sum_congr rfl (fun T _ => by rw [hpt T])]
  rw [Finset.sum_congr rfl (fun T _ => h4 T)]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hshift : ∀ B : homSub V₁ W₁,
      (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, ‖h₀ (B.1 + T)‖ ^ 4) =
        ∑ T : Matrix (Fin m) (Fin n) 𝔽₂, ‖h₀ T‖ ^ 4 := by
    intro B
    refine Fintype.sum_equiv (Equiv.addLeft B.1) (fun T => ‖h₀ (B.1 + T)‖ ^ 4)
      (fun T => ‖h₀ T‖ ^ 4) (fun T => ?_)
    simp [Equiv.coe_addLeft]
  rw [Finset.sum_congr rfl (fun B _ => hshift B)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have htot : (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, ‖h₀ T‖ ^ 4) =
      (2 : ℝ) ^ (m * n) * l4q h₀ := by
    rw [l4q, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0)), one_mul]
  rw [htot, ← Nat.card_eq_fintype_card]
  haveI hne : Nonempty (homSub V₁ W₁) := ⟨⟨(0 : Matrix (Fin m) (Fin n) 𝔽₂), by simp⟩⟩
  have hcard : ((Nat.card (homSub V₁ W₁) : ℝ)) ≠ 0 := by
    have hpos : 0 < Nat.card (homSub V₁ W₁) := Nat.card_pos
    exact_mod_cast ne_of_gt hpos
  field_simp

end

end Submission.Grassmann
