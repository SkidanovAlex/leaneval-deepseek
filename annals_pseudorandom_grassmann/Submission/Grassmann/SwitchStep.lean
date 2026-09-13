import Submission.Grassmann.SwitchingRoles
import Submission.Grassmann.HypHyperUC
import Submission.Grassmann.DopXReform
import Submission.Grassmann.Coords
import Submission.Grassmann.DerivativeDegree
import Submission.Grassmann.DerivativeComposition
import Submission.Grassmann.D4Rewrite
import Submission.Grassmann.Reparam
import Submission.Commons.LinearAlgebra.Submodule.card_complements_between
import Submission.Commons.LinearAlgebra.finrank_comap_eq

/-!
# Step (D) of §8 of arXiv:2209.04243: the switching-roles step

The switching-roles Proposition (`switching_roles_shift`) is stated for the *canonical*
coordinate systems `Qp V₁`/`Ip W₁` of the ambient.  In the induction step it has to be applied
to the derivative `D_X`, computed in the quotient coordinates `Vco V₂ V₁`/`Wco W₂ W₁`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## The `L²`-norm of a restriction depends only on kernel and range -/

/-- The `L²`-norm of a restriction depends only on the kernel and the range of the two maps (and
on the ambient). -/
theorem l2sq_restr_congr {m n m₁ n₁ m₂ n₂ : ℕ} (V : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Q₁ : Matrix (Fin n₁) (Fin n) 𝔽₂) (ι₁ : Matrix (Fin m) (Fin m₁) 𝔽₂)
    (Q₂ : Matrix (Fin n₂) (Fin n) 𝔽₂) (ι₂ : Matrix (Fin m) (Fin m₂) 𝔽₂)
    (hQ₁ : LinearMap.ker Q₁.mulVecLin = V) (hQ₁r : LinearMap.range Q₁.mulVecLin = ⊤)
    (hι₁ : LinearMap.range ι₁.mulVecLin = W) (hι₁k : LinearMap.ker ι₁.mulVecLin = ⊥)
    (hQ₂ : LinearMap.ker Q₂.mulVecLin = V) (hQ₂r : LinearMap.range Q₂.mulVecLin = ⊤)
    (hι₂ : LinearMap.range ι₂.mulVecLin = W) (hι₂k : LinearMap.ker ι₂.mulVecLin = ⊥)
    (h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (restr Q₁ ι₁ h) = l2sq (restr Q₂ ι₂ h) := by
  have h1 := l2sq_restr_shift_eq_homSub V W Q₁ ι₁ hQ₁ hQ₁r hι₁ hι₁k
    (0 : Matrix (Fin m) (Fin n) 𝔽₂) h
  have h2 := l2sq_restr_shift_eq_homSub V W Q₂ ι₂ hQ₂ hQ₂r hι₂ hι₂k
    (0 : Matrix (Fin m) (Fin n) 𝔽₂) h
  rw [shift_zero_left] at h1 h2
  rw [h1, h2]

/-- The `L⁴`-norm version of `l2sq_restr_congr`. -/
theorem l4q_restr_congr {m n m₁ n₁ m₂ n₂ : ℕ} (V : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Q₁ : Matrix (Fin n₁) (Fin n) 𝔽₂) (ι₁ : Matrix (Fin m) (Fin m₁) 𝔽₂)
    (Q₂ : Matrix (Fin n₂) (Fin n) 𝔽₂) (ι₂ : Matrix (Fin m) (Fin m₂) 𝔽₂)
    (hQ₁ : LinearMap.ker Q₁.mulVecLin = V) (hQ₁r : LinearMap.range Q₁.mulVecLin = ⊤)
    (hι₁ : LinearMap.range ι₁.mulVecLin = W) (hι₁k : LinearMap.ker ι₁.mulVecLin = ⊥)
    (hQ₂ : LinearMap.ker Q₂.mulVecLin = V) (hQ₂r : LinearMap.range Q₂.mulVecLin = ⊤)
    (hι₂ : LinearMap.range ι₂.mulVecLin = W) (hι₂k : LinearMap.ker ι₂.mulVecLin = ⊥)
    (h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l4q (restr Q₁ ι₁ h) = l4q (restr Q₂ ι₂ h) := by
  have h1 := l4q_restr_shift_eq_homSub V W Q₁ ι₁ hQ₁ hQ₁r hι₁ hι₁k
    (0 : Matrix (Fin m) (Fin n) 𝔽₂) h
  have h2 := l4q_restr_shift_eq_homSub V W Q₂ ι₂ hQ₂ hQ₂r hι₂ hι₂k
    (0 : Matrix (Fin m) (Fin n) 𝔽₂) h
  rw [shift_zero_left] at h1 h2
  rw [h1, h2]

/-! ## The `X`-derivative in the quotient coordinates -/

/-- The `X`-derivative with the restriction maps `Qp (Vco V₂ V₁)`, `Ip (Wco W₂ W₁)` — the
coordinate system in which the switching-roles Proposition has to be applied. -/
noncomputable def DopXq (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)))
      (Fin ((n - Module.finrank 𝔽₂ V₂) - Module.finrank 𝔽₂ (Vco V₂ V₁))) 𝔽₂ → ℂ :=
  restr (Qp (Vco V₂ V₁)) (Ip (Wco W₂ W₁))
    (lapMulN (plLE (XtOf V₂ W₂ X)) (Dop0S V₂ W₂ T f))

/-- `DopUpS (Vco V₂ V₁) (Wco W₂ W₁) (XtOf V₂ W₂ X) 0 (Dop0S V₂ W₂ T f)` is `DopXq`. -/
theorem DopUpS_DopXq (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DopUpS (Vco V₂ V₁) (Wco W₂ W₁) (XtOf V₂ W₂ X) 0 (Dop0S V₂ W₂ T f) =
      DopXq V₁ W₁ V₂ W₂ X T f := by
  rw [DopUpS, DopXq, shift_zero_left]

/-- **`DopXq` as a restriction of a Laplacian of the big space.** -/
theorem DopXq_eq_restr_big (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DopXq V₁ W₁ V₂ W₂ X T f =
      restr (Qp (Vco V₂ V₁) * Qp V₂) (Ip W₂ * Ip (Wco W₂ W₁))
        (lapMulN (fun Y : Matrix (Fin n) (Fin m) 𝔽₂ =>
          plLE (XtOf V₂ W₂ X) (charMat V₂ W₂ Y)) (shift T (Lsub V₂ W₂ f))) := by
  have hA : lapMulN (plLE (XtOf V₂ W₂ X)) (Dop0S V₂ W₂ T f) =
      restr (Qp V₂) (Ip W₂) (lapMulN (fun Y : Matrix (Fin n) (Fin m) 𝔽₂ =>
        plLE (XtOf V₂ W₂ X) (charMat V₂ W₂ Y)) (shift T (Lsub V₂ W₂ f))) := by
    rw [Dop0S]
    exact (restr_lapMulN_comp (Qp V₂) (Ip W₂) (plLE (XtOf V₂ W₂ X))
      (shift T (Lsub V₂ W₂ f))).symm
  rw [DopXq, hA, restr_restr]

/-- The kernel of the composite restriction of `DopXq`. -/
theorem ker_Qp_mul_Qp_Vco (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (h : V₂ ≤ V₁) :
    LinearMap.ker ((Qp (Vco V₂ V₁) * Qp V₂)).mulVecLin = V₁ := by
  rw [Matrix.mulVecLin_mul, LinearMap.ker_comp, ker_Qp]
  have hthis : Vco V₂ V₁ = Submodule.map (Qp V₂).mulVecLin V₁ := by
    rw [Vco, ← Submodule.map_comp, ← Qp_mulVecLin]
  rw [hthis, Submodule.comap_map_eq, ker_Qp, sup_eq_left.mpr h]

/-- The range of the composite restriction of `DopXq`. -/
theorem range_Qp_mul_Qp_Vco (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    LinearMap.range ((Qp (Vco V₂ V₁) * Qp V₂)).mulVecLin = ⊤ := by
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp, range_Qp, Submodule.map_top, range_Qp]

/-- The range of the composite inclusion of `DopXq`. -/
theorem range_Ip_mul_Ip_Wco {m : ℕ} (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (h : W₁ ≤ W₂) :
    LinearMap.range ((Ip W₂ * Ip (Wco W₂ W₁))).mulVecLin = W₁ := by
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp, range_Ip, Wco, ← Submodule.map_comp]
  have hcomp : ((Ip W₂).mulVecLin.comp (ecW W₂).symm.toLinearMap) = W₂.subtype := by
    rw [Ip_mulVecLin]
    ext x
    simp
  rw [hcomp, Submodule.map_comap_eq, Submodule.range_subtype, inf_comm, inf_eq_left.mpr h]

/-- The kernel of the composite inclusion of `DopXq`. -/
theorem ker_Ip_mul_Ip_Wco {m : ℕ} (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) :
    LinearMap.ker ((Ip W₂ * Ip (Wco W₂ W₁))).mulVecLin = ⊥ := by
  rw [Matrix.mulVecLin_mul, LinearMap.ker_comp, ker_Ip, Submodule.comap_bot, ker_Ip]

/-- **`DopXq` has the same `L⁴`-norm as `DopX`.** -/
theorem l4q_DopXq_eq_DopX (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂) :
    l4q (DopXq V₁ W₁ V₂ W₂ X T f) = l4q (DopX V₁ W₁ V₂ W₂ X T f) := by
  rw [DopXq_eq_restr_big, DopX_eq_restr V₁ W₁ V₂ W₂ X T f hV hW]
  exact l4q_restr_congr V₁ W₁ (Qp (Vco V₂ V₁) * Qp V₂) (Ip W₂ * Ip (Wco W₂ W₁))
    (Qp V₁) (Ip W₁)
    (ker_Qp_mul_Qp_Vco V₁ V₂ hV) (range_Qp_mul_Qp_Vco V₁ V₂)
    (range_Ip_mul_Ip_Wco W₁ W₂ hW) (ker_Ip_mul_Ip_Wco W₁ W₂)
    (ker_Qp V₁) (range_Qp V₁) (range_Ip W₁) (ker_Ip W₁) _

/-- **The degree of `DopXq`**: `DegLe (d - |t|) (DopXq …)` for `DegLe d f`. -/
theorem degLe_DopXq {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f)
    (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (_hV : V₂ ≤ V₁) (_hW : W₁ ≤ W₂)
    (hker : LinearMap.ker X = Submodule.comap W₂.subtype W₁)
    (hrange : LinearMap.range X = Submodule.map (Submodule.mkQ V₂) V₁) :
    DegLe (d - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂) +
      Module.finrank 𝔽₂ (LinearMap.range X))) (DopXq V₁ W₁ V₂ W₂ X T f) := by
  have h1 := degLe_Dop0S (V₂ := V₂) (W₂ := W₂) (T := T) hf
  have h2 : DegLe ((d - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂))) -
      (XtOf V₂ W₂ X).rank)
      (restr (Qp (Vco V₂ V₁)) (Ip (Wco W₂ W₁))
        (lapMulN (plLE (XtOf V₂ W₂ X)) (Dop0S V₂ W₂ T f))) := by
    refine degLe_restr_lapMulN_plLE (Qp (Vco V₂ V₁)) (Ip (Wco W₂ W₁)) (XtOf V₂ W₂ X)
      ?_ ?_ ?_ h1
    · rw [ker_Qp, Vco, ← hrange, ← range_XtOf]
    · rw [ker_Ip]
    · rw [range_Ip, ker_XtOf, hker, Wco]
  have harith : (d - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂))) -
      (XtOf V₂ W₂ X).rank =
      d - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂) +
        Module.finrank 𝔽₂ (LinearMap.range X)) := by
    rw [rank_XtOf]; omega
  rw [DopXq, ← harith]
  exact h2


/-! ## The lifted roles for the switching-roles Proposition -/

/-- `V₁ ≤ Qp V₁⁻¹ V₄`. -/
theorem le_comap_Qp {N : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (V₄ : Submodule 𝔽₂ (Fin (N - Module.finrank 𝔽₂ V₁r) → 𝔽₂)) :
    V₁r ≤ Submodule.comap (Qp V₁r).mulVecLin V₄ := by
  intro x hx
  have h : x ∈ LinearMap.ker (Qp V₁r).mulVecLin := by rwa [ker_Qp V₁r]
  rw [Submodule.mem_comap, LinearMap.mem_ker.mp h]
  exact V₄.zero_mem

/-- `Ip W₁ '' W₄ ≤ W₁`. -/
theorem map_Ip_le {M : ℕ} (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₁r) → 𝔽₂)) :
    Submodule.map (Ip W₁r).mulVecLin W₄ ≤ W₁r := by
  rintro x ⟨y, hy, rfl⟩
  exact Ip_mem W₁r y

/-- The lifted role-`V₂` of the switching-roles Proposition: the preimage of the coordinate
subspace `V₄` under `Qp V₁r`. -/
abbrev liftV {N : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (V₄ : Submodule 𝔽₂ (Fin (N - Module.finrank 𝔽₂ V₁r) → 𝔽₂)) : Submodule 𝔽₂ (Fin N → 𝔽₂) :=
  Submodule.comap (Qp V₁r).mulVecLin V₄

/-- The lifted role-`W₂` of the switching-roles Proposition: the image of the coordinate
subspace `W₄` under `Ip W₁r`. -/
abbrev liftW {M : ℕ} (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₁r) → 𝔽₂)) : Submodule 𝔽₂ (Fin M → 𝔽₂) :=
  Submodule.map (Ip W₁r).mulVecLin W₄

/-- The coordinates of the lift of `V₄` are `V₄`. -/
theorem Vco_liftV {N : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (V₄ : Submodule 𝔽₂ (Fin (N - Module.finrank 𝔽₂ V₁r) → 𝔽₂)) :
    Vco V₁r (liftV V₁r V₄) = V₄ := Vco_comap_Qp V₁r V₄

/-- The coordinates of the lift of `W₄` are `W₄`. -/
theorem Wco_liftW {M : ℕ} (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₁r) → 𝔽₂)) :
    Wco W₁r (liftW W₁r W₄) = W₄ := Wco_map_Ip W₁r W₄

/-- The kernel of the lifted outer restriction map. -/
theorem ker_Qsup_lift {N : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (V₄ : Submodule 𝔽₂ (Fin (N - Module.finrank 𝔽₂ V₁r) → 𝔽₂)) :
    LinearMap.ker (Qsup (liftV V₁r V₄) V₁r (le_comap_Qp V₁r V₄)).mulVecLin = V₄ := by
  rw [ker_Qsup, Vco_liftV]

/-- The range of the lifted outer inclusion map. -/
theorem range_Isub_lift {M : ℕ} (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₁r) → 𝔽₂)) :
    LinearMap.range (Isub (liftW W₁r W₄) W₁r (map_Ip_le W₁r W₄)).mulVecLin = W₄ := by
  rw [range_Isub, Wco_liftW]

/-- **Step (D) of §8, the core identity**: the `L²`-norm of the `X`-derivative followed by the
hybrid derivative at `(V₄,W₄)` equals that of the left-hand side of the switching-roles
Proposition at the lifted roles. -/
theorem l2sq_Dop0S_DopXq_eq (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ V₂) -
      Module.finrank 𝔽₂ (Vco V₂ V₁)) → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)) → 𝔽₂))
    (S : Matrix (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)))
      (Fin ((n - Module.finrank 𝔽₂ V₂) - Module.finrank 𝔽₂ (Vco V₂ V₁))) 𝔽₂) :
    l2sq (Dop0S V₄ W₄ S (DopXq V₁ W₁ V₂ W₂ X T f)) =
      l2sq (SwitchLHSS (Vco V₂ V₁) (Wco W₂ W₁)
        (Submodule.comap (Qp (Vco V₂ V₁)).mulVecLin V₄)
        (Submodule.map (Ip (Wco W₂ W₁)).mulVecLin W₄)
        (le_comap_Qp (Vco V₂ V₁) V₄) (map_Ip_le (Wco W₂ W₁) W₄)
        (XtOf V₂ W₂ X) 0 S (Dop0S V₂ W₂ T f)) := by
  rw [SwitchLHSS, DopUpS_DopXq, DopDownS, Dop0S, Lsub]
  have hmult : hybridPredSub (Vco (Vco V₂ V₁) (Submodule.comap (Qp (Vco V₂ V₁)).mulVecLin V₄))
      (Wco (Wco W₂ W₁) (Submodule.map (Ip (Wco W₂ W₁)).mulVecLin W₄))
      = hybridPredSub V₄ W₄ := by
    rw [Vco_comap_Qp, Wco_map_Ip]
  rw [hmult]
  exact l2sq_restr_congr V₄ W₄ (Qp V₄) (Ip W₄)
    (Qsup (Submodule.comap (Qp (Vco V₂ V₁)).mulVecLin V₄) (Vco V₂ V₁)
      (le_comap_Qp (Vco V₂ V₁) V₄))
    (Isub (Submodule.map (Ip (Wco W₂ W₁)).mulVecLin W₄) (Wco W₂ W₁)
      (map_Ip_le (Wco W₂ W₁) W₄))
    (ker_Qp V₄) (range_Qp V₄) (range_Ip W₄) (ker_Ip W₄)
    (ker_Qsup_lift (Vco V₂ V₁) V₄)
    (range_Qsup (Submodule.comap (Qp (Vco V₂ V₁)).mulVecLin V₄) (Vco V₂ V₁)
      (le_comap_Qp (Vco V₂ V₁) V₄))
    (range_Isub_lift (Wco W₂ W₁) W₄) (ker_Isub _ _ _)
    (shift S (lapMulN (hybridPredSub V₄ W₄) (DopXq V₁ W₁ V₂ W₂ X T f)))


/-! ## The Cauchy–Schwarz step -/

/-- Cauchy–Schwarz for the `L²`-norm of a finite sum. -/
lemma sq_l2sq_sum_le {m n : ℕ} {ι : Type*} [Fintype ι]
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (l2sq (∑ i, g i)) ^ 2 ≤ ((Fintype.card ι : ℝ)) ^ 3 * ∑ i, (l2sq (g i)) ^ 2 := by
  have heq : (∑ i : ι, g i) = fun A => ∑ i, g i A := by
    funext A
    exact Finset.sum_apply A Finset.univ g
  have h1 : l2sq (∑ i, g i) ≤ ((Fintype.card ι : ℝ)) * ∑ i, l2sq (g i) := by
    have h := l2sq_sum_le (s := (Finset.univ : Finset ι)) (g := g)
    rw [heq]
    exact h
  refine (pow_le_pow_left₀ (l2sq_nonneg _) h1 2).trans ?_
  have h3 : (∑ i, l2sq (g i)) ^ 2 ≤ ((Fintype.card ι : ℝ)) * ∑ i, (l2sq (g i)) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
      (f := fun i => l2sq (g i))
    exact h
  calc (((Fintype.card ι : ℝ)) * ∑ i, l2sq (g i)) ^ 2
      = ((Fintype.card ι : ℝ)) ^ 2 * (∑ i, l2sq (g i)) ^ 2 := by ring
    _ ≤ ((Fintype.card ι : ℝ)) ^ 2 *
        (((Fintype.card ι : ℝ)) * ∑ i, (l2sq (g i)) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ((Fintype.card ι : ℝ)) ^ 3 * ∑ i, (l2sq (g i)) ^ 2 := by ring

/-- Cauchy–Schwarz for the `L²`-norm of a finite sum over a `Finset`. -/
lemma sq_l2sq_sum_le_finset {m n : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (l2sq (fun A => ∑ i ∈ s, g i A)) ^ 2 ≤ (((s.card : ℕ) : ℝ)) ^ 3 *
      ∑ i ∈ s, (l2sq (g i)) ^ 2 := by
  have h1 : l2sq (fun A => ∑ i ∈ s, g i A) ≤ ((s.card : ℕ) : ℝ) *
      ∑ i ∈ s, l2sq (g i) := l2sq_sum_le s g
  refine (pow_le_pow_left₀ (l2sq_nonneg _) h1 2).trans ?_
  have h3 : (∑ i ∈ s, l2sq (g i)) ^ 2 ≤ ((s.card : ℕ) : ℝ) *
      ∑ i ∈ s, (l2sq (g i)) ^ 2 := sq_sum_le_card_mul_sum_sq
  calc (((s.card : ℕ) : ℝ) * ∑ i ∈ s, l2sq (g i)) ^ 2
      = ((s.card : ℕ) : ℝ) ^ 2 * (∑ i ∈ s, l2sq (g i)) ^ 2 := by ring
    _ ≤ ((s.card : ℕ) : ℝ) ^ 2 * (((s.card : ℕ) : ℝ) * ∑ i ∈ s, (l2sq (g i)) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (((s.card : ℕ) : ℝ)) ^ 3 * ∑ i ∈ s, (l2sq (g i)) ^ 2 := by ring

/-- Cauchy–Schwarz for the `L²`-norm of a finite sum whose non-vanishing terms are supported on
a predicate `q`. -/
lemma sq_l2sq_sum_filter_le {m n : ℕ} {ι : Type*} [Fintype ι] (q : ι → Prop)
    [DecidablePred q] (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hzero : ∀ i, ¬ q i → g i = 0) :
    (l2sq (∑ i, g i)) ^ 2 ≤ ((((Finset.univ.filter q).card : ℕ) : ℝ)) ^ 3 *
      ∑ i ∈ Finset.univ.filter q, (l2sq (g i)) ^ 2 := by
  have hsum : (∑ i : ι, g i) = fun A => ∑ i ∈ Finset.univ.filter q, g i A := by
    funext A
    have h1 : (∑ i : ι, g i) A = ∑ i, g i A := Finset.sum_apply A Finset.univ g
    rw [h1]
    exact (Finset.sum_subset (Finset.filter_subset q Finset.univ)
      (fun x _ hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact congrFun (hzero x hx) A)).symm
  rw [hsum]
  exact sq_l2sq_sum_le_finset _ _

/-- The index set of the switching-roles sum. -/
def FrSet {N M : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂)) (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂))
    (V₂r : Submodule 𝔽₂ (Fin N → 𝔽₂)) (W₂r : Submodule 𝔽₂ (Fin M → 𝔽₂)) :
    Finset (Submodule 𝔽₂ (Fin N → 𝔽₂) × Submodule 𝔽₂ (Fin M → 𝔽₂)) :=
  Finset.univ.filter fun p => Fr V₁r W₁r V₂r W₂r p.1 p.2

theorem mem_FrSet {N M : ℕ} {V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂)}
    {W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂)} {V₂r : Submodule 𝔽₂ (Fin N → 𝔽₂)}
    {W₂r : Submodule 𝔽₂ (Fin M → 𝔽₂)}
    {p : Submodule 𝔽₂ (Fin N → 𝔽₂) × Submodule 𝔽₂ (Fin M → 𝔽₂)} :
    p ∈ FrSet V₁r W₁r V₂r W₂r ↔ Fr V₁r W₁r V₂r W₂r p.1 p.2 := by
  simp only [FrSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Cauchy–Schwarz for a finite sum whose non-vanishing terms are supported on a `Finset` `s`:
the sum over all of `ι` on the right (the vanishing terms contribute nothing). -/
theorem sq_l2sq_sum_le_of_support {m n : ℕ} {ι : Type*} [Fintype ι]
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (s : Finset ι)
    (hzero : ∀ i, i ∉ s → g i = 0) :
    (l2sq (∑ i, g i)) ^ 2 ≤ (((s.card : ℕ) : ℝ)) ^ 3 * ∑ i, (l2sq (g i)) ^ 2 := by
  have hsum : (∑ i : ι, g i) = fun A => ∑ i ∈ s, g i A := by
    funext A
    have h1 : (∑ i : ι, g i) A = ∑ i, g i A := Finset.sum_apply A Finset.univ g
    rw [h1]
    exact (Finset.sum_subset (Finset.subset_univ s)
      (fun x _ hx => congrFun (hzero x hx) A)).symm
  rw [hsum]
  refine (sq_l2sq_sum_le_finset s g).trans ?_
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ s) (fun i _ _ => by positivity)) (by positivity)

/-- Cauchy–Schwarz for the right-hand side of the switching-roles Proposition. -/
theorem sq_l2sq_SwitchRHSS_le {N M : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂)) (V₂r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₂r : Submodule 𝔽₂ (Fin M → 𝔽₂)) (Xr : Matrix (Fin N) (Fin M) 𝔽₂)
    (S : Matrix (Fin M) (Fin N) 𝔽₂) (g : Matrix (Fin M) (Fin N) 𝔽₂ → ℂ) :
    (l2sq (SwitchRHSS V₁r W₁r V₂r W₂r Xr S g)) ^ 2 ≤
      ((((FrSet V₁r W₁r V₂r W₂r).card : ℕ) : ℝ)) ^ 3 *
        ∑ p : Submodule 𝔽₂ (Fin N → 𝔽₂) × Submodule 𝔽₂ (Fin M → 𝔽₂),
          (l2sq (SwitchSummandS V₁r W₁r V₂r W₂r p.1 p.2 Xr S g)) ^ 2 := by
  rw [SwitchRHSS]
  exact sq_l2sq_sum_le_of_support
    (fun p : Submodule 𝔽₂ (Fin N → 𝔽₂) × Submodule 𝔽₂ (Fin M → 𝔽₂) =>
      SwitchSummandS V₁r W₁r V₂r W₂r p.1 p.2 Xr S g)
    (FrSet V₁r W₁r V₂r W₂r)
    (fun p hp => by rw [SwitchSummandS_eq, if_neg (fun h => hp (mem_FrSet.mpr h))])

/-- **Step (D) of §8 (the switching-roles bound)**: for the `X`-derivative of a triple
`t = (V₂,W₂,X)` and the pair `(V₄,W₄)` in the quotient coordinates, the squared `L²`-norm of the
composite derivative is bounded by the sum of the squared `L²`-norms of the switched summands,
up to the Cauchy–Schwarz factor `#𝓕³`. -/
theorem stepD_bound (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hXker : LinearMap.ker (XtOf V₂ W₂ X).mulVecLin = Wco W₂ W₁)
    (hXrange : LinearMap.range (XtOf V₂ W₂ X).mulVecLin = Vco V₂ V₁)
    (V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ V₂) -
      Module.finrank 𝔽₂ (Vco V₂ V₁)) → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)) → 𝔽₂))
    (S : Matrix (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)))
      (Fin ((n - Module.finrank 𝔽₂ V₂) - Module.finrank 𝔽₂ (Vco V₂ V₁))) 𝔽₂) :
    (l2sq (Dop0S V₄ W₄ S (DopXq V₁ W₁ V₂ W₂ X T f))) ^ 2 ≤
      ((((FrSet (Vco V₂ V₁) (Wco W₂ W₁) (liftV (Vco V₂ V₁) V₄)
        (liftW (Wco W₂ W₁) W₄)).card : ℕ) : ℝ)) ^ 3 *
      ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ V₂) → 𝔽₂) ×
          Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₂) → 𝔽₂),
        (l2sq (SwitchSummandS (Vco V₂ V₁) (Wco W₂ W₁) (liftV (Vco V₂ V₁) V₄)
          (liftW (Wco W₂ W₁) W₄) p.1 p.2 (XtOf V₂ W₂ X)
          (0 + Ip (Wco W₂ W₁) * S * Qp (Vco V₂ V₁)) (Dop0S V₂ W₂ T f))) ^ 2 := by
  rw [l2sq_Dop0S_DopXq_eq V₁ W₁ V₂ W₂ X T f V₄ W₄ S]
  rw [switching_roles_shift (Vco V₂ V₁) (Wco W₂ W₁)
    (liftV (Vco V₂ V₁) V₄) (liftW (Wco W₂ W₁) W₄)
    hXker hXrange (le_comap_Qp (Vco V₂ V₁) V₄) (map_Ip_le (Wco W₂ W₁) W₄)
    0 S (Dop0S V₂ W₂ T f)]
  exact sq_l2sq_SwitchRHSS_le (Vco V₂ V₁) (Wco W₂ W₁) (liftV (Vco V₂ V₁) V₄)
    (liftW (Wco W₂ W₁) W₄) (XtOf V₂ W₂ X) (0 + Ip (Wco W₂ W₁) * S * Qp (Vco V₂ V₁))
    (Dop0S V₂ W₂ T f)


/-! ## The number of summands of the switching-roles sum -/

/-- The number of complements of `V₁r` in `V₂r` (the `V₃`-index set of the switching sum). -/
theorem card_FrV {N : ℕ} (V₁r V₂r : Submodule 𝔽₂ (Fin N → 𝔽₂)) (h : V₁r ≤ V₂r) :
    Nat.card {V₃ : Submodule 𝔽₂ (Fin N → 𝔽₂) // V₃ ⊓ V₁r = ⊥ ∧ V₃ ⊔ V₁r = V₂r} =
      2 ^ ((Module.finrank 𝔽₂ V₂r - Module.finrank 𝔽₂ V₁r) * Module.finrank 𝔽₂ V₁r) := by
  have hcard := Commons.LinearAlgebra.Submodule.card_complements_between
    (⊥ : Submodule 𝔽₂ (Fin N → 𝔽₂)) V₁r V₂r bot_le h
  have hbot : Module.finrank 𝔽₂ ↥(⊥ : Submodule 𝔽₂ (Fin N → 𝔽₂)) = 0 := finrank_bot 𝔽₂ _
  have heq : Nat.card {V₃ : Submodule 𝔽₂ (Fin N → 𝔽₂) // V₃ ⊓ V₁r = ⊥ ∧ V₃ ⊔ V₁r = V₂r} =
      Nat.card {U : Submodule 𝔽₂ (Fin N → 𝔽₂) //
        ⊥ ≤ U ∧ U ≤ V₂r ∧ U ⊓ V₁r = ⊥ ∧ U ⊔ V₁r = V₂r} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun U => ⟨
      fun hh => ⟨bot_le, le_trans le_sup_left hh.2.le, hh.1, hh.2⟩,
      fun hh => ⟨hh.2.2.1, hh.2.2.2⟩⟩))
  rw [heq, hcard, hbot, Nat.sub_zero, Nat.card_eq_fintype_card, ZMod.card]

/-- The number of `W₃` in the switching-roles index set is
`q^{(M - dim W₁r)·(dim W₁r - dim W₂r)}`. -/
theorem card_FrW {M : ℕ} (W₁r W₂r : Submodule 𝔽₂ (Fin M → 𝔽₂)) (h : W₂r ≤ W₁r) :
    Nat.card {W₃ : Submodule 𝔽₂ (Fin M → 𝔽₂) //
        W₂r ≤ W₃ ∧ W₃ ⊓ W₁r = W₂r ∧ W₃ ⊔ W₁r = ⊤} =
      2 ^ ((M - Module.finrank 𝔽₂ W₁r) *
        (Module.finrank 𝔽₂ W₁r - Module.finrank 𝔽₂ W₂r)) := by
  have hcard := Commons.LinearAlgebra.Submodule.card_complements_between
    W₂r W₁r (⊤ : Submodule 𝔽₂ (Fin M → 𝔽₂)) h le_top
  have htop : Module.finrank 𝔽₂ ↥(⊤ : Submodule 𝔽₂ (Fin M → 𝔽₂)) = M := by
    rw [finrank_top, Module.finrank_fin_fun]
  have heq : Nat.card {W₃ : Submodule 𝔽₂ (Fin M → 𝔽₂) //
        W₂r ≤ W₃ ∧ W₃ ⊓ W₁r = W₂r ∧ W₃ ⊔ W₁r = ⊤} =
      Nat.card {U : Submodule 𝔽₂ (Fin M → 𝔽₂) //
        W₂r ≤ U ∧ U ≤ ⊤ ∧ U ⊓ W₁r = W₂r ∧ U ⊔ W₁r = ⊤} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun U => ⟨
      fun hh => ⟨hh.1, le_top, hh.2.1, hh.2.2⟩,
      fun hh => ⟨hh.1, hh.2.2.1, hh.2.2.2⟩⟩))
  rw [heq, hcard, htop, Nat.card_eq_fintype_card, ZMod.card]

/-- **The number of summands of the switching-roles sum**: `#𝓕 = |𝓥(V₄)|·|𝓦(W₄)|`. -/
theorem card_FrSet {N M : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂)) (V₂r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₂r : Submodule 𝔽₂ (Fin M → 𝔽₂)) (hV : V₁r ≤ V₂r) (hW : W₂r ≤ W₁r) :
    (FrSet V₁r W₁r V₂r W₂r).card =
      2 ^ ((Module.finrank 𝔽₂ V₂r - Module.finrank 𝔽₂ V₁r) * Module.finrank 𝔽₂ V₁r +
        (M - Module.finrank 𝔽₂ W₁r) *
          (Module.finrank 𝔽₂ W₁r - Module.finrank 𝔽₂ W₂r)) := by
  rw [FrSet, ← Fintype.card_subtype (p := fun p : Submodule 𝔽₂ (Fin N → 𝔽₂) ×
    Submodule 𝔽₂ (Fin M → 𝔽₂) => Fr V₁r W₁r V₂r W₂r p.1 p.2)]
  have hprod : Fintype.card {p : Submodule 𝔽₂ (Fin N → 𝔽₂) × Submodule 𝔽₂ (Fin M → 𝔽₂) //
        Fr V₁r W₁r V₂r W₂r p.1 p.2} =
      Fintype.card {V₃ : Submodule 𝔽₂ (Fin N → 𝔽₂) // V₃ ⊓ V₁r = ⊥ ∧ V₃ ⊔ V₁r = V₂r} *
        Fintype.card {W₃ : Submodule 𝔽₂ (Fin M → 𝔽₂) //
          W₂r ≤ W₃ ∧ W₃ ⊓ W₁r = W₂r ∧ W₃ ⊔ W₁r = ⊤} := by
    rw [← Fintype.card_prod]
    refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨⟨V₃, W₃⟩, hV₃, hV₃', hW₃, hW₃', hW₃''⟩
      exact (⟨V₃, hV₃, hV₃'⟩, ⟨W₃, hW₃, hW₃', hW₃''⟩)
    · rintro ⟨⟨V₃, hV₃, hV₃'⟩, ⟨W₃, hW₃, hW₃', hW₃''⟩⟩
      exact ⟨⟨V₃, W₃⟩, hV₃, hV₃', hW₃, hW₃', hW₃''⟩
    · rintro ⟨⟨V₃, W₃⟩, hV₃, hV₃', hW₃, hW₃', hW₃''⟩
      rfl
    · rintro ⟨⟨V₃, hV₃, hV₃'⟩, ⟨W₃, hW₃, hW₃', hW₃''⟩⟩
      rfl
  rw [hprod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_FrV V₁r V₂r hV, card_FrW W₁r W₂r hW, ← pow_add]

/-- **The number of summands is at most `2 ^ (2 d ^ 2)`** when the two "orders" of the
switching data are at most `d`. -/
theorem card_FrSet_le {N M : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂)) (V₂r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₂r : Submodule 𝔽₂ (Fin M → 𝔽₂)) (hV : V₁r ≤ V₂r) (hW : W₂r ≤ W₁r) (d : ℕ)
    (ha : Module.finrank 𝔽₂ V₂r - Module.finrank 𝔽₂ V₁r ≤ d)
    (hb : Module.finrank 𝔽₂ V₁r ≤ d)
    (hc : M - Module.finrank 𝔽₂ W₁r ≤ d)
    (hd : Module.finrank 𝔽₂ W₁r - Module.finrank 𝔽₂ W₂r ≤ d) :
    (FrSet V₁r W₁r V₂r W₂r).card ≤ 2 ^ (2 * d ^ 2) := by
  rw [card_FrSet V₁r W₁r V₂r W₂r hV hW]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  calc (Module.finrank 𝔽₂ V₂r - Module.finrank 𝔽₂ V₁r) * Module.finrank 𝔽₂ V₁r +
        (M - Module.finrank 𝔽₂ W₁r) * (Module.finrank 𝔽₂ W₁r - Module.finrank 𝔽₂ W₂r)
      ≤ d * d + d * d :=
        Nat.add_le_add (Nat.mul_le_mul ha hb) (Nat.mul_le_mul hc hd)
    _ = 2 * d ^ 2 := by ring

/-- **Step (D) of §8 in the form used by the induction**: with the four order bounds, the
Cauchy–Schwarz factor `#𝓕³` is at most `2 ^ (6 d ^ 2)`. -/
theorem stepD_bound_le (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hXker : LinearMap.ker (XtOf V₂ W₂ X).mulVecLin = Wco W₂ W₁)
    (hXrange : LinearMap.range (XtOf V₂ W₂ X).mulVecLin = Vco V₂ V₁)
    (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂)
    (V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ V₂) -
      Module.finrank 𝔽₂ (Vco V₂ V₁)) → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)) → 𝔽₂))
    (S : Matrix (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)))
      (Fin ((n - Module.finrank 𝔽₂ V₂) - Module.finrank 𝔽₂ (Vco V₂ V₁))) 𝔽₂) (d : ℕ)
    (ha : Module.finrank 𝔽₂ (liftV (Vco V₂ V₁) V₄) - Module.finrank 𝔽₂ (Vco V₂ V₁) ≤ d)
    (hb : Module.finrank 𝔽₂ (Vco V₂ V₁) ≤ d)
    (hc : Module.finrank 𝔽₂ W₂ - Module.finrank 𝔽₂ (Wco W₂ W₁) ≤ d)
    (hd : Module.finrank 𝔽₂ (Wco W₂ W₁) - Module.finrank 𝔽₂ (liftW (Wco W₂ W₁) W₄) ≤ d) :
    (l2sq (Dop0S V₄ W₄ S (DopXq V₁ W₁ V₂ W₂ X T f))) ^ 2 ≤
      2 ^ (6 * d ^ 2) *
        ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ V₂) → 𝔽₂) ×
            Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₂) → 𝔽₂),
          (l2sq (SwitchSummandS (Vco V₂ V₁) (Wco W₂ W₁) (liftV (Vco V₂ V₁) V₄)
            (liftW (Wco W₂ W₁) W₄) p.1 p.2 (XtOf V₂ W₂ X)
            (0 + Ip (Wco W₂ W₁) * S * Qp (Vco V₂ V₁)) (Dop0S V₂ W₂ T f))) ^ 2 := by
  refine (stepD_bound V₁ W₁ V₂ W₂ X T f hXker hXrange V₄ W₄ S).trans ?_
  have hcard := card_FrSet_le (Vco V₂ V₁) (Wco W₂ W₁) (liftV (Vco V₂ V₁) V₄)
    (liftW (Wco W₂ W₁) W₄) (le_comap_Qp (Vco V₂ V₁) V₄) (map_Ip_le (Wco W₂ W₁) W₄) d
    ha hb hc hd
  have hcast : ((((FrSet (Vco V₂ V₁) (Wco W₂ W₁) (liftV (Vco V₂ V₁) V₄)
      (liftW (Wco W₂ W₁) W₄)).card : ℕ) : ℝ)) ^ 3 ≤ (2 : ℝ) ^ (6 * d ^ 2) := by
    have h3 : ((((FrSet (Vco V₂ V₁) (Wco W₂ W₁) (liftV (Vco V₂ V₁) V₄)
        (liftW (Wco W₂ W₁) W₄)).card : ℕ) : ℝ)) ^ 3 ≤
        ((((2 ^ (2 * d ^ 2)) : ℕ) : ℝ)) ^ 3 := by
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hcard) 3
    refine h3.trans (le_of_eq ?_)
    push_cast
    ring
  exact mul_le_mul_of_nonneg_right hcast (Finset.sum_nonneg (fun p _ => sq_nonneg _))

/-- `finrank (liftV V₁r V₄) = finrank V₄ + finrank V₁r`. -/
theorem finrank_liftV {N : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (V₄ : Submodule 𝔽₂ (Fin (N - Module.finrank 𝔽₂ V₁r) → 𝔽₂)) :
    Module.finrank 𝔽₂ (liftV V₁r V₄) = Module.finrank 𝔽₂ V₄ + Module.finrank 𝔽₂ V₁r := by
  rw [liftV, Commons.LinearAlgebra.finrank_comap_eq, ker_Qp, range_Qp, inf_top_eq, add_comm]

/-- `finrank (liftW W₁r W₄) = finrank W₄`. -/
theorem finrank_liftW {M : ℕ} (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₁r) → 𝔽₂)) :
    Module.finrank 𝔽₂ (liftW W₁r W₄) = Module.finrank 𝔽₂ W₄ :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (Ip W₁r).mulVecLin
    (by rw [← LinearMap.ker_eq_bot]; exact ker_Ip W₁r) W₄)).symm

/-- The `D4` bound for a single pair `(V₄,W₄)` in the quotient coordinates. -/
lemma D4_Lsub_DopXq_le (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂)
    (hXker : LinearMap.ker (XtOf V₂ W₂ X).mulVecLin = Wco W₂ W₁)
    (hXrange : LinearMap.range (XtOf V₂ W₂ X).mulVecLin = Vco V₂ V₁)
    (V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ V₂) -
      Module.finrank 𝔽₂ (Vco V₂ V₁)) → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)) → 𝔽₂)) (d : ℕ)
    (ha : Module.finrank 𝔽₂ (liftV (Vco V₂ V₁) V₄) - Module.finrank 𝔽₂ (Vco V₂ V₁) ≤ d)
    (hb : Module.finrank 𝔽₂ (Vco V₂ V₁) ≤ d)
    (hc : Module.finrank 𝔽₂ W₂ - Module.finrank 𝔽₂ (Wco W₂ W₁) ≤ d)
    (hd : Module.finrank 𝔽₂ (Wco W₂ W₁) - Module.finrank 𝔽₂ (liftW (Wco W₂ W₁) W₄) ≤ d) :
    D4 V₄ W₄ (Lsub V₄ W₄ (DopXq V₁ W₁ V₂ W₂ X T f)) ≤
      (((2 : ℝ) ^ (Module.finrank 𝔽₂ (Wco W₂ W₁) *
          ((n - Module.finrank 𝔽₂ V₂) - Module.finrank 𝔽₂ (Vco V₂ V₁))))⁻¹) *
        ((2 : ℝ) ^ (6 * d ^ 2) *
          ∑ S : Matrix (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)))
                (Fin ((n - Module.finrank 𝔽₂ V₂) - Module.finrank 𝔽₂ (Vco V₂ V₁))) 𝔽₂,
            ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ V₂) → 𝔽₂) ×
                Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₂) → 𝔽₂),
              (l2sq (SwitchSummandS (Vco V₂ V₁) (Wco W₂ W₁) (liftV (Vco V₂ V₁) V₄)
                (liftW (Wco W₂ W₁) W₄) p.1 p.2 (XtOf V₂ W₂ X)
                (0 + Ip (Wco W₂ W₁) * S * Qp (Vco V₂ V₁)) (Dop0S V₂ W₂ T f))) ^ 2) := by
  rw [D4_Lsub_eq_sum_l2sq V₄ W₄ (DopXq V₁ W₁ V₂ W₂ X T f)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun S _ => stepD_bound_le V₁ W₁ V₂ W₂ X T f hXker hXrange hV hW
    V₄ W₄ S d ha hb hc hd)

/-- **The `D4`-sum applied to `DopXq`, bounded by the switching sum**: for every pair `(V₄,W₄)`
of order `≤ d`, `D4 V₄ W₄ (Lsub V₄ W₄ (DopXq …))` is at most
`2 ^ (6 d ^ 2) · 2 ^ (-(M'N'))` times the sum of the squared `L²`-norms of the switched
summands. -/
lemma sum_D4_DopXq_le (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂)
    (hXker : LinearMap.ker (XtOf V₂ W₂ X).mulVecLin = Wco W₂ W₁)
    (hXrange : LinearMap.range (XtOf V₂ W₂ X).mulVecLin = Vco V₂ V₁) (d : ℕ)
    (hd0 : Module.finrank 𝔽₂ (Vco V₂ V₁) ≤ d)
    (hd1 : Module.finrank 𝔽₂ W₂ - Module.finrank 𝔽₂ (Wco W₂ W₁) ≤ d) :
    (∑ V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ V₂) -
          Module.finrank 𝔽₂ (Vco V₂ V₁)) → 𝔽₂),
      ∑ W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)) → 𝔽₂),
        (if Module.finrank 𝔽₂ V₄ +
            (Module.finrank 𝔽₂ (Wco W₂ W₁) - Module.finrank 𝔽₂ W₄) ≤ d
          then D4 V₄ W₄ (Lsub V₄ W₄ (DopXq V₁ W₁ V₂ W₂ X T f)) else 0))
      ≤ ∑ V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ V₂) -
            Module.finrank 𝔽₂ (Vco V₂ V₁)) → 𝔽₂),
          ∑ W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)) → 𝔽₂),
            (if Module.finrank 𝔽₂ V₄ +
                (Module.finrank 𝔽₂ (Wco W₂ W₁) - Module.finrank 𝔽₂ W₄) ≤ d
              then ((((2 : ℝ) ^ (Module.finrank 𝔽₂ (Wco W₂ W₁) *
                    ((n - Module.finrank 𝔽₂ V₂) - Module.finrank 𝔽₂ (Vco V₂ V₁))))⁻¹) *
                ((2 : ℝ) ^ (6 * d ^ 2) *
                  (∑ S : Matrix (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)))
                        (Fin ((n - Module.finrank 𝔽₂ V₂) -
                          Module.finrank 𝔽₂ (Vco V₂ V₁))) 𝔽₂,
                    ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ V₂) → 𝔽₂) ×
                        Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₂) → 𝔽₂),
                      (l2sq (SwitchSummandS (Vco V₂ V₁) (Wco W₂ W₁)
                        (liftV (Vco V₂ V₁) V₄) (liftW (Wco W₂ W₁) W₄) p.1 p.2
                        (XtOf V₂ W₂ X) (0 + Ip (Wco W₂ W₁) * S * Qp (Vco V₂ V₁))
                        (Dop0S V₂ W₂ T f))) ^ 2)))
              else 0) := by
  refine Finset.sum_le_sum (fun V₄ _ => Finset.sum_le_sum (fun W₄ _ => ?_))
  by_cases hg : Module.finrank 𝔽₂ V₄ +
      (Module.finrank 𝔽₂ (Wco W₂ W₁) - Module.finrank 𝔽₂ W₄) ≤ d
  · rw [if_pos hg, if_pos hg]
    exact D4_Lsub_DopXq_le V₁ W₁ V₂ W₂ X T f hV hW hXker hXrange V₄ W₄ d
      (by rw [finrank_liftV]; omega) hd0 hd1 (by rw [finrank_liftW]; omega)
  · rw [if_neg hg, if_neg hg]


/-! ## The sharpened switching-step count

`card_FrSet` computes the number of summands of the switching sum exactly:
`#𝓕 = 2 ^ ((dim V₂r - dim V₁r)·dim V₁r + (M - dim W₁r)·(dim W₁r - dim W₂r))`.  In the triple
context the two middle factors are *both* equal to the rank `R` of the triple's map, so the cube of
the Cauchy–Schwarz factor is `2 ^ (3·R·(ha + hd))` — a `d·R`-shaped quantity, far better than the
`d²`-shaped bound of `stepD_bound_le`.  This is what makes the constant bookkeeping of the
induction close (see `ROADMAP.md`, session 29).
-/

/-- **The number of summands in the sharp form.**  If the two "middle" dimensions are equal to `k`,
then `#𝓕 = 2 ^ (k · (ha + hd))`. -/
theorem card_FrSet_le_rank {N M : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂)) (V₂r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₂r : Submodule 𝔽₂ (Fin M → 𝔽₂)) (hV : V₁r ≤ V₂r) (hW : W₂r ≤ W₁r) (d k : ℕ)
    (hb : Module.finrank 𝔽₂ V₁r = k) (hc : M - Module.finrank 𝔽₂ W₁r = k)
    (hguard : Module.finrank 𝔽₂ V₂r - Module.finrank 𝔽₂ V₁r +
      (Module.finrank 𝔽₂ W₁r - Module.finrank 𝔽₂ W₂r) ≤ d) :
    (FrSet V₁r W₁r V₂r W₂r).card ≤ 2 ^ (k * d) := by
  rw [hb] at hguard
  rw [card_FrSet V₁r W₁r V₂r W₂r hV hW, hb, hc,
    Nat.mul_comm (Module.finrank 𝔽₂ V₂r - k) k, ← mul_add]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left k hguard)

/-- **Step (D) of §8, sharpened**: the Cauchy–Schwarz factor `#𝓕³` is at most
`2 ^ (3 · d · rank (XtOf V₂ W₂ X))`, using the *single* guard
`dim V₄ + (dim (Wco W₂ W₁) - dim W₄) ≤ d`. -/
theorem stepD_bound_le_rank (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hXker : LinearMap.ker (XtOf V₂ W₂ X).mulVecLin = Wco W₂ W₁)
    (hXrange : LinearMap.range (XtOf V₂ W₂ X).mulVecLin = Vco V₂ V₁)
    (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂)
    (V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ V₂) -
      Module.finrank 𝔽₂ (Vco V₂ V₁)) → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)) → 𝔽₂))
    (S : Matrix (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)))
      (Fin ((n - Module.finrank 𝔽₂ V₂) - Module.finrank 𝔽₂ (Vco V₂ V₁))) 𝔽₂) (d : ℕ)
    (hguard : Module.finrank 𝔽₂ V₄ +
      (Module.finrank 𝔽₂ (Wco W₂ W₁) - Module.finrank 𝔽₂ W₄) ≤ d) :
    (l2sq (Dop0S V₄ W₄ S (DopXq V₁ W₁ V₂ W₂ X T f))) ^ 2 ≤
      (2 : ℝ) ^ (3 * d * (XtOf V₂ W₂ X).rank) *
        ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ V₂) → 𝔽₂) ×
            Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₂) → 𝔽₂),
          (l2sq (SwitchSummandS (Vco V₂ V₁) (Wco W₂ W₁) (liftV (Vco V₂ V₁) V₄)
            (liftW (Wco W₂ W₁) W₄) p.1 p.2 (XtOf V₂ W₂ X)
            (0 + Ip (Wco W₂ W₁) * S * Qp (Vco V₂ V₁)) (Dop0S V₂ W₂ T f))) ^ 2 := by
  have hb : Module.finrank 𝔽₂ (Vco V₂ V₁) = (XtOf V₂ W₂ X).rank := by
    rw [← hXrange, Matrix.rank]
  have hc : (Module.finrank 𝔽₂ W₂ - Module.finrank 𝔽₂ (Wco W₂ W₁)) = (XtOf V₂ W₂ X).rank := by
    rw [← hXker, Matrix.rank]
    have h := LinearMap.finrank_range_add_finrank_ker (XtOf V₂ W₂ X).mulVecLin
    rw [Module.finrank_fin_fun] at h
    omega
  have hguard' : Module.finrank 𝔽₂ (liftV (Vco V₂ V₁) V₄) -
        Module.finrank 𝔽₂ (Vco V₂ V₁) +
      (Module.finrank 𝔽₂ (Wco W₂ W₁) - Module.finrank 𝔽₂ (liftW (Wco W₂ W₁) W₄)) ≤ d := by
    rw [finrank_liftV, finrank_liftW, Nat.add_sub_cancel]
    exact hguard
  have hcard := card_FrSet_le_rank (Vco V₂ V₁) (Wco W₂ W₁) (liftV (Vco V₂ V₁) V₄)
    (liftW (Wco W₂ W₁) W₄) (le_comap_Qp (Vco V₂ V₁) V₄) (map_Ip_le (Wco W₂ W₁) W₄) d
    (XtOf V₂ W₂ X).rank hb hc hguard'
  have hcast : ((((FrSet (Vco V₂ V₁) (Wco W₂ W₁) (liftV (Vco V₂ V₁) V₄)
      (liftW (Wco W₂ W₁) W₄)).card : ℕ) : ℝ)) ^ 3 ≤
      (2 : ℝ) ^ (3 * d * (XtOf V₂ W₂ X).rank) := by
    have h3 : ((((FrSet (Vco V₂ V₁) (Wco W₂ W₁) (liftV (Vco V₂ V₁) V₄)
        (liftW (Wco W₂ W₁) W₄)).card : ℕ) : ℝ)) ^ 3 ≤
        ((((2 ^ ((XtOf V₂ W₂ X).rank * d)) : ℕ) : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hcard) 3
    refine h3.trans (le_of_eq ?_)
    push_cast
    ring
  exact (stepD_bound V₁ W₁ V₂ W₂ X T f hXker hXrange V₄ W₄ S).trans
    (mul_le_mul_of_nonneg_right hcast (Finset.sum_nonneg (fun p _ => sq_nonneg _)))

/-- **The `D4`-bound for a single pair `(V₄,W₄)`**, sharpened. -/
lemma D4_Lsub_DopXq_le_rank (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂)
    (hXker : LinearMap.ker (XtOf V₂ W₂ X).mulVecLin = Wco W₂ W₁)
    (hXrange : LinearMap.range (XtOf V₂ W₂ X).mulVecLin = Vco V₂ V₁)
    (V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ V₂) -
      Module.finrank 𝔽₂ (Vco V₂ V₁)) → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)) → 𝔽₂)) (d : ℕ)
    (hguard : Module.finrank 𝔽₂ V₄ +
      (Module.finrank 𝔽₂ (Wco W₂ W₁) - Module.finrank 𝔽₂ W₄) ≤ d) :
    D4 V₄ W₄ (Lsub V₄ W₄ (DopXq V₁ W₁ V₂ W₂ X T f)) ≤
      (((2 : ℝ) ^ (Module.finrank 𝔽₂ (Wco W₂ W₁) *
          ((n - Module.finrank 𝔽₂ V₂) - Module.finrank 𝔽₂ (Vco V₂ V₁))))⁻¹) *
        ((2 : ℝ) ^ (3 * d * (XtOf V₂ W₂ X).rank) *
          ∑ S : Matrix (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)))
                (Fin ((n - Module.finrank 𝔽₂ V₂) - Module.finrank 𝔽₂ (Vco V₂ V₁))) 𝔽₂,
            ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ V₂) → 𝔽₂) ×
                Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₂) → 𝔽₂),
              (l2sq (SwitchSummandS (Vco V₂ V₁) (Wco W₂ W₁) (liftV (Vco V₂ V₁) V₄)
                (liftW (Wco W₂ W₁) W₄) p.1 p.2 (XtOf V₂ W₂ X)
                (0 + Ip (Wco W₂ W₁) * S * Qp (Vco V₂ V₁)) (Dop0S V₂ W₂ T f))) ^ 2) := by
  rw [D4_Lsub_eq_sum_l2sq V₄ W₄ (DopXq V₁ W₁ V₂ W₂ X T f)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun S _ => stepD_bound_le_rank V₁ W₁ V₂ W₂ X T f hXker hXrange hV hW
    V₄ W₄ S d hguard)

 
/-- **The `D4`-sum applied to `DopXq`, sharpened**: for every pair `(V₄,W₄)` of order `≤ d`,
`D4 V₄ W₄ (Lsub V₄ W₄ (DopXq …))` is at most
`2 ^ (3 d · rank (XtOf V₂ W₂ X)) · 2 ^ (-(M'N'))` times the sum of the squared `L²`-norms of the
switched summands. -/
lemma sum_D4_DopXq_le_rank (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂)
    (hXker : LinearMap.ker (XtOf V₂ W₂ X).mulVecLin = Wco W₂ W₁)
    (hXrange : LinearMap.range (XtOf V₂ W₂ X).mulVecLin = Vco V₂ V₁) (d : ℕ) :
    (∑ V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ V₂) -
          Module.finrank 𝔽₂ (Vco V₂ V₁)) → 𝔽₂),
      ∑ W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)) → 𝔽₂),
        (if Module.finrank 𝔽₂ V₄ +
            (Module.finrank 𝔽₂ (Wco W₂ W₁) - Module.finrank 𝔽₂ W₄) ≤ d
          then D4 V₄ W₄ (Lsub V₄ W₄ (DopXq V₁ W₁ V₂ W₂ X T f)) else 0))
      ≤ ∑ V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ V₂) -
            Module.finrank 𝔽₂ (Vco V₂ V₁)) → 𝔽₂),
          ∑ W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)) → 𝔽₂),
            (if Module.finrank 𝔽₂ V₄ +
                (Module.finrank 𝔽₂ (Wco W₂ W₁) - Module.finrank 𝔽₂ W₄) ≤ d
              then ((((2 : ℝ) ^ (Module.finrank 𝔽₂ (Wco W₂ W₁) *
                    ((n - Module.finrank 𝔽₂ V₂) - Module.finrank 𝔽₂ (Vco V₂ V₁))))⁻¹) *
                ((2 : ℝ) ^ (3 * d * (XtOf V₂ W₂ X).rank) *
                  (∑ S : Matrix (Fin (Module.finrank 𝔽₂ (Wco W₂ W₁)))
                        (Fin ((n - Module.finrank 𝔽₂ V₂) -
                          Module.finrank 𝔽₂ (Vco V₂ V₁))) 𝔽₂,
                    ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ V₂) → 𝔽₂) ×
                        Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₂) → 𝔽₂),
                      (l2sq (SwitchSummandS (Vco V₂ V₁) (Wco W₂ W₁)
                        (liftV (Vco V₂ V₁) V₄) (liftW (Wco W₂ W₁) W₄) p.1 p.2
                        (XtOf V₂ W₂ X) (0 + Ip (Wco W₂ W₁) * S * Qp (Vco V₂ V₁))
                        (Dop0S V₂ W₂ T f))) ^ 2)))
              else 0) := by
  refine Finset.sum_le_sum (fun V₄ _ => Finset.sum_le_sum (fun W₄ _ => ?_))
  by_cases hg : Module.finrank 𝔽₂ V₄ +
      (Module.finrank 𝔽₂ (Wco W₂ W₁) - Module.finrank 𝔽₂ W₄) ≤ d
  · rw [if_pos hg, if_pos hg]
    exact D4_Lsub_DopXq_le_rank V₁ W₁ V₂ W₂ X T f hV hW hXker hXrange V₄ W₄ d hg
  · rw [if_neg hg, if_neg hg]

 end

end Submission.Grassmann
