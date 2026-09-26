import Mathlib
import Submission.Work.FreeProduct.Bridge
import Submission.Work.FreeProduct.Tools
import Submission.Work.FreeProduct.Canonical
import Submission.Work.FreeProduct.Decomp
import Submission.Work.FreeProduct.LengthFacts
import Submission.Work.FreeProduct.orbit_corollary

/-!
# Tools for `(T - 1) ℂ[FP] ∩ μ ℂ[FP] = 0`

CKMRV Proposition 3.1 for `ℐ_-`: no nonzero element of `(T - 1) ℂ[FP]` is a multiple of
`μ = 1 + y + y²`.

This file contains the injectivity of `T - 1` and the first-letter computations on which the
proof of the main claim (delegated separately) rests.
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

theorem coeff_of_mul (g δ : FP) (r : RR) :
    MonoidAlgebra.coeff ((MonoidAlgebra.of ℂ FP) g * r) δ =
      MonoidAlgebra.coeff r (g⁻¹ * δ) := by
  rw [show (MonoidAlgebra.of ℂ FP) g = MonoidAlgebra.single g (1 : ℂ) from rfl,
    MonoidAlgebra.coeff_single_mul_apply]
  simp

/-! ## First-letter lemmas -/

theorem toList_x_mul {z : FP} (h : NX z) :
    (Monoid.CoprodI.Word.equiv (x * z)).toList =
      ⟨false, Lx.2⟩ :: (Monoid.CoprodI.Word.equiv z).toList := by
  rw [equiv_mul]
  exact toList_smul_of_fstIdx_ne (i := false) Lx.2 _ Lx_ne_one h

theorem startsLx_x_mul {z : FP} (h : NX z) : StartsLx (x * z) := by
  rw [StartsLx, toList_x_mul h]; rfl

theorem startsLx_x_mul_of_startsLy2 {z : FP} (h : StartsLy2 z) : StartsLx (x * z) :=
  startsLx_x_mul (NX_of_startsLy2 h)

theorem toList_y2_mul_of_startsLx {z : FP} (h : StartsLx z) :
    (Monoid.CoprodI.Word.equiv (y2 * z)).toList =
      ⟨true, Ly2.2⟩ :: (Monoid.CoprodI.Word.equiv z).toList := by
  have hne : (Monoid.CoprodI.Word.equiv z).fstIdx ≠ some true := by
    rw [Monoid.CoprodI.Word.fstIdx, h]; simp
  rw [show y2 = Monoid.CoprodI.of (M := Cyc) (i := true) Ly2.2 from of_Ly2.symm, equiv_mul]
  exact toList_smul_of_fstIdx_ne (i := true) Ly2.2 _ Ly2_ne_one hne

theorem startsLy2_y2_mul {z : FP} (h : StartsLx z) : StartsLy2 (y2 * z) := by
  rw [StartsLy2, toList_y2_mul_of_startsLx h]; rfl

/-- `y² * x * γ` starts with `y²` when `γ` does not start with `x`. -/
theorem startsLy2_y2x {γ : FP} (h : NX γ) : StartsLy2 (y2 * x * γ) := by
  have h1 : y2 * x * γ = y2 * (x * γ) := mul_assoc y2 x γ
  rw [h1]; exact startsLy2_y2_mul (startsLx_x_mul h)

theorem NX_y2x {γ : FP} (h : NX γ) : NX (y2 * x * γ) := NX_of_startsLy2 (startsLy2_y2x h)

theorem toList_y_mul {γ : FP} (h : NX γ) :
    (Monoid.CoprodI.Word.equiv (y * x * γ)).toList =
      ⟨true, Ly.2⟩ :: (Monoid.CoprodI.Word.equiv (x * γ)).toList := by
  rw [show y * x * γ = y * (x * γ) from mul_assoc y x γ, equiv_mul]
  refine toList_smul_of_fstIdx_ne (i := true) Ly.2 _ Ly_ne_one ?_
  rw [Monoid.CoprodI.Word.fstIdx, toList_x_mul h]; simp

theorem NX_yx {γ : FP} (h : NX γ) : NX (y * x * γ) := by
  rw [NX, Monoid.CoprodI.Word.fstIdx, toList_y_mul h]; simp

end

end Work.FreeProduct
