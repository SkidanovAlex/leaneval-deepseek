import Mathlib
import Submission.Work.FreeProduct.Bridge
import Submission.Work.FreeProduct.Tools

/-!
# Length facts for the prefixes appearing in the direct-sum arguments

For an element `γ` that is `1` or starts with a `ℤ/3`-letter (`NX γ`), left multiplication by any
of the prefixes `x`, `y x`, `y² x`, `x y x`, `x y² x` (all of which end in the letter `x`) is
cancellation free: the reduced word of the product is the concatenation.
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

theorem Lx_ne_one : Lx.2 ≠ 1 := by rw [Lx]; decide

theorem Ly_ne_one : Ly.2 ≠ 1 := by rw [Ly]; decide

theorem Ly2_ne_one : Ly2.2 ≠ 1 := by rw [Ly2]; decide

theorem elen_x_mul {γ : FP} (h : NX γ) : elen (x * γ) = elen γ + 1 := by
  have h' := elen_toProd_mul_of_fstIdx pX Lx (Monoid.CoprodI.Word.equiv γ) (by decide)
    (by decide) (rfl : pX.getLast? = some Lx) (by simpa [NX] using h)
  rw [toProd_pX, wlen_equiv] at h'
  have hl : pX.length = 1 := rfl
  simpa [hl, Nat.add_comm 1 (elen γ), prod_equiv] using h'

theorem elen_yx_mul {γ : FP} (h : NX γ) : elen (y * x * γ) = elen γ + 2 := by
  have h' := elen_toProd_mul_of_fstIdx pYX Lx (Monoid.CoprodI.Word.equiv γ) (by decide)
    (by decide) (rfl : pYX.getLast? = some Lx) (by simpa [NX] using h)
  rw [toProd_pYX, wlen_equiv] at h'
  have hl : pYX.length = 2 := rfl
  simpa [hl, Nat.add_comm 2 (elen γ), prod_equiv] using h'

theorem elen_y2x_mul {γ : FP} (h : NX γ) : elen (y2 * x * γ) = elen γ + 2 := by
  have h' := elen_toProd_mul_of_fstIdx pY2X Lx (Monoid.CoprodI.Word.equiv γ) (by decide)
    (by decide) (rfl : pY2X.getLast? = some Lx) (by simpa [NX] using h)
  rw [toProd_pY2X, wlen_equiv] at h'
  have hl : pY2X.length = 2 := rfl
  simpa [hl, Nat.add_comm 2 (elen γ), prod_equiv] using h'

theorem elen_xyx_mul {γ : FP} (h : NX γ) : elen (x * y * x * γ) = elen γ + 3 := by
  have h' := elen_toProd_mul_of_fstIdx pXYX Lx (Monoid.CoprodI.Word.equiv γ) (by decide)
    (by decide) (rfl : pXYX.getLast? = some Lx) (by simpa [NX] using h)
  rw [toProd_pXYX, wlen_equiv] at h'
  have hl : pXYX.length = 3 := rfl
  simpa [hl, Nat.add_comm 3 (elen γ), prod_equiv] using h'

theorem elen_xy2x_mul {γ : FP} (h : NX γ) : elen (x * y2 * x * γ) = elen γ + 3 := by
  have h' := elen_toProd_mul_of_fstIdx pXY2X Lx (Monoid.CoprodI.Word.equiv γ) (by decide)
    (by decide) (rfl : pXY2X.getLast? = some Lx) (by simpa [NX] using h)
  rw [toProd_pXY2X, wlen_equiv] at h'
  have hl : pXY2X.length = 3 := rfl
  simpa [hl, Nat.add_comm 3 (elen γ), prod_equiv] using h'

/-! ## The first-letter predicates for the orbit computation -/

/-- The reduced word starts with the letter `x`. -/
def StartsLx (z : FP) : Prop := (Monoid.CoprodI.Word.equiv z).toList.head? = some Lx

/-- The reduced word starts with the letter `y²`. -/
def StartsLy2 (z : FP) : Prop := (Monoid.CoprodI.Word.equiv z).toList.head? = some Ly2

theorem XF_of_startsLx {z : FP} (h : StartsLx z) : XF z := by
  rw [XF, Monoid.CoprodI.Word.fstIdx, h]; decide

theorem NX_of_startsLy2 {z : FP} (h : StartsLy2 z) : NX z := by
  rw [NX, Monoid.CoprodI.Word.fstIdx, h]; decide

theorem x_inv : x⁻¹ = x := inv_eq_of_mul_eq_one_right x_sq

theorem y_inv : y⁻¹ = y2 := by
  rw [y2]; exact inv_eq_of_mul_eq_one_right y_mul_y2

theorem Tinv_eq : T⁻¹ = y2 * x := by
  rw [T, mul_inv_rev, x_inv, y_inv]

/-- Prepending `x` to a word starting with `y²`. -/
theorem toList_x_mul_of_startsLy2 {z : FP} (h : StartsLy2 z) :
    (Monoid.CoprodI.Word.equiv (x * z)).toList =
      ⟨false, Lx.2⟩ :: (Monoid.CoprodI.Word.equiv z).toList := by
  rw [equiv_mul]
  exact toList_smul_of_fstIdx_ne (i := false) Lx.2 _ Lx_ne_one (NX_of_startsLy2 h)

theorem startsLy_mul {z : FP} (h : StartsLx z) :
    (Monoid.CoprodI.Word.equiv (y * z)).toList =
      ⟨true, Ly.2⟩ :: (Monoid.CoprodI.Word.equiv z).toList := by
  rw [equiv_mul]
  refine toList_smul_of_fstIdx_ne (i := true) Ly.2 _ Ly_ne_one ?_
  rw [Monoid.CoprodI.Word.fstIdx, h]; simp

/-- Left multiplication by `T = x * y` on an element whose word starts with `x`. -/
theorem T_mul_startsLx {z : FP} (h : StartsLx z) : StartsLx (T * z) := by
  have hy := startsLy_mul h
  have h1 : (Monoid.CoprodI.Word.equiv (y * z)).toList.head? = some ⟨true, Ly.2⟩ := by
    rw [hy]; rfl
  have hne : (Monoid.CoprodI.Word.equiv (y * z)).fstIdx ≠ some false := by
    rw [Monoid.CoprodI.Word.fstIdx, h1]; simp
  have h2 : (Monoid.CoprodI.Word.equiv (x * (y * z))).toList =
      ⟨false, Lx.2⟩ :: (Monoid.CoprodI.Word.equiv (y * z)).toList := by
    rw [equiv_mul]
    exact toList_smul_of_fstIdx_ne (i := false) Lx.2 _ Lx_ne_one hne
  have : T * z = x * (y * z) := by rw [T, mul_assoc]
  rw [this, StartsLx, h2]
  rfl

theorem T_mul_elen {z : FP} (h : StartsLx z) : elen (T * z) = elen z + 2 := by
  have hy := startsLy_mul h
  have h1 : (Monoid.CoprodI.Word.equiv (y * z)).fstIdx ≠ some false := by
    rw [Monoid.CoprodI.Word.fstIdx, hy]; simp
  have h2 : elen (y * z) = elen z + 1 := by
    simp only [elen, wlen, hy, List.length_cons, wlen_equiv]
  have h3 : elen (x * (y * z)) = elen (y * z) + 1 :=
    elen_x_mul (by simp [NX, Monoid.CoprodI.Word.fstIdx, hy])
  have : T * z = x * (y * z) := by rw [T, mul_assoc]
  rw [this, h3, h2]

/-- Left multiplication by `T⁻¹ = y² * x` on an element whose word starts with `y²`. -/
theorem Tinv_mul_startsLy2 {z : FP} (h : StartsLy2 z) : StartsLy2 (T⁻¹ * z) := by
  have hx : (Monoid.CoprodI.Word.equiv (x * z)).toList =
      ⟨false, Lx.2⟩ :: (Monoid.CoprodI.Word.equiv z).toList :=
    toList_x_mul_of_startsLy2 h
  have hne : (Monoid.CoprodI.Word.equiv (x * z)).fstIdx ≠ some true := by
    rw [Monoid.CoprodI.Word.fstIdx, hx]; simp
  have h2 : (Monoid.CoprodI.Word.equiv (y2 * (x * z))).toList =
      ⟨true, Ly2.2⟩ :: (Monoid.CoprodI.Word.equiv (x * z)).toList := by
    rw [show y2 = Monoid.CoprodI.of (M := Cyc) (i := true) Ly2.2 from of_Ly2.symm, equiv_mul]
    exact toList_smul_of_fstIdx_ne (i := true) Ly2.2 _ Ly2_ne_one hne
  have : T⁻¹ * z = y2 * (x * z) := by rw [Tinv_eq, mul_assoc]
  rw [this, StartsLy2, h2]
  rfl

theorem Tinv_mul_elen {z : FP} (h : StartsLy2 z) : elen (T⁻¹ * z) = elen z + 2 := by
  have hx : (Monoid.CoprodI.Word.equiv (x * z)).toList =
      ⟨false, Lx.2⟩ :: (Monoid.CoprodI.Word.equiv z).toList :=
    toList_x_mul_of_startsLy2 h
  have h1 : (Monoid.CoprodI.Word.equiv (x * z)).fstIdx ≠ some true := by
    rw [Monoid.CoprodI.Word.fstIdx, hx]; simp
  have h2 : elen (x * z) = elen z + 1 := by
    simp only [elen, wlen, hx, List.length_cons, wlen_equiv]
  have h3 : elen (y2 * (x * z)) = elen (x * z) + 1 := by
    have h' := elen_y2x_mul (γ := z) (NX_of_startsLy2 h)
    rw [mul_assoc] at h'
    rw [h', h2]
  have : T⁻¹ * z = y2 * (x * z) := by rw [Tinv_eq, mul_assoc]
  rw [this, h3, h2]

end

end Work.FreeProduct
