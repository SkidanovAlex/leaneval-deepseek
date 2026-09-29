import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Main.defs
import Submission.Work.Main.bridge
import Submission.Work.Main.chunks.hcoeff_lt
import Submission.Work.Main.chunks.sum_cyclic_eq_hcoeff
import Submission.Work.Main.conv.hcoeff_eq_convC
import Submission.Work.Main.recover.recov_eq
import Submission.Work.Main.recover.final_error

/-! The final mathematical identification of the main step. -/

set_option autoImplicit false

namespace Work.Main

open HvdH

/-- `take` of a list is the map of `getD` over the index range. -/
theorem take_eq_range_getD {α : Type} [Inhabited α] :
    ∀ (ys : List α) (k : ℕ), k ≤ ys.length →
      ys.take k = (List.range k).map (fun m => ys.getD m default) := by
  intro ys
  induction ys with
  | nil =>
    intro k hk
    obtain rfl : k = 0 := Nat.le_zero.mp (by simpa using hk)
    simp
  | cons a t ih =>
    intro k hk
    cases k with
    | zero => simp
    | succ k =>
      rw [List.take_succ_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        List.getD_cons_zero, ih k (by simpa using hk)]
      rfl

/-- the recovered coefficients equal the convolution coefficients -/
theorem recov_eq_hcoeff {sp : SP} {zs : List (ℤ × ℤ)} {F G : List (ℤ × ℤ)}
    (hOK : ParamOK (max sp.x.size sp.y.size) sp.ts sp.ss)
    (hSp : sp.S = sp.ss.prod)
    (hFl : ∀ m < sp.ss.prod,
      F.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.x sp.b sp.N' sp.S (sp.p - sp.b) m)
    (hGl : ∀ m < sp.ss.prod,
      G.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.y sp.b sp.N' sp.S (sp.p - sp.b) m)
    (hb : sp.b = HvdH.bpar (max sp.x.size sp.y.size))
    (hγ : 2 * HvdH.D * sp.α ^ 2 + 13 < sp.b) (hbp : sp.b ≤ sp.p) (h6 : 6 * sp.b ≤ sp.p)
    (hb12 : 12 ≤ sp.b) (hTb : sp.ts.prod * sp.b ≤ 10 * max sp.x.size sp.y.size)
    (hnb : max sp.x.size sp.y.size ≤ 2 ^ sp.b)
    (hApprox : HvdH.Approx sp.p zs
      (HvdH.convC sp.ss (HvdH.fxVec sp.p sp.ss.prod F) (HvdH.fxVec sp.p sp.ss.prod G))
      ((2 ^ (2 * HvdH.D * sp.α ^ 2 + 8) * sp.ts.prod ^ 2 * Nat.log 2 sp.ts.prod : ℕ) : ℝ))
    (hSlt : sp.S ≤ sp.ts.prod) (hN'2 : 2 * sp.N' ≤ sp.S + 1) {q : ℕ} (hq : q < sp.S)
    (hDFT : DFTMathProp) :
    ‖((hcoeff sp.x sp.y sp.b sp.N' (Pinv sp.ss q) : ℤ) : ℂ) -
      (2 : ℂ) ^ (2 * sp.b) * (sp.S : ℂ) * HvdH.fxC sp.p (zs.getD q (0,0))‖ < 1 / 4 := by
  obtain ⟨-, -, -, -, -, -, hcop, hodd⟩ := hOK
  have hpos : ∀ s ∈ sp.ss, 0 < s := fun s hs => (hodd s hs).pos
  have hprod : sp.ss.prod = sp.S := hSp.symm
  have hQQ : q < sp.ss.prod := by rw [hprod]; exact hq
  have hSN : 2 * sp.N' - 1 ≤ sp.ss.prod := by rw [hprod]; omega
  have hconv := conv.hcoeff_eq_convC (ss := sp.ss) (x := sp.x) (y := sp.y) (b := sp.b)
    (N := sp.N') hDFT hcop hpos hSN hQQ
  have hflatF : HvdH.fxVec sp.p sp.ss.prod F = flatv sp.b sp.N' sp.ss sp.x :=
    fxVec_eq_flatv hcop hpos hbp (fun m hm => hFl m hm)
  have hflatG : HvdH.fxVec sp.p sp.ss.prod G = flatv sp.b sp.N' sp.ss sp.y :=
    fxVec_eq_flatv hcop hpos hbp (fun m hm => hGl m hm)
  rw [hflatF, hflatG] at hApprox
  have happ := hApprox.2 ⟨q, hQQ⟩
  have hcast : ((hcoeff sp.x sp.y sp.b sp.N' (Pinv sp.ss q) : ℤ) : ℂ) =
      (hcoeff sp.x sp.y sp.b sp.N' (Pinv sp.ss q) : ℂ) := by push_cast; ring
  rw [hcast, hconv]
  have h1 : (2 : ℂ) ^ (2 * sp.b) * (sp.ss.prod : ℂ) *
      HvdH.convC sp.ss (flatv sp.b sp.N' sp.ss sp.x) (flatv sp.b sp.N' sp.ss sp.y) ⟨q, hQQ⟩ -
      (2 : ℂ) ^ (2 * sp.b) * (sp.S : ℂ) * HvdH.fxC sp.p (zs.getD q (0,0)) =
      ((2 : ℂ) ^ (2 * sp.b) * (sp.S : ℂ)) *
        (HvdH.convC sp.ss (flatv sp.b sp.N' sp.ss sp.x) (flatv sp.b sp.N' sp.ss sp.y) ⟨q, hQQ⟩ -
          HvdH.fxC sp.p (zs.getD q (0,0))) := by
    rw [← hprod]; ring
  rw [h1, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_natCast]
  have hlt : ‖HvdH.convC sp.ss (flatv sp.b sp.N' sp.ss sp.x) (flatv sp.b sp.N' sp.ss sp.y) ⟨q, hQQ⟩ -
      HvdH.fxC sp.p (zs.getD q (0,0))‖ * (2:ℝ) ^ sp.p <
      ((2 ^ (2 * HvdH.D * sp.α ^ 2 + 8) * sp.ts.prod ^ 2 * Nat.log 2 sp.ts.prod : ℕ) : ℝ) := by
    rw [norm_sub_rev, mul_comm]; exact happ
  have hfinal := recover.final_error (S := sp.S) (T := sp.ts.prod) (n := max sp.x.size sp.y.size)
    (b := sp.b) (p := sp.p) (γ := 2 * HvdH.D * sp.α ^ 2)
    hSlt (by omega) hnb h6 (by omega) hb12
  calc (2 : ℝ) ^ (2 * sp.b) * (sp.S : ℝ) *
        ‖HvdH.convC sp.ss (flatv sp.b sp.N' sp.ss sp.x) (flatv sp.b sp.N' sp.ss sp.y) ⟨q, hQQ⟩ -
          HvdH.fxC sp.p (zs.getD q (0,0))‖
      = (2 : ℝ) ^ (2 * sp.b) * (sp.S : ℝ) *
        (‖HvdH.convC sp.ss (flatv sp.b sp.N' sp.ss sp.x) (flatv sp.b sp.N' sp.ss sp.y) ⟨q, hQQ⟩ -
          HvdH.fxC sp.p (zs.getD q (0,0))‖ * (2:ℝ) ^ sp.p) / (2:ℝ) ^ sp.p := by
        field_simp
    _ ≤ (2 : ℝ) ^ (2 * sp.b) * (sp.S : ℝ) *
        ((2 ^ (2 * HvdH.D * sp.α ^ 2 + 8) * sp.ts.prod ^ 2 * Nat.log 2 sp.ts.prod : ℕ) : ℝ) /
          (2:ℝ) ^ sp.p := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hlt.le (by positivity)
    _ = (2 : ℝ) ^ (2 * sp.b) * (sp.S : ℝ) * ((2 : ℝ) ^ sp.p)⁻¹ *
        ((2 : ℝ) ^ (2 * HvdH.D * sp.α ^ 2 + 8) * (sp.ts.prod : ℝ) ^ 2 *
          (Nat.log 2 sp.ts.prod : ℝ)) := by
        rw [div_eq_mul_inv]; push_cast; ring
    _ < 1 / 4 := hfinal

end Work.Main
