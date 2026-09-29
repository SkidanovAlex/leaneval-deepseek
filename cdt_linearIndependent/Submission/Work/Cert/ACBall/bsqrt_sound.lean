import Mathlib
import Submission.Work.Cert.ACBall.Basic
import Submission.Work.Cert.ACBall.bsqrt_defs

/-!
# Soundness of the principal-square-root ball `bsqrt`

`Bl = ⟨x, y, r⟩` denotes the closed disc of centre `c = cx x y = (x + y i)/S` and radius `r/S`
(`S = 2^40·10^8`, `BallMem a w ↔ ‖w − c‖ ≤ r/S`).  Given a witness `s = cx sr si = (sr + si i)/S`
with `sr > 0`, `bsqrt a sr si` is the disc of centre `s` and radius
`R/S`, `R = ⌈(r + E)·S/sr⌉ + 1`, where `E = ⌊(|sr²−si²−a.x·S| + |2·sr·si−a.y·S|)/S⌋ + 1` is the exact
integer residual controlling `|c − s²|`.

The proof is the standard estimate.  Write `w = u^(1/2)` for the **principal** square root.  Then

* `(w − s)(w + s) = u − s²`,  and
* `‖w + s‖ ≥ Re(w + s) = Re w + Re s ≥ Re s = sr/S`,  because `Re w ≥ 0` on the principal branch,

whence `‖w − s‖ ≤ ‖u − s²‖ / (sr/S)`.  The numerator is bounded by the triangle inequality:
`‖u − s²‖ ≤ ‖u − c‖ + ‖c − s²‖ ≤ r/S + E/S`, using the exact complex identity
`c − s² = cx (a.x·S − (sr²−si²)) (a.y·S − 2·sr·si) / S` together with `norm_cx_le_abs` (the centre of
a ball dominates the ball `Bl`).  Finally `(r + E)/sr ≤ R/S` because `dvu` rounds up.

Everything below is proved from Mathlib and `ACBall.Basic` only; no certificate data is used.
-/

namespace Work.Cert.ACBall

open Work.Cert Complex

/-! ## Extracting the side condition, and the scale cast -/

/-- The side condition `bsqrtOK` unpacks to `sr > 0` and a nonnegative radius. -/
lemma of_bsqrtOK {a : Bl} {sr : ℤ} (h : bsqrtOK a sr = true) : 0 < sr ∧ 0 ≤ a.r := by
  simpa only [bsqrtOK, Bool.and_eq_true, decide_eq_true_eq] using h

lemma S_cast_ne_zero : (S : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt S_pos)

/-! ## The exact residual identity -/

/-- The exact algebraic identity behind `bsqrtE`: with `Z1 = a.x·S − (sr²−si²)` and
`Z2 = a.y·S − 2·sr·si` one has `cx a.x a.y − (cx sr si)² = cx Z1 Z2 / S`. -/
lemma cx_sub_sq_factor (a : Bl) (sr si : ℤ) :
    cx a.x a.y - (cx sr si) ^ 2
      = cx (a.x * S - (sr * sr - si * si)) (a.y * S - 2 * sr * si) / (S : ℂ) := by
  have hSne : (S : ℂ) ≠ 0 := S_cast_ne_zero
  simp only [cx]
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-! ## The residual bound `S·|c − s²| ≤ E` -/

/-- The integer residual `E = bsqrtE a sr si` dominates `S·|cx a.x a.y − (cx sr si)²|`. -/
lemma bsqrt_centerResidual (a : Bl) (sr si : ℤ) :
    ‖cx a.x a.y - (cx sr si) ^ 2‖ ≤ ((bsqrtE a sr si : ℤ) : ℝ) / (S : ℝ) := by
  have hSpos : (0 : ℝ) < (S : ℝ) := S_posR
  set Z1 : ℤ := a.x * S - (sr * sr - si * si) with hZ1
  set Z2 : ℤ := a.y * S - 2 * sr * si with hZ2
  have hid : cx a.x a.y - (cx sr si) ^ 2 = cx Z1 Z2 / (S : ℂ) := by
    rw [hZ1, hZ2]
    exact cx_sub_sq_factor a sr si
  have e1 : ((iabs (sr * sr - si * si - a.x * S) : ℤ) : ℝ) = |((Z1 : ℤ) : ℝ)| := by
    have hneg : ((a.x * S - (sr * sr - si * si) : ℤ) : ℝ)
        = -((sr * sr - si * si - a.x * S : ℤ) : ℝ) := by push_cast; ring
    rw [iabs_abs, hZ1, hneg, abs_neg]
  have e2 : ((iabs (2 * sr * si - a.y * S) : ℤ) : ℝ) = |((Z2 : ℤ) : ℝ)| := by
    have hneg : ((a.y * S - 2 * sr * si : ℤ) : ℝ)
        = -((2 * sr * si - a.y * S : ℤ) : ℝ) := by push_cast; ring
    rw [iabs_abs, hZ2, hneg, abs_neg]
  have hN : ((iabs (sr * sr - si * si - a.x * S) + iabs (2 * sr * si - a.y * S) : ℤ) : ℝ)
      = |((Z1 : ℤ) : ℝ)| + |((Z2 : ℤ) : ℝ)| := by
    push_cast
    rw [e1, e2]
  have hb : ‖cx Z1 Z2‖
      ≤ ((iabs (sr * sr - si * si - a.x * S) + iabs (2 * sr * si - a.y * S) : ℤ) : ℝ)
        / (S : ℝ) := by
    rw [hN]
    exact norm_cx_le_abs Z1 Z2
  have hE : ((iabs (sr * sr - si * si - a.x * S) + iabs (2 * sr * si - a.y * S) : ℤ) : ℝ)
        / (S : ℝ) ≤ ((bsqrtE a sr si : ℤ) : ℝ) := by
    have hf : ((iabs (sr * sr - si * si - a.x * S) + iabs (2 * sr * si - a.y * S) : ℤ) : ℝ)
          / (S : ℝ) - 1
        < ((fdiv (iabs (sr * sr - si * si - a.x * S) + iabs (2 * sr * si - a.y * S)) S : ℤ) : ℝ) :=
      fdiv_gt S_pos
    rw [bsqrtE]
    push_cast at hf ⊢
    linarith
  rw [hid, norm_div, Complex.norm_intCast, abs_of_nonneg (by exact_mod_cast S_pos.le)]
  calc ‖cx Z1 Z2‖ / (S : ℝ)
      ≤ (((iabs (sr * sr - si * si - a.x * S) + iabs (2 * sr * si - a.y * S) : ℤ) : ℝ)
          / (S : ℝ)) / (S : ℝ) :=
        div_le_div_of_nonneg_right hb hSpos.le
    _ ≤ ((bsqrtE a sr si : ℤ) : ℝ) / (S : ℝ) := div_le_div_of_nonneg_right hE hSpos.le

/-! ## The `(w − s)(w + s) = u − s²` estimate -/

/-- For a complex number `s` in the open right half-plane, the principal square root `w = z^(1/2)`
satisfies `‖w − s‖ ≤ ‖z − s²‖ / Re s`. -/
lemma cpow_sub_sq_norm_le {z s : ℂ} (hs : 0 < s.re) :
    ‖z ^ (1 / 2 : ℂ) - s‖ ≤ ‖z - s ^ 2‖ / s.re := by
  have hsq : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
    rw [one_div]
    exact Complex.cpow_nat_inv_pow _ (by norm_num)
  have hre : (0 : ℝ) ≤ (z ^ (1 / 2 : ℂ)).re := by
    rw [show (1 / 2 : ℂ) = 2⁻¹ by norm_num, Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hprod : (z ^ (1 / 2 : ℂ) - s) * (z ^ (1 / 2 : ℂ) + s) = z - s ^ 2 := by
    have h : (z ^ (1 / 2 : ℂ) - s) * (z ^ (1 / 2 : ℂ) + s)
        = (z ^ (1 / 2 : ℂ)) ^ 2 - s ^ 2 := by ring
    rw [h, hsq]
  have hge : s.re ≤ ‖z ^ (1 / 2 : ℂ) + s‖ := by
    have h1 : (z ^ (1 / 2 : ℂ) + s).re = (z ^ (1 / 2 : ℂ)).re + s.re := Complex.add_re _ _
    calc s.re ≤ (z ^ (1 / 2 : ℂ) + s).re := by rw [h1]; linarith
      _ ≤ |(z ^ (1 / 2 : ℂ) + s).re| := le_abs_self _
      _ ≤ ‖z ^ (1 / 2 : ℂ) + s‖ := Complex.abs_re_le_norm _
  have hmul : ‖z ^ (1 / 2 : ℂ) - s‖ * ‖z ^ (1 / 2 : ℂ) + s‖ = ‖z - s ^ 2‖ := by
    rw [← norm_mul, hprod]
  rw [le_div_iff₀ hs]
  calc ‖z ^ (1 / 2 : ℂ) - s‖ * s.re
      ≤ ‖z ^ (1 / 2 : ℂ) - s‖ * ‖z ^ (1 / 2 : ℂ) + s‖ :=
        mul_le_mul_of_nonneg_left hge (norm_nonneg _)
    _ = ‖z - s ^ 2‖ := hmul

/-! ## The rounding-up step -/

/-- `((r+E)/S)/(sr/S) ≤ R/S` where `R = ⌈(r+E)·S/sr⌉ + 1` and `0 < sr`. -/
lemma bsqrt_dvu_le (r E sr : ℤ) (hsr : 0 < sr) :
    (((r + E : ℤ) : ℝ) / (S : ℝ)) / ((sr : ℝ) / (S : ℝ))
      ≤ (((dvu (r + E) sr + 1 : ℤ)) : ℝ) / (S : ℝ) := by
  have hSpos : (0 : ℝ) < (S : ℝ) := S_posR
  have hsrR : (0 : ℝ) < (sr : ℝ) := by exact_mod_cast hsr
  have hSne : (S : ℝ) ≠ 0 := ne_of_gt hSpos
  have hsrne : (sr : ℝ) ≠ 0 := ne_of_gt hsrR
  have h1 : ((r + E : ℤ) : ℝ) * (S : ℝ) / (sr : ℝ) ≤ ((dvu (r + E) sr : ℤ) : ℝ) :=
    dvu_ge (a := r + E) (b := sr) hsr
  rw [div_le_iff₀ hsrR] at h1
  have h2 : ((dvu (r + E) sr : ℤ) : ℝ) + 1 ≤ (((dvu (r + E) sr + 1 : ℤ)) : ℝ) := by
    push_cast; linarith
  have h3 : (((dvu (r + E) sr : ℤ) : ℝ) + 1) * (sr : ℝ)
      ≤ (((dvu (r + E) sr + 1 : ℤ)) : ℝ) * (sr : ℝ) :=
    mul_le_mul_of_nonneg_right h2 hsrR.le
  have hkey : ((r + E : ℤ) : ℝ) * (S : ℝ) ≤ (((dvu (r + E) sr + 1 : ℤ)) : ℝ) * (sr : ℝ) := by
    linarith
  have hA : (((r + E : ℤ) : ℝ) / (S : ℝ)) / ((sr : ℝ) / (S : ℝ))
      = ((r + E : ℤ) : ℝ) / (sr : ℝ) := by
    field_simp
  rw [hA, div_le_div_iff₀ hsrR hSpos]
  exact hkey

/-! ## Assembly -/

/-- **Soundness of `bsqrt`.**  If `u` lies in the disc `a` and the witness `(sr, si)` is admissible
(`sr > 0`), then the principal square root `u^(1/2)` lies in the disc `bsqrt a sr si`. -/
theorem bsqrt_sound {a : Bl} {sr si : ℤ} {u : ℂ} (h : bsqrtOK a sr = true) (ha : BallMem a u) :
    BallMem (bsqrt a sr si) (u ^ (1 / 2 : ℂ)) := by
  have hsr : 0 < sr := (of_bsqrtOK h).1
  have hSpos : (0 : ℝ) < (S : ℝ) := S_posR
  have hsrR : (0 : ℝ) < (sr : ℝ) := by exact_mod_cast hsr
  have hcxre : (0 : ℝ) < (cx sr si).re := by
    rw [cx_re]
    exact div_pos hsrR hSpos
  have hcp := cpow_sub_sq_norm_le (z := u) (s := cx sr si) hcxre
  rw [cx_re] at hcp
  have ha' : ‖u - cx a.x a.y‖ ≤ (a.r : ℝ) / (S : ℝ) := ha
  have hcen := bsqrt_centerResidual a sr si
  have hres : ‖u - (cx sr si) ^ 2‖ ≤ ((a.r + bsqrtE a sr si : ℤ) : ℝ) / (S : ℝ) := by
    calc ‖u - (cx sr si) ^ 2‖
        = ‖(u - cx a.x a.y) + (cx a.x a.y - (cx sr si) ^ 2)‖ := by
          congr 1
          ring
      _ ≤ ‖u - cx a.x a.y‖ + ‖cx a.x a.y - (cx sr si) ^ 2‖ := norm_add_le _ _
      _ ≤ (a.r : ℝ) / (S : ℝ) + ((bsqrtE a sr si : ℤ) : ℝ) / (S : ℝ) := add_le_add ha' hcen
      _ = ((a.r + bsqrtE a sr si : ℤ) : ℝ) / (S : ℝ) := by push_cast; ring
  have hstep : ‖u ^ (1 / 2 : ℂ) - cx sr si‖
      ≤ (((a.r + bsqrtE a sr si : ℤ) : ℝ) / (S : ℝ)) / ((sr : ℝ) / (S : ℝ)) :=
    hcp.trans (div_le_div_of_nonneg_right hres (div_nonneg hsrR.le hSpos.le))
  have hfin := hstep.trans (bsqrt_dvu_le a.r (bsqrtE a sr si) sr hsr)
  rw [BallMem]
  show ‖u ^ (1 / 2 : ℂ) - cx sr si‖
      ≤ (((dvu (a.r + bsqrtE a sr si) sr + 1 : ℤ)) : ℝ) / (S : ℝ)
  exact hfin

end Work.Cert.ACBall
