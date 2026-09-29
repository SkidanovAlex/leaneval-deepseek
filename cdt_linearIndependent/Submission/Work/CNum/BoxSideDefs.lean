import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.NrmSpec

/-!
# `Work.CNum.BoxSideDefs` — the ball associated with a box

`toPB I` (in `Fx`) turns the rectangle `I` into a ball with centre `(b.x + i b.y)/SC` and radius
`b.e/SC`, where `b = toPB I`; `bpt b` is that centre as a complex number.

`BoxOK p` is the (mantissa level, decidable) bundle of side conditions needed to apply the series
bounds `SerUpSpec`/`SerDnSpec` at `toPB p`:

* `0 ≤ e ≤ 1024` (so the radius is below `10⁻⁶`),
* `|x|, |y| ≤ 2^34` (the `isqrt` range of `NrmSpec`),
* `(nrmUp x y + e) * 100 ≤ 79 * SC` (the ball stays inside the disc of radius `79/100`),
* `e < nrmDn x y` (the ball stays away from `0`).

The real-valued forms of these conditions are recorded below; the certificate that every grid box
satisfies them is `Work.CNum.BoxSide`.
-/

namespace Work.CNum

open Work.ANum

/-- The centre of the ball `toPB b`, as a complex number. -/
noncomputable def bpt (b : PB) : ℂ :=
  ((b.x : ℝ) + (b.y : ℝ) * Complex.I) / (SC : ℝ)

/-- Mantissa side conditions of the ball `toPB p`. -/
def BoxOK (p : Cpx) : Prop :=
  0 ≤ (toPB p).e ∧ (toPB p).e ≤ 1024 ∧ Int.natAbs (toPB p).x ≤ 2 ^ 34 ∧
    Int.natAbs (toPB p).y ≤ 2 ^ 34 ∧
    (nrmUp (toPB p).x (toPB p).y + (toPB p).e) * 100 ≤ 79 * SC ∧
    (toPB p).e < nrmDn (toPB p).x (toPB p).y

lemma BoxOK.e_nonneg {p : Cpx} (h : BoxOK p) : 0 ≤ (toPB p).e := h.1
lemma BoxOK.e_le {p : Cpx} (h : BoxOK p) : (toPB p).e ≤ 1024 := h.2.1
lemma BoxOK.natAbs_x {p : Cpx} (h : BoxOK p) : Int.natAbs (toPB p).x ≤ 2 ^ 34 := h.2.2.1
lemma BoxOK.natAbs_y {p : Cpx} (h : BoxOK p) : Int.natAbs (toPB p).y ≤ 2 ^ 34 := h.2.2.2.1
lemma BoxOK.sigma_le {p : Cpx} (h : BoxOK p) :
    (nrmUp (toPB p).x (toPB p).y + (toPB p).e) * 100 ≤ 79 * SC := h.2.2.2.2.1
lemma BoxOK.e_lt {p : Cpx} (h : BoxOK p) :
    (toPB p).e < nrmDn (toPB p).x (toPB p).y := h.2.2.2.2.2

lemma BoxOK.e_le_real {p : Cpx} (h : BoxOK p) : m2r (toPB p).e ≤ 1 / 10 ^ 6 := by
  have h1 := BoxOK.e_le h
  rw [m2r, div_le_div_iff₀ SC_posR (by norm_num : (0:ℝ) < 10 ^ 6)]
  have h2 : ((toPB p).e : ℝ) ≤ 1024 := by exact_mod_cast h1
  have h3 : (SC : ℝ) = 1073741824 := by norm_num [SC]
  rw [h3]; nlinarith

lemma BoxOK.sigma_le_real {p : Cpx} (h : BoxOK p) :
    m2r (nrmUp (toPB p).x (toPB p).y + (toPB p).e) ≤ 79 / 100 := by
  have h1 := BoxOK.sigma_le h
  rw [m2r, div_le_div_iff₀ SC_posR (by norm_num : (0:ℝ) < 100)]
  have h2 : ((nrmUp (toPB p).x (toPB p).y + (toPB p).e : ℤ) : ℝ) * 100 ≤ ((79 * SC : ℤ) : ℝ) := by
    exact_mod_cast h1
  have h3 : (SC : ℝ) = 1073741824 := by norm_num [SC]
  push_cast at h2 ⊢
  rw [h3] at h2 ⊢
  nlinarith

lemma BoxOK.e_lt_real {p : Cpx} (h : BoxOK p) :
    m2r (toPB p).e < m2r (nrmDn (toPB p).x (toPB p).y) := m2r_lt (BoxOK.e_lt h)

lemma BoxOK.e_nonneg_real {p : Cpx} (h : BoxOK p) : (0:ℝ) ≤ m2r (toPB p).e :=
  m2r_nonneg_NrmSpec (BoxOK.e_nonneg h)

end Work.CNum
