/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# The quarter-box 3-jet enclosure of `F'''` (the sharper `R = 4` Taylor constant)

`EE.lean` bounds `‖F'''‖` on `Xz2 = Xz ⊕ [-ρ₂,ρ₂]²` by one `decide`-checked evaluation of the
rounded 3-jet `jet3IterR 400 (pbox x₀ Xt) Xz2 5`.  The interval arithmetic of that single
evaluation is *grossly* inflated: it gives `Kee = 5056372`, whereas the sharp supremum is
`≈ 1.6·10⁶` (`M = sup |E|/|u|³ ≈ 2.7·10⁵`), a factor `3.16`.  The inflation is pure interval
dependency, and it shrinks with the box: splitting `Xz2` into the four quarters at the *centre* of
`Xz` (which is the midpoint of `Xz2`) gives `max = 3392734` — already enough for the ray area's
`R = 4` (see `EEConst4.lean`).

This file does that split.  Main results:

* `Qpp`, `Qpm`, `Qmp`, `Qmm` — the four quarter boxes of `Xz2`;
* `mem_Qpp` … `mem_Qmm` — `‖w‖ ≤ ρ₂` and the sign of `w.re`, `w.im` place `z₁ + w` in the
  corresponding quarter;
* `ee_d3_checkpp` … `ee_d3_checkmm` — the four `decide`-checked bounds
  `(d3.normSq).hi ≤ Kee4²`;
* `ee_third_bound4` — `‖F'''(z₁+w)‖ ≤ Kee4` for `‖w‖ ≤ ρ₂`;
* `ee_taylor4` — `‖F(z₁+u) − z₁ − u − A u²‖ ≤ Mee4‖u‖³` for `‖u‖ ≤ ρ₂`.
-/
import Mathlib
import Submission.Work.SeedCertNum.EE
import Submission.Work.SeedCertNum.EEConst4
import Submission.Work.SeedCertNum.norm_sq_le_jet3box

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

set_option maxRecDepth 8000

/-! ## The four quarters of `Xz2` -/

/-- The quarter `Re ≥ z₁.re`, `Im ≥ z₁.im` of `Xz2`. -/
def Qpp : CBox :=
  ⟨krawData.Xz.rlo, Dya.add krawData.Xz.rhi rho2,
   krawData.Xz.ilo, Dya.add krawData.Xz.ihi rho2⟩

/-- The quarter `Re ≥ z₁.re`, `Im ≤ z₁.im` of `Xz2`. -/
def Qpm : CBox :=
  ⟨krawData.Xz.rlo, Dya.add krawData.Xz.rhi rho2,
   Dya.sub krawData.Xz.ilo rho2, krawData.Xz.ihi⟩

/-- The quarter `Re ≤ z₁.re`, `Im ≥ z₁.im` of `Xz2`. -/
def Qmp : CBox :=
  ⟨Dya.sub krawData.Xz.rlo rho2, krawData.Xz.rhi,
   krawData.Xz.ilo, Dya.add krawData.Xz.ihi rho2⟩

/-- The quarter `Re ≤ z₁.re`, `Im ≤ z₁.im` of `Xz2`. -/
def Qmm : CBox :=
  ⟨Dya.sub krawData.Xz.rlo rho2, krawData.Xz.rhi,
   Dya.sub krawData.Xz.ilo rho2, krawData.Xz.ihi⟩

/-- The 3-jet of `Tsq^5` over the first quarter, and its `d3` box. -/
def d3pp : CBox := (jet3IterR 400 (pbox krawData.x₀ krawData.Xt) Qpp 5).d3
def d3pm : CBox := (jet3IterR 400 (pbox krawData.x₀ krawData.Xt) Qpm 5).d3
def d3mp : CBox := (jet3IterR 400 (pbox krawData.x₀ krawData.Xt) Qmp 5).d3
def d3mm : CBox := (jet3IterR 400 (pbox krawData.x₀ krawData.Xt) Qmm 5).d3

/-! ## The four `decide` checks -/

theorem ee_d3_checkpp : Dya.le d3pp.normSq.hi (Dya.mul Kee4 Kee4) = true := by decide
theorem ee_d3_checkpm : Dya.le d3pm.normSq.hi (Dya.mul Kee4 Kee4) = true := by decide
theorem ee_d3_checkmp : Dya.le d3mp.normSq.hi (Dya.mul Kee4 Kee4) = true := by decide
theorem ee_d3_checkmm : Dya.le d3mm.normSq.hi (Dya.mul Kee4 Kee4) = true := by decide

/-! ## Membership of the quarters -/

theorem mem_Qpp {w : ℂ} (hw : ‖w‖ ≤ rho2.toReal) (hre : 0 ≤ w.re) (him : 0 ≤ w.im) :
    z1 + w ∈ Qpp.toSet := by
  obtain ⟨h1, h2, h3, h4⟩ := z1_mem
  have hrho : 0 ≤ rho2.toReal := by rw [rho2R]; positivity
  have hwr : |w.re| ≤ rho2.toReal := le_trans (Complex.abs_re_le_norm w) hw
  have hwi : |w.im| ≤ rho2.toReal := le_trans (Complex.abs_im_le_norm w) hw
  rw [CBox.mem_toSet]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Qpp, Complex.add_re, Complex.add_im, Dya.toReal_sub, Dya.toReal_add]
  · linarith
  · linarith [(abs_le.mp hwr).2]
  · linarith
  · linarith [(abs_le.mp hwi).2]

theorem mem_Qpm {w : ℂ} (hw : ‖w‖ ≤ rho2.toReal) (hre : 0 ≤ w.re) (him : w.im ≤ 0) :
    z1 + w ∈ Qpm.toSet := by
  obtain ⟨h1, h2, h3, h4⟩ := z1_mem
  have hrho : 0 ≤ rho2.toReal := by rw [rho2R]; positivity
  have hwr : |w.re| ≤ rho2.toReal := le_trans (Complex.abs_re_le_norm w) hw
  have hwi : |w.im| ≤ rho2.toReal := le_trans (Complex.abs_im_le_norm w) hw
  rw [CBox.mem_toSet]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Qpm, Complex.add_re, Complex.add_im, Dya.toReal_sub, Dya.toReal_add]
  · linarith
  · linarith [(abs_le.mp hwr).2]
  · linarith [(abs_le.mp hwi).1]
  · linarith

theorem mem_Qmp {w : ℂ} (hw : ‖w‖ ≤ rho2.toReal) (hre : w.re ≤ 0) (him : 0 ≤ w.im) :
    z1 + w ∈ Qmp.toSet := by
  obtain ⟨h1, h2, h3, h4⟩ := z1_mem
  have hrho : 0 ≤ rho2.toReal := by rw [rho2R]; positivity
  have hwr : |w.re| ≤ rho2.toReal := le_trans (Complex.abs_re_le_norm w) hw
  have hwi : |w.im| ≤ rho2.toReal := le_trans (Complex.abs_im_le_norm w) hw
  rw [CBox.mem_toSet]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Qmp, Complex.add_re, Complex.add_im, Dya.toReal_sub, Dya.toReal_add]
  · linarith [(abs_le.mp hwr).1]
  · linarith
  · linarith
  · linarith [(abs_le.mp hwi).2]

theorem mem_Qmm {w : ℂ} (hw : ‖w‖ ≤ rho2.toReal) (hre : w.re ≤ 0) (him : w.im ≤ 0) :
    z1 + w ∈ Qmm.toSet := by
  obtain ⟨h1, h2, h3, h4⟩ := z1_mem
  have hrho : 0 ≤ rho2.toReal := by rw [rho2R]; positivity
  have hwr : |w.re| ≤ rho2.toReal := le_trans (Complex.abs_re_le_norm w) hw
  have hwi : |w.im| ≤ rho2.toReal := le_trans (Complex.abs_im_le_norm w) hw
  rw [CBox.mem_toSet]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Qmm, Complex.add_re, Complex.add_im, Dya.toReal_sub, Dya.toReal_add]
  · linarith [(abs_le.mp hwr).1]
  · linarith
  · linarith [(abs_le.mp hwi).1]
  · linarith

/-! ## The third derivative on a certified box -/

/-- **The `decide`-checked enclosure, decoded.**  If `z₁ + w` lies in a box `Q` whose `d3` enclosure
is `decide`-certified against `Kee4²`, then `‖F'''(z₁+w)‖ ≤ Kee4`. -/
theorem thirdBoundQ (Q : CBox) {w : ℂ} (hQ : z1 + w ∈ Q.toSet)
    (hchk : Dya.le (jet3IterR 400 (pbox krawData.x₀ krawData.Xt) Q 5).d3.normSq.hi
      (Dya.mul Kee4 Kee4) = true) :
    ‖iteratedDeriv 3 (Work.FSeed.F cb) (z1 + w)‖ ≤ Kee4.toReal := by
  have hc : ((krawData.x₀.toReal : ℝ) + krawU.2.2 * Complex.I)
      ∈ (pbox krawData.x₀ krawData.Xt).toSet := mem_pbox krawU_t_mem
  have hmem := (Work.SeedCertNum.Nsjb.jet3IterR_sound hc 400 5 hQ).2.2.2
  have h1 : ‖iteratedDeriv 3 ((Work.Landing.Tsq ((krawData.x₀.toReal : ℂ)
        + ↑krawU.2.2 * Complex.I))^[5]) (z1 + w)‖ ^ 2
      ≤ ((jet3IterR 400 (pbox krawData.x₀ krawData.Xt) Q 5).d3.normSq).hi.toReal :=
    (CBox.mem_normSq hmem).2
  have hd3 : iteratedDeriv 3 ((Work.Landing.Tsq ((krawData.x₀.toReal : ℂ)
      + ↑krawU.2.2 * Complex.I))^[5]) (z1 + w) =
      iteratedDeriv 3 (Work.FSeed.F cb) (z1 + w) := rfl
  rw [hd3] at h1
  have hK : (((jet3IterR 400 (pbox krawData.x₀ krawData.Xt) Q 5).d3.normSq).hi.toReal)
      ≤ (Kee4.toReal) ^ 2 := by
    have := (Dya.toReal_le_iff _ _).mp hchk
    simpa [Kee4, Dya.toReal_mul, pow_two] using this
  have h2 : ‖iteratedDeriv 3 (Work.FSeed.F cb) (z1 + w)‖ ^ 2 ≤ Kee4.toReal ^ 2 :=
    le_trans h1 hK
  have h3 : |‖iteratedDeriv 3 (Work.FSeed.F cb) (z1 + w)‖| ≤ |Kee4.toReal| := sq_le_sq.mp h2
  rwa [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (by rw [Kee4_toReal]; norm_num)] at h3

/-- **`‖F'''‖ ≤ Kee4` on `Xz2`**: the union of the four quarter bounds. -/
theorem ee_third_bound4 {w : ℂ} (hw : ‖w‖ ≤ rho2.toReal) :
    ‖iteratedDeriv 3 (Work.FSeed.F cb) (z1 + w)‖ ≤ Kee4.toReal := by
  by_cases hre : 0 ≤ w.re
  · by_cases him : 0 ≤ w.im
    · exact thirdBoundQ Qpp (mem_Qpp hw hre him) ee_d3_checkpp
    · exact thirdBoundQ Qpm (mem_Qpm hw hre (not_le.mp him).le) ee_d3_checkpm
  · by_cases him : 0 ≤ w.im
    · exact thirdBoundQ Qmp (mem_Qmp hw (not_le.mp hre).le him) ee_d3_checkmp
    · exact thirdBoundQ Qmm (mem_Qmm hw (not_le.mp hre).le (not_le.mp him).le) ee_d3_checkmm

/-- **The sharper Taylor model**: `‖F(z₁+u) − z₁ − u − A u²‖ ≤ Mee4‖u‖³` for `‖u‖ ≤ ρ₂`. -/
theorem ee_taylor4 {u : ℂ} (hu : ‖u‖ ≤ rho2.toReal) :
    ‖Work.FSeed.F cb (z1 + u) - z1 - u - Aquad * u ^ 2‖ ≤ Mee4 * ‖u‖ ^ 3 := by
  have h := Work.SeedCertNum.norm_taylor2_remainder (F := Work.FSeed.F cb) (z₀ := z1)
    (A := Aquad) (K := Kee4.toReal) (ρ := rho2.toReal) F_diff (Kee4_toReal ▸ by norm_num)
    (by rw [rho2R]; positivity) (fun w hw => ee_third_bound4 hw) F_fix F_deriv F_deriv2 hu
  simpa only [Mee4, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

end

end Work.SeedCert
