/-
# `Work.SeedCertRay.Q` — the decoding of the emitted mantissas (Mathlib layer)

Bridge between the core-only certificate data (`Submission.Work.SeedCertRay.DataAll`, mantissa
integers at scale `2 ^ 40`) and the analytic vocabulary of the ray chain (`Disk`, `Box`,
`diskUnion`, `Petal`).

* `MS` is `2 ^ 40` as a rational; `Q m` decodes the mantissa `m` as the rational `m / MS`;
* `Xb` is the parameter box (centre `PXM + i PYM`, half-width `2 ^ -30`), `Zb`/`Ab` the certified
  boxes for the parabolic point `z₁` and the quadratic coefficient `A`;
* `dskOf l q` decodes the `q`-th disk of a data list, `Dd k j i` the `i`-th sub-disk of angle
  `j mod 10` of level `k`, and `vdir k j` the half-plane direction of `(k,j)`;
* `qdir j` is the `j`-th base direction (a rational approximation of `rayDirection θ_j`).
-/
import Mathlib
import Submission.Work.SeedCertRay.DataAll
import Submission.Work.SeedCertRay.Disk

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-- The scale `2 ^ 40` of the mantissas, as a rational. -/
def MS : ℚ := 2 ^ 40

theorem MS_pos : (0 : ℚ) < MS := by norm_num [MS]

/-- Decoding of a mantissa. -/
def Q (m : ℤ) : ℚ := (m : ℚ) / MS

theorem Q_zero : Q 0 = 0 := by simp [Q]

theorem Q_le_iff {a b : ℤ} : Q a ≤ Q b ↔ a ≤ b := by
  rw [Q, Q, div_le_div_iff_of_pos_right MS_pos]
  exact Int.cast_le

theorem Q_lt_iff {a b : ℤ} : Q a < Q b ↔ a < b := by
  rw [Q, Q, div_lt_div_iff_of_pos_right MS_pos]
  exact Int.cast_lt

theorem Q_le {a b : ℤ} (h : a ≤ b) : Q a ≤ Q b := Q_le_iff.mpr h

theorem Q_nonneg {a : ℤ} (h : 0 ≤ a) : 0 ≤ Q a := by
  rw [← Q_zero]; exact Q_le h

theorem Q_add (a b : ℤ) : Q (a + b) = Q a + Q b := by
  simp only [Q, Int.cast_add]; field_simp <;> ring

theorem Q_sub (a b : ℤ) : Q (a - b) = Q a - Q b := by
  simp only [Q, Int.cast_sub]; field_simp <;> ring

/-- The multiplicative rule, with the unavoidable scale factor `MS`. -/
theorem Q_mul (a b : ℤ) : Q (a * b) = Q a * Q b * MS := by
  simp only [Q, Int.cast_mul]; field_simp <;> ring

theorem Q_neg (a : ℤ) : Q (-a) = -Q a := by
  simp only [Q, Int.cast_neg]; ring

/-- The square of a decoded mantissa. -/
theorem Q_sq (a : ℤ) : Q a * Q a = ((a * a : ℤ) : ℚ) / (MS * MS) := by
  simp only [Q, Int.cast_mul]
  rw [div_mul_div_comm]

/-- The `s ^ 2 ≤ |w₀| ^ 2` comparison, in decoded form. -/
theorem Q_sq_le_iff {a b c : ℤ} : Q a * Q a ≤ Q b * Q b + Q c * Q c ↔ a * a ≤ b * b + c * c := by
  rw [Q_sq, Q_sq, Q_sq, ← add_div, div_le_div_iff_of_pos_right (mul_pos MS_pos MS_pos)]
  rw [← Int.cast_add]
  exact Int.cast_le

/-- The quantity `s ^ 2 + R + rX` of the certificate, decoded. -/
theorem Q_sq_add (a b c : ℤ) :
    Q a * Q a + Q b + Q c = (((a * a + (b + c) * MSZ : ℤ)) : ℚ) / (MS * MS) := by
  have h : ((MSZ : ℤ) : ℚ) = MS := by
    simp only [MSZ]; unfold MS; push_cast; ring
  simp only [Q, Int.cast_add, Int.cast_mul, h]
  field_simp <;> ring

/-- The half-width of the parameter box, in mantissa units (`2 ^ -30`). -/
def HWM : ℤ := 1024

/-- The parameter box: `c_b` to within `2 ^ -30`.  (`RADM = 4 * HWM`, so `Xb.rad = Q RADM`.) -/
def Xb : Box := ⟨Q PXM - Q HWM, Q PXM + Q HWM, Q PYM - Q HWM, Q PYM + Q HWM⟩

theorem Xb_center_re : Xb.center.re = Q PXM := by
  have h1 : Xb.center.re = ((Xb.xl : ℝ) + Xb.xh) / 2 := by simp [Box.center]
  rw [h1]
  simp only [Xb]
  push_cast
  ring

theorem Xb_center_im : Xb.center.im = Q PYM := by
  have h1 : Xb.center.im = ((Xb.yl : ℝ) + Xb.yh) / 2 := by simp [Box.center]
  rw [h1]
  simp only [Xb]
  push_cast
  ring

theorem Xb_rad : Xb.rad = Q RADM := by
  have h1 : Xb.rad = (Xb.xh - Xb.xl) + (Xb.yh - Xb.yl) := rfl
  rw [h1]
  simp only [Xb, Q, HWM, RADM]
  push_cast
  field_simp <;> ring

/-- The certified box for the parabolic point `z₁` (half-width `2 ^ -20`). -/
def Zb : Box := ⟨Q ZCX - Q ETA1, Q ZCX + Q ETA1, Q ZCY - Q ETA1, Q ZCY + Q ETA1⟩

/-- The certified box for the quadratic coefficient `A = F''(z₁)/2` (half-width `2 ^ -20`). -/
def Ab : Box := ⟨Q ACX - Q ETAA, Q ACX + Q ETAA, Q ACY - Q ETAA, Q ACY + Q ETAA⟩

/-- The `q`-th disk of a data list. -/
def dskOf (l : List ℤ) (q : ℕ) : Disk :=
  ⟨Q (gI l (3 * q)), Q (gI l (3 * q + 1)), Q (gI l (3 * q + 2))⟩

/-- The `i`-th sub-disk of angle `j` of level `k`. -/
def Dd (k j : ℕ) (i : Fin NC) : Disk := dskOf (dsk k) ((j % 10) * NC + i.val)

/-- The half-plane direction of `(k,j)`. -/
def vdir (k j : ℕ) : ℚ × ℚ :=
  (Q (gI (dirs k) (2 * (j % 10))), Q (gI (dirs k) (2 * (j % 10) + 1)))

/-- The `j`-th base direction, as a complex number. -/
def qdirC (j : ℕ) : ℂ :=
  ((Q (gI dirBase (2 * j)) : ℚ) : ℂ) + ((Q (gI dirBase (2 * j + 1)) : ℚ) : ℂ) * Complex.I

/-- The ten base directions, as a function of the ray index (`j % 10`). -/
def qdir (j : ℕ) : ℚ × ℚ := (Q (gI dirBase (2 * (j % 10))), Q (gI dirBase (2 * (j % 10) + 1)))

theorem qdirC_eq (j : ℕ) :
    qdirC (j % 10) = ((qdir j).1 : ℂ) + ((qdir j).2 : ℂ) * Complex.I := by
  simp [qdirC, qdir]

/-- The petal depth certified by the data: `R = 4`. -/
def R4 : ℝ := RRM / MS

theorem R4_eq : R4 = 4 := by
  unfold R4
  simp only [RRM, MS]
  push_cast
  field_simp <;> ring

end

end Work.SeedCertRay
