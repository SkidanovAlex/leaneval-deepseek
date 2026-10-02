/-
# SeedPortraitCert — the periodic landing boxes of `12/33` and `13/33` miss the box `Zb` of `z₁`

Area `Submission/Work/SeedPortraitCert/`.  The chain (`Chain.lean`) puts the landing point of the
`12/33`-ray in the periodic family `CTA KT 0` and that of the `13/33`-ray in `CTB KT 0`.  This
module certifies the numerical statement that both of these sets are disjoint from
`Work.SeedCertRay.Zb`, the certified box of the seed's parabolic point `z₁`.

The separation is rectangular, hence elementary: every disk of the class-`0` periodic family lies
strictly to the *right* of `Zb` (`Zb.xh < cx - r`), and every disk of the class-`5` family
strictly to the *left* (`cx + r < Zb.xl`).  The inequalities are rational and closed by the
kernel (`decide` on the underlying integer comparison).
-/
import Mathlib
import Submission.Work.SeedPortraitCert.Chain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedPortraitCert

open Work.SeedCertRay

noncomputable section

/-! ## Rectangular separation of a disk from a box -/

theorem disk_re_bounds {D : Disk} {z : ℂ} (hz : D.mem z) :
    (D.cx : ℝ) - (D.r : ℝ) ≤ z.re ∧ z.re ≤ (D.cx : ℝ) + (D.r : ℝ) := by
  have hre : (z - D.center).re = z.re - (D.cx : ℝ) := by simp [Disk.center]
  have h1 : (z - D.center).re ≤ (D.r : ℝ) := le_trans (Complex.re_le_norm _) hz
  have hn : -((z - D.center).re) ≤ (D.r : ℝ) := by
    have h2 := Complex.re_le_norm (-(z - D.center))
    rw [Complex.neg_re, norm_neg] at h2
    exact le_trans h2 hz
  rw [hre] at h1 hn
  constructor <;> linarith

/-- A disk strictly left of the box `Zb` is disjoint from it. -/
theorem disk_disj_Zb_of_left {D : Disk} (h : ((D.cx : ℝ) + (D.r : ℝ)) < (Zb.xl : ℝ))
    {z : ℂ} (hz : D.mem z) : ¬ Zb.mem z := by
  intro hz'
  have h1 := (disk_re_bounds hz).2
  have h2 : (Zb.xl : ℝ) ≤ z.re := hz'.1
  linarith

/-- A disk strictly right of the box `Zb` is disjoint from it. -/
theorem disk_disj_Zb_of_right {D : Disk} (h : (Zb.xh : ℝ) < ((D.cx : ℝ) - (D.r : ℝ)))
    {z : ℂ} (hz : D.mem z) : ¬ Zb.mem z := by
  intro hz'
  have h1 := (disk_re_bounds hz).1
  have h2 : z.re ≤ (Zb.xh : ℝ) := hz'.2.1
  linarith

/-! ## The rational comparisons -/

theorem Q_add_lt_sub {a b c d : ℤ} : Q a + Q b < Q c - Q d ↔ a + b < c - d := by
  rw [← Q_sub, ← Q_add, Q_lt_iff]

/-- Every disk of the class-`0` periodic family lies strictly right of `Zb`. -/
theorem Zb_right (q : ℕ) (hq : q < 6) :
    (Zb.xh : ℚ) < (dskOf perP q).cx - (dskOf perP q).r := by
  have h : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [Zb, dskOf]
      rw [Q_add_lt_sub]
      decide

/-- Every disk of the class-`5` periodic family lies strictly left of `Zb`. -/
theorem Zb_left (q : ℕ) (hq : q < 6) :
    (dskOf perP (30 + q)).cx + (dskOf perP (30 + q)).r < (Zb.xl : ℚ) := by
  have h : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [Zb, dskOf]
      rw [← Q_sub, ← Q_add, Q_lt_iff]
      decide

/-! ## The two disjointness statements -/

theorem Zb_rightR (q : ℕ) (hq : q < 6) :
    (Zb.xh : ℝ) < ((dskOf perP q).cx : ℝ) - ((dskOf perP q).r : ℝ) := by
  have h := Zb_right q hq
  have h1 : ((Zb.xh : ℚ) : ℝ) < (((dskOf perP q).cx - (dskOf perP q).r : ℚ) : ℝ) := by
    exact_mod_cast h
  rwa [Rat.cast_sub] at h1

theorem Zb_leftR (q : ℕ) (hq : q < 6) :
    ((dskOf perP (30 + q)).cx : ℝ) + ((dskOf perP (30 + q)).r : ℝ) < (Zb.xl : ℝ) := by
  have h := Zb_left q hq
  have h1 : (((dskOf perP (30 + q)).cx + (dskOf perP (30 + q)).r : ℚ) : ℝ) < ((Zb.xl : ℚ) : ℝ) := by
    exact_mod_cast h
  rwa [Rat.cast_add] at h1

theorem boxP_KT_zero (i : Fin NC) : boxP KT 0 i = dskOf perP i.val := by
  have hidx : (0 % 10) * NC + i.val = i.val := by simp [NC]
  unfold boxP boxOfP
  rw [if_neg (by decide : ¬ KT < KT), hidx]

theorem boxP_KT_five (i : Fin NC) : boxP KT 5 i = dskOf perP (30 + i.val) := by
  have hidx : (5 % 10) * NC + i.val = 30 + i.val := by simp [NC]
  unfold boxP boxOfP
  rw [if_neg (by decide : ¬ KT < KT), hidx]

/-- **The landing box of the `12/33`-ray misses `Zb`.** -/
theorem CTA_KT0_disj (z : ℂ) (hz : z ∈ CTA KT 0) : ¬ Zb.mem z := by
  have hz' : z ∈ CT KT 0 := hz
  obtain ⟨i, hi⟩ := Work.SeedCertRay.mem_diskUnion.mp hz'
  rw [boxP_KT_zero i] at hi
  have hq : i.val < 6 := by simpa [NC] using i.isLt
  exact disk_disj_Zb_of_right (Zb_rightR i.val hq) hi

/-- **The landing box of the `13/33`-ray misses `Zb`.** -/
theorem CTB_KT0_disj (z : ℂ) (hz : z ∈ CTB KT 0) : ¬ Zb.mem z := by
  have e : CTB KT 0 = CT KT 5 := by simp [CTB]
  rw [e] at hz
  obtain ⟨i, hi⟩ := Work.SeedCertRay.mem_diskUnion.mp hz
  rw [boxP_KT_five i] at hi
  have hq : i.val < 6 := by simpa [NC] using i.isLt
  exact disk_disj_Zb_of_left (Zb_leftR i.val hq) hi

end

end Work.SeedPortraitCert
