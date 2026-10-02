import Mathlib
import Submission.Work.SeedCertRay.Q
import Submission.Work.SeedCertRay.diskCover_of_bounds_sharp
import Submission.Work.SeedCertRay.disk_mem_hZl
import Submission.Work.SeedCertRay.disk_mem_hE
import Submission.Work.SeedCertRay.disk_sub_box_normSq_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.SeedCertRay.stepOKB_sound` — soundness of the (D1) certificate check

The checker `stepOKB` (in `Work.SeedCertRay.Num`) validates one pull-back step of the ray chain
with all quantities stored as integer mantissas at scale `2 ^ 40`.  This file proves that the
checker really implies the geometric condition (D1) `DiskCover` of the disk chain, by
instantiating the sharp square-root cover estimate `diskCover_of_bounds_sharp` with

* `w₀ := conj E.center` (the reflected centre of the *target* disk `E = dskOf t qt`),
* `s := Q c₀` (the squared lower bound for `‖z - c‖` and `‖w₀‖`),
* `ρ := Q c₁ = E.r` (the target radius, which is exactly the radius of the disk around `conj w₀`),

and discharging the four analytic hypotheses from the nine integer inequalities of `stepOKB` via
the three ready-made estimates `disk_mem_hZl` (the `z`-distance bound), `disk_sub_box_normSq_le`
(the centre drift bound, from the check `h7` together with `h6`) and `disk_mem_hE` (the
containment of the `ρ`-disk about `conj w₀` in `E`, which here is the trivial identity).

All arithmetic conversions (mantissa `Q n = n / 2 ^ 40` vs. the rational data of the estimates)
are done with the single rewrite `Q_R` together with `push_cast`/`field_simp`/`nlinarith`.
-/

namespace Work.SeedCertRay

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The mantissa scale `2 ^ 40` is positive, as a real number. -/
private lemma MSZ_R_pos : (0 : ℝ) < (MSZ : ℝ) := by norm_num [MSZ]

/-- The two descriptions of the scale agree. -/
private lemma MSR : ((MS : ℚ) : ℝ) = (MSZ : ℝ) := by unfold MS MSZ; push_cast; norm_num

/-- The decoded mantissa `Q n`, as a real number. -/
private lemma Q_R (n : ℤ) : ((Q n : ℚ) : ℝ) = (n : ℝ) / (MSZ : ℝ) := by
  unfold Q
  rw [Rat.cast_div, Rat.cast_intCast, MSR]

/-- The multiplicative rule for `2`. -/
private lemma Q_two_mul (a : ℤ) : Q (2 * a) = 2 * Q a := by
  rw [Q_mul]; simp only [Q]; field_simp; ring

/-- The parameter-box radius is positive. -/
private lemma Q_RADM_pos : (0 : ℚ) < Q RADM := by rw [Q]; norm_num [RADM, MS]

/-- From `x ^ 2 ≤ M ^ 2` and `0 ≤ M`, `x ≤ M`. -/
private lemma le_of_sq_le_sq' {x M : ℝ} (h : x ^ 2 ≤ M ^ 2) (hM : 0 ≤ M) : x ≤ M := by
  have h1 : |x| ≤ |M| := sq_le_sq.mp h
  rw [abs_of_nonneg hM] at h1
  exact le_trans (le_abs_self x) h1

theorem stepOKB_sound (s t c : List ℤ) (qs qt : ℕ)
    (h : Work.SeedCertRay.stepOKB s t c Work.SeedCertRay.PXM Work.SeedCertRay.PYM Work.SeedCertRay.RADM qs qt = true) :
    Work.SeedCertRay.DiskCover (Work.SeedCertRay.dskOf s qs) Work.SeedCertRay.Xb (Work.SeedCertRay.dskOf t qt) := by
  simp only [stepOKB, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  -- names for the mantissas
  set c0 := gI c (3 * qt) with hc0
  set c1 := gI c (3 * qt + 1) with hc1
  set c2 := gI c (3 * qt + 2) with hc2
  set Sx := gI s (3 * qs) with hSx
  set Sy := gI s (3 * qs + 1) with hSy
  set Sr := gI s (3 * qs + 2) with hSr
  set Ex := gI t (3 * qt) with hEx
  set Ey := gI t (3 * qt + 1) with hEy
  have hMZ : (0 : ℝ) < (MSZ : ℝ) := MSZ_R_pos
  refine diskCover_of_bounds_sharp (dskOf s qs) Xb (dskOf t qt) (Q Ex) (-(Q Ey)) (Q c0) (Q c1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- `0 ≤ s`
    exact Q_nonneg h1
  · -- `0 ≤ ρ`
    exact Q_nonneg h2
  · -- `ρ ≤ 2 s`
    have hh : Q c1 ≤ 2 * Q c0 := by rw [← Q_two_mul]; exact Q_le h3
    exact_mod_cast hh
  · -- (D1): the drift estimate `‖(z - c) - w₀ ^ 2‖ ≤ ρ (2 s - ρ)`
    intro z cc hz hc
    by_cases hpos : (0 : ℚ) ≤ Q c2
    · -- the non-degenerate case: the drift bound `M = Q c2` is available
      have hMr : (((dskOf s qs).r + Xb.rad : ℚ) : ℝ) ≤ ((Q c2 : ℚ) : ℝ) := by
        have hh : Q Sr + Q RADM ≤ Q c2 := by
          have h6' := Q_le h6
          rwa [Q_add] at h6'
        rw [Xb_rad]
        simp only [dskOf]
        exact_mod_cast hh
      have hd : ∀ (z c : ℂ), (dskOf s qs).mem z → Xb.mem c →
          ‖z - c - ((((Q Ex : ℚ) : ℝ) : ℂ) + ((((-(Q Ey)) : ℚ) : ℝ) : ℂ) * Complex.I) ^ 2‖ ^ 2
            ≤ (((Q c2 : ℚ) : ℝ)) ^ 2 := by
        refine disk_sub_box_normSq_le (dskOf s qs) Xb (Q Ex) (-(Q Ey)) (Q c2) hpos hMr ?_
        -- the centre drift inequality, from the checks `h6` and `h7`
        rw [Xb_center_re, Xb_center_im, Xb_rad]
        simp only [dskOf]
        set x := c2 - Sr - RADM with hx
        set A := (Sx - PXM) * MSZ - (Ex * Ex - Ey * Ey) with hA
        set B := (Sy - PYM) * MSZ + 2 * Ex * Ey with hB
        have hcast : ((A * A + B * B : ℤ) : ℝ) ≤ ((MSZ * MSZ * (x * x) : ℤ) : ℝ) := by
          exact_mod_cast h7
        push_cast at hcast
        have hkey : (↑A : ℝ) ^ 2 + (↑B : ℝ) ^ 2 ≤ (↑MSZ : ℝ) ^ 2 * (↑x : ℝ) ^ 2 := by
          nlinarith [hcast]
        rw [hA, hB, hx] at hkey
        push_cast at hkey
        push_cast
        simp only [Q_R]
        field_simp
        nlinarith [hkey]
      have h8R : ((Q c2 : ℚ) : ℝ) ≤ ((Q c1 : ℚ) : ℝ) * (2 * ((Q c0 : ℚ) : ℝ) - ((Q c1 : ℚ) : ℝ)) := by
        have hcast : ((MSZ * c2 : ℤ) : ℝ) ≤ ((c1 * (2 * c0 - c1) : ℤ) : ℝ) := by
          exact_mod_cast h8
        push_cast at hcast
        have hkey : (↑MSZ : ℝ) * ↑c2 ≤ ↑c1 * (2 * ↑c0 - ↑c1) := by nlinarith [hcast]
        simp only [Q_R]
        field_simp
        nlinarith [hkey]
      refine le_trans ?_ h8R
      have hq : (0 : ℝ) ≤ ((Q c2 : ℚ) : ℝ) := by exact_mod_cast hpos
      exact le_of_sq_le_sq' (hd z cc hz hc) hq
    · -- the degenerate case: `Q c2 < 0` forces the source radius negative, so `D` is empty
      have hneg : Q c2 < 0 := not_le.mp hpos
      have hh : Q Sr + Q RADM ≤ Q c2 := by
        have h6' := Q_le h6
        rwa [Q_add] at h6'
      have hSr : Q Sr < 0 := by
        have hR := Q_RADM_pos
        linarith
      have hm : ((dskOf s qs).r : ℝ) < 0 := by
        simp only [dskOf]
        exact_mod_cast hSr
      simp only [Disk.mem] at hz
      linarith [hz, hm, norm_nonneg (z - (dskOf s qs).center)]
  · -- (D1): the `z`-distance bound `s ^ 2 ≤ ‖z - c‖`
    have hs0 : (0 : ℚ) ≤ Q c0 := Q_nonneg h1
    refine disk_mem_hZl (dskOf s qs) Xb (Q c0) hs0 ?_
    rw [Xb_center_re, Xb_center_im, Xb_rad]
    simp only [dskOf]
    set A := c0 * c0 + (Sr + RADM) * MSZ with hA
    set G := (Sx - PXM) * (Sx - PXM) + (Sy - PYM) * (Sy - PYM) with hG
    have hcast : ((A * A : ℤ) : ℝ) ≤ ((MSZ * MSZ * G : ℤ) : ℝ) := by
      exact_mod_cast h5
    push_cast at hcast
    have hkey : (↑A : ℝ) ^ 2 ≤ (↑MSZ : ℝ) ^ 2 * (↑G : ℝ) := by nlinarith [hcast]
    rw [hA, hG] at hkey
    push_cast at hkey
    push_cast
    simp only [Q_R]
    field_simp
    nlinarith [hkey]
  · -- (D1): `s ^ 2 ≤ ‖w₀‖ ^ 2`
    have hcast : ((c0 * c0 : ℤ) : ℝ) ≤ ((Ex * Ex + Ey * Ey : ℤ) : ℝ) := by
      exact_mod_cast h4
    push_cast at hcast
    have hkey : (↑c0 : ℝ) ^ 2 ≤ (↑Ex : ℝ) ^ 2 + (↑Ey : ℝ) ^ 2 := by nlinarith [hcast]
    push_cast
    simp only [Q_R]
    field_simp
    nlinarith [hkey]
  · -- the `ρ`-disk about `conj w₀` is the target disk `E` itself
    intro u hu
    have hcenter : (dskOf t qt).center
        = (((Q Ex : ℚ) : ℝ) : ℂ) + ((((Q Ey : ℚ) : ℝ)) : ℂ) * Complex.I := by
      simp only [Disk.center, dskOf, ← hEx, ← hEy]
    have hconj : starRingEnd ℂ ((((Q Ex : ℚ) : ℝ)) + ((((-(Q Ey)) : ℚ) : ℝ)) * Complex.I)
        = (dskOf t qt).center := by
      rw [hcenter]
      have hneg : (((((-((Q Ey)) : ℚ)) : ℝ)) : ℂ) = -(((((Q Ey : ℚ) : ℝ)) : ℂ)) := by
        push_cast; ring
      rw [hneg]
      apply Complex.ext <;> simp
    rw [hconj] at hu
    have hr : ((dskOf t qt).r : ℝ) = ((Q c1 : ℚ) : ℝ) := by
      simp only [dskOf]
      rw [h9]
    simp only [Disk.mem]
    rw [hr]
    exact hu

end Work.SeedCertRay
