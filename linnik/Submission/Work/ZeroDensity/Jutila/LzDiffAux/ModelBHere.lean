import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.LinnikAreas.JutilaPieces.S3ModelEval
import Submission.Work.ZeroDensity.Jutila.BzCross.ModelBDefs
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.KappaMertensHere
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRIBoundHere
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRIIBoundHere


/-! Re-homing into `Work.ZeroDensity.Jutila.LzDiffAux` of the proof of `ModelB` from
`Submission/Work/ZeroDensity/Jutila/BzCross/ModelB.lean`, required so that the dependency closure avoids a broken import
(see the module docstring of the original).  Contents are otherwise unchanged. -/

/-!
# The boundary term of the two-sided `S₃` model is `O(N)` (Linnik, `S₃` boundary)

This file contains the *reduction* of the target

`|czModelB w y N| ≤ C·N`   (`1 ≤ w ≤ y ≤ N < w·y`)

to its two regions (`ModelBDefs.lean`): writing `A_t = ⌊w/t⌋₊`, `C_r = ⌊y/r⌋₊`, the summand of
`czModelB` splits according to which of `A_t`, `C_r` attains `czLo w y r t = max A_t C_r`.  The
criterion `C_r ≥ A_t ⟺ r ≤ czD w y t := ⌊y/A_t⌋` (`czD_char`) turns the two cases into the
explicit ranges of `czRI` (region `r ≤ czD`, `B = ⌊y/r⌋`) and `czRII` (region `czD < r ≤ ⌊N/(qw)⌋`,
`B = ⌊w/t⌋`), and the pointwise factorisation `s3main (r*t) α β B = s3c (r*t)·B·(L₁L₂+1)`
(`cz_s3main_log`) together with `s3c (r*t) = ζ(2)⁻¹(r/κ r)(t/κ t)` for squarefree coprime `r,t`
(`cz_s3c_factor`) gives

`czModelB w y N = (π²/6)⁻¹ · (czRI w y N + czRII w y N)`     (`czModelB_split`).

The two region estimates `|czRI| ≤ C·N` and `|czRII| ≤ C·N` are the delegated lemmas in
`czRI_bound.lean` and `czRII_bound.lean`; this file assembles them into `ModelB`.
-/

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila
open Work.ZeroDensity.Jutila.BzCross

noncomputable section

lemma czD_char {w y : ℝ} {r t : ℕ} (hA : 0 < ⌊w / (t : ℝ)⌋₊) (hy : 0 ≤ y) (hr : 1 ≤ r) :
    (⌊y / (r : ℝ)⌋₊ ≥ ⌊w / (t : ℝ)⌋₊) ↔ r ≤ czD w y t := by
  have hA0 : (0 : ℝ) < ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hA
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hyr : 0 ≤ y / (r : ℝ) := div_nonneg hy hr0.le
  rw [czD]
  constructor
  · intro h
    have h1 : ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) ≤ y / (r : ℝ) :=
      le_trans (Nat.cast_le.mpr h) (Nat.floor_le hyr)
    have h3 : ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) ≤ y := (le_div_iff₀ hr0).mp h1
    apply Nat.le_floor
    rw [le_div_iff₀ hA0]
    linarith
  · intro h
    have h2 : ((r : ℕ) : ℝ) ≤ y / ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) :=
      le_trans (Nat.cast_le.mpr h) (Nat.floor_le (div_nonneg hy hA0.le))
    have h3 : (r : ℝ) * ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) ≤ y := (le_div_iff₀ hA0).mp h2
    apply Nat.le_floor
    rw [le_div_iff₀ hr0]
    linarith

lemma czD_char_lt {w y : ℝ} {r t : ℕ} (hA : 0 < ⌊w / (t : ℝ)⌋₊) (hy : 0 ≤ y) (hr : 1 ≤ r) :
    (¬ (r ≤ czD w y t)) ↔ ⌊y / (r : ℝ)⌋₊ < ⌊w / (t : ℝ)⌋₊ := by
  have hc := czD_char hA hy hr
  constructor
  · intro h
    rcases lt_or_ge (⌊y / (r : ℝ)⌋₊) ⌊w / (t : ℝ)⌋₊ with hlt | hge
    · exact hlt
    · exact absurd (hc.mp hge) h
  · intro h hr
    exact absurd (hc.mpr hr) (not_le.mpr h)

lemma Icc_filter_le (R D : ℕ) : (Finset.Icc 1 R).filter (fun r => r ≤ D) = Finset.Icc 1 (min R D) := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

lemma Icc_filter_not_le (R D : ℕ) :
    (Finset.Icc 1 R).filter (fun r => ¬ (r ≤ D)) = Finset.Icc (D + 1) R := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

lemma czMM_eq_zero_or {r t : ℕ} (h : czMM r t ≠ 0) :
    Nat.Coprime r t ∧ (ArithmeticFunction.moebius r : ℝ) ≠ 0
      ∧ (ArithmeticFunction.moebius t : ℝ) ≠ 0 := by
  by_cases hc : Nat.Coprime r t
  · refine ⟨hc, ?_, ?_⟩
    · intro h1; exact h (by simp [czMM, h1])
    · intro h2; exact h (by simp [czMM, h2])
  · exact absurd (by simp [czMM, hc]) h

lemma cz_s3c_factor (r t : ℕ) :
    czMM r t * LinnikAreas.Density4.BzS3.s3c (r * t)
      = czMM r t * ((Real.pi ^ 2 / 6)⁻¹ * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)) := by
  by_cases h : czMM r t = 0
  · rw [h]; ring
  · obtain ⟨hc, hr, ht⟩ := czMM_eq_zero_or h
    have hsr : Squarefree r :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp (Int.cast_ne_zero.mp hr)
    have hst : Squarefree t :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp (Int.cast_ne_zero.mp ht)
    rw [s3c_mul_eq_of_coprime hsr hst hc]

lemma cz_s3main_log {w y : ℝ} {r t B : ℕ} (hw : w ≠ 0) (hy : y ≠ 0)
    (ht : t ≠ 0) (hr : r ≠ 0) (hB : B ≠ 0) :
    LinnikAreas.Density4.BzS3.s3main (r * t) (czAl w t) (czBe y r) B
      = LinnikAreas.Density4.BzS3.s3c (r * t) * (B : ℝ)
        * ((Real.log ((B : ℝ) * (t : ℝ) / w) - 1)
            * (Real.log ((B : ℝ) * (r : ℝ) / y) - 1) + 1) := by
  have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have hwt : w / (t : ℝ) ≠ 0 := div_ne_zero hw htR
  have hyr : y / (r : ℝ) ≠ 0 := div_ne_zero hy hrR
  have h1 : Real.log (B : ℝ) - czAl w t - 1 = Real.log ((B : ℝ) * (t : ℝ) / w) - 1 := by
    rw [czAl, ← Real.log_div (Nat.cast_ne_zero.mpr hB) hwt]
    congr 1
    field_simp
  have h2 : Real.log (B : ℝ) - czBe y r - 1 = Real.log ((B : ℝ) * (r : ℝ) / y) - 1 := by
    rw [czBe, ← Real.log_div (Nat.cast_ne_zero.mpr hB) hyr]
    congr 1
    field_simp
  rw [LinnikAreas.Density4.BzS3.s3main, h1, h2]

lemma cz_row_split (w y : ℝ) (R : ℕ) (t : ℕ) (hw : w ≠ 0) (hy : y ≠ 0)
    (hD : 0 < ⌊w / (t : ℝ)⌋₊) (hy0 : 0 ≤ y)
    (hCr : ∀ r ∈ Finset.Icc 1 R, 1 ≤ ⌊y / (r : ℝ)⌋₊) (ht : t ≠ 0) :
    (∑ r ∈ Finset.Icc 1 R,
        czMM r t * LinnikAreas.Density4.BzS3.s3main (r * t) (czAl w t) (czBe y r)
          (czLo w y r t))
      = (Real.pi ^ 2 / 6)⁻¹ *
          ((∑ r ∈ Finset.Icc 1 (min R (czD w y t)),
              czMM r t * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)
                * ((⌊y / (r : ℝ)⌋₊ : ℝ) * czFI w y r t))
            + (∑ r ∈ Finset.Icc (czD w y t + 1) R,
              czMM r t * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)
                * ((⌊w / (t : ℝ)⌋₊ : ℝ) * czFII w y r t))) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 R) (fun r => r ≤ czD w y t)]
  rw [Icc_filter_le, Icc_filter_not_le]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrD : r ≤ czD w y t := le_trans (Finset.mem_Icc.mp hr).2 (min_le_right _ _)
    have hrR : r ≤ R := le_trans (Finset.mem_Icc.mp hr).2 (min_le_left _ _)
    have hC1 : 1 ≤ ⌊y / (r : ℝ)⌋₊ := hCr r (Finset.mem_Icc.mpr ⟨hr1, hrR⟩)
    have hge : (⌊y / (r : ℝ)⌋₊ ≥ ⌊w / (t : ℝ)⌋₊) := (czD_char hD hy0 hr1).mpr hrD
    have hmax : czLo w y r t = ⌊y / (r : ℝ)⌋₊ := by
      rw [czLo, max_eq_right]; exact hge
    have hB : czLo w y r t ≠ 0 := by rw [hmax]; omega
    have hrne : r ≠ 0 := by omega
    rw [cz_s3main_log hw hy ht hrne hB, hmax]
    simp only [czFI]
    have hfac := cz_s3c_factor r t
    calc czMM r t
            * (LinnikAreas.Density4.BzS3.s3c (r * t) * (⌊y / (r : ℝ)⌋₊ : ℝ)
                * ((Real.log ((⌊y / (r : ℝ)⌋₊ : ℝ) * (t : ℝ) / w) - 1)
                    * (Real.log ((⌊y / (r : ℝ)⌋₊ : ℝ) * (r : ℝ) / y) - 1) + 1))
        = (czMM r t * LinnikAreas.Density4.BzS3.s3c (r * t))
            * ((⌊y / (r : ℝ)⌋₊ : ℝ)
                * ((Real.log ((⌊y / (r : ℝ)⌋₊ : ℝ) * (t : ℝ) / w) - 1)
                    * (Real.log ((⌊y / (r : ℝ)⌋₊ : ℝ) * (r : ℝ) / y) - 1) + 1)) := by ring
      _ = (czMM r t
            * ((Real.pi ^ 2 / 6)⁻¹ * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)))
            * ((⌊y / (r : ℝ)⌋₊ : ℝ)
                * ((Real.log ((⌊y / (r : ℝ)⌋₊ : ℝ) * (t : ℝ) / w) - 1)
                    * (Real.log ((⌊y / (r : ℝ)⌋₊ : ℝ) * (r : ℝ) / y) - 1) + 1)) := by
            rw [hfac]
      _ = (Real.pi ^ 2 / 6)⁻¹ * (czMM r t * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)
            * ((⌊y / (r : ℝ)⌋₊ : ℝ)
                * ((Real.log ((⌊y / (r : ℝ)⌋₊ : ℝ) * (t : ℝ) / w) - 1)
                    * (Real.log ((⌊y / (r : ℝ)⌋₊ : ℝ) * (r : ℝ) / y) - 1) + 1))) := by ring
  · apply Finset.sum_congr rfl
    intro r hr
    have hr1 : czD w y t + 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : r ≤ R := (Finset.mem_Icc.mp hr).2
    have hrpos : 1 ≤ r := by omega
    have hrD : ¬ (r ≤ czD w y t) := by omega
    have hlt : ⌊y / (r : ℝ)⌋₊ < ⌊w / (t : ℝ)⌋₊ := (czD_char_lt hD hy0 hrpos).mp hrD
    have hmax : czLo w y r t = ⌊w / (t : ℝ)⌋₊ := by
      rw [czLo, max_eq_left]; exact le_of_lt hlt
    have hB : czLo w y r t ≠ 0 := by rw [hmax]; omega
    have hrne : r ≠ 0 := by omega
    rw [cz_s3main_log hw hy ht hrne hB, hmax]
    simp only [czFII]
    have hfac := cz_s3c_factor r t
    calc czMM r t
            * (LinnikAreas.Density4.BzS3.s3c (r * t) * (⌊w / (t : ℝ)⌋₊ : ℝ)
                * ((Real.log ((⌊w / (t : ℝ)⌋₊ : ℝ) * (t : ℝ) / w) - 1)
                    * (Real.log ((⌊w / (t : ℝ)⌋₊ : ℝ) * (r : ℝ) / y) - 1) + 1))
        = (czMM r t * LinnikAreas.Density4.BzS3.s3c (r * t))
            * ((⌊w / (t : ℝ)⌋₊ : ℝ)
                * ((Real.log ((⌊w / (t : ℝ)⌋₊ : ℝ) * (t : ℝ) / w) - 1)
                    * (Real.log ((⌊w / (t : ℝ)⌋₊ : ℝ) * (r : ℝ) / y) - 1) + 1)) := by ring
      _ = (czMM r t
            * ((Real.pi ^ 2 / 6)⁻¹ * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)))
            * ((⌊w / (t : ℝ)⌋₊ : ℝ)
                * ((Real.log ((⌊w / (t : ℝ)⌋₊ : ℝ) * (t : ℝ) / w) - 1)
                    * (Real.log ((⌊w / (t : ℝ)⌋₊ : ℝ) * (r : ℝ) / y) - 1) + 1)) := by
            rw [hfac]
      _ = (Real.pi ^ 2 / 6)⁻¹ * (czMM r t * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)
            * ((⌊w / (t : ℝ)⌋₊ : ℝ)
                * ((Real.log ((⌊w / (t : ℝ)⌋₊ : ℝ) * (t : ℝ) / w) - 1)
                    * (Real.log ((⌊w / (t : ℝ)⌋₊ : ℝ) * (r : ℝ) / y) - 1) + 1))) := by ring

/-! ## Range facts -/

lemma cz_r_lt_y {w y : ℝ} {N q r : ℕ} (hw1 : 1 ≤ w) (hwy : w ≤ y) (hNwy : (N : ℝ) < w * y)
    (hq : 1 ≤ q) (hr : r ∈ Finset.Icc 1 (czR w N q)) : (r : ℝ) < y := by
  have hw0 : (0 : ℝ) < w := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hrle : (r : ℝ) ≤ (czR w N q : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hr).2
  have hfloor : (czR w N q : ℝ) ≤ (N : ℝ) / ((q : ℝ) * w) := by
    rw [czR]; exact Nat.floor_le (by positivity)
  have hlt : (N : ℝ) / ((q : ℝ) * w) < y / (q : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hq0]
    nlinarith [hNwy, hw0, hq0]
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hle : y / (q : ℝ) ≤ y := by
    rw [div_le_iff₀ hq0]
    nlinarith [hwy, hw0, hq1]
  linarith

lemma czCr_ge_one {w y : ℝ} {N q r : ℕ} (hw1 : 1 ≤ w) (hwy : w ≤ y) (hNwy : (N : ℝ) < w * y)
    (hq : 1 ≤ q) (hr : r ∈ Finset.Icc 1 (czR w N q)) : 1 ≤ ⌊y / (r : ℝ)⌋₊ := by
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hlt : (r : ℝ) < y := cz_r_lt_y hw1 hwy hNwy hq hr
  apply Nat.le_floor
  rw [le_div_iff₀ hr0]
  simpa using le_of_lt hlt

lemma cz_t_lt_w {w y : ℝ} {N q t : ℕ} (hw1 : 1 ≤ w) (hwy : w ≤ y) (hNwy : (N : ℝ) < w * y)
    (hq : 1 ≤ q) (ht : t ∈ Finset.Icc 1 (czT y N q)) : (t : ℝ) < w := by
  have hw0 : (0 : ℝ) < w := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have htle : (t : ℝ) ≤ (czT y N q : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp ht).2
  have hfloor : (czT y N q : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) := by
    rw [czT]; exact Nat.floor_le (by positivity)
  have hlt : (N : ℝ) / ((q : ℝ) * y) < w / (q : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hq0]
    nlinarith [hNwy, hy0, hq0]
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hle : w / (q : ℝ) ≤ w := by
    rw [div_le_iff₀ hq0]
    nlinarith [hw0, hq0, hq1]
  linarith

lemma czAt_pos {w y : ℝ} {N q t : ℕ} (hw1 : 1 ≤ w) (hwy : w ≤ y) (hNwy : (N : ℝ) < w * y)
    (hq : 1 ≤ q) (ht : t ∈ Finset.Icc 1 (czT y N q)) : 0 < ⌊w / (t : ℝ)⌋₊ := by
  have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hlt : (t : ℝ) < w := cz_t_lt_w hw1 hwy hNwy hq ht
  have : 1 ≤ ⌊w / (t : ℝ)⌋₊ := by
    apply Nat.le_floor
    rw [le_div_iff₀ ht0]
    simpa using le_of_lt hlt
  omega

/-! ## The assembly -/

/-- **The reduction of `czModelB` to its two regions.** -/
theorem czModelB_split (w y : ℝ) (N : ℕ) (hw1 : 1 ≤ w) (hwy : w ≤ y) (hyN : y ≤ (N : ℝ))
    (hNwy : (N : ℝ) < w * y) :
    czModelB w y N = (Real.pi ^ 2 / 6)⁻¹ * (czRI w y N + czRII w y N) := by
  have hw0 : w ≠ 0 := by linarith
  have hy0 : 0 < y := by linarith
  have hy0' : 0 ≤ y := le_of_lt hy0
  have key : ∀ q ∈ Finset.Icc 1 (czQ y N), ∀ t ∈ Finset.Icc 1 (czT y N q),
      (∑ r ∈ Finset.Icc 1 (czR w N q),
        czMM r t * LinnikAreas.Density4.BzS3.s3main (r * t) (czAl w t) (czBe y r)
          (czLo w y r t))
        = (Real.pi ^ 2 / 6)⁻¹ *
            ((∑ r ∈ Finset.Icc 1 (min (czR w N q) (czD w y t)),
                czMM r t * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)
                  * ((⌊y / (r : ℝ)⌋₊ : ℝ) * czFI w y r t))
              + (∑ r ∈ Finset.Icc (czD w y t + 1) (czR w N q),
                czMM r t * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)
                  * ((⌊w / (t : ℝ)⌋₊ : ℝ) * czFII w y r t))) := by
    intro q hq t ht
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    exact cz_row_split w y (czR w N q) t hw0 (ne_of_gt hy0)
      (czAt_pos hw1 hwy hNwy hq1 ht) hy0'
      (fun r hr => czCr_ge_one hw1 hwy hNwy hq1 hr) (by omega)
  calc czModelB w y N
      = ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
          ∑ r ∈ Finset.Icc 1 (czR w N q),
            czMM r t * LinnikAreas.Density4.BzS3.s3main (r * t) (czAl w t) (czBe y r)
              (czLo w y r t) := by
        rw [czModelB]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ q ∈ Finset.Icc 1 (czQ y N), (Real.pi ^ 2 / 6)⁻¹ *
          ((∑ t ∈ Finset.Icc 1 (czT y N q),
              ∑ r ∈ Finset.Icc 1 (min (czR w N q) (czD w y t)),
                czMM r t * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)
                  * ((⌊y / (r : ℝ)⌋₊ : ℝ) * czFI w y r t))
            + (∑ t ∈ Finset.Icc 1 (czT y N q),
              ∑ r ∈ Finset.Icc (czD w y t + 1) (czR w N q),
                czMM r t * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)
                  * ((⌊w / (t : ℝ)⌋₊ : ℝ) * czFII w y r t))) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        refine (Finset.sum_congr rfl fun t ht => key q hq t ht).trans ?_
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ = (Real.pi ^ 2 / 6)⁻¹ * (czRI w y N + czRII w y N) := by
        rw [czRI, czRII, ← Finset.mul_sum, Finset.sum_add_distrib]



/-- **The boundary term of the two-sided `S₃` model is `O(N)` in the hard range.** -/
theorem ModelB (h : Work.ZeroDensity.Jutila.KappaMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) → (N : ℝ) < w * y →
      |Work.ZeroDensity.Jutila.czModelB w y N| ≤ C * (N : ℝ) := by
  obtain ⟨C₁, hC₁, h₁⟩ := CzRIBoundHere
  obtain ⟨C₂, hC₂, h₂⟩ := CzRIIBoundHere
  refine ⟨(Real.pi ^ 2 / 6)⁻¹ * (C₁ + C₂), by positivity, ?_⟩
  intro w y N hw hwy hyN hNwy
  have hsplit := czModelB_split w y N hw hwy hyN hNwy
  have hζpos : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
  have h1 := h₁ w y N hw hwy hyN hNwy
  have h2 := h₂ w y N hw hwy hyN hNwy
  rw [hsplit, abs_mul, abs_of_pos (inv_pos.mpr hζpos)]
  calc (Real.pi ^ 2 / 6)⁻¹ * |czRI w y N + czRII w y N|
      ≤ (Real.pi ^ 2 / 6)⁻¹ * (|czRI w y N| + |czRII w y N|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (le_of_lt (inv_pos.mpr hζpos))
    _ ≤ (Real.pi ^ 2 / 6)⁻¹ * (C₁ * (N : ℝ) + C₂ * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (le_of_lt (inv_pos.mpr hζpos))
    _ = (Real.pi ^ 2 / 6)⁻¹ * (C₁ + C₂) * (N : ℝ) := by ring

end

theorem ModelBHere :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) → (N : ℝ) < w * y →
      |Work.ZeroDensity.Jutila.czModelB w y N| ≤ C * (N : ℝ) :=
  ModelB (Work.ZeroDensity.Jutila.LzDiffAux.KappaMertensHere)

end Work.ZeroDensity.Jutila.LzDiffAux
