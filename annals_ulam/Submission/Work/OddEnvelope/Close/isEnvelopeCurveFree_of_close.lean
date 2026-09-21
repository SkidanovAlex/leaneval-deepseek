import Mathlib
import Submission.Work.OddCurve.Free
import Submission.Work.OddEnvelope.Close.isEnvelopeCurve_of_close

namespace Work.OddEnvelope.Close

open Set Filter
open scoped Topology ContDiff

noncomputable section

/-! ## Elementary facts about the semicircle chord function `profileX s = 1/√(1+s²)` -/

private lemma profileX_pos (s : ℝ) : 0 < Work.OddEnvelope.profileX s := by
  rw [Work.OddEnvelope.profileX]
  positivity

private lemma profileX_sq (s : ℝ) : Work.OddEnvelope.profileX s ^ 2 = 1 / (1 + s ^ 2) := by
  rw [Work.OddEnvelope.profileX, div_pow, one_pow, Real.sq_sqrt (by positivity)]

private lemma profileX_sq_mul (s : ℝ) : Work.OddEnvelope.profileX s ^ 2 * (1 + s ^ 2) = 1 := by
  rw [profileX_sq]
  field_simp

private lemma profileX_le_one (s : ℝ) : Work.OddEnvelope.profileX s ≤ 1 := by
  rw [Work.OddEnvelope.profileX, div_le_one (by positivity)]
  rw [Real.one_le_sqrt]
  linarith [sq_nonneg s]

private lemma profileX_ge {s : ℝ} (hs : 0 < s) (hs9 : s ≤ 9 / 10) :
    7 / 10 ≤ Work.OddEnvelope.profileX s := by
  have h2 : (7 / 10) ^ 2 ≤ Work.OddEnvelope.profileX s ^ 2 := by
    rw [profileX_sq s, le_div_iff₀ (by positivity : (0:ℝ) < 1 + s^2)]
    nlinarith [sq_nonneg s, hs, hs9]
  calc (7 / 10 : ℝ) = |(7 / 10 : ℝ)| := (abs_of_nonneg (by norm_num)).symm
    _ ≤ |Work.OddEnvelope.profileX s| := sq_le_sq.mp h2
    _ = Work.OddEnvelope.profileX s := abs_of_pos (profileX_pos s)

private lemma hasDerivAt_profileX (s : ℝ) :
    HasDerivAt Work.OddEnvelope.profileX (-s * Work.OddEnvelope.profileX s ^ 3) s := by
  have hpol : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_pow 2 s).const_add 1)
  have hsq : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2)) (s / Real.sqrt (1+s^2)) s := by
    have h := hpol.sqrt (by positivity : (1 : ℝ) + s^2 ≠ 0)
    exact h.congr_deriv (by field_simp)
  have hprof : Work.OddEnvelope.profileX = fun x : ℝ => (Real.sqrt (1 + x^2))⁻¹ := by
    funext x; simp [Work.OddEnvelope.profileX, one_div]
  rw [hprof]
  have hs := hsq.inv (by positivity : Real.sqrt (1+s^2) ≠ 0)
  refine hs.congr_deriv ?_
  field_simp

private lemma profileX_deriv (s : ℝ) :
    deriv Work.OddEnvelope.profileX s = -s * Work.OddEnvelope.profileX s ^ 3 :=
  (hasDerivAt_profileX s).deriv

private lemma profileX_deriv2 (s : ℝ) :
    deriv (deriv Work.OddEnvelope.profileX) s =
      (2 * s ^ 2 - 1) * Work.OddEnvelope.profileX s ^ 5 := by
  have hfun : deriv Work.OddEnvelope.profileX =
      fun x => -x * Work.OddEnvelope.profileX x ^ 3 := by
    funext x; exact profileX_deriv x
  rw [hfun]
  have h2 : HasDerivAt (fun x : ℝ => Work.OddEnvelope.profileX x ^ 3)
      (3 * Work.OddEnvelope.profileX s ^ 2 * deriv Work.OddEnvelope.profileX s) s := by
    have h := (hasDerivAt_profileX s).pow 3
    have hpow : (Work.OddEnvelope.profileX ^ 3 : ℝ → ℝ) =
        fun x => Work.OddEnvelope.profileX x ^ 3 := by funext x; simp
    rw [hpow] at h
    refine h.congr_deriv ?_
    simp only [Nat.reduceSub]
    rw [profileX_deriv]
    ring
  have h1 : HasDerivAt (fun x : ℝ => -x) (-1) s := (hasDerivAt_id s).neg
  have h3 : HasDerivAt (fun x : ℝ => -x * Work.OddEnvelope.profileX x ^ 3)
      ((-1) * Work.OddEnvelope.profileX s ^ 3 +
        (-s) * (3 * Work.OddEnvelope.profileX s ^ 2 * deriv Work.OddEnvelope.profileX s)) s := by
    have h := h1.mul h2
    have hmul : ((fun x : ℝ => -x) * fun x => Work.OddEnvelope.profileX x ^ 3) =
        fun x => -x * Work.OddEnvelope.profileX x ^ 3 := by funext x; rfl
    rwa [hmul] at h
  rw [h3.deriv, profileX_deriv]
  linear_combination (Work.OddEnvelope.profileX s ^ 3) * (profileX_sq_mul s)

private lemma profileX_add (s : ℝ) :
    Work.OddEnvelope.profileX s + s * deriv Work.OddEnvelope.profileX s =
      Work.OddEnvelope.profileX s ^ 3 := by
  rw [profileX_deriv]
  nlinarith [profileX_sq_mul s, profileX_pos s]

private lemma profileX_shape (s : ℝ) :
    2 * (deriv Work.OddEnvelope.profileX s) ^ 2 -
      Work.OddEnvelope.profileX s * deriv (deriv Work.OddEnvelope.profileX) s =
        Work.OddEnvelope.profileX s ^ 6 := by
  rw [profileX_deriv, profileX_deriv2]
  ring

private lemma abs_deriv_profileX_le {s : ℝ} (hs : 0 < s) (hs9 : s ≤ 9 / 10) :
    |deriv Work.OddEnvelope.profileX s| ≤ 9 / 10 := by
  rw [profileX_deriv]
  have hP := profileX_le_one s
  have hPnn := le_of_lt (profileX_pos s)
  have hP3 : Work.OddEnvelope.profileX s ^ 3 ≤ 1 := pow_le_one₀ hPnn hP
  rw [abs_mul, abs_neg, abs_of_pos hs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ Work.OddEnvelope.profileX s ^ 3)]
  nlinarith [hP3, hs, hs9]

private lemma abs_deriv2_profileX_le {s : ℝ} (hs : 0 ≤ s) (hs9 : s ≤ 9 / 10) :
    |deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 := by
  rw [profileX_deriv2, abs_mul]
  have hP := profileX_le_one s
  have hPnn := le_of_lt (profileX_pos s)
  have h1 : |2 * s ^ 2 - 1| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg s, hs, hs9]
  have h2 : |Work.OddEnvelope.profileX s ^ 5| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ hPnn hP
  calc |2 * s ^ 2 - 1| * |Work.OddEnvelope.profileX s ^ 5| ≤ 1 * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

/-! ## Triangle-inequality helpers -/

private lemma abs_le_abs_add (a b : ℝ) : |a| ≤ |b| + |a - b| := by
  calc |a| = |(a - b) + b| := by ring_nf
    _ ≤ |a - b| + |b| := abs_add_le _ _
    _ = |b| + |a - b| := by ring

private lemma abs_sq_sub_sq_le {a b e : ℝ} (h : |a - b| ≤ e) (he : 0 ≤ e) :
    |a ^ 2 - b ^ 2| ≤ e * (2 * |b| + e) := by
  have ha : |a| ≤ |b| + e := le_trans (abs_le_abs_add a b) (by linarith)
  have h2 : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [h2, abs_mul]
  refine mul_le_mul h ?_ (abs_nonneg _) he
  calc |a + b| ≤ |a| + |b| := abs_add_le _ _
    _ ≤ 2 * |b| + e := by linarith

private lemma one_sub_tau : (1 : ℝ) - Work.OddEnvelope.tau = 9 / 10 := by
  rw [Work.OddEnvelope.tau]; norm_num

/-! ## The four estimates on the `(0, 1-τ]` part -/

private lemma mono_y_close {y h : ℝ → ℝ} {δ s : ℝ} (hδ : δ ≤ 1 / 100) (hs : 0 < s)
    (hsle : s ≤ 1 - Work.OddEnvelope.tau)
    (h0 : |y s - Work.OddEnvelope.profileX s| ≤ δ)
    (h1 : |deriv y s - deriv Work.OddEnvelope.profileX s| ≤ δ)
    (h2 : |deriv h s| ≤ δ) :
    0 < y s + s * deriv y s + deriv h s := by
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) h0
  have hs9 : s ≤ 9 / 10 := by rw [one_sub_tau] at hsle; exact hsle
  have hP := profileX_ge hs hs9
  have hP3 : (7 / 10) ^ 3 ≤ Work.OddEnvelope.profileX s ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hP 3
  have hE : |(y s - Work.OddEnvelope.profileX s) +
      s * (deriv y s - deriv Work.OddEnvelope.profileX s) + deriv h s| ≤ δ * (2 + s) := by
    have h3 : |s * (deriv y s - deriv Work.OddEnvelope.profileX s)| ≤ s * δ := by
      rw [abs_mul, abs_of_pos hs]
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt hs)
    calc |(y s - Work.OddEnvelope.profileX s) +
          s * (deriv y s - deriv Work.OddEnvelope.profileX s) + deriv h s|
        ≤ |(y s - Work.OddEnvelope.profileX s) +
            s * (deriv y s - deriv Work.OddEnvelope.profileX s)| + |deriv h s| :=
          abs_add_le _ _
      _ ≤ (|y s - Work.OddEnvelope.profileX s| +
            |s * (deriv y s - deriv Work.OddEnvelope.profileX s)|) + |deriv h s| := by
          linarith [abs_add_le (y s - Work.OddEnvelope.profileX s)
            (s * (deriv y s - deriv Work.OddEnvelope.profileX s))]
      _ ≤ δ + s * δ + δ := by linarith
      _ = δ * (2 + s) := by ring
  have hV : y s + s * deriv y s + deriv h s =
      Work.OddEnvelope.profileX s ^ 3 +
        ((y s - Work.OddEnvelope.profileX s) +
          s * (deriv y s - deriv Work.OddEnvelope.profileX s) + deriv h s) := by
    rw [← profileX_add s]; ring
  have hb : δ * (2 + s) ≤ 1 / 100 * (29 / 10) := by
    have hs2 : 2 + s ≤ 29 / 10 := by linarith
    calc δ * (2 + s) ≤ δ * (29 / 10) := mul_le_mul_of_nonneg_left hs2 hδ0
      _ ≤ (1 / 100) * (29 / 10) := mul_le_mul_of_nonneg_right hδ (by norm_num)
  rw [hV]
  linarith [(abs_le.mp hE).1, hP3, hb]

private lemma mono_x_close {x h : ℝ → ℝ} {δ s : ℝ} (hδ : δ ≤ 1 / 100) (hs : 0 < s)
    (hsle : s ≤ 1 - Work.OddEnvelope.tau)
    (h0 : |x s - Work.OddEnvelope.profileX s| ≤ δ)
    (h1 : |deriv x s - deriv Work.OddEnvelope.profileX s| ≤ δ)
    (h2 : |deriv h s| ≤ δ) :
    0 < x s + s * deriv x s - deriv h s := by
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) h0
  have hs9 : s ≤ 9 / 10 := by rw [one_sub_tau] at hsle; exact hsle
  have hP := profileX_ge hs hs9
  have hP3 : (7 / 10) ^ 3 ≤ Work.OddEnvelope.profileX s ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hP 3
  have hE : |(x s - Work.OddEnvelope.profileX s) +
      s * (deriv x s - deriv Work.OddEnvelope.profileX s) - deriv h s| ≤ δ * (2 + s) := by
    have h3 : |s * (deriv x s - deriv Work.OddEnvelope.profileX s)| ≤ s * δ := by
      rw [abs_mul, abs_of_pos hs]
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt hs)
    have h4 : |-deriv h s| ≤ δ := by rwa [abs_neg]
    calc |(x s - Work.OddEnvelope.profileX s) +
          s * (deriv x s - deriv Work.OddEnvelope.profileX s) - deriv h s|
        = |((x s - Work.OddEnvelope.profileX s) +
            s * (deriv x s - deriv Work.OddEnvelope.profileX s)) + (-deriv h s)| := by ring_nf
      _ ≤ |(x s - Work.OddEnvelope.profileX s) +
            s * (deriv x s - deriv Work.OddEnvelope.profileX s)| + |-deriv h s| :=
          abs_add_le _ _
      _ ≤ (|x s - Work.OddEnvelope.profileX s| +
            |s * (deriv x s - deriv Work.OddEnvelope.profileX s)|) + |-deriv h s| := by
          linarith [abs_add_le (x s - Work.OddEnvelope.profileX s)
            (s * (deriv x s - deriv Work.OddEnvelope.profileX s))]
      _ ≤ δ + s * δ + δ := by linarith
      _ = δ * (2 + s) := by ring
  have hV : x s + s * deriv x s - deriv h s =
      Work.OddEnvelope.profileX s ^ 3 +
        ((x s - Work.OddEnvelope.profileX s) +
          s * (deriv x s - deriv Work.OddEnvelope.profileX s) - deriv h s) := by
    rw [← profileX_add s]; ring
  have hb : δ * (2 + s) ≤ 1 / 100 * (29 / 10) := by
    have hs2 : 2 + s ≤ 29 / 10 := by linarith
    calc δ * (2 + s) ≤ δ * (29 / 10) := mul_le_mul_of_nonneg_left hs2 hδ0
      _ ≤ (1 / 100) * (29 / 10) := mul_le_mul_of_nonneg_right hδ (by norm_num)
  rw [hV]
  linarith [(abs_le.mp hE).1, hP3, hb]

private lemma shape_y_close {y h : ℝ → ℝ} {δ s : ℝ} (hδ : δ ≤ 1 / 100) (hs : 0 < s)
    (hsle : s ≤ 1 - Work.OddEnvelope.tau)
    (h0 : |y s - Work.OddEnvelope.profileX s| ≤ δ)
    (h1 : |deriv y s - deriv Work.OddEnvelope.profileX s| ≤ δ)
    (h2 : |deriv (deriv y) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ δ)
    (h3 : |deriv h s| ≤ δ) (h4 : |deriv (deriv h) s| ≤ δ) :
    0 < 2 * (deriv y s) ^ 2 - y s * deriv (deriv y) s + deriv (deriv h) s * deriv y s
        - deriv h s * deriv (deriv y) s := by
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) h0
  have hs9 : s ≤ 9 / 10 := by rw [one_sub_tau] at hsle; exact hsle
  have hPpos : 0 < Work.OddEnvelope.profileX s := profileX_pos s
  have hPle : Work.OddEnvelope.profileX s ≤ 1 := profileX_le_one s
  have hPge : 7 / 10 ≤ Work.OddEnvelope.profileX s := profileX_ge hs hs9
  have hp : |deriv Work.OddEnvelope.profileX s| ≤ 9 / 10 := abs_deriv_profileX_le hs hs9
  have hpp : |deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 :=
    abs_deriv2_profileX_le (le_of_lt hs) hs9
  have hdya : |deriv y s| ≤ |deriv Work.OddEnvelope.profileX s| + δ :=
    le_trans (abs_le_abs_add (deriv y s) (deriv Work.OddEnvelope.profileX s)) (by linarith)
  have hddya : |deriv (deriv y) s| ≤ |deriv (deriv Work.OddEnvelope.profileX) s| + δ :=
    le_trans (abs_le_abs_add (deriv (deriv y) s) (deriv (deriv Work.OddEnvelope.profileX) s))
      (by linarith)
  -- estimates for the four summands
  have ht1 : |2 * ((deriv y s) ^ 2 - (deriv Work.OddEnvelope.profileX s) ^ 2)| ≤
      2 * (δ * (2 * |deriv Work.OddEnvelope.profileX s| + δ)) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (abs_sq_sub_sq_le h1 hδ0) (by norm_num)
  have ht2 : |y s * deriv (deriv y) s -
      Work.OddEnvelope.profileX s * deriv (deriv Work.OddEnvelope.profileX) s| ≤
      δ * (|deriv (deriv Work.OddEnvelope.profileX) s| + δ) +
        Work.OddEnvelope.profileX s * δ := by
    have hsplit : y s * deriv (deriv y) s -
        Work.OddEnvelope.profileX s * deriv (deriv Work.OddEnvelope.profileX) s =
        (y s - Work.OddEnvelope.profileX s) * deriv (deriv y) s +
          Work.OddEnvelope.profileX s *
            (deriv (deriv y) s - deriv (deriv Work.OddEnvelope.profileX) s) := by ring
    rw [hsplit]
    calc |(y s - Work.OddEnvelope.profileX s) * deriv (deriv y) s +
          Work.OddEnvelope.profileX s *
            (deriv (deriv y) s - deriv (deriv Work.OddEnvelope.profileX) s)|
        ≤ |(y s - Work.OddEnvelope.profileX s) * deriv (deriv y) s| +
          |Work.OddEnvelope.profileX s *
            (deriv (deriv y) s - deriv (deriv Work.OddEnvelope.profileX) s)| :=
          abs_add_le _ _
      _ = |y s - Work.OddEnvelope.profileX s| * |deriv (deriv y) s| +
          |Work.OddEnvelope.profileX s| *
            |deriv (deriv y) s - deriv (deriv Work.OddEnvelope.profileX) s| := by
          rw [abs_mul, abs_mul]
      _ ≤ δ * (|deriv (deriv Work.OddEnvelope.profileX) s| + δ) +
          Work.OddEnvelope.profileX s * δ := by
          rw [abs_of_pos hPpos]
          exact add_le_add (mul_le_mul h0 hddya (abs_nonneg _) hδ0)
            (mul_le_mul_of_nonneg_left h2 (le_of_lt hPpos))
  have ht3 : |deriv (deriv h) s * deriv y s| ≤ δ * (|deriv Work.OddEnvelope.profileX s| + δ) := by
    rw [abs_mul]
    exact mul_le_mul h4 hdya (abs_nonneg _) hδ0
  have ht4 : |deriv h s * deriv (deriv y) s| ≤
      δ * (|deriv (deriv Work.OddEnvelope.profileX) s| + δ) := by
    rw [abs_mul]
    exact mul_le_mul h3 hddya (abs_nonneg _) hδ0
  -- the difference from the unperturbed value
  set E := 2 * ((deriv y s) ^ 2 - (deriv Work.OddEnvelope.profileX s) ^ 2)
      - (y s * deriv (deriv y) s -
          Work.OddEnvelope.profileX s * deriv (deriv Work.OddEnvelope.profileX) s)
      + deriv (deriv h) s * deriv y s - deriv h s * deriv (deriv y) s with hEdef
  set C := 2 * (δ * (2 * |deriv Work.OddEnvelope.profileX s| + δ)) +
      (δ * (|deriv (deriv Work.OddEnvelope.profileX) s| + δ) +
        Work.OddEnvelope.profileX s * δ) +
      δ * (|deriv Work.OddEnvelope.profileX s| + δ) +
      δ * (|deriv (deriv Work.OddEnvelope.profileX) s| + δ) with hCdef
  have hCbound : C ≤ δ * (755 / 100) := by
    rw [hCdef]
    nlinarith [hp, hpp, hPle, hPpos, hδ0, hδ]
  have hEabs : |E| ≤ C := by
    rw [hEdef, hCdef]
    refine abs_le.mpr ⟨?_, ?_⟩ <;>
      linarith [(abs_le.mp ht1).1, (abs_le.mp ht1).2, (abs_le.mp ht2).1, (abs_le.mp ht2).2,
        (abs_le.mp ht3).1, (abs_le.mp ht3).2, (abs_le.mp ht4).1, (abs_le.mp ht4).2]
  have hEδ : |E| ≤ δ * (755 / 100) := le_trans hEabs hCbound
  have hδb : δ * (755 / 100) ≤ 755 / 10000 :=
    le_trans (mul_le_mul_of_nonneg_right hδ (by norm_num)) (by norm_num)
  have hV : 2 * (deriv y s) ^ 2 - y s * deriv (deriv y) s + deriv (deriv h) s * deriv y s
        - deriv h s * deriv (deriv y) s = Work.OddEnvelope.profileX s ^ 6 + E := by
    rw [hEdef, ← profileX_shape s]; ring
  have hP6 : (7 / 10) ^ 6 ≤ Work.OddEnvelope.profileX s ^ 6 :=
    pow_le_pow_left₀ (by norm_num) hPge 6
  rw [hV]
  have hb := (abs_le.mp hEδ).1
  nlinarith [hP6, hb, hδb]

private lemma shape_x_close {x h : ℝ → ℝ} {δ s : ℝ} (hδ : δ ≤ 1 / 100) (hs : 0 < s)
    (hsle : s ≤ 1 - Work.OddEnvelope.tau)
    (h0 : |x s - Work.OddEnvelope.profileX s| ≤ δ)
    (h1 : |deriv x s - deriv Work.OddEnvelope.profileX s| ≤ δ)
    (h2 : |deriv (deriv x) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ δ)
    (h3 : |deriv h s| ≤ δ) (h4 : |deriv (deriv h) s| ≤ δ) :
    0 < 2 * (deriv x s) ^ 2 - x s * deriv (deriv x) s - deriv (deriv h) s * deriv x s
        + deriv h s * deriv (deriv x) s := by
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) h0
  have hs9 : s ≤ 9 / 10 := by rw [one_sub_tau] at hsle; exact hsle
  have hPpos : 0 < Work.OddEnvelope.profileX s := profileX_pos s
  have hPle : Work.OddEnvelope.profileX s ≤ 1 := profileX_le_one s
  have hPge : 7 / 10 ≤ Work.OddEnvelope.profileX s := profileX_ge hs hs9
  have hp : |deriv Work.OddEnvelope.profileX s| ≤ 9 / 10 := abs_deriv_profileX_le hs hs9
  have hpp : |deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 :=
    abs_deriv2_profileX_le (le_of_lt hs) hs9
  have hdxa : |deriv x s| ≤ |deriv Work.OddEnvelope.profileX s| + δ :=
    le_trans (abs_le_abs_add (deriv x s) (deriv Work.OddEnvelope.profileX s)) (by linarith)
  have hddxa : |deriv (deriv x) s| ≤ |deriv (deriv Work.OddEnvelope.profileX) s| + δ :=
    le_trans (abs_le_abs_add (deriv (deriv x) s) (deriv (deriv Work.OddEnvelope.profileX) s))
      (by linarith)
  have ht1 : |2 * ((deriv x s) ^ 2 - (deriv Work.OddEnvelope.profileX s) ^ 2)| ≤
      2 * (δ * (2 * |deriv Work.OddEnvelope.profileX s| + δ)) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (abs_sq_sub_sq_le h1 hδ0) (by norm_num)
  have ht2 : |x s * deriv (deriv x) s -
      Work.OddEnvelope.profileX s * deriv (deriv Work.OddEnvelope.profileX) s| ≤
      δ * (|deriv (deriv Work.OddEnvelope.profileX) s| + δ) +
        Work.OddEnvelope.profileX s * δ := by
    have hsplit : x s * deriv (deriv x) s -
        Work.OddEnvelope.profileX s * deriv (deriv Work.OddEnvelope.profileX) s =
        (x s - Work.OddEnvelope.profileX s) * deriv (deriv x) s +
          Work.OddEnvelope.profileX s *
            (deriv (deriv x) s - deriv (deriv Work.OddEnvelope.profileX) s) := by ring
    rw [hsplit]
    calc |(x s - Work.OddEnvelope.profileX s) * deriv (deriv x) s +
          Work.OddEnvelope.profileX s *
            (deriv (deriv x) s - deriv (deriv Work.OddEnvelope.profileX) s)|
        ≤ |(x s - Work.OddEnvelope.profileX s) * deriv (deriv x) s| +
          |Work.OddEnvelope.profileX s *
            (deriv (deriv x) s - deriv (deriv Work.OddEnvelope.profileX) s)| :=
          abs_add_le _ _
      _ = |x s - Work.OddEnvelope.profileX s| * |deriv (deriv x) s| +
          |Work.OddEnvelope.profileX s| *
            |deriv (deriv x) s - deriv (deriv Work.OddEnvelope.profileX) s| := by
          rw [abs_mul, abs_mul]
      _ ≤ δ * (|deriv (deriv Work.OddEnvelope.profileX) s| + δ) +
          Work.OddEnvelope.profileX s * δ := by
          rw [abs_of_pos hPpos]
          exact add_le_add (mul_le_mul h0 hddxa (abs_nonneg _) hδ0)
            (mul_le_mul_of_nonneg_left h2 (le_of_lt hPpos))
  have ht3 : |deriv (deriv h) s * deriv x s| ≤ δ * (|deriv Work.OddEnvelope.profileX s| + δ) := by
    rw [abs_mul]
    exact mul_le_mul h4 hdxa (abs_nonneg _) hδ0
  have ht4 : |deriv h s * deriv (deriv x) s| ≤
      δ * (|deriv (deriv Work.OddEnvelope.profileX) s| + δ) := by
    rw [abs_mul]
    exact mul_le_mul h3 hddxa (abs_nonneg _) hδ0
  set E := 2 * ((deriv x s) ^ 2 - (deriv Work.OddEnvelope.profileX s) ^ 2)
      - (x s * deriv (deriv x) s -
          Work.OddEnvelope.profileX s * deriv (deriv Work.OddEnvelope.profileX) s)
      - deriv (deriv h) s * deriv x s + deriv h s * deriv (deriv x) s with hEdef
  set C := 2 * (δ * (2 * |deriv Work.OddEnvelope.profileX s| + δ)) +
      (δ * (|deriv (deriv Work.OddEnvelope.profileX) s| + δ) +
        Work.OddEnvelope.profileX s * δ) +
      δ * (|deriv Work.OddEnvelope.profileX s| + δ) +
      δ * (|deriv (deriv Work.OddEnvelope.profileX) s| + δ) with hCdef
  have hCbound : C ≤ δ * (755 / 100) := by
    rw [hCdef]
    nlinarith [hp, hpp, hPle, hPpos, hδ0, hδ]
  have hEabs : |E| ≤ C := by
    rw [hEdef, hCdef]
    refine abs_le.mpr ⟨?_, ?_⟩ <;>
      linarith [(abs_le.mp ht1).1, (abs_le.mp ht1).2, (abs_le.mp ht2).1, (abs_le.mp ht2).2,
        (abs_le.mp ht3).1, (abs_le.mp ht3).2, (abs_le.mp ht4).1, (abs_le.mp ht4).2]
  have hEδ : |E| ≤ δ * (755 / 100) := le_trans hEabs hCbound
  have hδb : δ * (755 / 100) ≤ 755 / 10000 :=
    le_trans (mul_le_mul_of_nonneg_right hδ (by norm_num)) (by norm_num)
  have hV : 2 * (deriv x s) ^ 2 - x s * deriv (deriv x) s - deriv (deriv h) s * deriv x s
        + deriv h s * deriv (deriv x) s = Work.OddEnvelope.profileX s ^ 6 + E := by
    rw [hEdef, ← profileX_shape s]; ring
  have hP6 : (7 / 10) ^ 6 ≤ Work.OddEnvelope.profileX s ^ 6 :=
    pow_le_pow_left₀ (by norm_num) hPge 6
  rw [hV]
  have hb := (abs_le.mp hEδ).1
  nlinarith [hP6, hb, hδb]

/-! ## The tail: beyond `1 - τ` the curve is the semicircle and `h` vanishes -/

private lemma tails_eq {h x y : ℝ → ℝ} {s : ℝ}
    (hs : 1 - Work.OddEnvelope.tau < s)
    (hh_supp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddEnvelope.tau) (1 - Work.OddEnvelope.tau))
    (hx_tail : ∀ t, 1 - Work.OddEnvelope.tau ≤ t → x t = Work.OddEnvelope.profileX t)
    (hy_tail : ∀ t, 1 - Work.OddEnvelope.tau ≤ t → y t = Work.OddEnvelope.profileX t) :
    x s = Work.OddEnvelope.profileX s ∧ y s = Work.OddEnvelope.profileX s ∧
    deriv x s = deriv Work.OddEnvelope.profileX s ∧
    deriv y s = deriv Work.OddEnvelope.profileX s ∧
    deriv (deriv x) s = deriv (deriv Work.OddEnvelope.profileX) s ∧
    deriv (deriv y) s = deriv (deriv Work.OddEnvelope.profileX) s ∧
    deriv h s = 0 ∧ deriv (deriv h) s = 0 := by
  have hzero : ∀ t, 1 - Work.OddEnvelope.tau < t → h t = 0 := by
    intro t ht
    by_contra hne
    have hmem := hh_supp (Function.mem_support.mpr hne)
    exact absurd hmem.2 (not_le.mpr ht)
  have hxev : x =ᶠ[𝓝 s] Work.OddEnvelope.profileX :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hs) (fun t ht => hx_tail t (le_of_lt ht))
  have hyev : y =ᶠ[𝓝 s] Work.OddEnvelope.profileX :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hs) (fun t ht => hy_tail t (le_of_lt ht))
  have hev : h =ᶠ[𝓝 s] (0 : ℝ → ℝ) :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hs) (fun t ht => hzero t ht)
  have hdev : deriv h =ᶠ[𝓝 s] (0 : ℝ → ℝ) := by
    filter_upwards [hev.deriv] with t ht
    rw [ht]; exact deriv_const t 0
  refine ⟨hx_tail s (le_of_lt hs), hy_tail s (le_of_lt hs), hxev.deriv_eq, hyev.deriv_eq,
    (hxev.deriv).deriv_eq, (hyev.deriv).deriv_eq, ?_, ?_⟩
  · rw [hev.deriv_eq]; exact deriv_const s 0
  · rw [hdev.deriv_eq]; exact deriv_const s 0
theorem isEnvelopeCurveFree_of_close {h x y : ℝ → ℝ} {δ : ℝ} (hδ : δ ≤ 1 / 100)
    (hx_smooth : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) x (Set.Ioi 0))
    (hy_smooth : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) y (Set.Ioi 0))
    (hh_smooth : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) h (Set.Ioi 0))
    (hx_deriv : ∀ s, 0 < s → deriv x s < 0) (hy_deriv : ∀ s, 0 < s → deriv y s < 0)
    (hx_free : ∃ a : ℝ, 0 < a ∧ Filter.Tendsto x (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds a))
    (hy_free : ∃ b : ℝ, 0 < b ∧ Filter.Tendsto y (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds b))
    (hx_tail : ∀ s, 1 - Work.OddEnvelope.tau ≤ s → x s = Work.OddEnvelope.profileX s)
    (hy_tail : ∀ s, 1 - Work.OddEnvelope.tau ≤ s → y s = Work.OddEnvelope.profileX s)
    (hh_zero : h 0 = 0)
    (hh_supp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddEnvelope.tau) (1 - Work.OddEnvelope.tau))
    (hx_close : ∀ s, 0 < s → |x s - Work.OddEnvelope.profileX s| ≤ δ ∧
      |deriv x s - deriv Work.OddEnvelope.profileX s| ≤ δ ∧
      |deriv (deriv x) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ δ)
    (hy_close : ∀ s, 0 < s → |y s - Work.OddEnvelope.profileX s| ≤ δ ∧
      |deriv y s - deriv Work.OddEnvelope.profileX s| ≤ δ ∧
      |deriv (deriv y) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ δ)
    (hh_close : ∀ s, |h s| ≤ δ ∧ |deriv h s| ≤ δ ∧ |deriv (deriv h) s| ≤ δ) :
    Work.OddCurve.Free.IsEnvelopeCurveFree h x y := by
  refine ⟨hh_smooth, hx_smooth, hy_smooth, hh_zero, hh_supp, hx_deriv, hy_deriv,
    hx_free, hy_free, hx_tail, hy_tail, ?_, ?_, ?_, ?_⟩
  · intro s hs
    by_cases hsle : s ≤ 1 - Work.OddEnvelope.tau
    · exact mono_y_close hδ hs hsle (hy_close s hs).1 (hy_close s hs).2.1 (hh_close s).2.1
    · push Not at hsle
      obtain ⟨-, hys, -, hdys, -, -, hdh, -⟩ := tails_eq hsle hh_supp hx_tail hy_tail
      rw [hys, hdys, hdh, profileX_add]
      simpa using pow_pos (profileX_pos s) 3
  · intro s hs
    by_cases hsle : s ≤ 1 - Work.OddEnvelope.tau
    · exact mono_x_close hδ hs hsle (hx_close s hs).1 (hx_close s hs).2.1 (hh_close s).2.1
    · push Not at hsle
      obtain ⟨hxs, -, hdxs, -, -, -, hdh, -⟩ := tails_eq hsle hh_supp hx_tail hy_tail
      rw [hxs, hdxs, hdh, profileX_add]
      simpa using pow_pos (profileX_pos s) 3
  · intro s hs
    by_cases hsle : s ≤ 1 - Work.OddEnvelope.tau
    · exact shape_y_close hδ hs hsle (hy_close s hs).1 (hy_close s hs).2.1 (hy_close s hs).2.2
        (hh_close s).2.1 (hh_close s).2.2
    · push Not at hsle
      obtain ⟨-, hys, -, hdys, -, hddys, hdh2, hddh2⟩ :=
        tails_eq hsle hh_supp hx_tail hy_tail
      rw [hys, hdys, hddys, hdh2, hddh2, profileX_shape]
      simp only [zero_mul, add_zero, sub_zero]
      exact pow_pos (profileX_pos s) 6
  · intro s hs
    by_cases hsle : s ≤ 1 - Work.OddEnvelope.tau
    · exact shape_x_close hδ hs hsle (hx_close s hs).1 (hx_close s hs).2.1 (hx_close s hs).2.2
        (hh_close s).2.1 (hh_close s).2.2
    · push Not at hsle
      obtain ⟨hxs, -, hdxs, -, hddxs, -, hdh2, hddh2⟩ :=
        tails_eq hsle hh_supp hx_tail hy_tail
      rw [hxs, hdxs, hddxs, hdh2, hddh2, profileX_shape]
      simp only [zero_mul, add_zero, sub_zero]
      exact pow_pos (profileX_pos s) 6

end

end Work.OddEnvelope.Close
