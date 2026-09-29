import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_add_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
import Submission.Work.TMC7Core.Cocycle.intervalIntegrable_log_frob
import Submission.Work.TMC7Core.Cocycle.continuous_frob_iterC
import Submission.Work.TMC7Core.Lyap.continuous_lyapAvg_energy
import Submission.Work.TMC7Core.Scale.frob_tmC_le
import Submission.Work.TMC7Core.Scale.frob_tmC_sub_le
import Submission.Work.TMC7Core.Scale.frob_matProd_le
import Submission.Work.TMC7Core.Scale.frob_matProd_sub_le

open MeasureTheory Filter Topology Set
open Work.TMC7Core
open Work.TMC7Core.Cocycle
open Work.TMC7Core.Lyap

noncomputable section

namespace Work.TMC7Core.Scale


theorem frob_neg (A : Matrix (Fin 2) (Fin 2) ℂ) : frob (-A) = frob A := by
  simp only [frob, Matrix.neg_apply, norm_neg]

theorem abs_frob_sub_le (A B : Matrix (Fin 2) (Fin 2) ℂ) : |frob A - frob B| ≤ frob (A - B) := by
  have h1 : frob A ≤ frob B + frob (A - B) := by
    have h := frob_add_le B (A - B)
    rwa [add_sub_cancel] at h
  have h2 : frob B ≤ frob A + frob (A - B) := by
    have h := frob_add_le A (-(A - B))
    have hneg : frob (-(A - B)) = frob (A - B) := frob_neg _
    have heq : A + -(A - B) = B := by abel
    rw [heq, hneg] at h
    exact h
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem abs_log_sub_log_le (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| := by
  have key : ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → x ≤ y → Real.log y - Real.log x ≤ y - x := by
    intro x y hx hy hxy
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
    have hxy0 : 0 < y / x := div_pos hy0 hx0
    rw [← Real.log_div (ne_of_gt hy0) (ne_of_gt hx0)]
    have h1 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos hxy0
    have hxne : x ≠ 0 := ne_of_gt hx0
    have h2 : y / x - 1 = (y - x) / x := by field_simp
    rw [h2] at h1
    have h3 : (y - x) / x ≤ y - x := by
      rw [div_le_iff₀ hx0]
      nlinarith [hxy, hx]
    linarith
  rcases le_total a b with h | h
  · have hl : Real.log a ≤ Real.log b := Real.log_le_log (lt_of_lt_of_le one_pos ha) h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith [key a b ha hb h]
  · have hl : Real.log b ≤ Real.log a := Real.log_le_log (lt_of_lt_of_le one_pos hb) h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith [key b a hb ha h]

theorem matProd_congr {A B : ℕ → Matrix (Fin 2) (Fin 2) ℂ} {n : ℕ}
    (h : ∀ j < n, A j = B j) : matProd A n = matProd B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [matProd_succ, matProd_succ, ih (fun j hj => h j (Nat.lt_succ_of_lt hj)),
      h n (Nat.lt_succ_self n)]

theorem one_le_frob_iterC (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    1 ≤ frob (iterC α lam E n x) := by
  have h := frob_sqrt_two_le_of_det_one (det_iterC α lam E n x)
  have h2 : (1:ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  linarith

noncomputable def lipM (lam R : ℝ) : ℝ := Real.sqrt ((R + 2 * |lam|) ^ 2 + 2) + 1
noncomputable def lipL (lam : ℝ) : ℝ := max 1 (4 * Real.pi * |lam|)
noncomputable def lipD (lam : ℝ) (N : ℕ) : ℝ := lipL lam * (N : ℝ)
noncomputable def lipC (lam : ℝ) (N : ℕ) (R : ℝ) : ℝ :=
  (N : ℝ) * (lipM lam R) ^ N * lipD lam N
noncomputable def lipK (lam : ℝ) (N : ℕ) (R : ℝ) : ℝ := max 1 (lipC lam N R)

theorem lipM_ge_one (lam R : ℝ) : 1 ≤ lipM lam R := by
  rw [lipM]; linarith [Real.sqrt_nonneg ((R + 2 * |lam|) ^ 2 + 2)]

theorem iterC_diff_le (lam R : ℝ) (N : ℕ) (hN : 1 ≤ N) (α E α' E' x : ℝ)
    (hE : |E| ≤ R) (hE' : |E'| ≤ R) :
    frob (iterC α lam (E:ℂ) N x - iterC α' lam (E':ℂ) N x) ≤
      lipC lam N R * (|α - α'| + |E - E'|) := by
  set M := lipM lam R with hMdef
  set L := lipL lam with hLdef
  set D := lipD lam N with hDdef
  set e := |α - α'| + |E - E'| with hedef
  have he0 : 0 ≤ e := by positivity
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hM1 : 1 ≤ M := by rw [hMdef]; exact lipM_ge_one lam R
  have hM2 : Real.sqrt 2 ≤ M := by
    rw [hMdef, lipM]
    have h2 : (2:ℝ) ≤ (R + 2 * |lam|) ^ 2 + 2 := by nlinarith [sq_nonneg (R + 2 * |lam|)]
    linarith [Real.sqrt_le_sqrt h2]
  have hL0 : 0 ≤ L := by rw [hLdef, lipL]; exact le_trans zero_le_one (le_max_left _ _)
  have hD0 : 0 ≤ D := by rw [hDdef, lipD]; exact mul_nonneg hL0 (by positivity)
  set A : ℕ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun j => tmC lam (E:ℂ) (x + min ((j:ℝ)) ((N:ℝ)) * α) with hAdef
  set B : ℕ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun j => tmC lam (E':ℂ) (x + min ((j:ℝ)) ((N:ℝ)) * α') with hBdef
  have hMA : matProd A N = iterC α lam (E:ℂ) N x := by
    rw [iterC_eq_matProd]
    apply matProd_congr
    intro j hj
    simp only [hAdef]
    rw [min_eq_left (by exact_mod_cast (le_of_lt hj) : (j:ℝ) ≤ (N:ℝ))]
  have hMB : matProd B N = iterC α' lam (E':ℂ) N x := by
    rw [iterC_eq_matProd]
    apply matProd_congr
    intro j hj
    simp only [hBdef]
    rw [min_eq_left (by exact_mod_cast (le_of_lt hj) : (j:ℝ) ≤ (N:ℝ))]
  have hAb : ∀ j, frob (A j) ≤ M := by
    intro j
    simp only [hAdef]
    have h1 := frob_tmC_le lam (E:ℂ) (x + min ((j:ℝ)) ((N:ℝ)) * α)
    have hnormE : ‖(E:ℂ)‖ = |E| := RCLike.norm_ofReal E
    rw [hnormE] at h1
    have h2 : |E| + 2 * |lam| ≤ R + 2 * |lam| := by linarith
    have h3 : Real.sqrt ((|E| + 2 * |lam|) ^ 2 + 2) ≤ Real.sqrt ((R + 2 * |lam|) ^ 2 + 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [h2, abs_nonneg E, abs_nonneg lam]
    have h4 : Real.sqrt ((R + 2 * |lam|) ^ 2 + 2) ≤ M := by
      rw [hMdef, lipM]; linarith
    linarith
  have hBb : ∀ j, frob (B j) ≤ M := by
    intro j
    simp only [hBdef]
    have h1 := frob_tmC_le lam (E':ℂ) (x + min ((j:ℝ)) ((N:ℝ)) * α')
    have hnormE' : ‖(E':ℂ)‖ = |E'| := RCLike.norm_ofReal E'
    rw [hnormE'] at h1
    have h2 : |E'| + 2 * |lam| ≤ R + 2 * |lam| := by linarith
    have h3 : Real.sqrt ((|E'| + 2 * |lam|) ^ 2 + 2) ≤ Real.sqrt ((R + 2 * |lam|) ^ 2 + 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [h2, abs_nonneg E', abs_nonneg lam]
    have h4 : Real.sqrt ((R + 2 * |lam|) ^ 2 + 2) ≤ M := by
      rw [hMdef, lipM]; linarith
    linarith
  have hABb : ∀ j, frob (A j - B j) ≤ D * e := by
    intro j
    simp only [hAdef, hBdef]
    have h1 := frob_tmC_sub_le lam (E:ℂ) (E':ℂ)
      (x + min ((j:ℝ)) ((N:ℝ)) * α) (x + min ((j:ℝ)) ((N:ℝ)) * α')
    have hnorm : ‖(E:ℂ) - (E':ℂ)‖ = |E - E'| := by
      rw [← Complex.ofReal_sub]
      exact RCLike.norm_ofReal (E - E')
    have harg : |(x + min ((j:ℝ)) ((N:ℝ)) * α) - (x + min ((j:ℝ)) ((N:ℝ)) * α')|
        = min ((j:ℝ)) ((N:ℝ)) * |α - α'| := by
      have hh : (x + min ((j:ℝ)) ((N:ℝ)) * α) - (x + min ((j:ℝ)) ((N:ℝ)) * α')
          = min ((j:ℝ)) ((N:ℝ)) * (α - α') := by ring
      rw [hh, abs_mul, abs_of_nonneg (le_min (by positivity) (by positivity))]
    have hminN : min ((j:ℝ)) ((N:ℝ)) ≤ (N:ℝ) := min_le_right _ _
    have hmin0 : 0 ≤ min ((j:ℝ)) ((N:ℝ)) := le_min (by positivity) (by positivity)
    have hstep : ‖(E:ℂ) - (E':ℂ)‖
        + |(x + min ((j:ℝ)) ((N:ℝ)) * α) - (x + min ((j:ℝ)) ((N:ℝ)) * α')| ≤ (N:ℝ) * e := by
      rw [hnorm, harg, hedef]
      have hA' : |E - E'| ≤ (N:ℝ) * |E - E'| := by nlinarith [abs_nonneg (E - E'), hN1]
      have hB' : min ((j:ℝ)) ((N:ℝ)) * |α - α'| ≤ (N:ℝ) * |α - α'| := by
        nlinarith [abs_nonneg (α - α'), hminN, hmin0]
      nlinarith
    calc frob (tmC lam (E:ℂ) (x + min ((j:ℝ)) ((N:ℝ)) * α) - tmC lam (E':ℂ) (x + min ((j:ℝ)) ((N:ℝ)) * α'))
        ≤ max 1 (4 * Real.pi * |lam|) * (‖(E:ℂ) - (E':ℂ)‖ + |(x + min ((j:ℝ)) ((N:ℝ)) * α) - (x + min ((j:ℝ)) ((N:ℝ)) * α')|) := h1
      _ ≤ max 1 (4 * Real.pi * |lam|) * ((N:ℝ) * e) := by
            apply mul_le_mul_of_nonneg_left hstep
            positivity
      _ = D * e := by rw [hDdef, lipD, lipL]; ring
  have hres := frob_matProd_sub_le A B M (D * e) hM2 (by positivity) hAb hBb hABb N
  rw [hMA, hMB] at hres
  calc frob (iterC α lam (E:ℂ) N x - iterC α' lam (E':ℂ) N x)
      ≤ (N:ℝ) * M ^ N * (D * e) := hres
    _ = lipC lam N R * e := by rw [lipC, hMdef, hDdef, lipD]; ring

theorem log_frob_iterC_diff_le (lam R : ℝ) (N : ℕ) (hN : 1 ≤ N) (α E α' E' x : ℝ)
    (hE : |E| ≤ R) (hE' : |E'| ≤ R) :
    |Real.log (frob (iterC α lam (E:ℂ) N x)) - Real.log (frob (iterC α' lam (E':ℂ) N x))|
      ≤ lipC lam N R * (|α - α'| + |E - E'|) := by
  have h1 : 1 ≤ frob (iterC α lam (E:ℂ) N x) := one_le_frob_iterC α lam (E:ℂ) N x
  have h2 : 1 ≤ frob (iterC α' lam (E':ℂ) N x) := one_le_frob_iterC α' lam (E':ℂ) N x
  calc |Real.log (frob (iterC α lam (E:ℂ) N x)) - Real.log (frob (iterC α' lam (E':ℂ) N x))|
      ≤ |frob (iterC α lam (E:ℂ) N x) - frob (iterC α' lam (E':ℂ) N x)| :=
        abs_log_sub_log_le _ _ h1 h2
    _ ≤ frob (iterC α lam (E:ℂ) N x - iterC α' lam (E':ℂ) N x) := abs_frob_sub_le _ _
    _ ≤ lipC lam N R * (|α - α'| + |E - E'|) := iterC_diff_le lam R N hN α E α' E' x hE hE'

theorem lyapAvg_lipschitz (lam : ℝ) (N : ℕ) (hN : 1 ≤ N) (R : ℝ) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ α E α' E' : ℝ, |α| ≤ R → |E| ≤ R → |α'| ≤ R → |E'| ≤ R →
      |lyapAvg α lam (E : ℂ) N - lyapAvg α' lam (E' : ℂ) N| ≤ K * (|α - α'| + |E - E'|) := by
  refine ⟨lipK lam N R, ?_, ?_⟩
  · rw [lipK]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · intro α E α' E' hα hE hα' hE'
    set e : ℝ := |α - α'| + |E - E'| with hedef
    have he0 : 0 ≤ e := by positivity
    have hNpos : (0:ℝ) < (N:ℝ) := by
      exact_mod_cast (show 0 < N from lt_of_lt_of_le Nat.zero_lt_one hN)
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hpt : ∀ x : ℝ,
        |Real.log (frob (iterC α lam (E:ℂ) N x)) - Real.log (frob (iterC α' lam (E':ℂ) N x))|
          ≤ lipC lam N R * e := by
      intro x
      rw [hedef]
      exact log_frob_iterC_diff_le lam R N hN α E α' E' x hE hE'
    have hcont1 : Continuous (fun x : ℝ => Real.log (frob (iterC α lam (E:ℂ) N x))) :=
      Continuous.log (continuous_frob_iterC α lam (E:ℂ) N)
        (fun x => ne_of_gt (frob_iterC_pos α lam (E:ℂ) N x))
    have hcont2 : Continuous (fun x : ℝ => Real.log (frob (iterC α' lam (E':ℂ) N x))) :=
      Continuous.log (continuous_frob_iterC α' lam (E':ℂ) N)
        (fun x => ne_of_gt (frob_iterC_pos α' lam (E':ℂ) N x))
    have hI1 : IntervalIntegrable (fun x : ℝ => Real.log (frob (iterC α lam (E:ℂ) N x)))
        volume (0:ℝ) 1 := intervalIntegrable_log_frob α lam (E:ℂ) N
    have hI2 : IntervalIntegrable (fun x : ℝ => Real.log (frob (iterC α' lam (E':ℂ) N x)))
        volume (0:ℝ) 1 := intervalIntegrable_log_frob α' lam (E':ℂ) N
    have hsub : (∫ x in (0:ℝ)..1, (Real.log (frob (iterC α lam (E:ℂ) N x))
          - Real.log (frob (iterC α' lam (E':ℂ) N x))))
        = (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam (E:ℂ) N x)))
          - (∫ x in (0:ℝ)..1, Real.log (frob (iterC α' lam (E':ℂ) N x))) :=
      intervalIntegral.integral_sub hI1 hI2
    have hlyap : lyapAvg α lam (E:ℂ) N - lyapAvg α' lam (E':ℂ) N
        = (∫ x in (0:ℝ)..1, (Real.log (frob (iterC α lam (E:ℂ) N x))
            - Real.log (frob (iterC α' lam (E':ℂ) N x)))) / (N:ℝ) := by
      rw [lyapAvg, lyapAvg, div_sub_div_same, ← hsub]
    have hmain : |lyapAvg α lam (E:ℂ) N - lyapAvg α' lam (E':ℂ) N|
        ≤ (∫ x in (0:ℝ)..1, |Real.log (frob (iterC α lam (E:ℂ) N x))
            - Real.log (frob (iterC α' lam (E':ℂ) N x))|) / (N:ℝ) := by
      rw [hlyap, abs_div, abs_of_pos hNpos]
      apply div_le_div_of_nonneg_right _ (le_of_lt hNpos)
      exact intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    have hmono : (∫ x in (0:ℝ)..1, |Real.log (frob (iterC α lam (E:ℂ) N x))
            - Real.log (frob (iterC α' lam (E':ℂ) N x))|)
        ≤ ∫ x in (0:ℝ)..1, (lipC lam N R * e) := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const ?_
      · exact ((hcont1.sub hcont2).abs).intervalIntegrable 0 1
      · intro x _; exact hpt x
    have hintc : (∫ x in (0:ℝ)..1, (lipC lam N R * e)) = lipC lam N R * e := by
      rw [intervalIntegral.integral_const]; simp
    have hC0 : 0 ≤ lipC lam N R := by
      rw [lipC, lipD, lipL]
      apply mul_nonneg
      · exact mul_nonneg (by positivity) (pow_nonneg (le_trans zero_le_one (lipM_ge_one lam R)) N)
      · exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (by positivity)
    calc |lyapAvg α lam (E:ℂ) N - lyapAvg α' lam (E':ℂ) N|
        ≤ (∫ x in (0:ℝ)..1, |Real.log (frob (iterC α lam (E:ℂ) N x))
            - Real.log (frob (iterC α' lam (E':ℂ) N x))|) / (N:ℝ) := hmain
      _ ≤ (∫ x in (0:ℝ)..1, (lipC lam N R * e)) / (N:ℝ) :=
            div_le_div_of_nonneg_right hmono (le_of_lt hNpos)
      _ = (lipC lam N R * e) / (N:ℝ) := by rw [hintc]
      _ ≤ lipK lam N R * e := by
            rw [lipK]
            have h1 : (lipC lam N R * e) / (N:ℝ) ≤ lipC lam N R * e := by
              rw [div_le_iff₀ hNpos]
              simpa using mul_le_mul_of_nonneg_left hN1 (mul_nonneg hC0 he0)
            have h2 : lipC lam N R * e ≤ max 1 (lipC lam N R) * e :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) he0
            linarith

end Work.TMC7Core.Scale
