import Mathlib
import Submission.Work.Cert.Spec

/-!
# Grid drift of the Theorem-A contour certificate

The certificate (`Work.Cert.Conj2Cert`) walks the circle `|z| = Rk k/S` in `4096` integer grid
steps `E j = (E j).1 + I·(E j).2`, each step produced by `gridStep`, i.e.
`(E (j+1)).1 ≈ (E j).1·WR − (E j).2·WI`, `(E (j+1)).2 ≈ (E j).1·WI + (E j).2·WR` (floors of the
products by `S`, tolerance `GTOL = 8`).  This file proves that the grid points stay within
`65536/S` of the exact circle points `(Rk k/S)·e^{2πi j/4096}`, which is what the arc-covering
argument (`ArcCover`) needs.

The elementary proof is a two-term recurrence: with `z_j = cx (E j).1 (E j).2`,
`u_j = (Rk k/S)·rot (j/4096)`, `W = cx WR WI`, `ρ = rot (1/4096)`,
`z_{j+1} − u_{j+1} = (z_{j+1} − z_j W) + z_j (W − ρ) + (z_j − u_j) ρ`, so
`δ_{j+1} ≤ g_j + (Rk k/S + δ_j)·(2/S) + δ_j`, where the step term `g_j = ‖z_{j+1} − z_j W‖` is
bounded by `27/(2S)` from the integer identities
`(E (j+1)).1·S − ((E j).1·WR − (E j).2·WI) = S·d₁ − r₁ + r₂` and
`(E (j+1)).2·S − ((E j).1·WI + (E j).2·WR) = S·d₂ − r₃ − r₄`
(`d₁, d₂` the `gridStep` discrepancies `≤ 8`, `r_i ∈ [0, S−1]` the divisions remainders), giving
`‖(9S) + (10S)I‖/S² = √181/S < 13.5/S`.  The `16/S`-per-step budget then closes since
`32·4096/S ≤ 1/2`, and `16·4096 = 65536`.
-/

namespace Work.Cert.ACore

open Submission.CDTPlan

/-! ## Elementary facts on `rot t = e^{2πit}` -/

lemma rot_zero : rot 0 = 1 := by simp [rot]

lemma rot_add (a b : ℝ) : rot (a + b) = rot a * rot b := by
  simp only [rot, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_rot (t : ℝ) : ‖rot t‖ = 1 := by
  rw [rot, Complex.norm_exp]
  simp

/-- The scale `S` is positive. -/
lemma S_pos_real : (0 : ℝ) < (Work.Cert.S : ℝ) := by norm_num [Work.Cert.S]

/-- The norm of a nonnegative real, viewed in `ℂ`. -/
lemma norm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖((r : ℝ) : ℂ)‖ = r := by
  have hsq : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  calc ‖((r : ℝ) : ℂ)‖ = Real.sqrt (‖((r : ℝ) : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [hsq]
    _ = |r| := Real.sqrt_sq_eq_abs r
    _ = r := abs_of_nonneg hr

/-- `(Rk k/S)·rot ((j+1)/4096) = ((Rk k/S)·rot (j/4096))·rot (1/4096)`. -/
lemma rot_step (k n : ℕ) :
    ((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot (((n + 1 : ℕ) : ℝ) / 4096)
      = (((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot ((n : ℝ) / 4096))
          * rot (1 / 4096) := by
  rw [show (((n + 1 : ℕ) : ℝ)) / 4096 = (n : ℝ) / 4096 + 1 / 4096 by push_cast; ring]
  rw [rot_add]
  ring

/-- `Rk k ≥ 0` and `Rk k ≤ S` for the three circles of the certificate. -/
lemma Rk_facts (k : ℕ) (hk : k ≤ 2) :
    0 ≤ Work.Cert.Rk k ∧ (Work.Cert.Rk k : ℝ) ≤ (Work.Cert.S : ℝ) := by
  interval_cases k <;> norm_num [Work.Cert.Rk, Work.Cert.fdiv, Work.Cert.S]

/-! ## The complex-mantissa algebra -/

/-- `cx x y = (x + y·I)/S`. -/
lemma cx_eq_div (x y : ℤ) :
    Work.Cert.cx x y = ((x : ℂ) + (y : ℂ) * Complex.I) / (Work.Cert.S : ℂ) := by
  simp only [Work.Cert.cx]
  push_cast
  ring

/-- Difference of a scaled point and a product of scaled points, with integer real and imaginary
parts: `cx e f − cx a b · cx c d = ((eS − (ac − bd)) + (fS − (ad + bc))·I)/S²`. -/
lemma cx_step_eq (a b c d e f : ℤ) :
    Work.Cert.cx e f - Work.Cert.cx a b * Work.Cert.cx c d
      = (((e * Work.Cert.S - (a * c - b * d) : ℤ) : ℂ) +
          (((f * Work.Cert.S - (a * d + b * c) : ℤ)) : ℂ) * Complex.I) / (Work.Cert.S : ℂ) ^ 2 := by
  simp only [Work.Cert.cx]
  push_cast
  have hS : (Work.Cert.S : ℂ) ≠ 0 := by norm_num [Work.Cert.S]
  field_simp
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

/-- `√(A² + B²) ≤ 13.5·S ≤ (27/2)·S` for `|A| ≤ 9S`, `|B| ≤ 10S`. -/
lemma norm_int_le (A B : ℤ) (hA : |A| ≤ 9 * Work.Cert.S) (hB : |B| ≤ 10 * Work.Cert.S) :
    ‖(A : ℂ) + (B : ℂ) * Complex.I‖ ≤ (27 / 2) * (Work.Cert.S : ℝ) := by
  have hS : (0 : ℝ) < (Work.Cert.S : ℝ) := S_pos_real
  have hns : Complex.normSq ((A : ℂ) + (B : ℂ) * Complex.I) = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 := by
    rw [Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    ring
  rw [Complex.normSq_eq_norm_sq] at hns
  have hA' : |(A : ℝ)| ≤ 9 * (Work.Cert.S : ℝ) := by exact_mod_cast hA
  have hB' : |(B : ℝ)| ≤ 10 * (Work.Cert.S : ℝ) := by exact_mod_cast hB
  have hx2 : (A : ℝ) ^ 2 ≤ (9 * (Work.Cert.S : ℝ)) ^ 2 := by nlinarith [abs_le.mp hA']
  have hy2 : (B : ℝ) ^ 2 ≤ (10 * (Work.Cert.S : ℝ)) ^ 2 := by nlinarith [abs_le.mp hB']
  have hsum : (A : ℝ) ^ 2 + (B : ℝ) ^ 2 ≤ ((27 / 2) * (Work.Cert.S : ℝ)) ^ 2 := by
    nlinarith [hS]
  calc ‖(A : ℂ) + (B : ℂ) * Complex.I‖ = Real.sqrt ((A : ℝ) ^ 2 + (B : ℝ) ^ 2) := by
        rw [← hns, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (((27 / 2) * (Work.Cert.S : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = (27 / 2) * (Work.Cert.S : ℝ) := Real.sqrt_sq (by positivity)

lemma iabs_eq (a : ℤ) : Work.Cert.iabs a = |a| := by
  simp only [Work.Cert.iabs]
  split
  next h => rw [abs_of_neg h]
  next h => rw [abs_of_nonneg (not_lt.mp h)]

/-! ## The one-step bound -/

/-- `gridStep ex ey nx ny` (tolerance `GTOL = 8`) implies `‖cx nx ny − cx ex ey · cx WR WI‖ ≤ 27/(2S)`.

The two mantissas of `S²·(cx nx ny − cx ex ey · cx WR WI)` are `nx·S − u` and `ny·S − v` with
`u = ex·WR − ey·WI`, `v = ex·WI + ey·WR`; writing `ex·WR = S·md ex WR + r₁`, … for the four
division remainders `r_i ∈ [0, S−1]` gives `nx·S − u = S·d₁ − r₁ + r₂` (`d₁ = nx − cmr ex ey WR WI`)
and `ny·S − v = S·d₂ − r₃ − r₄`, whence `|nx·S − u| ≤ 9S − 1` and `|ny·S − v| ≤ 10S − 2 < 10S`,
and the modulus is at most `√181·S < 13.5·S`. -/
lemma gridStep_norm_le (ex ey nx ny : ℤ) (h : Work.Cert.gridStep ex ey nx ny = true) :
    ‖Work.Cert.cx nx ny - Work.Cert.cx ex ey * Work.Cert.cx Work.Cert.WR Work.Cert.WI‖
      ≤ 27 / (2 * (Work.Cert.S : ℝ)) := by
  have hS : (0 : ℝ) < (Work.Cert.S : ℝ) := S_pos_real
  have hSpos : (0 : ℤ) < Work.Cert.S := by norm_num [Work.Cert.S]
  have hmem := h
  simp only [Work.Cert.gridStep, Bool.and_eq_true, decide_eq_true_eq] at hmem
  have hd1 : |nx - Work.Cert.cmr ex ey Work.Cert.WR Work.Cert.WI| ≤ 8 := by
    rw [← iabs_eq]; exact hmem.1
  have hd2 : |ny - Work.Cert.cmi ex ey Work.Cert.WR Work.Cert.WI| ≤ 8 := by
    rw [← iabs_eq]; exact hmem.2
  have h1 : Work.Cert.S * Work.Cert.md ex Work.Cert.WR + (ex * Work.Cert.WR) % Work.Cert.S
      = ex * Work.Cert.WR := by
    simp only [Work.Cert.md, Work.Cert.fdiv]
    exact Int.mul_ediv_add_emod (ex * Work.Cert.WR) Work.Cert.S
  have h2 : Work.Cert.S * Work.Cert.md ey Work.Cert.WI + (ey * Work.Cert.WI) % Work.Cert.S
      = ey * Work.Cert.WI := by
    simp only [Work.Cert.md, Work.Cert.fdiv]
    exact Int.mul_ediv_add_emod (ey * Work.Cert.WI) Work.Cert.S
  have h3 : Work.Cert.S * Work.Cert.md ex Work.Cert.WI + (ex * Work.Cert.WI) % Work.Cert.S
      = ex * Work.Cert.WI := by
    simp only [Work.Cert.md, Work.Cert.fdiv]
    exact Int.mul_ediv_add_emod (ex * Work.Cert.WI) Work.Cert.S
  have h4 : Work.Cert.S * Work.Cert.md ey Work.Cert.WR + (ey * Work.Cert.WR) % Work.Cert.S
      = ey * Work.Cert.WR := by
    simp only [Work.Cert.md, Work.Cert.fdiv]
    exact Int.mul_ediv_add_emod (ey * Work.Cert.WR) Work.Cert.S
  have e1 : nx * Work.Cert.S - (ex * Work.Cert.WR - ey * Work.Cert.WI)
      = Work.Cert.S * (nx - Work.Cert.cmr ex ey Work.Cert.WR Work.Cert.WI)
        - (ex * Work.Cert.WR) % Work.Cert.S + (ey * Work.Cert.WI) % Work.Cert.S := by
    simp only [Work.Cert.cmr]
    linarith
  have e2 : ny * Work.Cert.S - (ex * Work.Cert.WI + ey * Work.Cert.WR)
      = Work.Cert.S * (ny - Work.Cert.cmi ex ey Work.Cert.WR Work.Cert.WI)
        - (ex * Work.Cert.WI) % Work.Cert.S - (ey * Work.Cert.WR) % Work.Cert.S := by
    simp only [Work.Cert.cmi]
    linarith
  have b1 : |Work.Cert.S * (nx - Work.Cert.cmr ex ey Work.Cert.WR Work.Cert.WI)| ≤ 8 * Work.Cert.S := by
    rw [abs_mul, abs_of_nonneg (le_of_lt hSpos)]
    exact mul_le_mul_of_nonneg_left hd1 (le_of_lt hSpos)
  have b2 : |-((ex * Work.Cert.WR) % Work.Cert.S) + (ey * Work.Cert.WI) % Work.Cert.S|
      ≤ Work.Cert.S - 1 := by
    rw [abs_le]
    constructor
    · have ha := Int.emod_nonneg (ey * Work.Cert.WI) (by norm_num [Work.Cert.S] : Work.Cert.S ≠ 0)
      have hb := Int.emod_lt_of_pos (ex * Work.Cert.WR) hSpos
      linarith
    · have ha := Int.emod_nonneg (ex * Work.Cert.WR) (by norm_num [Work.Cert.S] : Work.Cert.S ≠ 0)
      have hb := Int.emod_lt_of_pos (ey * Work.Cert.WI) hSpos
      linarith
  have b3 : |Work.Cert.S * (ny - Work.Cert.cmi ex ey Work.Cert.WR Work.Cert.WI)| ≤ 8 * Work.Cert.S := by
    rw [abs_mul, abs_of_nonneg (le_of_lt hSpos)]
    exact mul_le_mul_of_nonneg_left hd2 (le_of_lt hSpos)
  have b4 : |-((ex * Work.Cert.WI) % Work.Cert.S) - ((ey * Work.Cert.WR) % Work.Cert.S)|
      ≤ 2 * Work.Cert.S - 2 := by
    rw [abs_le]
    constructor
    · have hb1 := Int.emod_lt_of_pos (ex * Work.Cert.WI) hSpos
      have hb2 := Int.emod_lt_of_pos (ey * Work.Cert.WR) hSpos
      linarith
    · have ha1 := Int.emod_nonneg (ex * Work.Cert.WI) (by norm_num [Work.Cert.S] : Work.Cert.S ≠ 0)
      have ha2 := Int.emod_nonneg (ey * Work.Cert.WR) (by norm_num [Work.Cert.S] : Work.Cert.S ≠ 0)
      linarith
  have hA : |nx * Work.Cert.S - (ex * Work.Cert.WR - ey * Work.Cert.WI)| ≤ 9 * Work.Cert.S := by
    rw [e1, show Work.Cert.S * (nx - Work.Cert.cmr ex ey Work.Cert.WR Work.Cert.WI)
          - (ex * Work.Cert.WR) % Work.Cert.S + (ey * Work.Cert.WI) % Work.Cert.S
        = Work.Cert.S * (nx - Work.Cert.cmr ex ey Work.Cert.WR Work.Cert.WI)
          + (-((ex * Work.Cert.WR) % Work.Cert.S) + (ey * Work.Cert.WI) % Work.Cert.S) by ring]
    have hh := abs_add_le (Work.Cert.S * (nx - Work.Cert.cmr ex ey Work.Cert.WR Work.Cert.WI))
      (-((ex * Work.Cert.WR) % Work.Cert.S) + (ey * Work.Cert.WI) % Work.Cert.S)
    linarith
  have hB : |ny * Work.Cert.S - (ex * Work.Cert.WI + ey * Work.Cert.WR)| ≤ 10 * Work.Cert.S := by
    rw [e2, show Work.Cert.S * (ny - Work.Cert.cmi ex ey Work.Cert.WR Work.Cert.WI)
          - (ex * Work.Cert.WI) % Work.Cert.S - (ey * Work.Cert.WR) % Work.Cert.S
        = Work.Cert.S * (ny - Work.Cert.cmi ex ey Work.Cert.WR Work.Cert.WI)
          + (-((ex * Work.Cert.WI) % Work.Cert.S) - (ey * Work.Cert.WR) % Work.Cert.S) by ring]
    have hh := abs_add_le (Work.Cert.S * (ny - Work.Cert.cmi ex ey Work.Cert.WR Work.Cert.WI))
      (-((ex * Work.Cert.WI) % Work.Cert.S) - (ey * Work.Cert.WR) % Work.Cert.S)
    linarith
  rw [cx_step_eq ex ey Work.Cert.WR Work.Cert.WI nx ny, norm_div]
  have hden : ‖(Work.Cert.S : ℂ) ^ 2‖ = (Work.Cert.S : ℝ) ^ 2 := by
    rw [norm_pow, Complex.norm_intCast, abs_of_pos hS]
  rw [hden]
  have hnum := norm_int_le _ _ hA hB
  calc ‖((nx * Work.Cert.S - (ex * Work.Cert.WR - ey * Work.Cert.WI) : ℤ) : ℂ) +
          (((ny * Work.Cert.S - (ex * Work.Cert.WI + ey * Work.Cert.WR) : ℤ)) : ℂ) * Complex.I‖
          / (Work.Cert.S : ℝ) ^ 2
      ≤ ((27 / 2) * (Work.Cert.S : ℝ)) / (Work.Cert.S : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = 27 / (2 * (Work.Cert.S : ℝ)) := by field_simp

/-! ## The metric recurrence and the arithmetic step -/

/-- Metric drift step: if `z'` is `z·W` up to `g`, and `W` is `ρ` up to `c` with `‖ρ‖ = 1`, then
`z'` is `u·ρ` up to `g + ‖z‖·c + ‖z − u‖`. -/
lemma drift_step {W ρ z z' u : ℂ} {g c Rz dd : ℝ}
    (hg : ‖z' - z * W‖ ≤ g) (hW : ‖W - ρ‖ ≤ c) (hρ : ‖ρ‖ = 1)
    (hz : ‖z‖ ≤ Rz) (hδ : ‖z - u‖ ≤ dd) :
    ‖z' - u * ρ‖ ≤ g + Rz * c + dd := by
  have hRz0 : 0 ≤ Rz := le_trans (norm_nonneg _) hz
  have hc0 : 0 ≤ c := le_trans (norm_nonneg _) hW
  have h1 : z' - u * ρ = (z' - z * W) + z * (W - ρ) + (z - u) * ρ := by ring
  rw [h1]
  have h2 : ‖z * (W - ρ)‖ ≤ Rz * c := by
    rw [norm_mul]
    exact mul_le_mul hz hW (norm_nonneg _) hRz0
  have h3 : ‖(z - u) * ρ‖ ≤ dd := by rw [norm_mul, hρ, mul_one]; exact hδ
  have h4 := norm_add_le ((z' - z * W) + z * (W - ρ)) ((z - u) * ρ)
  have h5 := norm_add_le (z' - z * W) (z * (W - ρ))
  linarith

/-- The arithmetic step of the induction: `27/(2S) + (R + d)·(2/S) + d ≤ 16·(n+1)/S` whenever
`R ≤ 1`, `d ≤ 16n/S` and `n ≤ 4096` (the last giving `32n/S ≤ 1/2`). -/
lemma step_arith (n : ℕ) (R d : ℝ) (hn : n ≤ 4096) (hR : R ≤ 1)
    (hd : d ≤ 16 * (n : ℝ) / (Work.Cert.S : ℝ)) :
    27 / (2 * (Work.Cert.S : ℝ)) + (R + d) * (2 / (Work.Cert.S : ℝ)) + d
      ≤ 16 * ((n : ℝ) + 1) / (Work.Cert.S : ℝ) := by
  have hS : (0 : ℝ) < (Work.Cert.S : ℝ) := S_pos_real
  have hn' : (n : ℝ) ≤ 4096 := by exact_mod_cast hn
  have h32 : 32 * (n : ℝ) / (Work.Cert.S : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hS]
    nlinarith [show (Work.Cert.S : ℝ) = 109951162777600000000 by norm_num [Work.Cert.S]]
  have hmain : 27 / (2 * (Work.Cert.S : ℝ)) + (1 + 16 * (n : ℝ) / (Work.Cert.S : ℝ))
        * (2 / (Work.Cert.S : ℝ)) + 16 * (n : ℝ) / (Work.Cert.S : ℝ)
      ≤ 16 * ((n : ℝ) + 1) / (Work.Cert.S : ℝ) := by
    have expand : (1 + 16 * (n : ℝ) / (Work.Cert.S : ℝ)) * (2 / (Work.Cert.S : ℝ))
        = 2 / (Work.Cert.S : ℝ) + 32 * (n : ℝ) / (Work.Cert.S : ℝ) ^ 2 := by
      field_simp
      ring
    rw [expand]
    have e : 27 / (2 * (Work.Cert.S : ℝ))
          + (2 / (Work.Cert.S : ℝ) + 32 * (n : ℝ) / (Work.Cert.S : ℝ) ^ 2)
          + 16 * (n : ℝ) / (Work.Cert.S : ℝ)
        = (27 / 2 + 2 + 32 * (n : ℝ) / (Work.Cert.S : ℝ) + 16 * (n : ℝ))
            / (Work.Cert.S : ℝ) := by
      field_simp
      ring
    have e2 : 16 * ((n : ℝ) + 1) / (Work.Cert.S : ℝ)
        = (16 * (n : ℝ) + 16) / (Work.Cert.S : ℝ) := by
      field_simp
    rw [e, e2]
    apply div_le_div_of_nonneg_right _ hS.le
    linarith
  have hmono : (R + d) * (2 / (Work.Cert.S : ℝ))
      ≤ (1 + 16 * (n : ℝ) / (Work.Cert.S : ℝ)) * (2 / (Work.Cert.S : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  linarith

open Submission.CDTPlan in
/-- **Grid drift.**  The certificate's grid points `E j` satisfy the exact circle points
`(Rk k / S) · rot (j/4096)` to within `65536/S`, by induction on `j` from the integer step
`gridStep` and the rotation tolerance `‖W − rot(1/4096)‖ ≤ 2/S`.

HINT (the constant is tight -- do NOT use a crude `‖z‖ ≤ 2R` or a `10√2/S` step estimate,
that gives 4096·(10√2+2)/S > 65536/S):
put `z_j := cx (E j).1 (E j).2`, `u_j := (Rk k : ℝ)/S * rot (j/4096)`, `W := cx WR WI`,
`ρ := rot (1/4096)`, and `δ_j := ‖z_j - u_j‖`.  Then

  `z_{j+1} - u_{j+1} = (z_{j+1} - z_j*W) + z_j*(W - ρ) + (z_j - u_j)*ρ`,

so with `g_j := ‖z_{j+1} - z_j*W‖`:
`δ_{j+1} ≤ g_j + (Rk k/S + δ_j)*(2/S) + δ_j`, using `hW` and `‖ρ‖ = 1`.
The step term is `g_j ≤ √181/S < 14/S`: writing `ex := (E j).1`, `ey := (E j).2`,
`nx := (E (j+1)).1`, `ny := (E (j+1)).2`, `u := ex*WR - ey*WI`, `v := ex*WI + ey*WR`, one has
`z_{j+1} - z_j*W = ((nx*S - u) + (ny*S - v)*I)/S²`, and with the residues
`r1 := ex*WR - S*(ex*WR/S)`, `r2 := ey*WI - S*(ey*WI/S)`, `r3 := ex*WI - S*(ex*WI/S)`,
`r4 := ey*WR - S*(ey*WR/S)` all in `[0, S-1]`:
`nx*S - u = -r1 + r2 + (nx - cmr ex ey WR WI)*S` (so `|nx*S - u| ≤ 9S - 1`) and
`ny*S - v = -r3 - r4 + (ny - cmi ex ey WR WI)*S` (so `|ny*S - v| ≤ 10S - 2`);
hence `g_j ≤ ‖(9S) + (10S)i‖/S² = √181/S < 14/S` (as `181 < 196 = 14²`).
Induct on `j` proving `δ_j ≤ j * 16/S` for all `j ≤ 4096`: the step needs
`√181 + 2 + 32*j/S ≤ 16`, true since `√181 < 13.5` and `32*j/S ≤ 1/2`; at `j = 4096` this is
exactly `65536/S`.  Base case: `h0` gives `z_0 = (Rk k : ℝ)/S = u_0` since `rot 0 = 1`.
Also `Rk k/S ≤ 1` for `k ≤ 2` (`Rk 0 = S/10000`, `Rk 1 = 283*S/500`, `Rk 2 = S`). -/
theorem drift_le (hW : ‖Work.Cert.cx Work.Cert.WR Work.Cert.WI - rot (1 / 4096)‖ ≤ 2 / (Work.Cert.S : ℝ))
    (k : ℕ) (hk : k ≤ 2) (E : ℕ → ℤ × ℤ) (h0 : E 0 = (Work.Cert.Rk k, 0))
    (hstep : ∀ j, j < 4096 → Work.Cert.gridStep (E j).1 (E j).2 (E (j + 1)).1 (E (j + 1)).2 = true)
    (j : ℕ) (hj : j ≤ 4096) :
    ‖Work.Cert.cx (E j).1 (E j).2 - ((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot ((j : ℝ) / 4096)‖
      ≤ 65536 / (Work.Cert.S : ℝ) := by
  have hS : (0 : ℝ) < (Work.Cert.S : ℝ) := S_pos_real
  have hk0 : (0 : ℝ) ≤ (Work.Cert.Rk k : ℝ) := by exact_mod_cast (Rk_facts k hk).1
  have hkS : (Work.Cert.Rk k : ℝ) ≤ (Work.Cert.S : ℝ) := (Rk_facts k hk).2
  have hR1 : (Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ) ≤ 1 := by
    rw [div_le_one hS]
    exact hkS
  have key : ∀ m : ℕ, m ≤ 4096 →
      ‖Work.Cert.cx (E m).1 (E m).2 - ((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ))
          * rot ((m : ℝ) / 4096)‖ ≤ 16 * (m : ℝ) / (Work.Cert.S : ℝ) := by
    intro m
    induction m with
    | zero =>
        intro _
        have hz : Work.Cert.cx (E 0).1 (E 0).2
            - ((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot (((0 : ℕ) : ℝ) / 4096) = 0 := by
          rw [h0]
          simp [Work.Cert.cx, rot]
        rw [hz]
        norm_num
    | succ n ih =>
        intro hn
        have hnlt : n < 4096 := by omega
        have ihn : ‖Work.Cert.cx (E n).1 (E n).2
            - ((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot ((n : ℝ) / 4096)‖
              ≤ 16 * (n : ℝ) / (Work.Cert.S : ℝ) := ih (by omega)
        have hstepn := hstep n hnlt
        have hg : ‖Work.Cert.cx (E (n + 1)).1 (E (n + 1)).2
            - Work.Cert.cx (E n).1 (E n).2 * Work.Cert.cx Work.Cert.WR Work.Cert.WI‖
              ≤ 27 / (2 * (Work.Cert.S : ℝ)) := gridStep_norm_le _ _ _ _ hstepn
        have hz_le : ‖Work.Cert.cx (E n).1 (E n).2‖
            ≤ (Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)
              + ‖Work.Cert.cx (E n).1 (E n).2
                  - ((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot ((n : ℝ) / 4096)‖ := by
          have h := norm_add_le
            (Work.Cert.cx (E n).1 (E n).2
              - ((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot ((n : ℝ) / 4096))
            (((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot ((n : ℝ) / 4096))
          have he : Work.Cert.cx (E n).1 (E n).2
                - ((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot ((n : ℝ) / 4096)
              + (((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot ((n : ℝ) / 4096))
              = Work.Cert.cx (E n).1 (E n).2 := by ring
          rw [he] at h
          have hu : ‖((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot ((n : ℝ) / 4096)‖
              = (Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ) := by
            rw [norm_mul, norm_rot, mul_one, ← Complex.ofReal_div]
            exact norm_ofReal_of_nonneg (div_nonneg hk0 hS.le)
          rw [hu] at h
          linarith [h]
        have hdr := drift_step (W := Work.Cert.cx Work.Cert.WR Work.Cert.WI)
          (ρ := rot (1 / 4096)) (z := Work.Cert.cx (E n).1 (E n).2)
          (z' := Work.Cert.cx (E (n + 1)).1 (E (n + 1)).2)
          (u := ((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot ((n : ℝ) / 4096))
          (g := 27 / (2 * (Work.Cert.S : ℝ))) (c := 2 / (Work.Cert.S : ℝ))
          (Rz := (Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)
            + ‖Work.Cert.cx (E n).1 (E n).2
                - ((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot ((n : ℝ) / 4096)‖)
          (dd := ‖Work.Cert.cx (E n).1 (E n).2
                - ((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot ((n : ℝ) / 4096)‖)
          hg hW (norm_rot _) hz_le (le_refl _)
        have harith := step_arith n ((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ))
          ‖Work.Cert.cx (E n).1 (E n).2
            - ((Work.Cert.Rk k : ℝ) / (Work.Cert.S : ℝ)) * rot ((n : ℝ) / 4096)‖
          (by omega) hR1 ihn
        rw [rot_step]
        have hfin := hdr.trans harith
        simpa using hfin
  have hmain := key j hj
  have hfin : 16 * (j : ℝ) / (Work.Cert.S : ℝ) ≤ 65536 / (Work.Cert.S : ℝ) := by
    apply div_le_div_of_nonneg_right _ hS.le
    have hj' : (j : ℝ) ≤ 4096 := by exact_mod_cast hj
    linarith
  linarith

end Work.Cert.ACore
