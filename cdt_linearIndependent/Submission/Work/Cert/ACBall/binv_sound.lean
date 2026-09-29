import Mathlib
import Submission.Work.Cert.ACBall.Basic

namespace Work.Cert.ACBall

open Work.Cert

/-! # Soundness of the ball inversion `binv`

`binvOK a L` (`= 0 ≤ a.r ∧ a.r < L ∧ L² ≤ a.x² + a.y²`) certifies that the disc of `a` stays
away from the origin (its centre has modulus `≥ L/S`, its radius is `r/S < L/S`).  The output ball
`binv a L` has centre the exactly-floored `S²·conj(c)/|c|²` and radius `r S/((L−r)L) + 2/S`, so it
contains `u⁻¹` for every `u ∈ a`.  The `+2` accounts for the two floors of the centre (one ulp per
coordinate).

The main estimate is
`‖u⁻¹ − c⁻¹‖ = ‖c − u‖/(‖u‖‖c‖) ≤ (r/S)/(((L−r)/S)(L/S)) = r S/((L−r)L)`,
combined with `‖c⁻¹ − centre‖ ≤ 2/S` (two integer floors) and the ceiling bound `dvu_ge`. -/

/-- Lower bound on `‖cx x y‖` from a square bound `m² ≤ x² + y²` (companion of `norm_cx_le_of_sq_le`). -/
lemma norm_cx_ge_of_sq_le {x y m : ℤ} (hm : 0 < m) (h : m * m ≤ x * x + y * y) :
    (m : ℝ) / (S : ℝ) ≤ ‖cx x y‖ := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h' : ((m : ℝ) ^ 2) ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by
    have h2 : ((m * m : ℤ) : ℝ) ≤ ((x * x + y * y : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h2
    nlinarith [h2]
  have hsq : ((m : ℝ) / (S : ℝ)) ^ 2 ≤ ‖cx x y‖ ^ 2 := by
    rw [norm_cx_sq, div_pow]
    exact div_le_div_of_nonneg_right h' (sq_nonneg _)
  have hnn : 0 ≤ (m : ℝ) / (S : ℝ) := div_nonneg hmR.le S_posR.le
  calc (m : ℝ) / S = Real.sqrt (((m : ℝ) / S) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (‖cx x y‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖cx x y‖ := Real.sqrt_sq (norm_nonneg _)

/-- Reciprocal is `B/((A−B)A)`-Lipschitz on the region `‖c‖ ≥ A` with `‖u − c‖ ≤ B < A`. -/
lemma norm_inv_sub_inv_le {u c : ℂ} {A B : ℝ} (hA : 0 < A) (hc : A ≤ ‖c‖)
    (hu : ‖u - c‖ ≤ B) (hB : B < A) :
    u ≠ 0 ∧ ‖u⁻¹ - c⁻¹‖ ≤ B / ((A - B) * A) := by
  have hAB : 0 < A - B := by linarith
  have huc : A - B ≤ ‖u‖ := by
    have h := norm_sub_norm_le c u
    rw [norm_sub_rev] at h
    linarith
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at huc
    linarith
  refine ⟨hu0, ?_⟩
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    linarith
  have hkey : u⁻¹ - c⁻¹ = (c - u) * (u * c)⁻¹ := by field_simp
  have hcn : ‖c - u‖ ≤ B := by rw [norm_sub_rev]; exact hu
  calc ‖u⁻¹ - c⁻¹‖ = ‖c - u‖ * ‖(u * c)⁻¹‖ := by rw [hkey, norm_mul]
    _ = ‖c - u‖ / (‖u‖ * ‖c‖) := by rw [norm_inv, norm_mul, div_eq_mul_inv]
    _ ≤ B / ((A - B) * A) := by
        have hden2 : (A - B) * A ≤ ‖u‖ * ‖c‖ := mul_le_mul huc hc hA.le (norm_nonneg u)
        have hdenpos : 0 < (A - B) * A := mul_pos hAB hA
        have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hcn
        calc ‖c - u‖ / (‖u‖ * ‖c‖) ≤ B / (‖u‖ * ‖c‖) :=
              div_le_div_of_nonneg_right hcn (by positivity)
          _ ≤ B / ((A - B) * A) :=
              div_le_div_of_nonneg_left hB0 hdenpos hden2

/-- The floored centre of `binv` approximates `(cx x y)⁻¹` to within `2/S`. -/
lemma cx_inv_approx {x y : ℤ} (hn : 0 < x * x + y * y) :
    ‖cx (fdiv (x * S * S) (x * x + y * y)) (-(fdiv (y * S * S) (x * x + y * y)))
      - (cx x y)⁻¹‖ ≤ 2 / (S : ℝ) := by
  have hS : (S : ℝ) ≠ 0 := ne_of_gt S_posR
  have hnormSq : Complex.normSq (cx x y) = ((x * x + y * y : ℤ) : ℝ) / (S : ℝ) ^ 2 := by
    rw [Complex.normSq_apply, cx_re, cx_im]
    push_cast
    field_simp
  have hre : (cx (fdiv (x * S * S) (x * x + y * y)) (-(fdiv (y * S * S) (x * x + y * y)))
      - (cx x y)⁻¹).re
      = ((fdiv (x * S * S) (x * x + y * y) : ℝ)
          - ((x * S * S : ℤ) : ℝ) / ((x * x + y * y : ℤ) : ℝ)) / (S : ℝ) := by
    rw [Complex.sub_re, cx_re, Complex.inv_re, cx_re, hnormSq]
    push_cast
    field_simp
  have him : (cx (fdiv (x * S * S) (x * x + y * y)) (-(fdiv (y * S * S) (x * x + y * y)))
      - (cx x y)⁻¹).im
      = ((-(fdiv (y * S * S) (x * x + y * y)) : ℝ)
          + ((y * S * S : ℤ) : ℝ) / ((x * x + y * y : ℤ) : ℝ)) / (S : ℝ) := by
    rw [Complex.sub_im, cx_im, Complex.inv_im, cx_im, hnormSq]
    push_cast
    field_simp
    ring
  have hXb : |(fdiv (x * S * S) (x * x + y * y) : ℝ)
      - ((x * S * S : ℤ) : ℝ) / ((x * x + y * y : ℤ) : ℝ)| ≤ 1 := by
    have h1 : (fdiv (x * S * S) (x * x + y * y) : ℝ)
        ≤ ((x * S * S : ℤ) : ℝ) / ((x * x + y * y : ℤ) : ℝ) := fdiv_le hn
    have h2 : ((x * S * S : ℤ) : ℝ) / ((x * x + y * y : ℤ) : ℝ) - 1
        < (fdiv (x * S * S) (x * x + y * y) : ℝ) := fdiv_gt hn
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hYb : |(-(fdiv (y * S * S) (x * x + y * y)) : ℝ)
      + ((y * S * S : ℤ) : ℝ) / ((x * x + y * y : ℤ) : ℝ)| ≤ 1 := by
    have h1 : (fdiv (y * S * S) (x * x + y * y) : ℝ)
        ≤ ((y * S * S : ℤ) : ℝ) / ((x * x + y * y : ℤ) : ℝ) := fdiv_le hn
    have h2 : ((y * S * S : ℤ) : ℝ) / ((x * x + y * y : ℤ) : ℝ) - 1
        < (fdiv (y * S * S) (x * x + y * y) : ℝ) := fdiv_gt hn
    rw [abs_le]
    constructor <;> linarith
  have h1 : |(cx (fdiv (x * S * S) (x * x + y * y)) (-(fdiv (y * S * S) (x * x + y * y)))
      - (cx x y)⁻¹).re| ≤ 1 / (S : ℝ) := by
    rw [hre, abs_div, abs_of_pos S_posR]
    exact div_le_div_of_nonneg_right hXb S_posR.le
  have h2 : |(cx (fdiv (x * S * S) (x * x + y * y)) (-(fdiv (y * S * S) (x * x + y * y)))
      - (cx x y)⁻¹).im| ≤ 1 / (S : ℝ) := by
    rw [him, abs_div, abs_of_pos S_posR]
    exact div_le_div_of_nonneg_right hYb S_posR.le
  calc ‖cx (fdiv (x * S * S) (x * x + y * y)) (-(fdiv (y * S * S) (x * x + y * y)))
        - (cx x y)⁻¹‖
      ≤ |(cx (fdiv (x * S * S) (x * x + y * y)) (-(fdiv (y * S * S) (x * x + y * y)))
          - (cx x y)⁻¹).re|
        + |(cx (fdiv (x * S * S) (x * x + y * y)) (-(fdiv (y * S * S) (x * x + y * y)))
          - (cx x y)⁻¹).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / (S : ℝ) + 1 / (S : ℝ) := add_le_add h1 h2
    _ = 2 / (S : ℝ) := by ring

theorem binv_sound {a : Bl} {L : ℤ} {u : ℂ} (h : binvOK a L = true) (ha : BallMem a u) :
    u ≠ 0 ∧ BallMem (binv a L) u⁻¹ := by
  rw [binvOK] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hr0, hrL⟩, hLL⟩ := h
  have hLpos : 0 < L := by omega
  have hn : 0 < a.x * a.x + a.y * a.y := by nlinarith
  have hc : (L : ℝ) / (S : ℝ) ≤ ‖cx a.x a.y‖ := norm_cx_ge_of_sq_le hLpos hLL
  have hA : 0 < (L : ℝ) / (S : ℝ) := div_pos (by exact_mod_cast hLpos) S_posR
  have hB : (a.r : ℝ) / (S : ℝ) < (L : ℝ) / (S : ℝ) := by
    rw [div_lt_div_iff_of_pos_right S_posR]
    exact_mod_cast hrL
  have hu : ‖u - cx a.x a.y‖ ≤ (a.r : ℝ) / (S : ℝ) := ha
  have hinv := norm_inv_sub_inv_le (c := cx a.x a.y) (u := u) hA hc hu hB
  have hT : ((a.r : ℝ) / (S : ℝ))
        / ((((L : ℝ) / (S : ℝ)) - (a.r : ℝ) / (S : ℝ)) * ((L : ℝ) / (S : ℝ)))
      = (a.r : ℝ) * (S : ℝ) / (((L : ℝ) - (a.r : ℝ)) * (L : ℝ)) := by
    field_simp

  have hb : 0 < (L - a.r) * L := mul_pos (by omega) hLpos
  have hTle : (a.r : ℝ) * (S : ℝ) / (((L : ℝ) - (a.r : ℝ)) * (L : ℝ))
      ≤ ((dvu (a.r * S) ((L - a.r) * L) : ℤ) : ℝ) / (S : ℝ) := by
    rw [le_div_iff₀ S_posR]
    have hg := dvu_ge (a := a.r * S) (b := (L - a.r) * L) hb
    push_cast at hg
    calc (a.r : ℝ) * (S : ℝ) / (((L : ℝ) - (a.r : ℝ)) * (L : ℝ)) * (S : ℝ)
        = ((a.r : ℝ) * (S : ℝ)) * (S : ℝ) / (((L : ℝ) - (a.r : ℝ)) * (L : ℝ)) := by ring
      _ ≤ ((dvu (a.r * S) ((L - a.r) * L) : ℤ) : ℝ) := hg
  have hcen : ‖cx (binv a L).x (binv a L).y - (cx a.x a.y)⁻¹‖ ≤ 2 / (S : ℝ) := by
    simp only [binv]
    exact cx_inv_approx hn
  refine ⟨hinv.1, ?_⟩
  have hbnd : ‖u⁻¹ - cx (binv a L).x (binv a L).y‖
      ≤ (a.r : ℝ) * (S : ℝ) / (((L : ℝ) - (a.r : ℝ)) * (L : ℝ)) + 2 / (S : ℝ) := by
    have hsplit : u⁻¹ - cx (binv a L).x (binv a L).y
        = (u⁻¹ - (cx a.x a.y)⁻¹) + ((cx a.x a.y)⁻¹ - cx (binv a L).x (binv a L).y) := by
      ring
    calc ‖u⁻¹ - cx (binv a L).x (binv a L).y‖
        = ‖(u⁻¹ - (cx a.x a.y)⁻¹)
            + ((cx a.x a.y)⁻¹ - cx (binv a L).x (binv a L).y)‖ := by rw [hsplit]
      _ ≤ ‖u⁻¹ - (cx a.x a.y)⁻¹‖ + ‖(cx a.x a.y)⁻¹ - cx (binv a L).x (binv a L).y‖ :=
            norm_add_le _ _
      _ ≤ (a.r : ℝ) * (S : ℝ) / (((L : ℝ) - (a.r : ℝ)) * (L : ℝ)) + 2 / (S : ℝ) := by
          refine add_le_add ?_ ?_
          · exact le_trans hinv.2 (le_of_eq hT)
          · rw [norm_sub_rev]; exact hcen
  rw [BallMem]
  have hrad : (((binv a L).r : ℤ) : ℝ) / (S : ℝ)
      = ((dvu (a.r * S) ((L - a.r) * L) : ℤ) : ℝ) / (S : ℝ) + 2 / (S : ℝ) := by
    simp only [binv]
    push_cast
    ring
  calc ‖u⁻¹ - cx (binv a L).x (binv a L).y‖
      ≤ (a.r : ℝ) * (S : ℝ) / (((L : ℝ) - (a.r : ℝ)) * (L : ℝ)) + 2 / (S : ℝ) := hbnd
    _ ≤ ((dvu (a.r * S) ((L - a.r) * L) : ℤ) : ℝ) / (S : ℝ) + 2 / (S : ℝ) :=
          add_le_add hTle le_rfl
    _ = (((binv a L).r : ℤ) : ℝ) / (S : ℝ) := by rw [hrad]

end Work.Cert.ACBall
