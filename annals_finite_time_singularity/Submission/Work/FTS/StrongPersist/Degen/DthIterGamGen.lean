/-
# `Work.FTS.StrongPersist.Degen.DthIterGamGen`

The pointwise angular jet bound

  `|D_θ^i Γ(θ)| ≤ 1000·(1+α²)²·Γ(θ)`   on `Iθ`, for **every real** `α` and `i ≤ 4`,

where `Γ = Gam α` and `D_θ = sin(2θ)∂_θ` (`Spaces.DthIter`), stated for the `z`-independent
function `(z,θ) ↦ Γ(θ)` evaluated at `z = 0`.

## Proof

`Work.FTS.LocData.DthIter_Gam_Pf` gives the exact jet formula

  `D_θ^i Γ(θ) = Γ(θ)·Pf i (cos 2θ) α`   (`i ≤ 4`, `θ ∈ Iθ`),

and `Γ(θ) ≥ 0` always (it is a real power of the nonnegative `sin θ·cos²θ`).  Hence it suffices to
bound the angular polynomial `Pf`:

  `|Pf i u α| ≤ 1000·(1+α²)²`   for `|u| ≤ 1`, `i ≤ 4`.

This is the elementary numerical bound `Pf_abs_le`, proved by the triangle inequality from the
explicit polynomials `Pf_zero … Pf_four` (which are `α` times the `Qf`'s of `HkFstarDefs`):
writing `B := 1 + α²` and using `|u| ≤ 1` one has `|1-u²| ≤ 1`, `|3u-1| ≤ 4`,
`|u-1/3| ≤ 4/3`, `|1-3u²| ≤ 2`, while `|α|^k ≤ B²` for `k ≤ 4` (since `|α| ≤ B` and
`α² ≤ B ≤ B²`).  The resulting constants are bounded by `4, 19, 113` for `i = 2, 3, 4`
(and `1`, `4/3` for `i = 0, 1`), well within `1000`.

Note that no hypothesis on the sign of `α` is needed (the earlier siblings
`DthIter_Gam_abs_le` and `Pf_bounds` assume `0 < α ≤ 1`), because the estimate is uniform in
`(1+α²)²`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.LocData.DthIter_Gam_Pf
import Submission.Work.FTS.LocData.HkFstarDefs
import Submission.Work.Spaces.Gam_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Work.FTS.LocData

namespace Work.FTS.StrongPersist.Degen

set_option autoImplicit false

/-! ## Elementary product bounds -/

/-- Product bound from bounds on the two factors. -/
lemma abs_prod2_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hA : 0 ≤ A) :
    |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) hA

/-- Product bound from bounds on the three factors. -/
lemma abs_prod3_le {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) : |a * b * c| ≤ A * B * C := by
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have h1 : |a * b| ≤ A * B := abs_prod2_le ha hb hA
  calc |a * b * c| = |a * b| * |c| := abs_mul (a * b) c
    _ ≤ (A * B) * C := mul_le_mul h1 hc (abs_nonneg c) hAB
    _ = A * B * C := by ring

/-- Product bound from bounds on the four factors. -/
lemma abs_prod4_le {a b c d A B C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    |a * b * c * d| ≤ A * B * C * D := by
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hABC : 0 ≤ A * B * C := mul_nonneg hAB hC
  have h1 : |a * b * c| ≤ A * B * C := abs_prod3_le ha hb hc hA hB
  calc |a * b * c * d| = |a * b * c| * |d| := abs_mul (a * b * c) d
    _ ≤ (A * B * C) * D := mul_le_mul h1 hd (abs_nonneg d) hABC
    _ = A * B * C * D := by ring

/-- Product bound from bounds on the five factors. -/
lemma abs_prod5_le {a b c d e A B C D E : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    |a * b * c * d * e| ≤ A * B * C * D * E := by
  have hABCD : 0 ≤ A * B * C * D := mul_nonneg (mul_nonneg (mul_nonneg hA hB) hC) hD
  have h1 : |a * b * c * d| ≤ A * B * C * D := abs_prod4_le ha hb hc hd hA hB hC
  calc |a * b * c * d * e| = |a * b * c * d| * |e| := abs_mul (a * b * c * d) e
    _ ≤ (A * B * C * D) * E := mul_le_mul h1 he (abs_nonneg e) hABCD
    _ = A * B * C * D * E := by ring

/-- Triangle inequality for a sum of three terms. -/
lemma abs_add3_le {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a + b + c| ≤ A + B + C := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  linarith

/-- Triangle inequality for a sum of five terms. -/
lemma abs_add5_le {a b c d e A B C D E : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E) : |a + b + c + d + e| ≤ A + B + C + D + E := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b + c + d) e
  linarith

/-! ## Pointwise bounds for `u ∈ [-1,1]` -/

lemma abs_one_sub_sq_le_one_g {u : ℝ} (hu : |u| ≤ 1) : |1 - u ^ 2| ≤ 1 := by
  have h1 : -1 ≤ u := (abs_le.mp hu).1
  have h2 : u ≤ 1 := (abs_le.mp hu).2
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg u]

lemma abs_u_sub_third_le_g {u : ℝ} (hu : |u| ≤ 1) : |u - 1 / 3| ≤ 4 / 3 := by
  rw [abs_le]
  have h1 : -1 ≤ u := (abs_le.mp hu).1
  have h2 : u ≤ 1 := (abs_le.mp hu).2
  constructor <;> linarith

lemma abs_three_u_sub_one_le_four_g {u : ℝ} (hu : |u| ≤ 1) : |3 * u - 1| ≤ 4 := by
  rw [abs_le]
  have h1 : -1 ≤ u := (abs_le.mp hu).1
  have h2 : u ≤ 1 := (abs_le.mp hu).2
  constructor <;> linarith

lemma abs_one_sub_three_sq_le_two_g {u : ℝ} (hu : |u| ≤ 1) : |1 - 3 * u ^ 2| ≤ 2 := by
  rw [abs_le]
  have h1 : -1 ≤ u := (abs_le.mp hu).1
  have h2 : u ≤ 1 := (abs_le.mp hu).2
  have hu2 : u ^ 2 ≤ 1 := by nlinarith
  constructor <;> nlinarith [sq_nonneg u]

/-! ## Monomial bounds in `α` -/

lemma abs_alpha_le_B (α : ℝ) : |α| ≤ 1 + α ^ 2 := by
  nlinarith [sq_nonneg α, abs_nonneg α, sq_abs α]

lemma one_add_sq_le_sq (α : ℝ) : 1 + α ^ 2 ≤ (1 + α ^ 2) ^ 2 := by
  nlinarith [sq_nonneg α]

lemma abs_alpha_le_B2 (α : ℝ) : |α| ≤ (1 + α ^ 2) ^ 2 :=
  (abs_alpha_le_B α).trans (one_add_sq_le_sq α)

lemma abs_alpha_sq_le_B2 (α : ℝ) : |α| ^ 2 ≤ (1 + α ^ 2) ^ 2 := by
  rw [sq_abs]
  exact (by nlinarith [sq_nonneg α] : α ^ 2 ≤ (1 + α ^ 2) ^ 2)

lemma abs_alpha_cube_le_B2 (α : ℝ) : |α| ^ 3 ≤ (1 + α ^ 2) ^ 2 := by
  have h : |α| ^ 3 = |α| * |α| ^ 2 := by ring
  rw [h]
  calc |α| * |α| ^ 2 ≤ (1 + α ^ 2) * (1 + α ^ 2) :=
        mul_le_mul (abs_alpha_le_B α) (by rw [sq_abs]; nlinarith [sq_nonneg α])
          (by positivity) (by positivity)
    _ = (1 + α ^ 2) ^ 2 := by ring

lemma abs_alpha_pow4_le_B2 (α : ℝ) : |α| ^ 4 ≤ (1 + α ^ 2) ^ 2 := by
  have h : |α| ^ 4 = (|α| ^ 2) ^ 2 := by ring
  rw [h]
  have h2 : |α| ^ 2 ≤ 1 + α ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg α]
  exact pow_le_pow_left₀ (by positivity) h2 2

/-! ## The explicit polynomials in a canonical (sum-of-signed-terms) shape -/

lemma Pf_three_expand (u α : ℝ) :
    Pf 3 u α = α * (((-8) * u * (1 - u ^ 2)) + ((-6) * α * (u - 1 / 3) * (1 - u ^ 2))
      + (α ^ 2 * (u - 1 / 3) ^ 3)) := by
  rw [Pf_three]; ring

lemma Pf_four_expand (u α : ℝ) :
    Pf 4 u α = α * ((16 * (1 - u ^ 2) * (1 - 3 * u ^ 2))
      + (12 * α * (1 - u ^ 2) * (1 - u ^ 2))
      + ((-32) * α * u * (u - 1 / 3) * (1 - u ^ 2))
      + (((-12) * α ^ 2) * (u - 1 / 3) ^ 2 * (1 - u ^ 2))
      + (((α ^ 3) * (u - 1 / 3) ^ 2) * (u - 1 / 3) ^ 2)) := by
  rw [Pf_four]; ring

/-! ## The numerical bound on the angular polynomials -/

/-- `|Pf i u α| ≤ 1000·(1+α²)²` for `|u| ≤ 1` and `i ≤ 4`, for **every** real `α`. -/
theorem Pf_abs_le (i : ℕ) (hi : i ≤ 4) (u α : ℝ) (hu : |u| ≤ 1) :
    |Pf i u α| ≤ 1000 * (1 + α ^ 2) ^ 2 := by
  have hB : (0 : ℝ) ≤ (1 + α ^ 2) ^ 2 := by positivity
  interval_cases i
  · rw [Pf_zero, abs_one]
    nlinarith [one_add_sq_le_sq α, sq_nonneg α]
  · rw [Pf_one]
    have h1 : |u - 1 / 3| ≤ 4 / 3 := abs_u_sub_third_le_g hu
    have h2 : |α| ≤ (1 + α ^ 2) ^ 2 := abs_alpha_le_B2 α
    calc |α * ((3 * u - 1) / 3)|
        = |α| * |u - 1 / 3| := by
          rw [show (3 * u - 1) / 3 = u - 1 / 3 by ring, abs_mul]
      _ ≤ (1 + α ^ 2) ^ 2 * (4 / 3) := mul_le_mul h2 h1 (abs_nonneg _) hB
      _ ≤ 1000 * (1 + α ^ 2) ^ 2 := by nlinarith
  · rw [Pf_two, abs_mul]
    have h1 : |(-2) * (1 - u ^ 2)| ≤ 2 := by
      rw [abs_mul, show |(-2 : ℝ)| = 2 from by norm_num]
      linarith [abs_one_sub_sq_le_one_g hu]
    have h2 : |α * (3 * u - 1) ^ 2 / 9| ≤ (16 / 9) * |α| := by
      rw [abs_div, show |(9 : ℝ)| = 9 from by norm_num, abs_mul]
      have hs : |(3 * u - 1) ^ 2| ≤ 16 := by
        rw [abs_pow]
        have h3 := abs_three_u_sub_one_le_four_g hu
        nlinarith [abs_nonneg (3 * u - 1)]
      have hmul : |α| * |(3 * u - 1) ^ 2| ≤ |α| * 16 :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg α)
      linarith
    have hX : |(-2) * (1 - u ^ 2) + α * (3 * u - 1) ^ 2 / 9| ≤ 2 + (16 / 9) * |α| := by
      have h := abs_add_le ((-2) * (1 - u ^ 2)) (α * (3 * u - 1) ^ 2 / 9)
      linarith
    have hα : |α| ≤ (1 + α ^ 2) ^ 2 := abs_alpha_le_B2 α
    have hα2 : |α| ^ 2 ≤ (1 + α ^ 2) ^ 2 := abs_alpha_sq_le_B2 α
    have hstep : |α| * |(-2) * (1 - u ^ 2) + α * (3 * u - 1) ^ 2 / 9|
        ≤ |α| * (2 + (16 / 9) * |α|) := mul_le_mul_of_nonneg_left hX (abs_nonneg α)
    nlinarith [hstep, hα, hα2, hB]
  · rw [Pf_three_expand, abs_mul]
    have h1 : |1 - u ^ 2| ≤ 1 := abs_one_sub_sq_le_one_g hu
    have h3 : |u - 1 / 3| ≤ 4 / 3 := abs_u_sub_third_le_g hu
    have ht1 : |(-8) * u * (1 - u ^ 2)| ≤ 8 := by
      have h := abs_prod3_le (a := (-8)) (b := u) (c := 1 - u ^ 2) (A := 8) (B := 1) (C := 1)
        (by norm_num) hu h1 (by norm_num) (by norm_num)
      linarith
    have ht2 : |(-6) * α * (u - 1 / 3) * (1 - u ^ 2)| ≤ 8 * |α| := by
      have h := abs_prod4_le (a := (-6)) (b := α) (c := u - 1 / 3) (d := 1 - u ^ 2)
        (A := 6) (B := |α|) (C := 4 / 3) (D := 1)
        (by norm_num) (le_refl |α|) h3 h1 (by norm_num) (abs_nonneg α) (by norm_num)
      linarith
    have ht3 : |α ^ 2 * (u - 1 / 3) ^ 3| ≤ (64 / 27) * |α| ^ 2 := by
      rw [show α ^ 2 * (u - 1 / 3) ^ 3 = α * α * (u - 1 / 3) * (u - 1 / 3) * (u - 1 / 3)
        by ring]
      have h := abs_prod5_le (a := α) (b := α) (c := u - 1 / 3) (d := u - 1 / 3) (e := u - 1 / 3)
        (A := |α|) (B := |α|) (C := 4 / 3) (D := 4 / 3) (E := 4 / 3)
        (le_refl |α|) (le_refl |α|) h3 h3 h3
        (abs_nonneg α) (abs_nonneg α) (by norm_num) (by norm_num)
      linarith
    have hX : |((-8) * u * (1 - u ^ 2)) + ((-6) * α * (u - 1 / 3) * (1 - u ^ 2))
        + (α ^ 2 * (u - 1 / 3) ^ 3)| ≤ 8 + 8 * |α| + (64 / 27) * |α| ^ 2 :=
      abs_add3_le ht1 ht2 ht3
    have hstep := mul_le_mul_of_nonneg_left hX (abs_nonneg α)
    have hα : |α| ≤ (1 + α ^ 2) ^ 2 := abs_alpha_le_B2 α
    have hα2 : |α| ^ 2 ≤ (1 + α ^ 2) ^ 2 := abs_alpha_sq_le_B2 α
    have hα3 : |α| ^ 3 ≤ (1 + α ^ 2) ^ 2 := abs_alpha_cube_le_B2 α
    nlinarith [hstep, hα, hα2, hα3, hB]
  · rw [Pf_four_expand, abs_mul]
    have h1 : |1 - u ^ 2| ≤ 1 := abs_one_sub_sq_le_one_g hu
    have h2 : |1 - 3 * u ^ 2| ≤ 2 := abs_one_sub_three_sq_le_two_g hu
    have h3 : |u - 1 / 3| ≤ 4 / 3 := abs_u_sub_third_le_g hu
    have h3sq : |(u - 1 / 3) ^ 2| ≤ 16 / 9 := by
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) h3 2).trans_eq (by norm_num)
    have h12a : |12 * α| ≤ 12 * |α| := by
      rw [abs_mul, show |(12 : ℝ)| = 12 from by norm_num]
    have h12a2 : |(-12) * α ^ 2| ≤ 12 * |α| ^ 2 := by
      rw [abs_mul, abs_pow, show |(-12 : ℝ)| = 12 from by norm_num]
    have h32a : |(-32) * α| ≤ 32 * |α| := by
      rw [abs_mul, show |(-32 : ℝ)| = 32 from by norm_num]
    have ha3 : |α ^ 3| ≤ |α| ^ 3 := by rw [abs_pow]
    have ht1 : |16 * (1 - u ^ 2) * (1 - 3 * u ^ 2)| ≤ 32 := by
      have h := abs_prod3_le (a := 16) (b := 1 - u ^ 2) (c := 1 - 3 * u ^ 2)
        (A := 16) (B := 1) (C := 2) (by norm_num) h1 h2 (by norm_num) (by norm_num)
      linarith
    have ht2 : |12 * α * (1 - u ^ 2) * (1 - u ^ 2)| ≤ 12 * |α| := by
      have h := abs_prod3_le (a := 12 * α) (b := 1 - u ^ 2) (c := 1 - u ^ 2)
        (A := 12 * |α|) (B := 1) (C := 1) h12a h1 h1 (by positivity) (by norm_num)
      linarith
    have ht3 : |(-32) * α * u * (u - 1 / 3) * (1 - u ^ 2)| ≤ (128 / 3) * |α| := by
      have h := abs_prod4_le (a := (-32) * α) (b := u) (c := u - 1 / 3) (d := 1 - u ^ 2)
        (A := 32 * |α|) (B := 1) (C := 4 / 3) (D := 1)
        h32a hu h3 h1 (by positivity) (by norm_num) (by norm_num)
      linarith
    have ht4 : |((-12) * α ^ 2) * (u - 1 / 3) ^ 2 * (1 - u ^ 2)| ≤ (64 / 3) * |α| ^ 2 := by
      have h := abs_prod3_le (a := (-12) * α ^ 2) (b := (u - 1 / 3) ^ 2) (c := 1 - u ^ 2)
        (A := 12 * |α| ^ 2) (B := 16 / 9) (C := 1) h12a2 h3sq h1 (by positivity) (by norm_num)
      linarith
    have ht5 : |((α ^ 3) * (u - 1 / 3) ^ 2) * (u - 1 / 3) ^ 2| ≤ (256 / 81) * |α| ^ 3 := by
      have h := abs_prod3_le (a := α ^ 3) (b := (u - 1 / 3) ^ 2) (c := (u - 1 / 3) ^ 2)
        (A := |α| ^ 3) (B := 16 / 9) (C := 16 / 9) ha3 h3sq h3sq (by positivity) (by norm_num)
      linarith
    have hX : |(16 * (1 - u ^ 2) * (1 - 3 * u ^ 2))
        + (12 * α * (1 - u ^ 2) * (1 - u ^ 2))
        + ((-32) * α * u * (u - 1 / 3) * (1 - u ^ 2))
        + (((-12) * α ^ 2) * (u - 1 / 3) ^ 2 * (1 - u ^ 2))
        + (((α ^ 3) * (u - 1 / 3) ^ 2) * (u - 1 / 3) ^ 2)|
        ≤ 32 + 12 * |α| + (128 / 3) * |α| + (64 / 3) * |α| ^ 2 + (256 / 81) * |α| ^ 3 :=
      abs_add5_le ht1 ht2 ht3 ht4 ht5
    have hstep := mul_le_mul_of_nonneg_left hX (abs_nonneg α)
    have hα : |α| ≤ (1 + α ^ 2) ^ 2 := abs_alpha_le_B2 α
    have hα2 : |α| ^ 2 ≤ (1 + α ^ 2) ^ 2 := abs_alpha_sq_le_B2 α
    have hα3 : |α| ^ 3 ≤ (1 + α ^ 2) ^ 2 := abs_alpha_cube_le_B2 α
    have hα4 : |α| ^ 4 ≤ (1 + α ^ 2) ^ 2 := abs_alpha_pow4_le_B2 α
    nlinarith [hstep, hα, hα2, hα3, hα4, hB]

/-! ## The angular jet bound -/

theorem DthIterGamGen (i : ℕ) (hi : i ≤ 4) (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
      ≤ 1000 * (1 + α ^ 2) ^ 2 * Work.Spaces.Gam α θ := by
  rw [Work.FTS.LocData.DthIter_Gam_Pf α i hi 0 θ hθ]
  have hG0 : 0 ≤ Work.Spaces.Gam α θ :=
    Real.rpow_nonneg (Work.Spaces.sin_mul_cos_sq_mem_Icc θ hθ).1 _
  have hPf : |Pf i (Real.cos (2 * θ)) α| ≤ 1000 * (1 + α ^ 2) ^ 2 :=
    Pf_abs_le i hi _ α (Real.abs_cos_le_one _)
  rw [abs_mul, abs_of_nonneg hG0]
  have h1 : Work.Spaces.Gam α θ * |Pf i (Real.cos (2 * θ)) α|
      ≤ Work.Spaces.Gam α θ * (1000 * (1 + α ^ 2) ^ 2) :=
    mul_le_mul_of_nonneg_left hPf hG0
  nlinarith [h1]

end Work.FTS.StrongPersist.Degen
