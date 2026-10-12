import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Conv.num_comparison`

Scalar bookkeeping for the `B³` convolution estimate.  With

* `X = 4|I| ℓ^{-3} (Cdec D⁸⁰) + 2 ℓ^{-3} ρmax χM` the two weighted pieces,
* `n ≤ 2 μ ℓ³` the particle-number bound,
* `|I| ≤ 16 π A`, `D⁸⁰ ℓ² ≤ A²` the lattice-sum / diluteness inputs,
* `ρmax ≤ Ccv (2R/ℓ)² (16 π A)` the high-density input,

one has

`X · n² · normB ≤ max(1, 512 π Cdec A²/R², 1024 π Ccv χM) · μ² A ℓ³ (R²/ℓ²) · normB`.

The proof is elementary: bound `n² ≤ (2μℓ³)²`, absorb the two negative powers
of `ℓ` into the two diluteness inequalities, and compare term by term with the
two branches of the maximum.

The `π` notation is the scoped `Real.pi` notation (`open scoped Real`).
-/

open scoped Real

namespace Work.BoseFixB3.Conv

theorem num_comparison {n : ℕ} {μ R ℓ A D Cdec Ccv χM I ρmax normB : ℝ}
    (hμ : 0 < μ) (hR : 0 < R) (hℓ : 0 < ℓ) (hA : 0 < A) (hD : 0 ≤ D)
    (hCdec : 0 ≤ Cdec) (hCcv : 0 ≤ Ccv) (hχM : 0 ≤ χM)
    (hn : (n : ℝ) ≤ 2 * μ * ℓ ^ 3) (hnB : 0 ≤ normB)
    (hI : |I| ≤ 16 * π * A) (hf : ρmax ≤ Ccv * (2 * R / ℓ) ^ 2 * (16 * π * A))
    (hDℓ : D ^ 80 * ℓ ^ 2 ≤ A ^ 2) :
    (4 * |I| * ℓ ^ (-(3 : ℤ)) * (Cdec * D ^ 80) + 2 * ℓ ^ (-(3 : ℤ)) * ρmax * χM)
        * ((n : ℝ) ^ 2 * normB)
      ≤ max 1 (max (512 * π * Cdec * A ^ 2 / R ^ 2) (1024 * π * Ccv * χM))
        * μ ^ 2 * A * ℓ ^ 3 * (R ^ 2 / ℓ ^ 2) * normB := by
  set M := max 1 (max (512 * π * Cdec * A ^ 2 / R ^ 2) (1024 * π * Ccv * χM)) with hM
  -- `n² ≤ (2 μL³)²`
  have hn2 : ((n : ℝ)) ^ 2 ≤ 4 * μ ^ 2 * ℓ ^ 6 := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [sq_nonneg (2 * μ * ℓ ^ 3 - (n : ℝ)), sq_nonneg (2 * μ * ℓ ^ 3), hμ, hℓ, hD]
  -- cleaned form of the `ρmax` bound
  have hf2 : ρmax * ℓ ^ 2 ≤ 64 * π * Ccv * A * R ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hf (by positivity : (0 : ℝ) ≤ ℓ ^ 2)
    have he : Ccv * (2 * R / ℓ) ^ 2 * (16 * π * A) * ℓ ^ 2 = 64 * π * Ccv * A * R ^ 2 := by
      field_simp
      ring
    linarith [h, he.le, he.ge]
  -- the two branches of the maximum
  have hM1 : 512 * π * Cdec * A ^ 2 / R ^ 2 ≤ M := by
    rw [hM]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hM2 : 1024 * π * Ccv * χM ≤ M := by
    rw [hM]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hM1c : 512 * π * Cdec * A ^ 2 ≤ M * R ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < R ^ 2)] at hM1
    exact hM1
  -- diluteness inequalities, cleared of `ℓ`-powers
  have t2 : D ^ 80 * (n : ℝ) ^ 2 * ℓ ^ 6 ≤ 4 * μ ^ 2 * A ^ 2 * ℓ ^ 10 := by
    calc D ^ 80 * (n : ℝ) ^ 2 * ℓ ^ 6
        = (D ^ 80 * ℓ ^ 2) * ((n : ℝ) ^ 2 * ℓ ^ 4) := by ring
      _ ≤ A ^ 2 * (4 * μ ^ 2 * ℓ ^ 6 * ℓ ^ 4) :=
            mul_le_mul hDℓ (mul_le_mul_of_nonneg_right hn2 (by positivity))
              (by positivity) (by positivity)
      _ = 4 * μ ^ 2 * A ^ 2 * ℓ ^ 10 := by ring
  have t3 : ρmax * (n : ℝ) ^ 2 * ℓ ^ 6 ≤ 256 * π * Ccv * A * R ^ 2 * μ ^ 2 * ℓ ^ 10 := by
    calc ρmax * (n : ℝ) ^ 2 * ℓ ^ 6
        = (ρmax * ℓ ^ 2) * ((n : ℝ) ^ 2 * ℓ ^ 4) := by ring
      _ ≤ (64 * π * Ccv * A * R ^ 2) * (4 * μ ^ 2 * ℓ ^ 6 * ℓ ^ 4) :=
            mul_le_mul hf2 (mul_le_mul_of_nonneg_right hn2 (by positivity))
              (by positivity) (by positivity)
      _ = 256 * π * Ccv * A * R ^ 2 * μ ^ 2 * ℓ ^ 10 := by ring
  -- the two summands against half the right-hand side
  have u1 : 4 * |I| * Cdec * (D ^ 80 * (n : ℝ) ^ 2 * ℓ ^ 6)
      ≤ 256 * π * Cdec * A ^ 3 * μ ^ 2 * ℓ ^ 10 := by
    calc 4 * |I| * Cdec * (D ^ 80 * (n : ℝ) ^ 2 * ℓ ^ 6)
        = (4 * |I|) * (Cdec * (D ^ 80 * (n : ℝ) ^ 2 * ℓ ^ 6)) := by ring
      _ ≤ (4 * (16 * π * A)) * (Cdec * (4 * μ ^ 2 * A ^ 2 * ℓ ^ 10)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hI (by norm_num))
              (mul_le_mul_of_nonneg_left t2 hCdec) (by positivity) (by positivity)
      _ = 256 * π * Cdec * A ^ 3 * μ ^ 2 * ℓ ^ 10 := by ring
  have u2 : 2 * χM * (ρmax * (n : ℝ) ^ 2 * ℓ ^ 6)
      ≤ 512 * π * Ccv * A * R ^ 2 * μ ^ 2 * χM * ℓ ^ 10 := by
    calc 2 * χM * (ρmax * (n : ℝ) ^ 2 * ℓ ^ 6)
        = 2 * (χM * (ρmax * (n : ℝ) ^ 2 * ℓ ^ 6)) := by ring
      _ ≤ 2 * (χM * (256 * π * Ccv * A * R ^ 2 * μ ^ 2 * ℓ ^ 10)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left t3 hχM) (by norm_num)
      _ = 512 * π * Ccv * A * R ^ 2 * μ ^ 2 * χM * ℓ ^ 10 := by ring
  have u3 : 256 * π * Cdec * A ^ 3 * μ ^ 2 * ℓ ^ 10 ≤ M * μ ^ 2 * A * R ^ 2 * ℓ ^ 10 / 2 := by
    calc 256 * π * Cdec * A ^ 3 * μ ^ 2 * ℓ ^ 10
        = (512 * π * Cdec * A ^ 2) * (μ ^ 2 * A * ℓ ^ 10 / 2) := by ring
      _ ≤ (M * R ^ 2) * (μ ^ 2 * A * ℓ ^ 10 / 2) :=
            mul_le_mul_of_nonneg_right hM1c (by positivity)
      _ = M * μ ^ 2 * A * R ^ 2 * ℓ ^ 10 / 2 := by ring
  have u4 : 512 * π * Ccv * A * R ^ 2 * μ ^ 2 * χM * ℓ ^ 10
      ≤ M * μ ^ 2 * A * R ^ 2 * ℓ ^ 10 / 2 := by
    calc 512 * π * Ccv * A * R ^ 2 * μ ^ 2 * χM * ℓ ^ 10
        = (1024 * π * Ccv * χM) * (μ ^ 2 * A * R ^ 2 * ℓ ^ 10 / 2) := by ring
      _ ≤ M * (μ ^ 2 * A * R ^ 2 * ℓ ^ 10 / 2) :=
            mul_le_mul_of_nonneg_right hM2 (by positivity)
      _ = M * μ ^ 2 * A * R ^ 2 * ℓ ^ 10 / 2 := by ring
  -- the polynomial core, with `ℓ` cleared
  have hpoly : (4 * |I| * Cdec * D ^ 80 + 2 * ρmax * χM) * (n : ℝ) ^ 2 * ℓ ^ 6
      ≤ M * μ ^ 2 * A * R ^ 2 * ℓ ^ 10 := by
    have hL : (4 * |I| * Cdec * D ^ 80 + 2 * ρmax * χM) * (n : ℝ) ^ 2 * ℓ ^ 6
        = 4 * |I| * Cdec * (D ^ 80 * (n : ℝ) ^ 2 * ℓ ^ 6)
          + 2 * χM * (ρmax * (n : ℝ) ^ 2 * ℓ ^ 6) := by ring
    rw [hL]
    linarith [u1, u2, u3, u4]
  -- reinsert `normB` and divide by `ℓ⁶`
  have hcleared : (4 * |I| * Cdec * D ^ 80 + 2 * ρmax * χM) * ((n : ℝ) ^ 2 * normB)
      ≤ M * μ ^ 2 * A * R ^ 2 * ℓ ^ 4 * normB := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < ℓ ^ 6)
    calc (4 * |I| * Cdec * D ^ 80 + 2 * ρmax * χM) * ((n : ℝ) ^ 2 * normB) * ℓ ^ 6
        = ((4 * |I| * Cdec * D ^ 80 + 2 * ρmax * χM) * (n : ℝ) ^ 2 * ℓ ^ 6) * normB := by ring
      _ ≤ (M * μ ^ 2 * A * R ^ 2 * ℓ ^ 10) * normB :=
            mul_le_mul_of_nonneg_right hpoly hnB
      _ = (M * μ ^ 2 * A * R ^ 2 * ℓ ^ 4 * normB) * ℓ ^ 6 := by ring
  -- multiplying by `ℓ³` turns `ℓ^{-3}` into `1` and `ℓ³·(R²/ℓ²)` into `R²ℓ`
  have e1 : (4 * |I| * ℓ ^ (-(3 : ℤ)) * (Cdec * D ^ 80) + 2 * ℓ ^ (-(3 : ℤ)) * ρmax * χM)
        * ℓ ^ 3 = 4 * |I| * Cdec * D ^ 80 + 2 * ρmax * χM := by
    have hzp : ℓ ^ (-(3 : ℤ)) = (ℓ ^ 3)⁻¹ := by rw [zpow_neg]; norm_num
    rw [hzp]
    field_simp
  have e2 : (M * μ ^ 2 * A * ℓ ^ 3 * (R ^ 2 / ℓ ^ 2) * normB) * ℓ ^ 3
      = M * μ ^ 2 * A * R ^ 2 * ℓ ^ 4 * normB := by
    field_simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < ℓ ^ 3)
  calc (4 * |I| * ℓ ^ (-(3 : ℤ)) * (Cdec * D ^ 80) + 2 * ℓ ^ (-(3 : ℤ)) * ρmax * χM)
          * ((n : ℝ) ^ 2 * normB) * ℓ ^ 3
      = ((4 * |I| * ℓ ^ (-(3 : ℤ)) * (Cdec * D ^ 80)
            + 2 * ℓ ^ (-(3 : ℤ)) * ρmax * χM) * ℓ ^ 3) * ((n : ℝ) ^ 2 * normB) := by ring
    _ = (4 * |I| * Cdec * D ^ 80 + 2 * ρmax * χM) * ((n : ℝ) ^ 2 * normB) := by rw [e1]
    _ ≤ M * μ ^ 2 * A * R ^ 2 * ℓ ^ 4 * normB := hcleared
    _ = (M * μ ^ 2 * A * ℓ ^ 3 * (R ^ 2 / ℓ ^ 2) * normB) * ℓ ^ 3 := e2.symm

end Work.BoseFixB3.Conv
