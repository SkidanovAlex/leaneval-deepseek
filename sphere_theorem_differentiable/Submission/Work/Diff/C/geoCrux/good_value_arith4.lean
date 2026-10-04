import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.geoCrux

/-- Core numerical bound behind `good_value_arith4`.

With `u = √c ∈ (0, 1/√96]`, `w = ε₁π ≥ 0`, `γ ∈ [0, 53u + 50w]` and `ρ ≥ 0` satisfying
`ρ² = 2u² - u⁴` and `ρ ≤ (3/2)u` (so that `ρ` plays the role of `√(2c - c²)` at `u² = c`), we have
`(4u² + (1 - cos γ))² + (ρ + sin γ)² ≤ (58u + 59w)²`.

The proof expands the square, uses `(1-cos γ)² + sin²γ = 2(1-cos γ)`, the elementary bounds
`1 - cos γ ≤ γ²/2`, `sin γ ≤ γ` on `γ ≥ 0`, and `1 + 4u² ≤ 25/24`. -/
lemma geoCrux4_core {u w γ ρ : ℝ} (hu0 : 0 ≤ u) (hu2le : u ^ 2 ≤ 1 / 96) (hw0 : 0 ≤ w)
    (hγ0 : 0 ≤ γ) (hγG : γ ≤ 53 * u + 50 * w)
    (hρ0 : 0 ≤ ρ) (hρ2 : ρ ^ 2 = 2 * u ^ 2 - u ^ 4) (hρu : ρ ≤ (3 / 2) * u) :
    (4 * u ^ 2 + (1 - Real.cos γ)) ^ 2 + (ρ + Real.sin γ) ^ 2 ≤ (58 * u + 59 * w) ^ 2 := by
  have hsin : Real.sin γ ^ 2 + Real.cos γ ^ 2 = 1 := Real.sin_sq_add_cos_sq γ
  have hkey : (4 * u ^ 2 + (1 - Real.cos γ)) ^ 2 + (ρ + Real.sin γ) ^ 2
      = 15 * u ^ 4 + 2 * u ^ 2 + 2 * (1 - Real.cos γ) * (1 + 4 * u ^ 2)
        + 2 * ρ * Real.sin γ := by
    nlinarith [hsin, hρ2]
  have hT1 : 15 * u ^ 4 + 2 * u ^ 2 ≤ (69 / 32) * u ^ 2 := by nlinarith [hu2le, hu0]
  have hA1le : 1 - Real.cos γ ≤ γ ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := γ)]
  have hg1 : 1 + 4 * u ^ 2 ≤ 25 / 24 := by nlinarith [hu2le]
  have hT2 : 2 * (1 - Real.cos γ) * (1 + 4 * u ^ 2) ≤ (25 / 24) * (53 * u + 50 * w) ^ 2 := by
    have hstep : 2 * (1 - Real.cos γ) * (1 + 4 * u ^ 2) ≤ γ ^ 2 * (25 / 24) := by
      apply mul_le_mul
      · linarith [hA1le]
      · exact hg1
      · positivity
      · positivity
    have h32 : γ ^ 2 ≤ (53 * u + 50 * w) ^ 2 := pow_le_pow_left₀ hγ0 hγG 2
    calc 2 * (1 - Real.cos γ) * (1 + 4 * u ^ 2) ≤ γ ^ 2 * (25 / 24) := hstep
      _ = (25 / 24) * γ ^ 2 := by ring
      _ ≤ (25 / 24) * (53 * u + 50 * w) ^ 2 := mul_le_mul_of_nonneg_left h32 (by norm_num)
  have hS1 : Real.sin γ ≤ γ := Real.sin_le hγ0
  have hT3 : 2 * ρ * Real.sin γ ≤ 3 * u * (53 * u + 50 * w) := by
    have h1 : 2 * ρ * Real.sin γ ≤ 2 * ρ * γ := mul_le_mul_of_nonneg_left hS1 (by linarith)
    have h2 : 2 * ρ * γ ≤ 2 * ((3 / 2) * u) * γ := by
      have : ρ * γ ≤ ((3 / 2) * u) * γ := mul_le_mul_of_nonneg_right hρu hγ0
      linarith
    have h3 : 3 * u * γ ≤ 3 * u * (53 * u + 50 * w) := mul_le_mul_of_nonneg_left hγG (by linarith)
    linarith [h1, h2, h3]
  have hsq : (53 * u + 50 * w) ^ 2 = 2809 * u ^ 2 + 5300 * u * w + 2500 * w ^ 2 := by ring
  have hmid : (25 / 24) * (53 * u + 50 * w) ^ 2 ≤ 2927 * u ^ 2 + 5521 * u * w + 2605 * w ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg u, sq_nonneg w, mul_nonneg hu0 hw0]
  have hmid2 : 3 * u * (53 * u + 50 * w) ≤ 159 * u ^ 2 + 150 * u * w := by nlinarith [hu0, hw0]
  have hsq2 : (58 * u + 59 * w) ^ 2 = 3364 * u ^ 2 + 6844 * u * w + 3481 * w ^ 2 := by ring
  rw [hkey, hsq2]
  linarith [hT1, hT2, hmid, hT3, hmid2, sq_nonneg u, sq_nonneg w, mul_nonneg hu0 hw0]

theorem good_value_arith4 {c ε₁ A B γ' L : ℝ} (hc : 0 < c) (hc96 : c ≤ 1 / 96)
    (hε₁ : 0 ≤ ε₁) (hnum : 4 * ε₁ * Real.pi < c) (hL : L = Real.sqrt c + ε₁ * Real.pi)
    (hγ0 : 0 ≤ γ')
    (hγup : γ' ≤ min (50 * (Real.sqrt c + ε₁ * Real.pi) + 2.6 * Real.sqrt c) (Real.pi / 2))
    (hA : |A| ≤ 4 * c + (1 - Real.cos γ')) (hB : |B| ≤ Real.sqrt (2 * c - c * c) + Real.sin γ') :
    min (|A| + |B| * Real.cos γ') (Real.sqrt (A ^ 2 + B ^ 2)) + ε₁ * Real.pi + 2 * Real.sqrt c
      ≤ 60 * L := by
  set u : ℝ := Real.sqrt c with hu
  set w : ℝ := ε₁ * Real.pi with hw
  set ρ : ℝ := Real.sqrt (2 * c - c * c) with hρdef
  have hc0 : 0 ≤ c := le_of_lt hc
  have hu0 : 0 ≤ u := by rw [hu]; exact Real.sqrt_nonneg c
  have hu2 : u ^ 2 = c := by rw [hu]; exact Real.sq_sqrt hc0
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact Real.sqrt_nonneg _
  have h2cc0 : 0 ≤ 2 * c - c * c := by nlinarith [hc, hc96]
  have hρ2 : ρ ^ 2 = 2 * u ^ 2 - u ^ 4 := by
    have hu4 : u ^ 4 = c ^ 2 := by rw [← hu2]; ring
    rw [hρdef, Real.sq_sqrt h2cc0, hu2, hu4]; ring
  have hρu : ρ ≤ (3 / 2) * u := by
    rw [hρdef, Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ (3 / 2) * u)]
    nlinarith [hu2, hc, hc96]
  have hγπ2 : γ' ≤ Real.pi / 2 := le_trans hγup (min_le_right _ _)
  have hγG : γ' ≤ 53 * u + 50 * w := by
    have h1 : γ' ≤ 50 * (u + w) + 2.6 * u := le_trans hγup (min_le_left _ _)
    linarith
  have hcore := geoCrux4_core hu0 (by rw [hu2]; exact hc96) hw0 hγ0 hγG hρ0 hρ2 hρu
  have hA' : |A| ≤ 4 * u ^ 2 + (1 - Real.cos γ') := by rw [hu2]; exact hA
  have hB' : |B| ≤ ρ + Real.sin γ' := hB
  have hA2 : A ^ 2 ≤ (4 * u ^ 2 + (1 - Real.cos γ')) ^ 2 :=
    sq_le_sq' (abs_le.mp hA').1 (abs_le.mp hA').2
  have hB2 : B ^ 2 ≤ (ρ + Real.sin γ') ^ 2 :=
    sq_le_sq' (abs_le.mp hB').1 (abs_le.mp hB').2
  have hY2 : A ^ 2 + B ^ 2 ≤ (4 * u ^ 2 + (1 - Real.cos γ')) ^ 2 + (ρ + Real.sin γ') ^ 2 :=
    add_le_add hA2 hB2
  have hsqrt1 : Real.sqrt (A ^ 2 + B ^ 2)
      ≤ Real.sqrt ((4 * u ^ 2 + (1 - Real.cos γ')) ^ 2 + (ρ + Real.sin γ') ^ 2) :=
    Real.sqrt_le_sqrt hY2
  have hsqrt2 : Real.sqrt ((4 * u ^ 2 + (1 - Real.cos γ')) ^ 2 + (ρ + Real.sin γ') ^ 2)
      ≤ 58 * u + 59 * w := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith [hu0, hw0], hcore⟩
  have hmin : min (|A| + |B| * Real.cos γ') (Real.sqrt (A ^ 2 + B ^ 2)) ≤ 58 * u + 59 * w :=
    le_trans (min_le_right _ _) (le_trans hsqrt1 hsqrt2)
  rw [hL]
  linarith [hmin]

end Work.Diff.C.geoCrux
