import Mathlib
import Submission.Work.EQ.DefsCore

namespace Work.EQ.FanTri

/-- **Constants for the uniform radius theorem.**
For `0 < a < 1`, `lam = eqLam a ∈ (0,1)`, and `K, C > 0` there are constants
`ρ, 𝔸, 𝒞, 𝔹, 𝒟` with `ρ ≤ 1`, `𝔸, 𝔹 ≥ 1`, `𝒞, 𝒟 ≥ 0` satisfying the four inequalities

`ρ(𝔸 + 𝒞 + 𝔹K + 𝒟K) ≤ (1-a)/8`,
`C(𝔹+𝒟·lam)²K²lam²ρ ≤ 𝒞(1-lam²)((1-a)/2)²`,
`3C(𝔹+𝒟·lam)𝔸ρ ≤ 𝒟(1-lam)((1-a)/2)²`,
`3C(𝔹+𝒟·lam)𝒞ρ·lam² ≤ 𝒟(1-lam)((1-a)/2)²`.

These are exactly the numerical side conditions of the induction proving
`Work.EQ.FanTri.branchComp_radius` (all of them are of the form "ρ small enough", once `𝒞` and
`𝒟` are chosen as explicit multiples of `ρ`), so they are satisfiable with `𝔸 = 𝔹 = 𝒟 = 1`,
`𝒞 = 2C(1+lam)²K²lam²ρ/((1-lam²)((1-a)/2)²)` and `ρ` an explicit small minimum. -/
theorem radius_constants {a lam K C : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hlam : lam = Work.EQ.eqLam a) (hK : 0 < K) (hC : 0 < C) :
    ∃ (ρ 𝔸 𝒞 𝔹 𝒟 : ℝ), 0 < ρ ∧ 1 ≤ 𝔸 ∧ 1 ≤ 𝔹 ∧ 0 ≤ 𝒞 ∧ 0 ≤ 𝒟 ∧ ρ ≤ 1 ∧
      ρ * (𝔸 + 𝒞 + 𝔹 * K + 𝒟 * K) ≤ (1 - a) / 8 ∧
      C * (𝔹 + 𝒟 * lam) ^ 2 * K ^ 2 * lam ^ 2 * ρ ≤ 𝒞 * (1 - lam ^ 2) * ((1 - a) / 2) ^ 2 ∧
      3 * C * (𝔹 + 𝒟 * lam) * 𝔸 * ρ ≤ 𝒟 * (1 - lam) * ((1 - a) / 2) ^ 2 ∧
      3 * C * (𝔹 + 𝒟 * lam) * 𝒞 * ρ * lam ^ 2 ≤ 𝒟 * (1 - lam) * ((1 - a) / 2) ^ 2 := by
  -- `lam = (1-a)/(1+a) ∈ (0,1)`.
  have hlam0 : 0 < lam := by rw [hlam, Work.EQ.eqLam]; exact div_pos (by linarith) (by linarith)
  have hlam1 : lam < 1 := by
    rw [hlam, Work.EQ.eqLam, div_lt_one (by linarith)]; linarith
  have h1s : 0 < 1 - lam := by linarith
  have h1s2 : 0 < 1 - lam ^ 2 := by nlinarith [sq_nonneg lam, sq_nonneg (1 - lam)]
  -- Write `β = (1-a)/2 > 0`; all conditions are of the form `ρ small enough`.
  set β : ℝ := (1 - a) / 2 with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  -- The multiplier `M` with `𝒞 = M·ρ`; condition (R2) holds for *every* `ρ > 0` with this `M`.
  set M : ℝ := 2 * C * (1 + lam) ^ 2 * K ^ 2 * lam ^ 2 / ((1 - lam ^ 2) * β ^ 2) with hM
  have h1plam : 0 < 1 + lam := by linarith
  have hprod0 : 0 < 2 * C * (1 + lam) ^ 2 * K ^ 2 * lam ^ 2 := by positivity
  have hM0 : 0 < M := by
    rw [hM]; exact div_pos hprod0 (mul_pos h1s2 (pow_pos hβ0 2))
  have hMval : M * (1 - lam ^ 2) * β ^ 2 = 2 * C * (1 + lam) ^ 2 * K ^ 2 * lam ^ 2 := by
    rw [hM]; field_simp
  have hden1 : 0 < 1 + 2 * K + M := by linarith
  have hden2 : 0 < 3 * C * (1 + lam) := by positivity
  have hden3 : 0 < 3 * C * (1 + lam) * M * lam ^ 2 := by positivity
  have hnum : 0 < (1 - lam) * β ^ 2 := mul_pos h1s (pow_pos hβ0 2)
  -- The explicit small radius `ρ`: a minimum of four positive quantities.
  set ρ : ℝ := min (1/2) (min (β / 4 / (1 + 2 * K + M))
      (min ((1 - lam) * β ^ 2 / (3 * C * (1 + lam)))
           ((1 - lam) * β ^ 2 / (3 * C * (1 + lam) * M * lam ^ 2)))) with hρ
  have hρ0 : 0 < ρ := by
    rw [hρ]
    exact lt_min (by norm_num) (lt_min (div_pos (by positivity : (0:ℝ) < β / 4) hden1)
      (lt_min (div_pos hnum hden2) (div_pos hnum hden3)))
  have hρle_half : ρ ≤ 1/2 := by rw [hρ]; exact min_le_left _ _
  have hρle_A : ρ ≤ β / 4 / (1 + 2 * K + M) := by
    rw [hρ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρle_B : ρ ≤ (1 - lam) * β ^ 2 / (3 * C * (1 + lam)) := by
    rw [hρ]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρle_C : ρ ≤ (1 - lam) * β ^ 2 / (3 * C * (1 + lam) * M * lam ^ 2) := by
    rw [hρ]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hρle1 : ρ ≤ 1 := by linarith
  have hsq : ρ ^ 2 ≤ ρ := by nlinarith [hρ0, hρle1]
  have hA : ρ * (1 + 2 * K + M) ≤ β / 4 := (le_div_iff₀ hden1).mp hρle_A
  have hB : ρ * (3 * C * (1 + lam)) ≤ (1 - lam) * β ^ 2 := (le_div_iff₀ hden2).mp hρle_B
  have hCc : ρ * (3 * C * (1 + lam) * M * lam ^ 2) ≤ (1 - lam) * β ^ 2 :=
    (le_div_iff₀ hden3).mp hρle_C
  refine ⟨ρ, 1, M * ρ, 1, 1, hρ0, le_refl 1, le_refl 1, by positivity, by norm_num,
    hρle1, ?_, ?_, ?_, ?_⟩
  · -- (R1)
    simp only [one_mul]; nlinarith [hA, hsq, hM0, hρ0]
  · -- (R2): `M` was chosen so that this holds for every `ρ`.
    simp only [one_mul]; nlinarith [hMval, hρ0]
  · -- (R3a)
    simp only [one_mul]; nlinarith [hB]
  · -- (R3b)
    simp only [one_mul]; nlinarith [hCc, hsq, hρ0]

end Work.EQ.FanTri
