import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.FanTri.radius_constants

namespace Work.EQ.FanTri

/-- **Constants for the uniform radius theorem (final form, factor 9).**
For `0 < a < 1`, `lam = eqLam a ∈ (0,1)`, and `K, C > 0` there are `ρ, 𝔸, 𝒞, 𝔹, 𝒟` with
`ρ ≤ 1`, `𝔸, 𝔹 ≥ 1`, `𝒞, 𝒟 ≥ 0`, `ρ > 0` and
`ρ(𝔸 + 𝒞 + 𝔹K + 𝒟K) ≤ (1-a)/8`,
`C(𝔹+𝒟·lam)²K²lam²ρ ≤ 𝒞(1-lam²)((1-a)/2)²`,
`9C(𝔹+𝒟·lam)𝔸ρ ≤ 𝒟(1-lam)((1-a)/2)²`,
`9C(𝔹+𝒟·lam)𝒞ρ·lam² ≤ 𝒟(1-lam)((1-a)/2)²`,
`9C(𝔹+𝒟·lam)²K·lam·ρ ≤ 𝒟(1-lam)((1-a)/2)²`.
Satisfiable with `𝔸 = 𝔹 = 𝒟 = 1`, `𝒞 = 2C(1+lam)²K²lam²ρ/((1-lam²)((1-a)/2)²)` and `ρ` an
explicit small minimum of positive quantities; every condition is then of the form "ρ small".
Same proof scheme as the already-proved `Work.EQ.FanTri.radius_constants`
(`Submission/Work/EQ/FanTri/radius_constants.lean`; it has the factor 3 and lacks the fifth
condition — this one has `9` and the extra `9C(𝔹+𝒟lam)²K·lam·ρ` condition, both used by the
chosen split of the correction terms in the `branchComp_radius` induction). -/
theorem radius_constants_v3 {a lam K C : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hlam : lam = Work.EQ.eqLam a) (hK : 0 < K) (hC : 0 < C) :
    ∃ (ρ 𝔸 𝒞 𝔹 𝒟 : ℝ), 0 < ρ ∧ 1 ≤ 𝔸 ∧ 1 ≤ 𝔹 ∧ 0 ≤ 𝒞 ∧ 0 ≤ 𝒟 ∧ ρ ≤ 1 ∧
      ρ * (𝔸 + 𝒞 + 𝔹 * K + 𝒟 * K) ≤ (1 - a) / 8 ∧
      C * (𝔹 + 𝒟 * lam) ^ 2 * K ^ 2 * lam ^ 2 * ρ ≤ 𝒞 * (1 - lam ^ 2) * ((1 - a) / 2) ^ 2 ∧
      9 * C * (𝔹 + 𝒟 * lam) * 𝔸 * ρ ≤ 𝒟 * (1 - lam) * ((1 - a) / 2) ^ 2 ∧
      9 * C * (𝔹 + 𝒟 * lam) * 𝒞 * ρ * lam ^ 2 ≤ 𝒟 * (1 - lam) * ((1 - a) / 2) ^ 2 ∧
      9 * C * (𝔹 + 𝒟 * lam) ^ 2 * K * lam * ρ ≤ 𝒟 * (1 - lam) * ((1 - a) / 2) ^ 2 := by
  -- Basic positivity facts.
  have hlam0 : 0 < lam := by rw [hlam]; unfold Work.EQ.eqLam; positivity
  have hlam1 : lam < 1 := by
    rw [hlam]; unfold Work.EQ.eqLam; rw [div_lt_one (by linarith)]; linarith
  have h1l : 0 < 1 - lam := by linarith
  have h1l2 : 0 < 1 - lam ^ 2 := by nlinarith [hlam0, hlam1]
  have h1plam : 0 < 1 + lam := by linarith
  have hbe : 0 < (1 - a) / 2 := by linarith
  have h1a : 0 < 1 - a := by linarith
  -- The quadratic coefficient of `𝒞` as a multiple of `ρ`: `𝒞 = γ ρ`.
  set γ : ℝ := 2 * C * (1 + lam) ^ 2 * K ^ 2 * lam ^ 2 / ((1 - lam ^ 2) * ((1 - a) / 2) ^ 2)
    with hγ
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  -- Upper bounds on `ρ`, one per side condition.
  set p1 : ℝ := (1 - a) / 8 / (1 + 2 * K + γ) with hp1
  set p3 : ℝ := (1 - lam) * ((1 - a) / 2) ^ 2 / (9 * C * (1 + lam)) with hp3
  set p4 : ℝ := (1 - lam) * ((1 - a) / 2) ^ 2 / (9 * C * (1 + lam) * γ * lam ^ 2) with hp4
  set p5 : ℝ := (1 - lam) * ((1 - a) / 2) ^ 2 / (9 * C * (1 + lam) ^ 2 * K * lam) with hp5
  have hp1pos : 0 < p1 := by rw [hp1]; positivity
  have hp3pos : 0 < p3 := by rw [hp3]; positivity
  have hp4pos : 0 < p4 := by rw [hp4]; positivity
  have hp5pos : 0 < p5 := by rw [hp5]; positivity
  -- The chosen radius, a minimum of `1` and the four bounds.
  set ρ : ℝ := min 1 (min p1 (min p3 (min p4 p5))) with hρ
  have hρ0 : 0 < ρ := by
    rw [hρ]
    exact lt_min one_pos (lt_min hp1pos (lt_min hp3pos (lt_min hp4pos hp5pos)))
  have hρ_le_one : ρ ≤ 1 := by rw [hρ]; exact min_le_left _ _
  have hρ_le_p1 : ρ ≤ p1 := by
    rw [hρ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_le_p3 : ρ ≤ p3 := by
    rw [hρ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ_le_p4 : ρ ≤ p4 := by
    rw [hρ]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρ_le_p5 : ρ ≤ p5 := by
    rw [hρ]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨ρ, 1, γ * ρ, 1, 1, hρ0, le_refl 1, le_refl 1, by positivity, by norm_num,
    hρ_le_one, ?_, ?_, ?_, ?_, ?_⟩
  · -- (R1): `ρ (𝔸 + 𝒞 + 𝔹K + 𝒟K) ≤ (1-a)/8`.
    simp only [one_mul]
    have hd : 0 < 1 + 2 * K + γ := by linarith [hK, hγ0]
    have h1a' : ρ * (1 + 2 * K + γ) ≤ (1 - a) / 8 := by
      have h := mul_le_mul_of_nonneg_right hρ_le_p1 (le_of_lt hd)
      have hp1' : p1 * (1 + 2 * K + γ) = (1 - a) / 8 := by rw [hp1]; field_simp
      rwa [hp1'] at h
    have hρsq : ρ ^ 2 ≤ ρ := by nlinarith [hρ0, hρ_le_one]
    have hγρ : γ * ρ ^ 2 ≤ γ * ρ := mul_le_mul_of_nonneg_left hρsq (le_of_lt hγ0)
    nlinarith [h1a', hγρ, hρ0]
  · -- (R2): `C (1+lam)² K² lam² ρ ≤ 𝒞 (1-lam²) ((1-a)/2)²`; equality up to the factor `2`.
    simp only [one_mul]
    have hγv : γ * (1 - lam ^ 2) * ((1 - a) / 2) ^ 2 = 2 * (C * (1 + lam) ^ 2 * K ^ 2 * lam ^ 2) := by
      rw [hγ]; field_simp
    have hm : 0 ≤ C * (1 + lam) ^ 2 * K ^ 2 * lam ^ 2 * ρ := by positivity
    nlinarith [hγv, hm]
  · -- (R3): `9 C (1+lam) 𝔸 ρ ≤ 𝒟 (1-lam) ((1-a)/2)²` with `𝔸 = 𝒟 = 1`.
    simp only [one_mul]
    have hd3 : 0 < 9 * C * (1 + lam) := by positivity
    have h := mul_le_mul_of_nonneg_left hρ_le_p3 (le_of_lt hd3)
    have hp3' : 9 * C * (1 + lam) * p3 = (1 - lam) * ((1 - a) / 2) ^ 2 := by rw [hp3]; field_simp
    rw [hp3'] at h
    linarith [h]
  · -- (R4): `9 C (1+lam) 𝒞 ρ lam² ≤ 𝒟 (1-lam) ((1-a)/2)²`; this is the constraint giving `p4`.
    simp only [one_mul]
    have hρsq : ρ ^ 2 ≤ p4 := by nlinarith [hρ0, hρ_le_one, hρ_le_p4]
    have hd4 : 0 ≤ 9 * C * (1 + lam) * γ * lam ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hρsq hd4
    have hp4' : 9 * C * (1 + lam) * γ * lam ^ 2 * p4 = (1 - lam) * ((1 - a) / 2) ^ 2 := by
      rw [hp4]; field_simp
    rw [hp4'] at h
    nlinarith [h]
  · -- (R5): `9 C (1+lam)² K lam ρ ≤ 𝒟 (1-lam) ((1-a)/2)²` with `𝒟 = 1`.
    simp only [one_mul]
    have hd5 : 0 < 9 * C * (1 + lam) ^ 2 * K * lam := by positivity
    have h := mul_le_mul_of_nonneg_left hρ_le_p5 (le_of_lt hd5)
    have hp5' : 9 * C * (1 + lam) ^ 2 * K * lam * p5 = (1 - lam) * ((1 - a) / 2) ^ 2 := by
      rw [hp5]; field_simp
    rw [hp5'] at h
    linarith [h]

end Work.EQ.FanTri
