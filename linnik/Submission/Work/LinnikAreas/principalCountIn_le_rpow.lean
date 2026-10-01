import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Work.ZeroDensity.Zeta.ZetaZeroDefs
import Submission.Work.ZeroDensity.Basic
import Submission.Work.LinnikAreas.PrincipalZeroCount

namespace Work.LinnikAreas

/-- The principal character mod `q` has, for every `q`, the same zero multiset: its primitive
character is the trivial character mod `1`, whose completed L-function is `Λ`.  Hence the zero
count of the principal character is independent of the level `q` (it is the count of the
non-trivial zeros of `ζ` in the rectangle). -/
lemma zeroCountIn_one_level_indep (q : ℕ) [NeZero q] (σ T : ℝ) :
    zeroCountIn (1 : DirichletCharacter ℂ q) σ T = zeroCountIn (1 : DirichletCharacter ℂ 2) σ T := by
  rw [zeroCountIn, zeroCountIn]
  refine finsum_congr (fun ρ => ?_)
  by_cases h : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
  · simp only [h, zeroMult_one_eq q, zeroMult_one_eq 2]
  · simp only [h, if_false]

/-- For `T ≥ 1`, the (logarithmic) factor `(T+2)(log(2(T+2)) + 2)` that bounds the number of
non-trivial zeros of `ζ` up to height `T` is dominated by `100·T^{3/2}`. -/
lemma mul_log_bound (T : ℝ) (hT : 1 ≤ T) :
    (T + 2) * (Real.log (2 * (T + 2)) + 2) ≤ (100 : ℝ) * T ^ ((3 : ℝ) / 2) := by
  have hTpos : (0 : ℝ) < T := by linarith
  have hx0 : (0 : ℝ) ≤ 2 * (T + 2) := by linarith
  have hlog1 : Real.log (2 * (T + 2)) ≤ (2 * (T + 2)) ^ ((1 : ℝ) / 2) / (1 / 2) :=
    Real.log_le_rpow_div hx0 (by norm_num)
  have hlog2 : (2 * (T + 2)) ^ ((1 : ℝ) / 2) / (1 / 2) = 2 * (2 * (T + 2)) ^ ((1 : ℝ) / 2) := by
    ring
  have hle : 2 * (T + 2) ≤ 6 * T := by linarith
  have hrpow1 : (2 * (T + 2)) ^ ((1 : ℝ) / 2) ≤ (6 * T) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hx0 hle (by norm_num)
  have hrpow2 : (6 * T) ^ ((1 : ℝ) / 2) = (6 : ℝ) ^ ((1 : ℝ) / 2) * T ^ ((1 : ℝ) / 2) :=
    Real.mul_rpow (by norm_num) (le_of_lt hTpos)
  have h6 : (6 : ℝ) ^ ((1 : ℝ) / 2) ≤ 6 := by
    have h : (6 : ℝ) ^ ((1 : ℝ) / 2) ≤ (6 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6) (by norm_num)
    simpa using h
  have hT12nn : (0 : ℝ) ≤ T ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hTpos) _
  have hT12 : (1 : ℝ) ≤ T ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hT (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
    simpa using h
  have hrpow3 : (6 * T) ^ ((1 : ℝ) / 2) ≤ 6 * T ^ ((1 : ℝ) / 2) := by
    rw [hrpow2]
    nlinarith [h6, hT12nn]
  have hlog3 : Real.log (2 * (T + 2)) ≤ 12 * T ^ ((1 : ℝ) / 2) := by
    linarith [hlog1, hlog2, hrpow3, hrpow1]
  have hlog4 : Real.log (2 * (T + 2)) + 2 ≤ 14 * T ^ ((1 : ℝ) / 2) := by
    have h2 : (2 : ℝ) ≤ 2 * T ^ ((1 : ℝ) / 2) := by linarith [hT12]
    linarith [hlog3, h2]
  have hT2le : T + 2 ≤ 3 * T := by linarith
  have hprod : (T + 2) * (Real.log (2 * (T + 2)) + 2) ≤ (3 * T) * (14 * T ^ ((1 : ℝ) / 2)) := by
    apply mul_le_mul hT2le hlog4
    · linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 * (T + 2) by linarith)]
    · linarith
  have hrpowT : T * T ^ ((1 : ℝ) / 2) = T ^ ((3 : ℝ) / 2) := by
    calc T * T ^ ((1 : ℝ) / 2) = T ^ (1 : ℝ) * T ^ ((1 : ℝ) / 2) := by rw [Real.rpow_one]
      _ = T ^ ((1 : ℝ) + (1 : ℝ) / 2) := (Real.rpow_add hTpos 1 ((1 : ℝ) / 2)).symm
      _ = T ^ ((3 : ℝ) / 2) := by norm_num
  calc (T + 2) * (Real.log (2 * (T + 2)) + 2)
      ≤ (3 * T) * (14 * T ^ ((1 : ℝ) / 2)) := hprod
    _ = 42 * (T * T ^ ((1 : ℝ) / 2)) := by ring
    _ = 42 * T ^ ((3 : ℝ) / 2) := by rw [hrpowT]
    _ ≤ (100 : ℝ) * T ^ ((3 : ℝ) / 2) := by
        have : (0 : ℝ) ≤ T ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hTpos) _
        linarith

theorem principalCountIn_le_rpow : ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      Work.LinnikAreas.zeroCountIn (1 : DirichletCharacter ℂ q) σ T ≤ C * T ^ ((3 : ℝ) / 2) := by
  obtain ⟨c, hcpos, hc⟩ := PrincipalZeroCount
  refine ⟨100 * c, by positivity, ?_⟩
  intro q hq hqne σ T hσ0 hσ1 hT
  rw [zeroCountIn_one_level_indep q σ T]
  have hb := hc 2 (by norm_num) σ T hσ0 hσ1 hT
  have harith := mul_log_bound T hT
  calc zeroCountIn (1 : DirichletCharacter ℂ 2) σ T
      ≤ c * (T + 2) * (Real.log (((2 : ℕ) : ℝ) * (T + 2)) + 2) := hb
    _ = c * ((T + 2) * (Real.log (2 * (T + 2)) + 2)) := by push_cast; ring
    _ ≤ c * ((100 : ℝ) * T ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left harith (le_of_lt hcpos)
    _ = (100 * c) * T ^ ((3 : ℝ) / 2) := by ring

end Work.LinnikAreas
