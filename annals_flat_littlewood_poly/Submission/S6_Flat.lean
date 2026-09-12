import Submission.S6Core
import Submission.NumC
import Submission.NumSe
import Submission.NumG
import Submission.NumUp
import Submission.LittlewoodFlat

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

open FlatLittlewoodPoly

namespace Submission
namespace Flat
/-- Choose a level `s` with `q + 1 ≤ 2^s`. -/
lemma exists_level (q : ℕ) : ∃ s : ℕ, q + 1 ≤ 2 ^ s := by
  refine ⟨q + 1, ?_⟩
  exact Nat.le_of_lt (Nat.lt_two_pow_self (n := q + 1))

/-- Main construction theorem. -/
theorem flat_deg4q (t q : ℕ) (ht : Odd t)
    (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * Sec3.m_t t ≤ q) (hhi : q ≤ 2 ^ (t + 60)) :
    ∃ P : ℂ[X], IsLittlewoodPolynomial P ∧ P.natDegree = 4 * q ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ((2 : ℝ) ^ 170)⁻¹ * Real.sqrt (q : ℝ) ≤ ‖P.eval z‖ ∧
        ‖P.eval z‖ ≤ (2 ^ 14 : ℝ) * Real.sqrt (q : ℝ) := by
  classical
  -- tile level
  have hqbig : 2 ^ 43 * mt 1 ≤ q := by
    have h1 : 2 ^ 43 * mt 1 ≤ 2 ^ 43 * 2 ^ 13 := by
      have hmt : mt 1 ≤ 2 ^ 13 := by
        unfold mt
        norm_num
      exact Nat.mul_le_mul_left _ hmt
    have h2 : 2 ^ 43 * 2 ^ 13 ≤ 2 ^ 400 := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    exact le_trans (le_trans h1 h2) hq0
  rcases exists_odd_t_tile q hqbig with ⟨t0, ht0odd, hlo0 : 2 ^ 43 * mt t0 ≤ q, hup0 : q < 2 ^ 43 * mt (t0 + 2)⟩
  have hlo0s : 2 ^ 43 * Sec3.m_t t0 ≤ q := by
    simpa [mt_eq_mt] using hlo0
  have hmq : Sec3.m_t t0 ≤ q := by
    have hm1 : Sec3.m_t t0 ≤ 2 ^ 43 * Sec3.m_t t0 := by
      exact Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hmt2 : mt (t0 + 2) < 2 ^ (t0 + 14) := by
    have h := mt_lt_two_pow (t0 + 2)
    simpa using h
  have hq57n : q < 2 ^ (t0 + 57) := by
    calc
      q < 2 ^ 43 * mt (t0 + 2) := hup0
      _ < 2 ^ 43 * 2 ^ (t0 + 14) := by
          exact Nat.mul_lt_mul_of_pos_left hmt2 (by positivity : 0 < 2 ^ 43)
      _ = 2 ^ (t0 + 57) := by
          rw [← pow_add]
          congr 1
          omega
  have hq57r : (q : ℝ) ≤ (2 : ℝ) ^ (t0 + 57) := by
    exact_mod_cast (Nat.le_of_lt hq57n)
  have hq1r : 1 ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0r : (2 : ℝ) ^ 400 ≤ (q : ℝ) := by
    exact_mod_cast hq0
  have hsq0 : q + 1 ≤ 2 ^ (t0 + 61) := by
    have h1 : q + 1 ≤ 2 ^ (t0 + 57) := Nat.succ_le_of_lt hq57n
    have h2 : 2 ^ (t0 + 57) ≤ 2 ^ (t0 + 61) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    omega
  have ht3r : (2 : ℝ) ^ (t0 + 3) ≤ (q : ℝ) := by
    have hmtbig : 2 ^ (t0 + 11) ≤ Sec3.m_t t0 := by
      unfold Sec3.m_t
      have hx : 1 ≤ 2 ^ t0 := RudinShapiro.two_pow_ge_one t0
      omega
    have h1n : 2 ^ (t0 + 54) ≤ q := by
      calc
        2 ^ (t0 + 54) = 2 ^ 43 * 2 ^ (t0 + 11) := by
            rw [← pow_add]
            congr 1
            omega
        _ ≤ 2 ^ 43 * Sec3.m_t t0 := by
            exact Nat.mul_le_mul_left _ hmtbig
        _ ≤ q := hlo0s
    have h2n : 2 ^ (t0 + 3) ≤ 2 ^ (t0 + 54) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    exact_mod_cast (le_trans h2n h1n)
  have hhi0 : q ≤ 2 ^ (t0 + 60) := by
    have h1 : q ≤ 2 ^ (t0 + 57) := le_of_lt hq57n
    have h2 : 2 ^ (t0 + 57) ≤ 2 ^ (t0 + 60) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    omega
  have hq16 : 2 ^ 16 ≤ q := by
    have h1 : 2 ^ 16 ≤ 2 ^ 400 := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by norm_num : 16 ≤ 400)
    exact le_trans h1 hq0
  -- cosine family (quadrant coverage) and odd sine colouring
  rcases Sec3.cosine_family t0 q ht0odd hq0 hlo0s hhi0 with ⟨N, F, hN, hcov⟩
  rcases S5.theorem_sine q N hq16 F hN with ⟨eps, heps, ⟨α, hαcol, hαehat⟩, hlowu, hupodd⟩
  let s0 : ℕ := t0 + 61
  have hsq : q + 1 ≤ 2 ^ s0 := by simpa [s0] using hsq0
  have hs12 : t0 + 12 ≤ s0 := by dsimp [s0]; omega
  -- littlewood + degree
  have hlittle := flatPoly_littlewood t0 s0 q eps heps hsq hmq
  let P : ℂ[X] := flatPoly t0 s0 q eps
  have hm1 : ∀ r : ℕ, r < 2 ^ t0 → Sec3H.T t0 + r ≤ q := by
    intro r hr
    have h1 : Sec3H.T t0 + r ≤ Sec3.m_t t0 := by
      unfold Sec3.m_t Sec3H.T
      have hpow : 2 ^ (t0 + 10) ≤ 2 ^ (t0 + 11) := by
        exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
      omega
    omega
  have hm2 : ∀ r : ℕ, r < 2 ^ t0 → 2 * Sec3H.T t0 + r ≤ q := by
    intro r hr
    have h1 : 2 * Sec3H.T t0 + r ≤ Sec3.m_t t0 := by
      unfold Sec3.m_t Sec3H.T
      have hpow : 2 ^ (t0 + 11) = 2 * 2 ^ (t0 + 10) := by
        rw [show t0 + 11 = (t0 + 10) + 1 by omega, pow_succ]
        ring
      omega
    omega
  -- global bounds
  have hc_le : ∀ θ : ℝ, |Sec3.c t0 θ| ≤ Real.sqrt (q : ℝ) := fun θ =>
    NumBounds.abs_c_le_sqrt ht3r θ
  have hse_le : ∀ θ : ℝ, |Sec3.s_e s0 t0 q θ| ≤ 9 * Real.sqrt (q : ℝ) := fun θ =>
    NumBounds.abs_s_e_le_nine hq1r ht3r hsq θ
  have hso_le : ∀ θ : ℝ, |S5.sOdd q eps θ| ≤ 2 ^ 12 * Real.sqrt (q : ℝ) := hupodd
  have hsqn : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  refine ⟨P, hlittle.1, hlittle.2, ?_⟩
  intro z hz
  rcases exists_theta_of_unit z hz with ⟨θ, hzθ⟩
  rw [hzθ]
  have hnorm : ‖(flatPoly t0 s0 q eps).eval (Sec3.eθ θ)‖ = ‖flatInner t0 s0 q eps θ‖ :=
    norm_eval_eq_inner t0 s0 q eps hm1 hm2 θ
  rw [hnorm]
  have hupθ : ‖flatInner t0 s0 q eps θ‖ ≤ (2 ^ 14 : ℝ) * Real.sqrt (q : ℝ) := by
    have hn := norm_le_abs_re_add_abs_im (flatInner t0 s0 q eps θ)
    have hre := flatInner_re t0 s0 q eps θ
    have him := flatInner_im t0 s0 q eps hs12 hmq θ
    have hwr : |(flatInner t0 s0 q eps θ).re| = |1 + 2 * Sec3.c t0 θ| := by
      rw [hre]
    have hwi : |(flatInner t0 s0 q eps θ).im| =
        2 * |Sec3.s_e s0 t0 q θ + S5.sOdd q eps θ| := by
      rw [him]
      rw [abs_mul]
      simp
    have hcθ := hc_le θ
    have hseθ := hse_le θ
    have hsoθ := hso_le θ
    have hc1 : |1 + 2 * Sec3.c t0 θ| ≤ 1 + 2 * Real.sqrt (q : ℝ) := by
      have hb := abs_one_add_two_mul_le (Sec3.c t0 θ)
      linarith [hb, hcθ]
    have hse1 : |Sec3.s_e s0 t0 q θ + S5.sOdd q eps θ| ≤
        |Sec3.s_e s0 t0 q θ| + |S5.sOdd q eps θ| := abs_add_le _ _
    have h1 : |1 + 2 * Sec3.c t0 θ| + 2 * |Sec3.s_e s0 t0 q θ + S5.sOdd q eps θ|
        ≤ 1 + 2 * Real.sqrt (q : ℝ) + 2 * (9 + 2 ^ 12) * Real.sqrt (q : ℝ) := by
      linarith [hc1, hse1, hseθ, hsoθ]
    have h2 : ‖flatInner t0 s0 q eps θ‖ ≤
        |1 + 2 * Sec3.c t0 θ| + 2 * |Sec3.s_e s0 t0 q θ + S5.sOdd q eps θ| := by
      linarith [hn, hwr, hwi]
    exact le_trans (le_trans h2 h1) (NumBounds.upper_bound_total hq1r)
  have hlowθ : ((2 : ℝ) ^ 170)⁻¹ * Real.sqrt (q : ℝ) ≤ ‖flatInner t0 s0 q eps θ‖ := by
    rcases reduce_to_quadrant_c_sOdd t0 q eps θ with ⟨φ, hφmem, hφc, hφso⟩
    rcases hcov φ hφmem with hφF | hφbig
    · have hsoφ : 10 * Real.sqrt (q : ℝ) ≤ |S5.sOdd q eps φ| := hlowu φ hφmem hφF
      have hsoθ : 10 * Real.sqrt (q : ℝ) ≤ |S5.sOdd q eps θ| := by
        rw [hφso]
        exact hsoφ
      have hseθ : |Sec3.s_e s0 t0 q θ| ≤ 9 * Real.sqrt (q : ℝ) := hse_le θ
      have hdiff : Real.sqrt (q : ℝ) ≤ |Sec3.s_e s0 t0 q θ + S5.sOdd q eps θ| := by
        have ht := abs_add_ge_sub (S5.sOdd q eps θ) (Sec3.s_e s0 t0 q θ)
        have htmp : Real.sqrt (q : ℝ) ≤ |S5.sOdd q eps θ| - |Sec3.s_e s0 t0 q θ| := by
          linarith [hsoθ, hseθ]
        exact le_trans htmp (by simpa [add_comm] using ht)
      have hwi : |(flatInner t0 s0 q eps θ).im| =
          2 * |Sec3.s_e s0 t0 q θ + S5.sOdd q eps θ| := by
        have him := flatInner_im t0 s0 q eps hs12 hmq θ
        rw [him]
        rw [abs_mul]
        simp
      have hnorm := norm_ge_abs_im (flatInner t0 s0 q eps θ)
      have h20 : (2 : ℝ) ^ 170 > 0 := by positivity
      have hsmall : ((2 : ℝ) ^ 170)⁻¹ * Real.sqrt (q : ℝ) ≤ 2 * Real.sqrt (q : ℝ) := by
        have hle : ((2 : ℝ) ^ 170)⁻¹ ≤ 2 := by
          have hposb : (0 : ℝ) < 2 := by norm_num
          exact (inv_le_comm₀ h20 hposb).mpr (by norm_num)
        linarith [hsqn, hle]
      exact le_trans hsmall (by linarith [hnorm, hwi, hdiff])
    · have hcθ : Sec3.goodCellBound t0 q ≤ |Sec3.c t0 θ| := by
        rw [hφc] at hφbig
        exact hφbig
      have htri : 2 * |Sec3.c t0 θ| - 1 ≤ |1 + 2 * Sec3.c t0 θ| := by
        have h := abs_add_le (1 + 2 * Sec3.c t0 θ) (-1)
        have h1 : |(1 + 2 * Sec3.c t0 θ) + -1| = 2 * |Sec3.c t0 θ| := by
          have harg : (1 + 2 * Sec3.c t0 θ) + -1 = 2 * Sec3.c t0 θ := by ring
          rw [harg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        have h2 : 2 * |Sec3.c t0 θ| ≤ |1 + 2 * Sec3.c t0 θ| + 1 := by
          simpa [h1, abs_neg] using h
        linarith
      have hnum : ((2 : ℝ) ^ 170)⁻¹ * Real.sqrt (q : ℝ) ≤
          2 * Sec3.goodCellBound t0 q - 1 := by
        have hg := NumBounds.goodCellBound_lower hq0r hq57r
        linarith
      have hwr : |(flatInner t0 s0 q eps θ).re| = |1 + 2 * Sec3.c t0 θ| := by
        have hre := flatInner_re t0 s0 q eps θ
        rw [hre]
      have hnorm := norm_ge_abs_re (flatInner t0 s0 q eps θ)
      linarith [hnorm, hwr, htri, hnum, hcθ]
  exact ⟨hlowθ, hupθ⟩

end Flat
end Submission
