import Mathlib
import Submission.Work.FIArea6Hecke.S16CleanDefs
import Submission.Work.FIArea6.S16MellinInversion
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea6Road.MellinVerticalOfHpd
import Submission.Work.FIArea6Road.ThetaMulInvSqLeInvHeight
import Submission.Work.FIArea6Road.RpowMulSubLeOne

namespace Work.FIArea6Road

open MeasureTheory

theorem HeartZcHorizLeft
    (Pa : Work.FITop.Params) (p : ℝ → ℝ) (Zc : ℂ → ℂ) (σ₀ : ℝ) (d : ℕ) (C_z : ℝ) (y : ℝ)
    (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpsupp : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hpd : ∀ k : ℕ, k ≤ 2 → ∀ u : ℝ,
        |iteratedDeriv k p u| ≤ Work.FITop4.cMoll k * (Pa.θ * Pa.N) ^ (-(k : ℝ)))
    (hy : |y| = Work.FIArea6Hecke.heightT Pa)
    (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ ≤ 1)
    (hZc : ∀ x : ℝ, σ₀ ≤ x → x ≤ 1 →
        ‖Zc ((x : ℂ) + (y : ℂ) * Complex.I)‖
          ≤ C_z * (d : ℝ) * Pa.C ^ (1 - x) * (4 * Real.log Pa.N) ^ (6 : ℕ)) :
    ‖∫ x in σ₀..1, mellin (fun u : ℝ => (p u : ℂ)) ((x : ℂ) + (y : ℂ) * Complex.I)
          * Zc ((x : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ (10 ^ 7 * (C_z * (d : ℝ)) * (4 * Real.log Pa.N) ^ (6 : ℕ))
          * (1 / Work.FIArea6Hecke.heightT Pa) * Pa.N * (1 - σ₀) := by
  have hNpos : 0 < Pa.N := lt_of_lt_of_le zero_lt_one Pa.hN1
  have hCpos : (0 : ℝ) < Pa.C := by linarith [Pa.hC1]
  -- `C ≤ N`, from (2.12) `C ≤ N^{1-η}` and `N ≥ 1`.
  have hCN : Pa.C ≤ Pa.N := by
    calc Pa.C ≤ Pa.N ^ (1 - Pa.η) := Pa.hC2
      _ ≤ Pa.N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le Pa.hN1 (by linarith [Pa.hη])
      _ = Pa.N := Real.rpow_one Pa.N
  have hHpos : 0 < Work.FIArea6Hecke.heightT Pa := by
    rw [Work.FIArea6Hecke.heightT]; positivity
  have hyne : y ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hy
    rw [Work.FIArea6Hecke.heightT] at hy
    have := Real.exp_pos (Real.sqrt (Real.log Pa.N))
    linarith
  let K0 : ℝ := C_z * (d : ℝ) * (4 * Real.log Pa.N) ^ (6 : ℕ)
  have hK0def : K0 = C_z * (d : ℝ) * (4 * Real.log Pa.N) ^ (6 : ℕ) := rfl
  -- `K0 ≥ 0`: the bound `hZc` cannot hold at `x = σ₀` otherwise (`Pa.C^{1-σ₀} > 0`).
  have hK0nn : 0 ≤ K0 := by
    have hZ0 := hZc σ₀ le_rfl hσ₀1
    have hCpow : 0 < Pa.C ^ (1 - σ₀) := Real.rpow_pos_of_pos hCpos _
    have heq : C_z * (d : ℝ) * Pa.C ^ (1 - σ₀) * (4 * Real.log Pa.N) ^ (6 : ℕ)
        = K0 * Pa.C ^ (1 - σ₀) := by rw [hK0def]; ring
    have h0 : 0 ≤ K0 * Pa.C ^ (1 - σ₀) := by
      rw [← heq]; exact le_trans (norm_nonneg _) hZ0
    exact nonneg_of_mul_nonneg_left h0 hCpow
  -- the pointwise bound on the whole segment `]σ₀, 1]`
  have hmain : ∀ x ∈ Set.uIoc σ₀ 1,
      ‖mellin (fun u : ℝ => (p u : ℂ)) ((x : ℂ) + (y : ℂ) * Complex.I)
          * Zc ((x : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ (10 ^ 7 * K0) * (1 / Work.FIArea6Hecke.heightT Pa) * Pa.N := by
    intro x hxI
    rw [Set.uIoc_of_le hσ₀1] at hxI
    obtain ⟨hσ₀x, hx1⟩ := hxI
    have hxhalf : 1 / 2 ≤ x := le_trans hσ₀ hσ₀x.le
    have hx2 : x ≤ 2 := by linarith
    have hm := MellinVerticalOfHpd Pa p x y hpC hp0 hp1 hpsupp hpd hxhalf hx2 hyne
    have hz := hZc x hσ₀x.le hx1
    rw [norm_mul]
    have hA : (0 : ℝ) ≤ 10 ^ 7 * Pa.θ * Pa.N ^ x * (1 + (Pa.θ * y) ^ 2)⁻¹ := by
      have h1 : (0 : ℝ) ≤ Pa.N ^ x := Real.rpow_nonneg hNpos.le x
      have h2 : (0 : ℝ) ≤ (1 + (Pa.θ * y) ^ 2)⁻¹ := by rw [inv_nonneg]; positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) Pa.hθ0.le) h1) h2
    have hθH : Pa.θ * (1 + (Pa.θ * y) ^ 2)⁻¹ ≤ 1 / Work.FIArea6Hecke.heightT Pa :=
      ThetaMulInvSqLeInvHeight Pa.θ (Work.FIArea6Hecke.heightT Pa) y Pa.hθ0 hHpos hy
    have hNC : Pa.N ^ x * Pa.C ^ (1 - x) ≤ Pa.N :=
      RpowMulSubLeOne Pa.N Pa.C x Pa.hN1 Pa.hC1 hCN hx1
    have hK0C : (0 : ℝ) ≤ K0 * (Pa.N ^ x * Pa.C ^ (1 - x)) :=
      mul_nonneg hK0nn (mul_nonneg (Real.rpow_nonneg hNpos.le x) (Real.rpow_nonneg hCpos.le _))
    calc ‖mellin (fun u : ℝ => (p u : ℂ)) ((x : ℂ) + (y : ℂ) * Complex.I)‖
          * ‖Zc ((x : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ (10 ^ 7 * Pa.θ * Pa.N ^ x * (1 + (Pa.θ * y) ^ 2)⁻¹)
            * (C_z * (d : ℝ) * Pa.C ^ (1 - x) * (4 * Real.log Pa.N) ^ (6 : ℕ)) :=
          mul_le_mul hm hz (norm_nonneg _) hA
      _ = (10 ^ 7 * Pa.θ * (1 + (Pa.θ * y) ^ 2)⁻¹) * (K0 * (Pa.N ^ x * Pa.C ^ (1 - x))) := by
          rw [hK0def]; ring
      _ ≤ (10 ^ 7 * (1 / Work.FIArea6Hecke.heightT Pa)) * (K0 * Pa.N) := by
          have h1 : 10 ^ 7 * Pa.θ * (1 + (Pa.θ * y) ^ 2)⁻¹
              ≤ 10 ^ 7 * (1 / Work.FIArea6Hecke.heightT Pa) := by
            have h := mul_le_mul_of_nonneg_left hθH (show (0 : ℝ) ≤ 10 ^ 7 by positivity)
            calc 10 ^ 7 * Pa.θ * (1 + (Pa.θ * y) ^ 2)⁻¹
                = 10 ^ 7 * (Pa.θ * (1 + (Pa.θ * y) ^ 2)⁻¹) := by ring
              _ ≤ 10 ^ 7 * (1 / Work.FIArea6Hecke.heightT Pa) := h
          have h2 : K0 * (Pa.N ^ x * Pa.C ^ (1 - x)) ≤ K0 * Pa.N :=
            mul_le_mul_of_nonneg_left hNC hK0nn
          have hb : (0 : ℝ) ≤ 10 ^ 7 * (1 / Work.FIArea6Hecke.heightT Pa) :=
            mul_nonneg (by positivity) (div_nonneg zero_le_one hHpos.le)
          exact mul_le_mul h1 h2 hK0C hb
      _ = (10 ^ 7 * K0) * (1 / Work.FIArea6Hecke.heightT Pa) * Pa.N := by ring
  have hstep := intervalIntegral.norm_integral_le_of_norm_le_const hmain
  refine hstep.trans (le_of_eq ?_)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - σ₀), hK0def]
  ring

end Work.FIArea6Road
