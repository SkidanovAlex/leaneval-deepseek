import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtBAux.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools
namespace PtB

open Function Set

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The mixed slots.**  Each mixed slot `mixed J I (A·D_z f)` of `HkIntegrand α 6 (A·D_z f)`
with `1 ≤ I`, `I + J ≤ 6` is dominated by the majorant. -/
theorem mslot_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {A f : ℝ → ℝ → ℝ} {MA KA CPw : ℝ}
    (hAO : Work.FTS.EllipticEst.SmoothOpen A) (hfO : Work.FTS.EllipticEst.SmoothOpen f)
    (hMA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA)
    (hKA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ KA)
    (hPwA : SupPw α CPw A) (hPwf : SupPw α CPw f) (hCPw : 0 < CPw) :
    ∀ I J : ℕ, 1 ≤ I → I + J ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
        ≤ 10 ^ 11 * max CPw 1 * Maj α A f MA KA z θ := by
  intro I J hI hIJ z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hMnn : 0 ≤ Maj α A f MA KA z θ := Maj_nonneg hα A f MA KA z θ
  have hCMnn : 0 ≤ max CPw 1 * Maj α A f MA KA z θ :=
    mul_nonneg (le_trans hCPw.le (le_max_left _ _)) hMnn
  have hCM1 : (1 : ℝ) ≤ max CPw 1 := le_max_right _ _
  -- the `L^∞`-bound of `A`
  have hAz : (A z θ) ^ 2 ≤ MA ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hMA z θ hz hθ0 hθ1) 2
  -- Leibniz
  have hleib := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed J I A (Work.Spaces.Dz f)
    hAO hfO.Dz z θ hz hθ0 hθ1
  set Y : ℕ → ℕ → ℝ := fun a b => (I.choose a : ℝ) * (J.choose b : ℝ)
    * (Work.Spaces.mixed b a A z θ * Work.Spaces.mixed (J - b + 1) (I - a) f z θ
      * Work.Spaces.Wt α z θ) with hYdef
  have hsplit : (Work.Spaces.mixed J I (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
        * Work.Spaces.Wt α z θ)
      = ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b := by
    rw [hleib, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [mixed_Dz_shift hfO (J - b) (I - a) hz hθ]
    simp only [hYdef]
    ring
  -- the per-term bound
  have hterm : ∀ a ∈ Finset.range (I + 1), ∀ b ∈ Finset.range (J + 1),
      (Y a b) ^ 2 ≤ 16777216 * (max CPw 1 * Maj α A f MA KA z θ) := by
    intro a ha b hb
    have haI : a ≤ I := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbJ : b ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hcha : (I.choose a : ℝ) ^ 2 ≤ 4096 :=
      Work.FTS.StrongPersist.N6.binom_sq_le_4096 I a (by omega) (by omega)
    have hchb : (J.choose b : ℝ) ^ 2 ≤ 4096 :=
      Work.FTS.StrongPersist.N6.binom_sq_le_4096 J b (by omega) (by omega)
    have hch : (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 16777216 := by
      nlinarith [hcha, hchb, sq_nonneg (I.choose a : ℝ), sq_nonneg (J.choose b : ℝ)]
    have hcore : (Work.Spaces.mixed b a A z θ * Work.Spaces.mixed (J - b + 1) (I - a) f z θ
        * Work.Spaces.Wt α z θ) ^ 2 ≤ max CPw 1 * Maj α A f MA KA z θ := by
      by_cases h00 : a = 0 ∧ b = 0
      · -- the undifferentiated coefficient
        obtain ⟨ha0, hb0⟩ := h00
        rw [ha0, hb0]
        have hnum1 : (J - 0 + 1 : ℕ) = J + 1 := by omega
        have hnum2 : (I - 0 : ℕ) = I := by omega
        rw [hnum1, hnum2]
        have hY7 : (Work.Spaces.mixed (J + 1) I f z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 7 f z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α 7 f z θ I (J + 1) hI (by omega)
        exact close_MA (W := Work.Spaces.Wt α z θ) hα hCPw hAz hY7
      · by_cases ha0 : a = 0
        · -- `a = 0`, `b ≥ 1`: the `A`-slot is a pure `D_z`-slot
          have hb1 : 1 ≤ b := by omega
          rw [ha0]
          have hnum2 : (I - 0 : ℕ) = I := by omega
          rw [hnum2]
          by_cases hb4 : b ≤ 4
          · have hX : (Work.Spaces.mixed b 0 A z θ) ^ 2
                ≤ CPw / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 A :=
              hPwA b 0 (by omega) z θ hz hθ
            have hY := Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ I (J - b + 1)
              (by omega) (by omega)
            exact close_supA_localf (W := Work.Spaces.Wt α z θ) hα hCPw hX hY
          · -- `b = 5`: the exceptional slot `D_z⁵A · D_θ²f`
            have hb5 : b = 5 := by omega
            have hJ5 : J = 5 := by omega
            have hI1 : I = 1 := by omega
            rw [hb5, hJ5, hI1]
            exact le_trans (Maj4_le_Maj hα A f MA KA z θ)
              (le_mul_of_one_le_left hMnn hCM1)
        · -- `a ≥ 1`
          have ha1 : 1 ≤ a := by omega
          by_cases hai : I - a = 0
          · -- the `f`-factor is a pure `D_z`-slot
            have hmix0 : Work.Spaces.mixed (J - b + 1) (I - a) f
                = Work.Spaces.DzIter (J - b + 1) f := by
              rw [hai, Work.Spaces.mixed_zero_right]
            rw [hmix0]
            by_cases hb4 : J - b + 1 ≤ 4
            · have hX := Work.Spaces.sq_le_HkIntegrand_mixed α 6 A z θ a b ha1 (by omega)
              have hY : (Work.Spaces.DzIter (J - b + 1) f z θ) ^ 2
                  ≤ CPw / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 f := by
                have h := hPwf (J - b + 1) 0 (by omega) z θ hz hθ
                simpa only [Work.Spaces.mixed_zero_right] using h
              exact close_locA_supf (W := Work.Spaces.Wt α z θ) hα hCPw hX hY
            · by_cases hb5 : J - b + 1 = 5
              · -- the three exceptional slots `D_θ^iA · D_z⁵f`
                have hcases : (a = 1 ∧ b = 0 ∧ I = 1 ∧ J = 4)
                    ∨ (a = 1 ∧ b = 1 ∧ I = 1 ∧ J = 5)
                    ∨ (a = 2 ∧ b = 0 ∧ I = 2 ∧ J = 4) := by omega
                rcases hcases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
                  | ⟨rfl, rfl, rfl, rfl⟩
                · exact le_trans (Maj6_le_Maj hα A f MA KA z θ)
                    (le_mul_of_one_le_left hMnn hCM1)
                · exact le_trans (Maj5_le_Maj hα A f MA KA z θ)
                    (le_mul_of_one_le_left hMnn hCM1)
                · exact le_trans (Maj7_le_Maj hα A f MA KA z θ)
                    (le_mul_of_one_le_left hMnn hCM1)
              · -- `J - b + 1 = 6`: the `KA`-route
                have hcases : a = 1 ∧ b = 0 ∧ I = 1 ∧ J = 5 := by omega
                rcases hcases with ⟨rfl, rfl, rfl, rfl⟩
                have hDth : (Work.Spaces.Dth A z θ) ^ 2
                    ≤ KA ^ 2 * (Real.sin (2 * θ)) ^ 2 := by
                  have hp : |Work.Spaces.pth A z θ| ≤ KA := hKA z θ hz hθ0 hθ1
                  have h1 : |Work.Spaces.Dth A z θ| ≤ KA * |Real.sin (2 * θ)| := by
                    rw [Work.Spaces.Dth, abs_mul, mul_comm]
                    exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)
                  calc (Work.Spaces.Dth A z θ) ^ 2 = |Work.Spaces.Dth A z θ| ^ 2 := by
                        rw [sq_abs]
                    _ ≤ (KA * |Real.sin (2 * θ)|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
                    _ = KA ^ 2 * (Real.sin (2 * θ)) ^ 2 := by rw [mul_pow, sq_abs]
                have hY6 : (Work.Spaces.DzIter 6 f z θ * Hv z θ) ^ 2
                    ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
                  Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ 6 (by norm_num)
                exact close_KA (W := Work.Spaces.Wt α z θ) hα hα1 hCPw hθ hDth rfl hY6
          · -- both factors carry `θ`-derivatives
            have hIa1 : 1 ≤ I - a := by omega
            by_cases hab4 : a + b ≤ 4
            · exact close_supA_localf (W := Work.Spaces.Wt α z θ) hα hCPw
                (hPwA b a hab4 z θ hz hθ)
                (Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ (I - a) (J - b + 1)
                  hIa1 (by omega))
            · exact close_locA_supf (W := Work.Spaces.Wt α z θ) hα hCPw
                (Work.Spaces.sq_le_HkIntegrand_mixed α 6 A z θ a b ha1 (by omega))
                (hPwf (J - b + 1) (I - a) (by omega) z θ hz hθ)
    have hYeq : (Y a b) ^ 2 = (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
        * (Work.Spaces.mixed b a A z θ * Work.Spaces.mixed (J - b + 1) (I - a) f z θ
          * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [hYdef]; ring
    rw [hYeq]
    exact mul_le_mul hch hcore (sq_nonneg _) (by norm_num)
  -- the two Cauchy–Schwarz steps and the summation
  have hcardI : (((Finset.range (I + 1)).card : ℕ) : ℝ) = (I : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (J + 1)).card : ℕ) : ℝ) = (J : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hIJ49 : ((I : ℝ) + 1) * ((J : ℝ) + 1) ≤ 49 := by
    have hI6 : (I : ℝ) ≤ 6 := by
      have : I ≤ 6 := by omega
      exact_mod_cast this
    have hJ6 : (J : ℝ) ≤ 6 := by
      have : J ≤ 6 := by omega
      exact_mod_cast this
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
      ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1)
        * (16777216 * (max CPw 1 * Maj α A f MA KA z θ)) := by
    have h1 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
        ≤ ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
            (16777216 * (max CPw 1 * Maj α A f MA KA z θ)) :=
      Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hterm a ha b hb))
    refine le_trans h1 (le_of_eq ?_)
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hcs1 := sq_sum_le_card_mul_sum_sq (s := Finset.range (I + 1))
    (f := fun a => ∑ b ∈ Finset.range (J + 1), Y a b)
  have hstep1 : (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
      ≤ ((I : ℝ) + 1) * ∑ a ∈ Finset.range (I + 1),
          (∑ b ∈ Finset.range (J + 1), Y a b) ^ 2 := by
    simpa only [hcardI] using hcs1
  have hstep2 : ((I : ℝ) + 1) * ∑ a ∈ Finset.range (I + 1),
        (∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
      ≤ ((I : ℝ) + 1) * (((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hinner : ∀ a, (∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
        ≤ ((J : ℝ) + 1) * ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := fun a => by
      simpa only [hcardJ] using sq_sum_le_card_mul_sum_sq (s := Finset.range (J + 1))
        (f := fun b => Y a b)
    calc ∑ a ∈ Finset.range (I + 1), (∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
        ≤ ∑ a ∈ Finset.range (I + 1),
            ((J : ℝ) + 1) * ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 :=
          Finset.sum_le_sum (fun a _ => hinner a)
      _ = ((J : ℝ) + 1) * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
          rw [Finset.mul_sum]
  have hfinal : (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
        * (16777216 * (max CPw 1 * Maj α A f MA KA z θ))
      ≤ 10 ^ 11 * max CPw 1 * Maj α A f MA KA z θ := by
    have hIJnn : 0 ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1) := by positivity
    have hcoef : (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2 * 16777216 ≤ 10 ^ 11 := by
      nlinarith [hIJ49, hIJnn, sq_nonneg (((I : ℝ) + 1) * ((J : ℝ) + 1))]
    have h1 : (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
          * (16777216 * (max CPw 1 * Maj α A f MA KA z θ))
        = ((((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2 * 16777216)
          * (max CPw 1 * Maj α A f MA KA z θ) := by ring
    rw [h1]
    calc ((((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2 * 16777216)
          * (max CPw 1 * Maj α A f MA KA z θ)
        ≤ 10 ^ 11 * (max CPw 1 * Maj α A f MA KA z θ) :=
          mul_le_mul_of_nonneg_right hcoef hCMnn
      _ = 10 ^ 11 * max CPw 1 * Maj α A f MA KA z θ := by ring
  rw [hsplit]
  calc (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
      ≤ ((I : ℝ) + 1) * ∑ a ∈ Finset.range (I + 1),
          (∑ b ∈ Finset.range (J + 1), Y a b) ^ 2 := hstep1
    _ ≤ ((I : ℝ) + 1) * (((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2) := hstep2
    _ ≤ ((I : ℝ) + 1) * (((J : ℝ) + 1)
          * (((I : ℝ) + 1) * ((J : ℝ) + 1)
            * (16777216 * (max CPw 1 * Maj α A f MA KA z θ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum2 (by positivity))
          (by positivity)
    _ = (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
          * (16777216 * (max CPw 1 * Maj α A f MA KA z θ)) := by ring
    _ ≤ 10 ^ 11 * max CPw 1 * Maj α A f MA KA z θ := hfinal

end

end PtB

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
