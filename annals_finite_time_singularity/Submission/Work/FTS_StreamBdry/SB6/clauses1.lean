import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.rates_aux
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.oddPerS_pieces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

theorem Phi_clause1 {αG M L Kf : ℝ} (hαG : 0 < αG) (hL : 0 < L) (hM : 0 ≤ M) (hKf0 : 0 ≤ Kf)
    {Ψ : ℝ → ℝ → ℝ} (hPpi : ∀ z, (psiP αG Ψ) z (Real.pi / 2) = 0)
    (hDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ)
    (hfar : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |(if 0 < w then oddPerS (psiP αG Ψ) w θ else 0)|
        ≤ A * (Real.pi / 2 - θ) * (1 + w) ^ (-(4 / αG)) := by
  refine ⟨2 * max M Kf * (1 + L) ^ (4 / αG), ?_, ?_⟩
  · have hmm : 0 ≤ max M Kf := le_max_of_le_left hM
    have hr : 0 ≤ (1 + L) ^ (4 / αG) := Real.rpow_nonneg (by linarith) _
    positivity
  intro w θ hw hθ hθ2
  have hmm : 0 ≤ max M Kf := le_max_of_le_left hM
  have hwd : 0 ≤ (1 + w) ^ (-(4 / αG)) := Real.rpow_nonneg (by linarith) _
  have hLw : 0 ≤ (1 + L) ^ (4 / αG) := Real.rpow_nonneg (by linarith) _
  have hA : 0 ≤ 2 * max M Kf * (1 + L) ^ (4 / αG) * (Real.pi / 2 - θ) := by positivity
  by_cases hw0 : 0 < w
  · by_cases hθ0 : 0 < θ
    · rw [Phi_eq_of_pos hPpi hw0 hθ0 (le_of_lt hθ2)]
      have hmem : (w, θ) ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hw0, hθ0, hθ2⟩
      have hs2nn : 0 ≤ Work.Construction.s2 θ :=
        Work.FTS_StreamBdry.s2_nonneg_of_Iθ (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)
      have hs2le : Work.Construction.s2 θ ≤ 2 * (Real.pi / 2 - θ) :=
        s2_le_two_mul_sub (le_of_lt hθ2)
      have hπ : 0 ≤ Real.pi / 2 - θ := by linarith
      by_cases hwL : w ≤ L
      · -- compact
        have h1 : |(psiP αG Ψ) w θ| ≤ max M Kf * Work.Construction.s2 θ :=
          (hDz w θ hmem 0 (by norm_num)).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hs2nn)
        have h3 : 1 ≤ (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) := by
          have h4 := one_add_rpow_neg_le hL (by positivity : (0:ℝ) ≤ 4 / αG) hw hwL
          have h5 : (1 + L) ^ (4 / αG) * (1 + L) ^ (-(4 / αG)) = 1 := by
            rw [← Real.rpow_add (by linarith), show 4 / αG + -(4 / αG) = 0 by ring]
            simp
          calc (1 : ℝ) = (1 + L) ^ (4 / αG) * (1 + L) ^ (-(4 / αG)) := h5.symm
            _ ≤ (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) :=
                mul_le_mul_of_nonneg_left h4 hLw
        calc |(psiP αG Ψ) w θ| ≤ max M Kf * Work.Construction.s2 θ := h1
          _ ≤ 2 * max M Kf * (Real.pi / 2 - θ) := by
              calc max M Kf * Work.Construction.s2 θ
                  ≤ max M Kf * (2 * (Real.pi / 2 - θ)) :=
                    mul_le_mul_of_nonneg_left hs2le hmm
                _ = 2 * max M Kf * (Real.pi / 2 - θ) := by ring
          _ = 2 * max M Kf * (Real.pi / 2 - θ) * 1 := by ring
          _ ≤ 2 * max M Kf * (Real.pi / 2 - θ)
                * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = 2 * max M Kf * (1 + L) ^ (4 / αG) * (Real.pi / 2 - θ)
                * (1 + w) ^ (-(4 / αG)) := by ring
      · -- far
        have hwL' : L ≤ w := le_of_not_ge hwL
        have h2 : |(psiP αG Ψ) w θ|
            ≤ Kf * Work.Construction.s2 θ * (L / w) ^ (4 / αG) :=
          hfar w θ hmem hwL' 0 (by norm_num)
        have h3 : (L / w) ^ (4 / αG) ≤ (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) :=
          div_rpow_le hL (by positivity : (0:ℝ) ≤ 4 / αG) hwL'
        have h4 : Kf * Work.Construction.s2 θ * (L / w) ^ (4 / αG)
            ≤ Kf * Work.Construction.s2 θ * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hKf0 hs2nn)
        have h5 : Kf * Work.Construction.s2 θ * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)))
            ≤ 2 * max M Kf * (Real.pi / 2 - θ)
              * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hLw hwd)
          calc Kf * Work.Construction.s2 θ ≤ 2 * Kf * (Real.pi / 2 - θ) := by
                calc Kf * Work.Construction.s2 θ ≤ Kf * (2 * (Real.pi / 2 - θ)) :=
                      mul_le_mul_of_nonneg_left hs2le hKf0
                  _ = 2 * Kf * (Real.pi / 2 - θ) := by ring
            _ ≤ 2 * max M Kf * (Real.pi / 2 - θ) := by
                exact mul_le_mul_of_nonneg_right
                  (by linarith [le_max_right M Kf]) (by linarith)
        calc |(psiP αG Ψ) w θ| ≤ Kf * Work.Construction.s2 θ * (L / w) ^ (4 / αG) := h2
          _ ≤ Kf * Work.Construction.s2 θ
                * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) := h4
          _ ≤ 2 * max M Kf * (Real.pi / 2 - θ)
                * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) := h5
          _ = 2 * max M Kf * (1 + L) ^ (4 / αG) * (Real.pi / 2 - θ)
                * (1 + w) ^ (-(4 / αG)) := by ring
    · have hθeq : θ = 0 := le_antisymm (not_lt.mp hθ0) hθ
      rw [hθeq, Phi_zero_theta hPpi, abs_zero]
      have hwk : 0 ≤ (1 + (0:ℝ)) ^ (-(4 / αG)) := Real.rpow_nonneg (by norm_num) _
      have hπ : 0 ≤ Real.pi / 2 - 0 := by linarith [Real.pi_pos]
      have hr : 0 ≤ (1 + L) ^ (4 / αG) := Real.rpow_nonneg (by linarith) _
      positivity
  · rw [Phi_eq_zero_of_nonpos hw0, abs_zero]
    have hwk : 0 ≤ (1 + w) ^ (-(4 / αG)) := Real.rpow_nonneg (by linarith) _
    have hπ : 0 ≤ Real.pi / 2 - θ := by linarith
    have hr : 0 ≤ (1 + L) ^ (4 / αG) := Real.rpow_nonneg (by linarith) _
    positivity

end Work.FTS_StreamBdry.SB6
