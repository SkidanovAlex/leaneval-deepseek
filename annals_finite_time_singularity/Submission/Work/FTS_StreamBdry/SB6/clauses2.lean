import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
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

/-!
# `Work.FTS_StreamBdry.SB6.Phi_clause2` — the `w`-derivative rate of `Φ`

`Φ w θ = if 0 < w then oddPerS (psiP αG Ψ) w θ else 0` and
`|∂_wΦ w θ| ≤ A (π/2-θ) (1+w)^{-4/αG-1}` on `w ≥ 0`, `0 ≤ θ < π/2`.

Three regimes: the interior `w > 0`, `θ > 0`, where `∂_wΦ = ∂_w(psiP)` splits into the compact
bound `|∂_w psiP| ≤ max K0 M·sin 2θ` (from `D_z psiP` for `w ≥ 1`, and from the near-axis
hypothesis for `w ≤ 1`) and the far-field bound `|∂_w psiP| ≤ Kf sin 2θ (L/w)^{4/αG}/w`; the
axis `θ = 0`, where the whole function in `w` vanishes; and `w = 0`, where it vanishes on
`(-∞,0)` and at `0`, so its derivative at `0` is `0`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

/-- **Clause 2**: `|∂_w Φ w θ| ≤ A₂ (π/2 - θ) (1+w)^{-4/αG-1}`. -/
theorem Phi_clause2 {αG M L Kf K0 : ℝ} (hαG : 0 < αG) (hL : 0 < L) (hM : 0 ≤ M)
    (hKf0 : 0 ≤ Kf) (hK00 : 0 ≤ K0)
    {Ψ : ℝ → ℝ → ℝ} (hPpi : ∀ z, (psiP αG Ψ) z (Real.pi / 2) = 0)
    (hpz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.pz (psiP αG Ψ) z θ| ≤ K0 * Work.Construction.s2 θ)
    (hDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ)
    (hfar : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun w' : ℝ => (if 0 < w' then oddPerS (psiP αG Ψ) w' θ else 0)) w|
        ≤ A * (Real.pi / 2 - θ) * (1 + w) ^ (-(4 / αG) - 1) := by
  have hk0 : (0 : ℝ) ≤ 4 / αG := by positivity
  have hk1 : (0 : ℝ) ≤ 4 / αG + 1 := by positivity
  have hLw : 0 ≤ (1 + L) ^ (4 / αG + 1) := Real.rpow_nonneg (by linarith) _
  have hMm : (0 : ℝ) ≤ max K0 M := le_max_of_le_left hK00
  have hA0 : 0 ≤ max (2 * max K0 M * (1 + L) ^ (4 / αG + 1))
      (2 * Kf * L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)) := by
    refine le_max_iff.mpr (Or.inl ?_)
    exact mul_nonneg (mul_nonneg (by norm_num) hMm) hLw
  refine ⟨max (2 * max K0 M * (1 + L) ^ (4 / αG + 1))
    (2 * Kf * L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)), hA0, ?_⟩
  intro w θ hw hθ hθ2
  have hwd : 0 ≤ (1 + w) ^ (-(4 / αG) - 1) := Real.rpow_nonneg (by linarith) _
  have hπ : 0 ≤ Real.pi / 2 - θ := by linarith [hθ2, Real.pi_pos]
  by_cases hw0 : 0 < w
  · by_cases hθ0 : 0 < θ
    · rw [Phi_deriv_w hPpi hw0 hθ0 hθ2]
      have hmem : (w, θ) ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hw0, hθ0, hθ2⟩
      have hs2nn : 0 ≤ Work.Construction.s2 θ :=
        Work.FTS_StreamBdry.s2_nonneg_of_Iθ (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)
      have hs2le : Work.Construction.s2 θ ≤ 2 * (Real.pi / 2 - θ) :=
        s2_le_two_mul_sub (le_of_lt hθ2)
      by_cases hwL : w ≤ L
      · -- compact: `w ≤ L`
        have hpz' : |Work.Spaces.pz (psiP αG Ψ) w θ| ≤ max K0 M * Work.Construction.s2 θ := by
          by_cases hw1 : w ≤ 1
          · exact (hpz w θ hmem hw1).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) hs2nn)
          · have hw1' : 1 ≤ w := le_of_not_ge hw1
            have hD := hDz w θ hmem 1 (by norm_num)
            rw [show Work.Spaces.DzIter 1 (psiP αG Ψ) w θ
                = w * Work.Spaces.pz (psiP αG Ψ) w θ from rfl, abs_mul,
              abs_of_pos hw0] at hD
            have h1 : |Work.Spaces.pz (psiP αG Ψ) w θ| ≤ M * Work.Construction.s2 θ / w :=
              (le_div_iff₀ hw0).mpr (by linarith [hD])
            have h2 : M * Work.Construction.s2 θ / w ≤ M * Work.Construction.s2 θ := by
              rw [div_le_iff₀ hw0]
              calc M * Work.Construction.s2 θ = M * Work.Construction.s2 θ * 1 :=
                    (mul_one _).symm
                _ ≤ M * Work.Construction.s2 θ * w :=
                    mul_le_mul_of_nonneg_left hw1' (mul_nonneg hM hs2nn)
            exact (h1.trans h2).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hs2nn)
        have h3 : (1 : ℝ) ≤ (1 + L) ^ (4 / αG + 1) * (1 + w) ^ (-(4 / αG) - 1) := by
          have h4 : (1 + L) ^ (-(4 / αG + 1)) ≤ (1 + w) ^ (-(4 / αG + 1)) :=
            one_add_rpow_neg_le hL hk1 hw hwL
          have h4' : (1 + L) ^ (-(4 / αG + 1)) ≤ (1 + w) ^ (-(4 / αG) - 1) := by
            rw [show -(4 / αG) - 1 = -(4 / αG + 1) by ring]
            exact h4
          have h5 : (1 + L) ^ (4 / αG + 1) * (1 + L) ^ (-(4 / αG + 1)) = 1 := by
            rw [← Real.rpow_add (by linarith),
              show 4 / αG + 1 + -(4 / αG + 1) = 0 by ring]
            simp
          calc (1 : ℝ) = (1 + L) ^ (4 / αG + 1) * (1 + L) ^ (-(4 / αG + 1)) := h5.symm
            _ ≤ (1 + L) ^ (4 / αG + 1) * (1 + w) ^ (-(4 / αG) - 1) :=
                mul_le_mul_of_nonneg_left h4' hLw
        calc |Work.Spaces.pz (psiP αG Ψ) w θ| ≤ max K0 M * Work.Construction.s2 θ := hpz'
          _ ≤ max K0 M * (2 * (Real.pi / 2 - θ)) :=
              mul_le_mul_of_nonneg_left hs2le (le_max_of_le_left hK00)
          _ = (2 * max K0 M) * (Real.pi / 2 - θ) := by ring
          _ = (2 * max K0 M) * (Real.pi / 2 - θ) * 1 := by ring
          _ ≤ (2 * max K0 M) * (Real.pi / 2 - θ)
                * ((1 + L) ^ (4 / αG + 1) * (1 + w) ^ (-(4 / αG) - 1)) :=
              mul_le_mul_of_nonneg_left h3
                (mul_nonneg (mul_nonneg (by norm_num) hMm) hπ)
          _ = (2 * max K0 M * (1 + L) ^ (4 / αG + 1)) * (Real.pi / 2 - θ)
                * (1 + w) ^ (-(4 / αG) - 1) := by ring
          _ ≤ max (2 * max K0 M * (1 + L) ^ (4 / αG + 1))
                (2 * Kf * L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)) * (Real.pi / 2 - θ)
                * (1 + w) ^ (-(4 / αG) - 1) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hπ) hwd
      · -- far field: `L ≤ w`
        have hwL' : L ≤ w := le_of_not_ge hwL
        have hwpos : 0 < w := lt_of_lt_of_le hL hwL'
        have hD := hfar w θ hmem hwL' 1 (by norm_num)
        rw [show Work.Spaces.DzIter 1 (psiP αG Ψ) w θ
            = w * Work.Spaces.pz (psiP αG Ψ) w θ from rfl, abs_mul,
          abs_of_pos hwpos] at hD
        have hpz1 : |Work.Spaces.pz (psiP αG Ψ) w θ|
            ≤ Kf * Work.Construction.s2 θ * (L / w) ^ (4 / αG) / w :=
          (le_div_iff₀ hwpos).mpr (by linarith [hD])
        have hkey : (L / w) ^ (4 / αG) / w
            ≤ L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)
              * (1 + w) ^ (-(4 / αG) - 1) := by
          simpa only [show -(4 / αG + 1) = -(4 / αG) - 1 by ring]
            using div_rpow_succ_le (w := w) (L := L) (k := 4 / αG) hL hk0 hwL'
        have hker : 0 ≤ L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)
            * (1 + w) ^ (-(4 / αG) - 1) :=
          mul_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt hL) _)
            (Real.rpow_nonneg (by positivity) _)) hwd
        calc |Work.Spaces.pz (psiP αG Ψ) w θ|
            ≤ Kf * Work.Construction.s2 θ * (L / w) ^ (4 / αG) / w := hpz1
          _ = Kf * Work.Construction.s2 θ * ((L / w) ^ (4 / αG) / w) := by ring
          _ ≤ Kf * Work.Construction.s2 θ
                * (L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)
                  * (1 + w) ^ (-(4 / αG) - 1)) :=
              mul_le_mul_of_nonneg_left hkey (mul_nonneg hKf0 hs2nn)
          _ ≤ Kf * (2 * (Real.pi / 2 - θ))
                * (L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)
                  * (1 + w) ^ (-(4 / αG) - 1)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2le hKf0) hker
          _ = (2 * Kf * L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)) * (Real.pi / 2 - θ)
                * (1 + w) ^ (-(4 / αG) - 1) := by ring
          _ ≤ max (2 * max K0 M * (1 + L) ^ (4 / αG + 1))
                (2 * Kf * L ^ (4 / αG) * (1 + 1 / L) ^ (4 / αG + 1)) * (Real.pi / 2 - θ)
                * (1 + w) ^ (-(4 / αG) - 1) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hπ) hwd
    · -- `θ = 0`: the function of `w` is identically zero
      have hθeq : θ = 0 := le_antisymm (not_lt.mp hθ0) hθ
      rw [hθeq]
      have hfun : (fun w' : ℝ => (if 0 < w' then oddPerS (psiP αG Ψ) w' 0 else 0))
          = fun _ => 0 := by
        funext w'
        by_cases hw' : 0 < w'
        · exact Phi_zero_theta hPpi
        · exact ite_eq_right hw'
      rw [hfun, deriv_const, abs_zero]
      exact mul_nonneg (mul_nonneg hA0 (by linarith [Real.pi_pos])) hwd
  · -- `w ≤ 0`, so `w = 0`
    have hw_eq : w = 0 := le_antisymm (not_lt.mp hw0) hw
    subst hw_eq
    by_cases hd : DifferentiableAt ℝ
      (fun w' : ℝ => (if 0 < w' then oddPerS (psiP αG Ψ) w' θ else 0)) 0
    · have hder : deriv (fun w' : ℝ => (if 0 < w' then oddPerS (psiP αG Ψ) w' θ else 0)) 0
          = 0 :=
        deriv_eq_zero_of_left_eq_zero hd
          (fun y hy => Phi_eq_zero_of_nonpos (P := psiP αG Ψ) (not_lt.mpr (le_of_lt hy)))
          (ite_eq_right (lt_irrefl (0 : ℝ)))
      rw [hder, abs_zero]
      exact mul_nonneg (mul_nonneg hA0 hπ) hwd
    · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
      exact mul_nonneg (mul_nonneg hA0 hπ) hwd

end Work.FTS_StreamBdry.SB6
