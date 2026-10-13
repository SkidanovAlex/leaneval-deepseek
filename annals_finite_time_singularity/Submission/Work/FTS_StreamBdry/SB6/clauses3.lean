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
# `Work.FTS_StreamBdry.SB6.Phi_clause3` — the `θ`-derivative rate of `Φ`

`Φ w θ = if 0 < w then oddPerS (psiP αG Ψ) w θ else 0` and
`|∂_θΦ w θ| ≤ A (1+w)^{-4/αG}` on `w ≥ 0`, `0 ≤ θ < π/2`.

The interior bound `|∂_θ psiP| ≤ Kpth` (compact, `w ≤ L`) or
`∂_θ psiP = V(psiP) + tan θ·psiP` with `|V(psiP)| ≤ Kv (L/w)^{4/αG}` and
`|tan θ·psiP| ≤ 2 Kf (L/w)^{4/αG}` (far).  On the axis `θ = 0` the derivative of the odd
extension is the right difference quotient, controlled by `deriv_theta_zero_le` / `_far`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

/-- The compact weight trick: for `w ≤ L`, `1 ≤ (1+L)^k · (1+w)^{-k}`. -/
lemma one_le_weight {w L k : ℝ} (hL : 0 < L) (hk : 0 ≤ k) (hw0 : 0 ≤ w) (hwL : w ≤ L) :
    (1 : ℝ) ≤ (1 + L) ^ k * (1 + w) ^ (-k) := by
  have hLk : 0 ≤ (1 + L) ^ k := Real.rpow_nonneg (by linarith) _
  have h4 := one_add_rpow_neg_le hL hk hw0 hwL
  have h5 : (1 + L) ^ k * (1 + L) ^ (-k) = 1 := by
    rw [← Real.rpow_add (by linarith), show k + -k = 0 by ring]
    simp
  calc (1 : ℝ) = (1 + L) ^ k * (1 + L) ^ (-k) := h5.symm
    _ ≤ (1 + L) ^ k * (1 + w) ^ (-k) := mul_le_mul_of_nonneg_left h4 hLk

/-- **Clause 3**: `|∂_θ Φ w θ| ≤ A₃ (1+w)^{-4/αG}`. -/
theorem Phi_clause3 {αG M L Kf Kpth Kv : ℝ} (hαG : 0 < αG) (hL : 0 < L) (hM : 0 ≤ M)
    (hKf0 : 0 ≤ Kf) (hKpth0 : 0 ≤ Kpth) (hKv0 : 0 ≤ Kv)
    {Ψ : ℝ → ℝ → ℝ} (hPpi : ∀ z, (psiP αG Ψ) z (Real.pi / 2) = 0)
    (hDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ)
    (hfar : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG))
    (hKpth : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 1,
      |Work.Spaces.pth (Work.Spaces.DzIter j (psiP αG Ψ)) z θ| ≤ Kpth)
    (hVop : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
      |Work.Construction.Vop (psiP αG Ψ) z θ| ≤ Kv * (L / z) ^ (4 / αG)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun θ' : ℝ => (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0)) θ|
        ≤ A * (1 + w) ^ (-(4 / αG)) := by
  have hk0 : (0 : ℝ) ≤ 4 / αG := by positivity
  have hLk : 0 ≤ (1 + L) ^ (4 / αG) := Real.rpow_nonneg (by linarith) _
  have hBk : 0 ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) := by
    refine le_max_iff.mpr (Or.inl ?_)
    exact le_max_of_le_left hKpth0
  refine ⟨max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG),
    mul_nonneg hBk hLk, ?_⟩
  intro w θ hw hθ hθ2
  have hwk : 0 ≤ (1 + w) ^ (-(4 / αG)) := Real.rpow_nonneg (by linarith) _
  by_cases hw0 : 0 < w
  · by_cases hθ0 : 0 < θ
    · rw [Phi_deriv_theta hPpi hw0 hθ0 hθ2]
      have hmem : (w, θ) ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hw0, hθ0, hθ2⟩
      by_cases hwL : w ≤ L
      · -- compact: `w ≤ L`
        have h1 : |Work.Spaces.pth (psiP αG Ψ) w θ| ≤ Kpth := hKpth w θ hmem 0 (by norm_num)
        have h3 := one_le_weight (k := 4 / αG) hL hk0 hw hwL
        calc |Work.Spaces.pth (psiP αG Ψ) w θ| ≤ Kpth := h1
          _ = Kpth * 1 := (mul_one _).symm
          _ ≤ Kpth * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
              mul_le_mul_of_nonneg_left h3 hKpth0
          _ = Kpth * (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) := by ring
          _ ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG)
                * (1 + w) ^ (-(4 / αG)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) hLk) hwk
      · -- far field: `L ≤ w`
        have hwL' : L ≤ w := le_of_not_ge hwL
        have hV := hVop w θ hmem hwL'
        have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd hmem)
        have htans : Real.tan θ * Work.Construction.s2 θ = 2 * Real.sin θ ^ 2 :=
          Work.FTS_StreamBdry.tan_mul_s2 hcos
        have htan0 : 0 ≤ Real.tan θ := by
          rw [Real.tan_eq_sin_div_cos]
          refine div_nonneg ?_ (le_of_lt (Work.FTS_StreamBdry.cos_pos_of_Qd hmem))
          exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ0])
            (by linarith [hθ2, Real.pi_pos]))
        have htan2 : |Real.tan θ| * Work.Construction.s2 θ ≤ 2 := by
          rw [abs_of_nonneg htan0, htans]
          linarith [Real.sin_sq_le_one θ]
        have hP := hfar w θ hmem hwL' 0 (by norm_num)
        have h1 : |Work.Spaces.pth (psiP αG Ψ) w θ| ≤ (Kv + 2 * Kf) * (L / w) ^ (4 / αG) := by
          have hpth_eq : Work.Spaces.pth (psiP αG Ψ) w θ
              = Work.Construction.Vop (psiP αG Ψ) w θ
                + Real.tan θ * (psiP αG Ψ) w θ := by
            rw [Work.Construction.Vop]
            ring
          rw [hpth_eq]
          have h2 : |Real.tan θ * (psiP αG Ψ) w θ|
              ≤ (|Real.tan θ| * Work.Construction.s2 θ) * (Kf * (L / w) ^ (4 / αG)) := by
            rw [abs_mul]
            calc |Real.tan θ| * |(psiP αG Ψ) w θ|
                ≤ |Real.tan θ| * (Kf * Work.Construction.s2 θ * (L / w) ^ (4 / αG)) :=
                  mul_le_mul_of_nonneg_left hP (abs_nonneg _)
              _ = (|Real.tan θ| * Work.Construction.s2 θ) * (Kf * (L / w) ^ (4 / αG)) := by ring
          have h3 : (|Real.tan θ| * Work.Construction.s2 θ) * (Kf * (L / w) ^ (4 / αG))
              ≤ 2 * (Kf * (L / w) ^ (4 / αG)) :=
            mul_le_mul_of_nonneg_right htan2
              (mul_nonneg hKf0 (Real.rpow_nonneg (by positivity) _))
          have h4 : |Work.Construction.Vop (psiP αG Ψ) w θ| + 2 * (Kf * (L / w) ^ (4 / αG))
              ≤ Kv * (L / w) ^ (4 / αG) + 2 * (Kf * (L / w) ^ (4 / αG)) :=
            add_le_add hV (le_refl _)
          have h5 : Kv * (L / w) ^ (4 / αG) + 2 * (Kf * (L / w) ^ (4 / αG))
              = (Kv + 2 * Kf) * (L / w) ^ (4 / αG) := by ring
          calc |Work.Construction.Vop (psiP αG Ψ) w θ + Real.tan θ * (psiP αG Ψ) w θ|
              ≤ |Work.Construction.Vop (psiP αG Ψ) w θ|
                + |Real.tan θ * (psiP αG Ψ) w θ| := abs_add_le _ _
            _ ≤ |Work.Construction.Vop (psiP αG Ψ) w θ| + 2 * (Kf * (L / w) ^ (4 / αG)) :=
                add_le_add (le_refl _) (h2.trans h3)
            _ ≤ Kv * (L / w) ^ (4 / αG) + 2 * (Kf * (L / w) ^ (4 / αG)) := h4
            _ = (Kv + 2 * Kf) * (L / w) ^ (4 / αG) := h5
        have h2 : (Kv + 2 * Kf) * (L / w) ^ (4 / αG)
            ≤ (Kv + 2 * Kf) * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
          mul_le_mul_of_nonneg_left (div_rpow_le hL hk0 hwL') (by linarith)
        have h3 : (Kv + 2 * Kf) * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)))
            ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG)
              * (1 + w) ^ (-(4 / αG)) := by
          have h4 : Kv + 2 * Kf ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) :=
            le_max_of_le_left (le_max_right _ _)
          calc (Kv + 2 * Kf) * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)))
              = (Kv + 2 * Kf) * (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) := by ring
            _ ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG)
                  * (1 + w) ^ (-(4 / αG)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hLk) hwk
        calc |Work.Spaces.pth (psiP αG Ψ) w θ| ≤ (Kv + 2 * Kf) * (L / w) ^ (4 / αG) := h1
          _ ≤ (Kv + 2 * Kf) * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) := h2
          _ ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG)
                * (1 + w) ^ (-(4 / αG)) := h3
    · -- `θ = 0`: the derivative is the right difference quotient
      have hθeq : θ = 0 := le_antisymm (not_lt.mp hθ0) hθ
      rw [hθeq]
      by_cases hd : DifferentiableAt ℝ
        (fun θ' : ℝ => (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0)) 0
      · by_cases hwL : w ≤ L
        · have hbd : |deriv (fun θ' : ℝ =>
              (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0)) 0| ≤ 2 * M :=
            deriv_theta_zero_le hPpi hw0 hM
              (fun t ht0 htπ => hDz w t
                (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hw0, ht0, htπ⟩) 0 (by norm_num)) hd
          have h3 := one_le_weight (k := 4 / αG) hL hk0 hw hwL
          have hB1 : 2 * max M Kf ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) :=
            le_max_right _ _
          have hMk0 : 0 ≤ 2 * max M Kf :=
            mul_nonneg (by norm_num) (le_max_of_le_left hM)
          calc |deriv (fun θ' : ℝ =>
                (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0)) 0| ≤ 2 * M := hbd
            _ ≤ 2 * max M Kf := mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
            _ = 2 * max M Kf * 1 := (mul_one _).symm
            _ ≤ 2 * max M Kf * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
                mul_le_mul_of_nonneg_left h3 hMk0
            _ = 2 * max M Kf * (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) := by ring
            _ ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG)
                  * (1 + w) ^ (-(4 / αG)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB1 hLk) hwk
        · have hwL' : L ≤ w := le_of_not_ge hwL
          have hbd : |deriv (fun θ' : ℝ =>
                (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0)) 0|
              ≤ 2 * Kf * (L / w) ^ (4 / αG) :=
            deriv_theta_zero_le_far hPpi hL hwL' hKf0
              (fun t ht0 htπ => hfar w t
                (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hw0, ht0, htπ⟩) hwL' 0 (by norm_num)) hd
          have h2 : 2 * Kf * (L / w) ^ (4 / αG)
              ≤ 2 * max M Kf * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) := by
            have h5 : (L / w) ^ (4 / αG)
                ≤ (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) := div_rpow_le hL hk0 hwL'
            have h6 : 0 ≤ 2 * Kf := by linarith
            have h7 : 2 * Kf ≤ 2 * max M Kf :=
              mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
            have h8 : 0 ≤ (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) :=
              mul_nonneg hLk hwk
            calc 2 * Kf * (L / w) ^ (4 / αG)
                ≤ 2 * Kf * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
                  mul_le_mul_of_nonneg_left h5 h6
              _ ≤ 2 * max M Kf * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) :=
                  mul_le_mul_of_nonneg_right h7 h8
          calc |deriv (fun θ' : ℝ =>
                (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0)) 0|
              ≤ 2 * Kf * (L / w) ^ (4 / αG) := hbd
            _ ≤ 2 * max M Kf * ((1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG))) := h2
            _ = 2 * max M Kf * (1 + L) ^ (4 / αG) * (1 + w) ^ (-(4 / αG)) := by ring
            _ ≤ max (max Kpth (Kv + 2 * Kf)) (2 * max M Kf) * (1 + L) ^ (4 / αG)
                  * (1 + w) ^ (-(4 / αG)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hLk) hwk
      · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
        exact mul_nonneg (mul_nonneg hBk hLk) hwk
  · have hfun : (fun θ' : ℝ => (if 0 < w then oddPerS (psiP αG Ψ) w θ' else 0))
        = fun _ => 0 := by
      funext θ'
      exact ite_eq_right hw0
    rw [hfun, deriv_const, abs_zero]
    exact mul_nonneg (mul_nonneg hBk hLk) hwk

end Work.FTS_StreamBdry.SB6
