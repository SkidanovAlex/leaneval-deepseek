import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB25Aux4.EdgeAxisAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux4.psiP_edge_axis_zero123`

The three vanishing limits of `psiP αG Ψ` at `(z₀, π/2)`: `P`, `∂_zP`, `∂_z²P` all tend to `0`,
uniformly in `z` near `z₀ > 0`.

`|D_z^j P| ≤ M sin 2θ` (`psiP_DzLe`, `j ≤ 2`) with `sin 2θ ≤ 2(π/2 - θ)` gives the first two
directly; for `∂_z²P` one uses `D_z² = z∂_z + z²∂_z²` (`DzIter_two_eq`) and `z ≥ z₀/2`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux4

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

theorem psiP_edge_axis_zero123 {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∀ z0 : ℝ, 0 < z0 →
      Tendsto (Function.uncurry (psiP αG Ψ)) (𝓝[Work.Construction.Qd] (z0, Real.pi / 2))
          (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pz (psiP αG Ψ)))
            (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) ∧
          Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ))))
            (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) := by
  have hMnn : 0 ≤ M := by
    have h1 := Work.FTS_StreamBdry.SlotBd.Dz_le hslot (z := 1) (θ := Real.pi / 4)
      Work.FTS_StreamBdry.SB1.Qd_nonempty (j := 0) (by norm_num)
    exact le_trans (abs_nonneg _) h1
  have hDz := Work.FTS_StreamBdry.SB3.psiP_DzLe (αG := αG) (M := M) hαG h3 hslot
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 (αG := αG) (M := M) hαG h3 hslot
  intro z0 hz0
  refine ⟨?_, ?_, ?_⟩
  · -- `P → 0`
    refine tendsto_nhdsWithin_of_abs_le (L := 0)
      (g := fun p : ℝ × ℝ => 2 * M * (Real.pi / 2 - p.2)) ?_ ?_
    · simpa using tendsto_const_mul_sub_snd_zero (2 * M) z0
    · refine eventually_nhdsWithin_Qd (fun z θ hmem => ?_)
      have h1 : |Work.Spaces.DzIter 0 (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ :=
        hDz z θ hmem 0 (by norm_num)
      rw [Work.Spaces.DzIter_zero] at h1
      have h2 := s2_le_two_sub (Work.FTS_StreamBdry.Qd_theta_mem hmem)
      have h4 : M * Work.Construction.s2 θ ≤ 2 * M * (Real.pi / 2 - θ) := by
        have h5 := mul_le_mul_of_nonneg_left h2 hMnn
        have h6 : M * (2 * (Real.pi / 2 - θ)) = 2 * M * (Real.pi / 2 - θ) := by ring
        linarith [h5, h6]
      have hgoal : |psiP αG Ψ z θ| ≤ 2 * M * (Real.pi / 2 - θ) := by linarith [h1, h4]
      simpa [Function.uncurry, sub_zero] using hgoal
  · -- `∂_zP → 0`
    refine tendsto_nhdsWithin_of_abs_le (L := 0)
      (g := fun p : ℝ × ℝ => (4 * M / z0) * (Real.pi / 2 - p.2)) ?_ ?_
    · simpa using tendsto_const_mul_sub_snd_zero (4 * M / z0) z0
    · refine eventually_nhdsWithin_iff.mpr ?_
      have hz_ev : ∀ᶠ p : ℝ × ℝ in 𝓝 (z0, Real.pi / 2), z0 / 2 < p.1 :=
        (tendsto_fst' (a := z0) (b := Real.pi / 2)).eventually
          ((isOpen_Ioi (a := z0 / 2)).mem_nhds (by linarith : z0 / 2 < z0))
      filter_upwards [hz_ev] with p hpz hmem
      obtain ⟨z, θ⟩ := p
      have hzpos : 0 < z := Work.FTS_StreamBdry.Qd_pos hmem
      have hs2nn : 0 ≤ Work.Construction.s2 θ :=
        Work.FTS_StreamBdry.s2_nonneg_of_Iθ (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)
      have h1 : |z * Work.Spaces.pz (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ := by
        have h0 := hDz z θ hmem 1 (by norm_num)
        rwa [show Work.Spaces.DzIter 1 (psiP αG Ψ) z θ
          = z * Work.Spaces.pz (psiP αG Ψ) z θ from rfl] at h0
      rw [abs_mul, abs_of_pos hzpos] at h1
      have hpz : |Work.Spaces.pz (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ / z := by
        rw [le_div_iff₀ hzpos]
        calc |Work.Spaces.pz (psiP αG Ψ) z θ| * z
            = z * |Work.Spaces.pz (psiP αG Ψ) z θ| := by ring
          _ ≤ M * Work.Construction.s2 θ := h1
      have hMpos : 0 ≤ M * Work.Construction.s2 θ := mul_nonneg hMnn hs2nn
      have h4 : M * Work.Construction.s2 θ / z ≤ M * Work.Construction.s2 θ / (z0 / 2) :=
        div_le_div_of_nonneg_left hMpos (by linarith) (by linarith)
      have h5 : M * Work.Construction.s2 θ / (z0 / 2)
          = 2 * (M * Work.Construction.s2 θ) / z0 := by field_simp
      have h6 : 2 * (M * Work.Construction.s2 θ) / z0
          ≤ 2 * (M * (2 * (Real.pi / 2 - θ))) / z0 := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hz0)
        nlinarith [mul_le_mul_of_nonneg_left
          (s2_le_two_sub (Work.FTS_StreamBdry.Qd_theta_mem hmem)) hMnn]
      have h7 : 2 * (M * (2 * (Real.pi / 2 - θ))) / z0
          = (4 * M / z0) * (Real.pi / 2 - θ) := by ring
      have hgoal : |Work.Spaces.pz (psiP αG Ψ) z θ| ≤ (4 * M / z0) * (Real.pi / 2 - θ) := by
        linarith [hpz, h4, h5 ▸ h4, h6, h7]
      simpa [Function.uncurry, sub_zero] using hgoal
  · -- `∂_z²P → 0`
    refine tendsto_nhdsWithin_of_abs_le (L := 0)
      (g := fun p : ℝ × ℝ => (16 * M / z0 ^ 2) * (Real.pi / 2 - p.2)) ?_ ?_
    · simpa using tendsto_const_mul_sub_snd_zero (16 * M / z0 ^ 2) z0
    · refine eventually_nhdsWithin_iff.mpr ?_
      have hz_ev : ∀ᶠ p : ℝ × ℝ in 𝓝 (z0, Real.pi / 2), z0 / 2 < p.1 :=
        (tendsto_fst' (a := z0) (b := Real.pi / 2)).eventually
          ((isOpen_Ioi (a := z0 / 2)).mem_nhds (by linarith : z0 / 2 < z0))
      filter_upwards [hz_ev] with p hpz hmem
      obtain ⟨z, θ⟩ := p
      have hzpos : 0 < z := Work.FTS_StreamBdry.Qd_pos hmem
      have hθmem := Work.FTS_StreamBdry.Qd_theta_mem hmem
      have hI2 := hDz z θ hmem 2 (by norm_num)
      have hI1 := hDz z θ hmem 1 (by norm_num)
      have hI1' : |z * Work.Spaces.pz (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ := by
        rwa [show Work.Spaces.DzIter 1 (psiP αG Ψ) z θ
          = z * Work.Spaces.pz (psiP αG Ψ) z θ from rfl] at hI1
      have hsplit := DzIter_two_eq (P := psiP αG Ψ) hP2 hmem
      have hkey : z ^ 2 * |Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ)) z θ|
          ≤ 2 * (M * Work.Construction.s2 θ) := by
        rw [← abs_of_nonneg (sq_nonneg z), ← abs_mul]
        have heq : z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ)) z θ
            = Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
              - z * Work.Spaces.pz (psiP αG Ψ) z θ := by linarith [hsplit]
        rw [heq]
        calc |Work.Spaces.DzIter 2 (psiP αG Ψ) z θ - z * Work.Spaces.pz (psiP αG Ψ) z θ|
            ≤ |Work.Spaces.DzIter 2 (psiP αG Ψ) z θ|
              + |z * Work.Spaces.pz (psiP αG Ψ) z θ| := abs_sub _ _
          _ ≤ M * Work.Construction.s2 θ + M * Work.Construction.s2 θ := by linarith [hI2, hI1']
          _ = 2 * (M * Work.Construction.s2 θ) := by ring
      have hpzz : |Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ)) z θ|
          ≤ 2 * (M * Work.Construction.s2 θ) / z ^ 2 := by
        rw [le_div_iff₀ (pow_pos hzpos 2)]
        calc |Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ)) z θ| * z ^ 2
            = z ^ 2 * |Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ)) z θ| := by ring
          _ ≤ 2 * (M * Work.Construction.s2 θ) := hkey
      have hMpos : 0 ≤ 2 * (M * Work.Construction.s2 θ) :=
        mul_nonneg (by norm_num) (mul_nonneg hMnn
          (Work.FTS_StreamBdry.s2_nonneg_of_Iθ (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)))
      have h4 : 2 * (M * Work.Construction.s2 θ) / z ^ 2
          ≤ 2 * (M * Work.Construction.s2 θ) / (z0 / 2) ^ 2 :=
        div_le_div_of_nonneg_left hMpos (pow_pos (by linarith) 2) (by nlinarith)
      have h5 : 2 * (M * Work.Construction.s2 θ) / (z0 / 2) ^ 2
          = 8 * (M * Work.Construction.s2 θ) / z0 ^ 2 := by field_simp; ring
      have h6 : 8 * (M * Work.Construction.s2 θ) / z0 ^ 2
          ≤ 8 * (M * (2 * (Real.pi / 2 - θ))) / z0 ^ 2 := by
        apply div_le_div_of_nonneg_right _ (le_of_lt (pow_pos hz0 2))
        nlinarith [mul_le_mul_of_nonneg_left (s2_le_two_sub hθmem) hMnn]
      have h7 : 8 * (M * (2 * (Real.pi / 2 - θ))) / z0 ^ 2
          = (16 * M / z0 ^ 2) * (Real.pi / 2 - θ) := by ring
      have hgoal : |Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ)) z θ|
          ≤ (16 * M / z0 ^ 2) * (Real.pi / 2 - θ) := by
        linarith [hpzz, h4, h5 ▸ h4, h6, h7]
      simpa [Function.uncurry, sub_zero] using hgoal

end Work.FTS_StreamBdry.SB25Aux4
