import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS_BSIdentP.Slim.Dev5
import Submission.Work.FTS_BSIdentP.Slim.DevStub
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.Dev6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdentP.Dev6

open Work.FTS.BSIdent

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdentP.Dev5 (GG)

variable {τ : ℝ}

/-! ## The chain-rule formulas for the meridian derivatives -/

theorem pdZ_merPsiT_eq {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hB : 0 < B τ) {r z : ℝ} (hr : 0 < r) (hz : z ≠ 0) :
    Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z
      = 2 * z * (A τ)⁻¹ * GG Φ τ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP r z)
        + (A τ)⁻¹ *
          (Work.FTS.Regularity.pExp α * z * (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
              * Work.Cyl.pdR (GG Φ τ) (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP r z)
            + r * Work.Cyl.pdZ (GG Φ τ) (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP r z)) := by
  rw [Dev5.merPsiT_eq_core α A B Φ C t hτ]
  refine Work.FTS.BSIdent.Cyl.pdZ_psiCore_eq (G := GG Φ τ) ?hG hr
  refine Dev5.diffAt2_GG_of_ne (τ := τ) hsm ?_ ?_ ?_
  · have := Work.Cyl.rhoP_pos (z := z) hr
    have : (0:ℝ) < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ :=
      div_pos (Real.rpow_pos_of_pos this _) hB
    linarith
  · simp only [Work.Cyl.thetaP]
    exact fun h => hz (by
      have hzr : z / r = 0 := Real.arctan_eq_zero_iff.mp h
      rcases div_eq_zero_iff.mp hzr with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hr))
  · have := Work.FTS.BSIdent.Cyl.abs_thetaP_lt r z
    linarith [Real.pi_pos]

theorem pdR_merPsiT_eq {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hB : 0 < B τ) {r z : ℝ} (hr : 0 < r) (hz : z ≠ 0) :
    Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z
      = 2 * r * (A τ)⁻¹ * GG Φ τ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP r z)
        + (A τ)⁻¹ *
          (Work.FTS.Regularity.pExp α * r * (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
              * Work.Cyl.pdR (GG Φ τ) (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP r z)
            + (-z) * Work.Cyl.pdZ (GG Φ τ)
                  (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
                  (Work.Cyl.thetaP r z)) := by
  rw [Dev5.merPsiT_eq_core α A B Φ C t hτ]
  refine Work.FTS.BSIdent.Cyl.pdR_psiCore_eq (G := GG Φ τ) ?hG hr
  refine Dev5.diffAt2_GG_of_ne (τ := τ) hsm ?_ ?_ ?_
  · have := Work.Cyl.rhoP_pos (z := z) hr
    have : (0:ℝ) < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ :=
      div_pos (Real.rpow_pos_of_pos this _) hB
    linarith
  · simp only [Work.Cyl.thetaP]
    exact fun h => hz (by
      have hzr : z / r = 0 := Real.arctan_eq_zero_iff.mp h
      rcases div_eq_zero_iff.mp hzr with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hr))
  · have := Work.FTS.BSIdent.Cyl.abs_thetaP_lt r z
    linarith [Real.pi_pos]

end Work.FTS.BSIdentP.Dev6
end
-- ===== merged: Submission.Work.FTS_BSIdentP.Slim.Dev7 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdentP.Dev7

open Work.FTS.BSIdent

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdentP.Dev5 (GG)

variable {τ : ℝ}

/-- Along the filter `r → 0⁺`, `z → z₀ > 0`, the ratio `z/r` tends to `+∞`. -/
theorem tendsto_snd_div_fst_atTop {z₀ : ℝ} (hz₀ : 0 < z₀) :
    Tendsto (fun p : ℝ × ℝ => p.2 / p.1) (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) atTop := by
  have h1 : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 0) := by
    have := (continuousAt_fst (p := ((0:ℝ), z₀))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 < p.1}))
    simpa using this
  have h2 : Tendsto (fun p : ℝ × ℝ => p.2) (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 z₀) := by
    have := (continuousAt_snd (p := ((0:ℝ), z₀))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 < p.1}))
    simpa using this
  rw [tendsto_atTop]
  intro M
  rcases le_or_gt M 0 with hM | hM
  · have e2 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)), z₀ / 2 < p.2 := by
      have hnb : Set.Ioi (z₀ / 2) ∈ 𝓝 z₀ := Ioi_mem_nhds (by linarith)
      exact h2.eventually hnb
    have e1 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)), 0 < p.1 := self_mem_nhdsWithin
    filter_upwards [e1, e2] with p hp1 hp2
    have : 0 < p.2 / p.1 := div_pos (by linarith) hp1
    linarith
  · have e1 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)), 0 < p.1 := self_mem_nhdsWithin
    have e2 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)), p.1 < z₀ / (2 * M) := by
      have hnb : Set.Iio (z₀ / (2 * M)) ∈ 𝓝 (0:ℝ) := Iio_mem_nhds (by positivity)
      exact h1.eventually hnb
    have e3 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)), z₀ / 2 < p.2 := by
      have hnb : Set.Ioi (z₀ / 2) ∈ 𝓝 z₀ := Ioi_mem_nhds (by linarith)
      exact h2.eventually hnb
    filter_upwards [e1, e2, e3] with p hp1 hp2 hp3
    rw [le_div_iff₀ hp1]
    have hkey : M * (z₀ / (2 * M)) = z₀ / 2 := by field_simp
    have := mul_le_mul_of_nonneg_left hp2.le hM.le
    linarith [this]

/-- Along the filter `r → 0⁺`, `z → z₀ < 0`, the ratio `z/r` tends to `-∞`. -/
theorem tendsto_snd_div_fst_atBot {z₀ : ℝ} (hz₀ : z₀ < 0) :
    Tendsto (fun p : ℝ × ℝ => p.2 / p.1) (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) atBot := by
  have h1 : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 0) := by
    have := (continuousAt_fst (p := ((0:ℝ), z₀))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 < p.1}))
    simpa using this
  have h2 : Tendsto (fun p : ℝ × ℝ => p.2) (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 z₀) := by
    have := (continuousAt_snd (p := ((0:ℝ), z₀))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 < p.1}))
    simpa using this
  rw [tendsto_atBot]
  intro M
  rcases le_or_gt 0 M with hM | hM
  · have e2 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)), p.2 < z₀ / 2 := by
      have hnb : Set.Iio (z₀ / 2) ∈ 𝓝 z₀ := Iio_mem_nhds (by linarith)
      exact h2.eventually hnb
    have e1 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)), 0 < p.1 := self_mem_nhdsWithin
    filter_upwards [e1, e2] with p hp1 hp2
    have : p.2 / p.1 < 0 := div_neg_of_neg_of_pos (by linarith) hp1
    linarith
  · have hMpos : 0 < -M := by linarith
    have e1 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)), 0 < p.1 := self_mem_nhdsWithin
    have e2 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)), p.1 < (-z₀) / (2 * (-M)) := by
      have hnb : Set.Iio ((-z₀) / (2 * (-M))) ∈ 𝓝 (0:ℝ) := Iio_mem_nhds (by
        have h1 : 0 < -z₀ := by linarith
        have h2 : 0 < -M := by linarith
        positivity)
      exact h1.eventually hnb
    have e3 : ∀ᶠ p in (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)), p.2 < z₀ / 2 := by
      have hnb : Set.Iio (z₀ / 2) ∈ 𝓝 z₀ := Iio_mem_nhds (by linarith)
      exact h2.eventually hnb
    filter_upwards [e1, e2, e3] with p hp1 hp2 hp3
    rw [div_le_iff₀ hp1]
    have hkey : (-M) * ((-z₀) / (2 * (-M))) = (-z₀) / 2 := by
      field_simp [ne_of_lt hM]
    have h4 : (-M) * p.1 < (-M) * ((-z₀) / (2 * (-M))) := mul_lt_mul_of_pos_left hp2 hMpos
    linarith

/-- Along `r → 0⁺`, `z → z₀ > 0`, the polar angle tends to `π/2`. -/
theorem tendsto_thetaP_pi_div_two {z₀ : ℝ} (hz₀ : 0 < z₀) :
    Tendsto (fun p : ℝ × ℝ => Work.Cyl.thetaP p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 (Real.pi / 2)) := by
  have h := Real.tendsto_arctan_atTop.comp (tendsto_snd_div_fst_atTop hz₀)
  exact h.mono_right (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2)))

theorem tendsto_thetaP_neg_pi_div_two {z₀ : ℝ} (hz₀ : z₀ < 0) :
    Tendsto (fun p : ℝ × ℝ => Work.Cyl.thetaP p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] (0, z₀)) (𝓝 (-(Real.pi / 2))) := by
  have h := Real.tendsto_arctan_atBot.comp (tendsto_snd_div_fst_atBot hz₀)
  exact h.mono_right (nhdsWithin_le_nhds (s := Set.Ioi (-(Real.pi / 2))))

end Work.FTS.BSIdentP.Dev7
end
