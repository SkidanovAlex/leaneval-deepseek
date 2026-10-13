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
import Submission.Work.FTS_StreamBdry.SB25.axis_tan_bound
import Submission.Work.FTS_StreamBdry.SB25Aux4.EdgeAxisAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux4.psiP_edge_axis_pth`

The limit of `∂_θP` at `(z₀, π/2)`: it is `Vb z₀ / 2`.

`∂_θP = V(P) + tan θ·P`; the edge trace `Vb` of `V(P)` gives `V(P) → Vb z` at rate `K_V`, and
`SB25.axis_tan_bound` per `z`-slice turns that rate into `tan θ·P → -Vb z/2` (also at rate `K_V`),
so `∂_θP → Vb z₀/2`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux4

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

theorem psiP_edge_axis_pth {αG M Mf : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M)
    (Vb : ℝ → ℝ) (hVbc : ContinuousOn Vb (Set.Ioi 0))
    (hVb : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Construction.Vop (psiP αG Ψ) z θ - Vb z|
        ≤ ((αG ^ 2 + 5 * αG + 6) * M + Mf) * (Real.pi / 2 - θ)) :
    ∀ z0 : ℝ, 0 < z0 →
      ∃ l, Tendsto (Function.uncurry (Work.Spaces.pth (psiP αG Ψ)))
        (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l) := by
  have hMnn : 0 ≤ M := by
    have h1 := Work.FTS_StreamBdry.SlotBd.Dz_le hslot (z := 1) (θ := Real.pi / 4)
      Work.FTS_StreamBdry.SB1.Qd_nonempty (j := 0) (by norm_num)
    exact le_trans (abs_nonneg _) h1
  have hDz := Work.FTS_StreamBdry.SB3.psiP_DzLe (αG := αG) (M := M) hαG h3 hslot
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 (αG := αG) (M := M) hαG h3 hslot
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  intro z0 hz0
  have hVbc_at : ContinuousAt Vb z0 := hVbc.continuousAt (isOpen_Ioi.mem_nhds hz0)
  set CV := |Vb z0| + 1 with hCV
  have hCVnn : 0 ≤ CV := by rw [hCV]; positivity
  have hCV_ev : ∀ᶠ p : ℝ × ℝ in 𝓝 (z0, Real.pi / 2), |Vb p.1| ≤ CV := by
    have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (z0, Real.pi / 2), dist (Vb p.1) (Vb z0) < 1 :=
      hVbc_at.tendsto.comp (tendsto_fst' (a := z0) (b := Real.pi / 2))
        |>.eventually (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [h1] with p hp
    rw [Real.dist_eq] at hp
    have h2 : |Vb p.1| ≤ |Vb p.1 - Vb z0| + |Vb z0| := by
      calc |Vb p.1| = |(Vb p.1 - Vb z0) + Vb z0| := by ring_nf
        _ ≤ |Vb p.1 - Vb z0| + |Vb z0| := abs_add_le _ _
    rw [hCV]; linarith
  refine ⟨Vb z0 / 2, ?_⟩
  refine tendsto_nhdsWithin_of_abs_le (L := Vb z0 / 2)
    (g := fun p : ℝ × ℝ => |Vb p.1 - Vb z0| / 2
      + (((αG ^ 2 + 5 * αG + 6) * M + Mf) + CV * (Real.pi / 2)
          + 3 * ((αG ^ 2 + 5 * αG + 6) * M + Mf)) * (Real.pi / 2 - p.2)) ?_ ?_
  · have h1 : Tendsto (fun p : ℝ × ℝ => |Vb p.1 - Vb z0| / 2)
        (𝓝 (z0, Real.pi / 2)) (𝓝 0) := by
      simpa using (tendsto_abs_sub_const hVbc_at).div_const 2
    have h2 := tendsto_const_mul_sub_snd_zero
      (((αG ^ 2 + 5 * αG + 6) * M + Mf) + CV * (Real.pi / 2)
        + 3 * ((αG ^ 2 + 5 * αG + 6) * M + Mf)) z0
    simpa using h1.add h2
  · refine eventually_nhdsWithin_iff.mpr ?_
    filter_upwards [hCV_ev] with p hpV hmem
    obtain ⟨z, θ⟩ := p
    have hpV' : |Vb z| ≤ CV := hpV
    have hθ := Work.FTS_StreamBdry.Qd_theta_mem hmem
    have hzpos : 0 < z := Work.FTS_StreamBdry.Qd_pos hmem
    have hb3 := Work.FTS_StreamBdry.SB25.axis_tan_bound (fun θ' => psiP αG Ψ z θ')
      (Vb z) ((αG ^ 2 + 5 * αG + 6) * M + Mf) M
    simp only [Work.FTS_StreamBdry.SB25.AxisTanBound] at hb3
    have hdiff : ∀ θ' ∈ Ioo (0 : ℝ) (Real.pi / 2),
        DifferentiableAt ℝ (fun θ'' => psiP αG Ψ z θ'') θ' := by
      intro θ' hθ'
      have hmem' : (z, θ') ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hθ'.1, hθ'.2⟩
      exact Work.Spaces.differentiableAt_curry_right
        ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem'))
    have hbd : ∀ θ' ∈ Ioo (0 : ℝ) (Real.pi / 2),
        |(fun θ'' => psiP αG Ψ z θ'') θ'| ≤ M := by
      intro θ' hθ'
      have hmem' : (z, θ') ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hθ'.1, hθ'.2⟩
      have h0 := hDz z θ' hmem' 0 (by norm_num)
      rw [Work.Spaces.DzIter_zero] at h0
      have hs1 : Work.Construction.s2 θ' ≤ 1 := by
        rw [Work.Construction.s2_eq]; exact Real.sin_le_one _
      exact le_trans h0 (by simpa using mul_le_of_le_one_right hMnn hs1)
    have hcl : ∀ θ' ∈ Ioo (0 : ℝ) (Real.pi / 2),
        |deriv (fun θ'' => psiP αG Ψ z θ'') θ' - Real.tan θ' * psiP αG Ψ z θ' - Vb z|
          ≤ ((αG ^ 2 + 5 * αG + 6) * M + Mf) * (Real.pi / 2 - θ') := by
      intro θ' hθ'
      have hmem' : (z, θ') ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hθ'.1, hθ'.2⟩
      show |Work.Construction.Vop (psiP αG Ψ) z θ' - Vb z| ≤ _
      exact hVb z θ' hmem'
    have hres := hb3 hdiff hbd hcl θ hθ
    have hVbd2 : |Work.Construction.Vop (psiP αG Ψ) z θ - Vb z|
        ≤ ((αG ^ 2 + 5 * αG + 6) * M + Mf) * (Real.pi / 2 - θ) := hVb z θ hmem
    have hsq : (Real.pi / 2 - θ) ^ 2 ≤ (Real.pi / 2) * (Real.pi / 2 - θ) := by
      have hp0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
      have hp1 : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
      nlinarith
    have hmid : |Real.tan θ * psiP αG Ψ z θ + Vb z / 2|
        ≤ CV * (Real.pi / 2) * (Real.pi / 2 - θ)
          + 3 * ((αG ^ 2 + 5 * αG + 6) * M + Mf) * (Real.pi / 2 - θ) := by
      have hp0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
      have h1 : |Vb z| * (Real.pi / 2 - θ) ^ 2 ≤ CV * ((Real.pi / 2) * (Real.pi / 2 - θ)) := by
        nlinarith [hsq, hpV', hp0, hCVnn]
      linarith [hres, h1]
    have hident : Work.Spaces.pth (psiP αG Ψ) z θ - Vb z0 / 2
        = (Work.Construction.Vop (psiP αG Ψ) z θ - Vb z)
          + (Real.tan θ * psiP αG Ψ z θ + Vb z / 2) + (Vb z - Vb z0) / 2 := by
      rw [Work.Construction.Vop]; ring
    have hgoal : |Work.Spaces.pth (psiP αG Ψ) z θ - Vb z0 / 2|
        ≤ |Vb z - Vb z0| / 2
          + (((αG ^ 2 + 5 * αG + 6) * M + Mf) + CV * (Real.pi / 2)
              + 3 * ((αG ^ 2 + 5 * αG + 6) * M + Mf)) * (Real.pi / 2 - θ) := by
      rw [hident]
      calc |(Work.Construction.Vop (psiP αG Ψ) z θ - Vb z)
              + (Real.tan θ * psiP αG Ψ z θ + Vb z / 2) + (Vb z - Vb z0) / 2|
          ≤ |Work.Construction.Vop (psiP αG Ψ) z θ - Vb z|
            + |Real.tan θ * psiP αG Ψ z θ + Vb z / 2| + |(Vb z - Vb z0) / 2| := by
            linarith [abs_add_three (Work.Construction.Vop (psiP αG Ψ) z θ - Vb z)
              (Real.tan θ * psiP αG Ψ z θ + Vb z / 2) ((Vb z - Vb z0) / 2)]
        _ ≤ |Vb z - Vb z0| / 2
              + (((αG ^ 2 + 5 * αG + 6) * M + Mf) + CV * (Real.pi / 2)
                  + 3 * ((αG ^ 2 + 5 * αG + 6) * M + Mf)) * (Real.pi / 2 - θ) := by
            rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            nlinarith [hVbd2, hmid]
    simpa [Function.uncurry] using hgoal

end Work.FTS_StreamBdry.SB25Aux4
