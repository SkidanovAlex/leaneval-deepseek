import Mathlib
import Submission.Work.HFN.seminormK_cusp0_half
import Submission.Work.HFN.BlLowTS.Main
import Submission.Work.HFN.HalfFunnel.lowF2_eq_paperLayer
import Submission.Work.HFN.kernelTransform_seminorm_on_compact
import Submission.Work.HFN.Kaxis_local_tail
import Submission.Work.Asymptotics.MFix.Cusp0Flat
import Submission.Work.Asymptotics.seminormK_cusp0_defs
import Submission.Work.Asymptotics.Kcomp_isCompact_subset
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.F2LayerDefs

namespace Work.Asymptotics

open UpperHalfPlane

/-- **The `r`-seminorm bound for the CKMRV layer on the cusp-`0` half tile.**

The half tile `Tregion = {w ∈ 𝒟 : 1/2 ≤ Im (S • w) ≤ 2}` is the union of the two bad-line
neighbourhoods `BLregion (±1)` (where a pole of `z ↦ K(τ,z)` grazes the contour but the *signed*
integral stays bounded), the tangency-arc region `arcT`, and the compact remainder `Kcomp`
(bounded away from `∂𝒟`).  On each of the three the layer seminorm bound is available. -/
theorem LayerSemiTregionTS (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ Work.Asymptotics.Tregion →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s) r‖ ≤ C := by
  intro k l
  have hG : ∀ i j : Fin 2,
      Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (Work.Asymptotics.Gcusp ℓ d i j) :=
    fun i j => Work.HFN.Gcusp_moderate ℓ d i j
  have h8 : d = 8 → ∀ j : Fin 2, Work.Asymptotics.Gcusp ℓ d 1 j = 0 := by
    intro h8d j
    rw [Work.Asymptotics.Gcusp, if_pos h8d]
    funext τ
    fin_cases j <;> simp [Work.Asymptotics.Gcusp8]
  -- ### The bound on the bad-line set, which contains `BLregion (±1)`
  have hLow : ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      Work.Asymptotics.HalfFunnel.lowBadSet τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        layer (Gcusp ℓ d) ℓ d τ s) r‖ ≤ C := by
    obtain ⟨Cks, hCks, hks⟩ := Work.HFN.HalfFunnel.lowBad_kernel_spike_b ℓ d hd
    obtain ⟨Cdec, hCdec, hdec1, hdec2⟩ :=
      Work.HFN.HalfFunnel.lowBad_spike_b_adapter ℓ d hCks hks
    obtain ⟨Ct, Mt, hCt, hMt, htail⟩ := Work.HFN.HalfFunnel.lowBad_Aexp_tail ℓ d hd
    obtain ⟨C, hC, hb⟩ := Work.HFN.blLowF2_seminorm ℓ d hd hCdec hdec1 hdec2
      ⟨Ct, Mt, hCt, hMt, htail⟩
      (fun m N => Work.Asymptotics.HalfFunnel.lowBad_PhiSpike_deriv ℓ d hd m N)
      (fun m N => Work.HFN.HalfFunnel.lowBad_Phi12_deriv ℓ d hd Cdec hCdec hdec1 m N)
      k l
    refine ⟨C, hC, fun τ r hτ => ?_⟩
    have hfun : (fun s : ℝ => layer (Gcusp ℓ d) ℓ d τ s)
        = fun s : ℝ => Work.HFN.blLowF2 ℓ d τ s := by
      funext s
      rw [layer, Work.HFN.blLowF2]
      by_cases hs : s = 0
      · rw [if_pos hs, if_pos hs]
      · rw [if_neg hs, if_neg hs]
        exact (Work.HFN.HalfFunnel.lowF2_eq_paperLayer ℓ d hd Cdec hCdec hdec1 hdec2
          τ s hτ).symm
    rw [hfun]
    exact hb τ r hτ
  obtain ⟨Cl, hCl, hbl⟩ := hLow
  -- ### The bound on the tangency-arc region
  obtain ⟨Ca, hCa, hba⟩ := Work.HFN.arcT_layer_seminorm_clean ℓ d hd (Gcusp ℓ d) hG
    (Work.HFN.arcT_flat_clean ℓ d hd) (Work.HFN.arcT_tail ℓ d hd) k l
  -- ### The bound on the compact remainder
  obtain ⟨Ck, hCk, hbk⟩ := Work.HFN.layer_seminorm_on_compact ℓ d hd (Gcusp ℓ d) hG h8
    Kcomp_isCompact_subset.1 Kcomp_isCompact_subset.2
    (MFix.Kaxis_local_flat ℓ d hd Kcomp_isCompact_subset.1 Kcomp_isCompact_subset.2)
    (Work.HFN.cusp_expansion_of_kernel ℓ d hd Kcomp_isCompact_subset.1 Kcomp_isCompact_subset.2) k l
  refine ⟨Cl + Ca + Ck, by linarith, ?_⟩
  intro w r hw
  obtain ⟨hwD, hlo, hhi⟩ := mem_Tregion.mp hw
  by_cases hbad : ‖(w : ℂ) - ((1 : ℂ) + Complex.I)‖ < 1 / 10 ∨
      ‖(w : ℂ) - ((-1 : ℂ) + Complex.I)‖ < 1 / 10
  · rcases hbad with hb1 | hb2
    · refine le_trans (hbl w r (Work.HFN.BLregion_subset_lowBadSet (n := 1) (Or.inl rfl)
        (Work.HFN.mem_BLregion.mpr ⟨hwD, hlo, hhi, by simpa using hb1⟩))) (by linarith)
    · refine le_trans (hbl w r (Work.HFN.BLregion_subset_lowBadSet (n := -1) (Or.inr rfl)
        (Work.HFN.mem_BLregion.mpr ⟨hwD, hlo, hhi, by simpa using hb2⟩))) (by linarith)
  · by_cases harc : ‖(w : ℂ) - (1 / 2 : ℂ)‖ < 1 / 2 + 1 / 10 ∨
        ‖(w : ℂ) + (1 / 2 : ℂ)‖ < 1 / 2 + 1 / 10
    · exact le_trans (hba w r (mem_arcT.mpr ⟨hwD, hlo, hhi, harc⟩)) (by linarith)
    · have hbad' := not_or.mp hbad
      have harc' := not_or.mp harc
      have hwK : w ∈ Kcomp := subset_closure ⟨⟨hwD, hlo, hhi⟩,
        not_lt.mp hbad'.1, not_lt.mp hbad'.2, not_lt.mp harc'.1, not_lt.mp harc'.2⟩
      exact le_trans (hbk w r hwK) (by linarith)

end Work.Asymptotics
