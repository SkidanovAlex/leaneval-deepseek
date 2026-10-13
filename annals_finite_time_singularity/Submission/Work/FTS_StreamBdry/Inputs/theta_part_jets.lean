import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.SysAux.FK_L12_slice_facts
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffSmooth
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_aux
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_l12
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

theorem theta_part_jets {a C₀ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S →
      Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ, 0 ≤ τ → ∃ C : ℝ, 0 < C ∧
      (∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter k (fun z _ => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z) z 0| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp a)
          (Work.Construction.Theta (Work.FTS.Regularity.pExp a)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ)) z θ
          / Real.sin (2 * θ)) z θ| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (fun z θ => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z
          * Work.Construction.c2m θ) z θ| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.Construction.Vop (Work.Construction.Theta
          (Work.FTS.Regularity.pExp a) (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ)))
          z θ| ≤ C) := by
  intro τ hτ
  obtain ⟨CL, hCL0, hL12jet, hFKjet, hL12diff, hFKdiff, hL12d⟩ :=
    theta_part_l12 ha ha13 hOK τ hτ
  obtain ⟨Cθ, hCθ0, hc2, hc3, hc4⟩ := theta_part_theta
    (α := Work.FTS.Regularity.pExp a) (Work.FTS.Regularity.pExp_pos ha) hCL0
    hL12jet hFKjet hL12diff hFKdiff hL12d
  refine ⟨max CL Cθ + 1, by
      have h : (0 : ℝ) ≤ max CL Cθ := le_trans hCL0.le (le_max_left _ _)
      linarith, ?_, ?_, ?_, ?_⟩
  · intro k hk z hz
    have h1 := hL12jet k hk z hz
    rw [← Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z) k z 0] at h1
    exact le_trans h1 (by have h : CL ≤ max CL Cθ := le_max_left _ _; linarith)
  · intro j i hji z θ hz hθ0 hθ1
    exact le_trans (hc2 j i hji z θ hz hθ0 hθ1)
      (by have h : Cθ ≤ max CL Cθ := le_max_right _ _; linarith)
  · intro j i hji z θ hz hθ0 hθ1
    exact le_trans (hc3 j i hji z θ hz hθ0 hθ1)
      (by have h : Cθ ≤ max CL Cθ := le_max_right _ _; linarith)
  · intro j i hji z θ hz hθ0 hθ1
    exact le_trans (hc4 j i hji z θ hz hθ0 hθ1)
      (by have h : Cθ ≤ max CL Cθ := le_max_right _ _; linarith)

end Work.FTS_StreamBdry.Inputs
