/-
# `Work.FTS.PhiStar.Psi0_exists` — the explicit angular model of `Φ_*` (P1)

There is a universal constant `C` such that for every `0 < α ≤ 1/4` there is an explicit
function `ψ : ℝ → ℝ` with

* `ψ` of class `C^∞` on `(0,π/2)`, continuous on `[0,π/2]`, `ψ 0 = ψ(π/2) = 0`;
* `Lzero1 ψ = Γ̄` on `(0,π/2)`, `∫_0^{π/2} ψ sinθcos²θ = 0`;
* `WlInfMem α 5 (ψ'')` and `WlInf α 5 (ψ'') ≤ C`;
* `|D_θ^j ψ| ≤ C sin 2θ` for `j ≤ 6`.

The witness is `psiSol α` (`Psi0Ode.lean`), the explicit solution of the angular model
`ψ = sin 2θ (Kc + w₀)` with `w₀' = P/sin²θ`, `P = G₀/(2cos³θ)`, `G₀ = ∫_θ^{π/2} S C² Γ̄`.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.Psi0Ident
import Submission.Work.FTS.PhiStar.Psi0Classes
import Submission.Work.FTS.PhiStar.Psi0Aux.cos_sq_Gam_div_sin_bounds
import Submission.Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired
import Submission.Work.FTS.PhiStar.Psi0Aux.GamBar_dthU_le
import Submission.Work.FTS.PhiStar.Psi0Est.exists_ZClass
import Submission.Work.FTS.PhiStar.Psi0Est.exists_AClass
import Submission.Work.FTS.PhiStar.Psi0Est.exists_WBound
import Submission.Work.FTS.PhiStar.Psi0Est.WlInf_psiSol

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem Psi0_exists : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∃ ψ : ℝ → ℝ,
    ContDiffOn ℝ Work.Stability.smoothOrder ψ (Set.Ioo 0 (π / 2)) ∧
    ContinuousOn ψ (Set.Icc 0 (π / 2)) ∧ ψ 0 = 0 ∧ ψ (π / 2) = 0 ∧
    (∀ θ ∈ Set.Ioo 0 (π / 2), Work.FTS.EllipticEst.Lzero1 ψ θ = Work.FTS.VocabO.GamBar α θ) ∧
    (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0 ∧
    Work.Spaces.WlInfMem α 5 (fun _ θ => iteratedDeriv 2 ψ θ) ∧
    Work.Spaces.WlInf α 5 (fun _ θ => iteratedDeriv 2 ψ θ) ≤ C ∧
    (∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.DthIter j (fun _ θ' => ψ θ') 0 θ| ≤ C * Real.sin (2 * θ)) := by
  -- the three auxiliary classes
  have hI : ∃ K : ℝ, IClass K := by
    obtain ⟨K, hKpos, hK1, hK2⟩ := Psi0Aux.cos_sq_Gam_div_sin_bounds
    exact ⟨K, hKpos, hK1, hK2⟩
  have hb : ∃ b : ℕ → ℝ, ElemClass b := by
    obtain ⟨b, hb0, hb1, hb2, hb3, hb4⟩ := Psi0Aux.dthU_iter_elementary_bounds_repaired
    exact ⟨b, hb0, hb2, hb3, hb4⟩
  have hH : ∃ cc dd : ℕ → ℝ, HClass cc dd := by
    obtain ⟨_, hHL⟩ := Psi0Aux.GamBar_dthU_le
    obtain ⟨cc, dd, hcc0, hdd0, hccdd⟩ := hHL
    exact ⟨cc, dd, hcc0, hdd0, hccdd⟩
  obtain ⟨κ, ell, hZ⟩ := Psi0Est.exists_ZClass hI hb hH
  obtain ⟨ν, hA⟩ := Psi0Est.exists_AClass ⟨κ, ell, hZ⟩
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Psi0Est.exists_WBound
    (fun α hα hα1 θ hθ => psiSol_sndDeriv α hα hα1 hθ) ⟨κ, ell, hZ⟩ ⟨ν, hA⟩ hH
  have hνnn : ∀ j, 0 ≤ ν j := hA.1
  refine ⟨max (6 * C₁) (max 1 ((∑ j ∈ Finset.range 7, ν j) + 1)), ?_, fun α hα hα1 => ?_⟩
  · refine lt_of_lt_of_le (by norm_num :
      (0:ℝ) < max 1 ((∑ j ∈ Finset.range 7, ν j) + 1)) (le_max_right _ _)
  · obtain ⟨hWmem, hWle⟩ := Psi0Est.WlInf_psiSol C₁ hC₁pos α hα hα1
      (fun θ hθ => (hC₁ α hα hα1 θ hθ).1)
      (fun j hj1 hj5 θ hθ => (hC₁ α hα hα1 θ hθ).2 j hj1 hj5)
    refine ⟨psiSol α, contDiffOn_psiSol α hα hα1, continuousOn_psiSol α hα hα1,
      psiSol_zero α, psiSol_pi_div_two α,
      (fun θ hθ => psiSol_ode α hα hα1 hθ), psiSol_moment α hα hα1, hWmem, ?_, ?_⟩
    · refine le_trans hWle (le_trans (le_max_left _ _) le_rfl)
    · intro j hj6 θ hθ
      have hAj := hA.2 α hα hα1 j hj6 θ hθ
      have hDth : Work.Spaces.DthIter j (fun _ θ' => psiSol α θ') 0 θ
          = Work.Spaces.dthU^[j] (psiSol α) θ := by
        have h := Work.Spaces.DthIter_decomp j (psiSol α) (fun _ : ℝ => (1:ℝ)) 0 θ
        simpa using h
      rw [hDth]
      have hmem : j ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
      have hνle : ν j ≤ (∑ i ∈ Finset.range 7, ν i) + 1 := by
        have := Finset.single_le_sum (fun i _ => hνnn i) hmem
        linarith
      have hmain : ν j ≤ max (6 * C₁) (max 1 ((∑ i ∈ Finset.range 7, ν i) + 1)) :=
        le_trans (le_trans hνle (le_max_right 1 _)) (le_max_right (6 * C₁) _)
      exact le_trans hAj (mul_le_mul_of_nonneg_right hmain
        (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩))

end Work.FTS.PhiStar
