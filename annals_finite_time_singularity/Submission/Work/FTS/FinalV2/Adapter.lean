import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.FinalV2.TauExt
import Submission.Work.FTS.FinalV2.LocVanish
import Submission.Work.FTS.Final.Recon.diffAt2_merProfile
import Submission.Work.FTS.Top.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FinalV2.Adapter` — PROVED (curric-46 lead install, 2026-10-10)

`exists_blowupAt_of_inputs'`: `∃ α, Inputs' α` gives the blow-up. The firing
(`FireFix.blowupAtTop_of_regPkg'`) runs on `extG G` with `Φ := psiFire Φs E G`, where
`G := tauExt g` is the right-Taylor τ-extension of the strong solution `g` (REVIEW FIX-2); every
conjunct of `Inputs'` is applied at `G` through `sol_dynOK'_tauExt`. Old conjunct (11) is proved
here (`dynOK_extG` + `diffAt2_merProfile`); (12), (13) are no longer inputs.

`theorem_1_of_inputs'` is `Final.Wire.theorem_1_of_inputs` re-pointed at `Inputs'`.

**RegExport REVIEW F1 (2026-10-10).** (7″) is applied at `G = tauExt g₁` with `hdat` from the (4′)
initial-value clause (+ `tauExt_of_nonneg`), and the firing runs on the SANITISED `extG (gS α G)`;
`hsmall` is transported by `extG_gS_of_mem`, `hMer`/`hW` by `merProfile_gS`, `hHid` by
`physOmega_gS` (`FinalV2.Sanitize`). `hPsi`, `ClockData` are untouched.

**StreamBdry REVIEW FIX-A (2026-10-10).** (9″) is applied at `G := gS α g` with `hRegG` and
`hG` by `simp [gS]`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.FinalV2

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Physical (PhysClock)
open Work.FTS.Final
open Work.FTS.FinalClock
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG)

set_option autoImplicit false

theorem exists_blowupAt_of_inputs' (h : ∃ α : ℝ, Inputs' α) :
    ∃ α : ℝ≥0, 0 < (α : ℝ) ∧ Nonempty (Work.FTS.Top.BlowupAt α 1) := by
  obtain ⟨α, hα, hα13, hpress, core⟩ := h
  obtain ⟨Ce, Cs, Cg, C₀, K, ρ, E, Φs, _hCe, hCg, hC₀, hK, hscale, _hρ, _hEll, _hEL, _hML,
    _hMLip, _hStar, hEps, hDat, hDyn, hSup, hMu, hReg, hMer, hHid, hPsi⟩ := core
  have hαG : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the datum
  obtain ⟨L₀, _hL₀, hL⟩ := Work.FTS.LocData6.locG6_data (pExp α) hαG hαG1 K hK
  obtain ⟨β, _hβ, _hAdm, hRegQ, _hGal, hL12, hXn4₀, hXn6₀⟩ := hL (max L₀ 1) (le_max_left _ _)
  have hU := hEps K (Work.FTS.LocData6.locG6 (pExp α) (max L₀ 1) β)
      hRegQ (locG6_vanish hαG _ _) (hDat (max L₀ 1) β (le_max_right _ _) hRegQ hL12) hXn4₀ hXn6₀
  obtain ⟨g₁, hSol₁, hinit₁, hOK₁⟩ := hDyn (Work.FTS.LocData6.locG6 (pExp α) (max L₀ 1) β) K hU
  -- REVIEW FIX-2: work with the right-Taylor τ-extension `g := tauExt g₁`
  set g : Fam := tauExt g₁ with hgdef
  obtain ⟨hSol, hOK⟩ := sol_dynOK'_tauExt hSol₁ hOK₁
  have hdat : ∃ L β' : ℝ, 1 ≤ L ∧ ∀ z θ,
      g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β' z θ :=
    ⟨max L₀ 1, β, le_max_right _ _, fun z θ => by
      show tauExt g₁ z θ 0 = _
      rw [tauExt_of_nonneg _ le_rfl]
      exact hinit₁ z θ⟩
  have hRegG := hReg g hSol hOK hdat
  rw [hgdef, tauExt_tauExt, ← hgdef] at hRegG
  -- the clock
  obtain ⟨hμ, hc, _hμh⟩ := hMu g hSol hOK
  set m : ℝ → ℝ := maxMu (pExp α) (PsiCan Φs E g) g with hm
  have hcm : Continuous m := continuous_maxExt hc
  have hmb : MuBound m := maxExt_bound hμ
  set C : PhysClock := physClockOf m hcm hmb with hC
  set A : ℝ → ℝ := ampA m with hA
  set B : ℝ → ℝ := ampB m with hB
  have hCmuA : C.mu = m := rfl
  have hClock : ClockData (pExp α) (PsiCan Φs E g) g A B C := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro τ hτ
      rw [hCmuA, hm, maxMu, max_eq_left hτ]
    · intro τ hτ
      rw [hA]
      rfl
    · intro τ hτ
      rw [hA, hCmuA]
      simpa only [ampA] using Avort_hasDerivAt hcm τ
    · intro τ hτ
      rw [hB, hCmuA]
      have h := hasDerivAt_Bdyn_of_clock m hcm hmb 1 τ
      rw [physClockOf_mu] at h
      simpa only [ampB, one_mul] using h
    · intro τ hτ
      rw [hB]
      simpa only [ampB] using Bdyn_pos m τ
  -- the smallness of the extension
  have hsmall : ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |extG g z θ τ| ≤ 3 * α / 200 := by
    intro τ hτ z hz θ hθ
    have h1 := hSup g hOK τ hτ z hz θ hθ
    have hkey : Cg * C₀ * (9 * α) ≤ 3 / 200 := by
      have h1' : (α * (600 * Cg * C₀)) * (1 / 200 : ℝ) ≤ 1 * (1 / 200 : ℝ) :=
        mul_le_mul_of_nonneg_right hscale (by norm_num)
      nlinarith [h1', hα, hCg, hC₀.le]
    have h3 : Cg * (C₀ * (pExp α) ^ 2) ≤ 3 * α / 200 := by
      rw [Work.FTS.Regularity.pExp_eq]
      have h : Cg * (C₀ * (3 * α) ^ 2) = α * (Cg * C₀ * (9 * α)) := by ring
      rw [h]
      calc α * (Cg * C₀ * (9 * α)) ≤ α * (3 / 200) := mul_le_mul_of_nonneg_left hkey hα.le
        _ = 3 * α / 200 := by ring
    exact le_trans h1 h3
  -- the D²-clause, now PROVED for the extension (was conjunct (11))
  have hOKe : DynOK (pExp α) C₀ (extG g) := Work.FTS.Final.ExtG.dynOK_extG hαG hOK.1
  have hW : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      Work.Cyl.DiffAt2 (fun r z => Work.FTS.Physical.merProfile α A B (extG g) C r z t) r z :=
    fun t ht r z hr hz =>
      Work.FTS.Final.Recon.diffAt2_merProfile (g := extG g) (A := A) (B := B) (C := C)
        hOKe.1.c4 (fun τ hτ => hClock.2.2.2.2 τ hτ) ht hr hz
  -- transport to the sanitised family (RegExport REVIEW F1)
  have hsmallS : ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |extG (gS α g) z θ τ| ≤ 3 * α / 200 := by
    intro τ hτ z hz θ hθ
    rw [extG_gS_of_mem α g hθ.1 hθ.2]
    exact hsmall τ hτ z hz θ hθ
  have hMerS := hMer g A B C hSol hOK hClock
  rw [← merProfile_gS α A B g C] at hMerS
  have hGS : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → gS α g z θ τ = g z θ τ :=
    fun z θ τ hz hθ _ => by simp [gS, hz, hθ.1, hθ.2]
  have hHidS := hHid g (gS α g) A B C hSol hOK hClock hRegG hGS
  simp only [← physOmega_gS α A B g C] at hHidS
  have hWS : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      Work.Cyl.DiffAt2
        (fun r z => Work.FTS.Physical.merProfile α A B (extG (gS α g)) C r z t) r z := by
    rw [merProfile_gS α A B g C]
    exact hW
  -- the firing on `extG (gS α g)` with `Φ := psiFire Φs E g`, then the rescale
  exact ⟨⟨α, hα.le⟩, hα, ⟨Work.FTS.Top.blowupAt_one_of_blowupAt
    (Work.FTS.FireFix.blowupAtTop_of_regPkg' (α := ⟨α, hα.le⟩) (A := A) (B := B)
      (g := extG (gS α g)) (C := C) (Φ := psiFire Φs E g)
      (hRegG) hClock.2.1 hsmallS Work.FTS.BSSwirl.biotSavartSwirl hpress
      hMerS hHidS (hPsi g A B C hSol hOK hClock) hWS)⟩⟩

open FiniteTimeSingularity Gradient Matrix MeasureTheory in
/-- **The challenge statement from the corrected bundle** (`Final.Wire.theorem_1_of_inputs`
re-pointed at `Inputs'`; same conclusion, character for character). -/
theorem theorem_1_of_inputs' (h : ∃ α : ℝ, Inputs' α) :
    ∃ β > 0, ∃ u₀ : Work.FTS.Top.R3 → Work.FTS.Top.R3, div u₀ = 0 ∧ IsOdd u₀ ∧
      IsContDiffHolder ℝ β u₀ ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : Work.FTS.Top.R3, ‖vorticity u₀ x‖ ≤ C / (‖x‖ ^ (β : ℝ) + 1)) ∧
        ∃ p : Work.FTS.Top.R3 → ℝ → ℝ, ∃ u : Work.FTS.Top.R3 → ℝ → Work.FTS.Top.R3,
            (∀ t ∈ Set.Ico 0 1, IsOdd (u · t)) ∧
            IsLocalEulerEquationSolution p u₀ 1 u ∧
              (∀ T ∈ Set.Ioo 0 1,
                IsContDiffHolderOn ℝ β u.uncurry (Set.univ ×ˢ Set.Icc 0 T)) ∧
                Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u y s) x‖)
                  (𝓝[<] 1) Filter.atTop := by
  obtain ⟨α, hα, ⟨B⟩⟩ := exists_blowupAt_of_inputs' h
  exact Work.FTS.Top.theorem_1_of_blowupAt hα B

end Work.FTS.FinalV2
